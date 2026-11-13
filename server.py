"""Txn Fee Sum — exact Etherscan transaction-fee totals for a block range.

Run start.bat, or:  python server.py
Self-test:         python server.py --self-test
"""

from __future__ import annotations

import argparse
import json
import math
import queue
import re
import sqlite3
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DB_PATH = ROOT / "data" / "cache.db"
STATIC = ROOT / "static" / "index.html"
API_URL = "https://api.etherscan.io/v2/api"
WINDOW_LIMIT = 10_000
REORG_DEPTH = 64
ADDR_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")
SUB = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
RPCS = (
    "https://ethereum.publicnode.com",
    "https://eth.llamarpc.com",
    "https://rpc.ankr.com/eth",
    "https://cloudflare-eth.com",
)
PLANS = {
    "free": (1000, 3),
    "lite": (10000, 5),
    "standard": (10000, 10),
    "advanced": (10000, 20),
    "professional": (10000, 30),
}

scan_lock = threading.Lock()


class ApiError(Exception):
    pass


class RateLimit(ApiError):
    pass


class Cancelled(Exception):
    pass


# --- Etherscan number formatting (integer wei only, never float) ---

def format_exact(wei: int) -> str:
    """Full ether value, trailing zeros removed. Matches the transaction page."""
    sign = "-" if wei < 0 else ""
    wei = abs(wei)
    whole, frac = divmod(wei, 10**18)
    if frac == 0:
        return f"{sign}{whole}"
    text = f"{frac:018d}".rstrip("0")
    return f"{sign}{whole}.{text}"


def format_fee_list(wei: int) -> str:
    """Txn Fee column: drop anything past 8 decimal places, then trailing zeros.

    Live row for 41,642,283,703,625 wei is 0.00004164 (the next digit is not rounded).
    """
    if wei <= 0:
        return "0"
    units = wei // 10**10
    if units == 0:
        return "0"
    whole, frac = divmod(units, 10**8)
    text = f"{frac:08d}".rstrip("0")
    return f"{whole}.{text}" if text else str(whole)


def format_amount_list(wei: int) -> str:
    """Amount column on the transaction list.

    Under 0.001 ETH, Etherscan prints 0.0 plus a subscript zero-count and four
    significant digits (0.00030625… is shown as 0.0₃3062). Larger values keep
    nine decimal places and drop trailing zeros.
    """
    if wei == 0:
        return "0 ETH"
    sign = "-" if wei < 0 else ""
    wei = abs(wei)
    whole, frac = divmod(wei, 10**18)
    frac18 = f"{frac:018d}"
    zeros = len(frac18) - len(frac18.lstrip("0"))
    if whole == 0 and zeros >= 3:
        sig = frac18.lstrip("0")[:4]
        return f"{sign}0.0{str(zeros).translate(SUB)}{sig} ETH"
    frac9 = frac18[:9].rstrip("0")
    if frac9:
        return f"{sign}{whole}.{frac9} ETH"
    return f"{sign}{whole} ETH"


def pretty_method(function_name: str, method_id: str) -> tuple[str, str]:
    """Return (badge text, tooltip). Empty calldata is Transfer, same as Etherscan."""
    raw = (function_name or "").strip()
    method_id = (method_id or "").strip()
    if not raw:
        if method_id.lower() in ("", "0x", "0x0"):
            return "Transfer", "Transfer"
        return method_id, method_id
    name = raw.split("(", 1)[0].strip()
    if not name:
        label = method_id or "Unknown"
        return label, raw
    spaced = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1 \2", name)
    spaced = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", spaced).replace("_", " ")
    parts = [part for part in spaced.split(" ") if part]
    if parts and parts[0][:1].islower():
        parts[0] = parts[0][:1].upper() + parts[0][1:]
    label = " ".join(parts) or name
    return label, raw


def age_text(timestamp: int, now: int | None = None) -> str:
    now = int(time.time()) if now is None else now
    seconds = max(0, now - timestamp)
    if seconds < 60:
        return "1 sec ago" if seconds == 1 else f"{seconds} secs ago"
    if seconds < 3600:
        minutes = seconds // 60
        return "1 min ago" if minutes == 1 else f"{minutes} mins ago"
    if seconds < 86400:
        hours = seconds // 3600
        return "1 hr ago" if hours == 1 else f"{hours} hrs ago"
    days = seconds // 86400
    return "1 day ago" if days == 1 else f"{days} days ago"


def age_title(timestamp: int) -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime(timestamp))


def comma(n: int) -> str:
    return f"{n:,}"


# --- block intervals ---

class IntervalSet:
    def __init__(self) -> None:
        self.parts: list[tuple[int, int]] = []
        self.lock = threading.Lock()

    def add(self, start: int, end: int) -> None:
        if end < start:
            return
        with self.lock:
            self.parts = _merge(self.parts + [(start, end)])

    def count_within(self, start: int, end: int) -> int:
        with self.lock:
            total = 0
            for left, right in self.parts:
                lo = max(left, start)
                hi = min(right, end)
                if hi >= lo:
                    total += hi - lo + 1
            return total

    def gaps(self, start: int, end: int) -> list[tuple[int, int]]:
        with self.lock:
            missing: list[tuple[int, int]] = []
            cursor = start
            for left, right in self.parts:
                if right < start:
                    continue
                if left > end:
                    break
                lo = max(left, start)
                hi = min(right, end)
                if lo > cursor:
                    missing.append((cursor, lo - 1))
                cursor = max(cursor, hi + 1)
                if cursor > end:
                    break
            if cursor <= end:
                missing.append((cursor, end))
            return missing

    def load(self, parts: list[tuple[int, int]]) -> None:
        with self.lock:
            self.parts = _merge(parts)


def _merge(parts: list[tuple[int, int]]) -> list[tuple[int, int]]:
    if not parts:
        return []
    ordered = sorted(parts)
    merged = [ordered[0]]
    for start, end in ordered[1:]:
        left, right = merged[-1]
        if start <= right + 1:
            merged[-1] = (left, max(right, end))
        else:
            merged.append((start, end))
    return merged


def split_range(start: int, end: int, parts: int) -> list[tuple[int, int]]:
    span = end - start + 1
    parts = max(1, min(parts, span))
    if parts == 1:
        return [(start, end)]
    size = span // parts
    pieces = []
    cursor = start
    for index in range(parts):
        nxt = end if index == parts - 1 else min(end, cursor + size - 1)
        pieces.append((cursor, nxt))
        cursor = nxt + 1
        if cursor > end:
            break
    return pieces


# --- storage ---

class Database:
    def __init__(self, path: str | Path) -> None:
        if str(path) != ":memory:":
            Path(path).parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(path), check_same_thread=False)
        self.lock = threading.Lock()
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA synchronous=NORMAL")
        self.conn.execute("PRAGMA busy_timeout=5000")
        self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS tx (
                address TEXT NOT NULL,
                hash TEXT NOT NULL,
                block INTEGER NOT NULL,
                tx_index INTEGER NOT NULL,
                timestamp INTEGER NOT NULL,
                from_addr TEXT NOT NULL,
                to_addr TEXT NOT NULL,
                value_wei TEXT NOT NULL,
                gas_used TEXT NOT NULL,
                gas_price TEXT NOT NULL,
                fee_wei TEXT NOT NULL,
                method_id TEXT NOT NULL,
                function_name TEXT NOT NULL,
                is_error INTEGER NOT NULL,
                PRIMARY KEY (address, hash)
            );
            CREATE INDEX IF NOT EXISTS ix_tx_range ON tx(address, block);
            CREATE TABLE IF NOT EXISTS coverage (
                address TEXT NOT NULL,
                start_block INTEGER NOT NULL,
                end_block INTEGER NOT NULL,
                PRIMARY KEY (address, start_block, end_block)
            );
            CREATE TABLE IF NOT EXISTS incomplete (
                address TEXT NOT NULL,
                block INTEGER NOT NULL,
                note TEXT NOT NULL,
                PRIMARY KEY (address, block)
            );
            """
        )

    def insert_many(self, rows: list[tuple]) -> None:
        if not rows:
            return
        with self.lock:
            self.conn.executemany(
                """
                INSERT OR IGNORE INTO tx (
                    address, hash, block, tx_index, timestamp, from_addr, to_addr,
                    value_wei, gas_used, gas_price, fee_wei, method_id, function_name, is_error
                ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                rows,
            )
            self.conn.commit()

    def add_coverage(self, address: str, start: int, end: int) -> None:
        with self.lock:
            existing = self.conn.execute(
                "SELECT start_block, end_block FROM coverage WHERE address=?",
                (address,),
            ).fetchall()
            merged = _merge([(start, end)] + [(row[0], row[1]) for row in existing])
            self.conn.execute("DELETE FROM coverage WHERE address=?", (address,))
            self.conn.executemany(
                "INSERT INTO coverage(address, start_block, end_block) VALUES (?,?,?)",
                [(address, left, right) for left, right in merged],
            )
            self.conn.commit()

    def load_coverage(self, address: str) -> list[tuple[int, int]]:
        with self.lock:
            rows = self.conn.execute(
                "SELECT start_block, end_block FROM coverage WHERE address=? ORDER BY start_block",
                (address,),
            ).fetchall()
        return [(row[0], row[1]) for row in rows]

    def mark_incomplete(self, address: str, block: int, note: str) -> None:
        with self.lock:
            self.conn.execute(
                "INSERT OR REPLACE INTO incomplete(address, block, note) VALUES (?,?,?)",
                (address, block, note),
            )
            self.conn.commit()

    def incomplete_in(self, address: str, start: int, end: int) -> list[tuple[int, str]]:
        with self.lock:
            rows = self.conn.execute(
                "SELECT block, note FROM incomplete WHERE address=? AND block>=? AND block<=? ORDER BY block",
                (address, start, end),
            ).fetchall()
        return [(row[0], row[1]) for row in rows]

    def invalidate_tip(self, address: str, tip: int) -> None:
        with self.lock:
            self.conn.execute("DELETE FROM tx WHERE address=? AND block>=?", (address, tip))
            self.conn.execute("DELETE FROM incomplete WHERE address=? AND block>=?", (address, tip))
            rows = self.conn.execute(
                "SELECT start_block, end_block FROM coverage WHERE address=?",
                (address,),
            ).fetchall()
            kept: list[tuple[int, int]] = []
            for start, end in rows:
                if end < tip:
                    kept.append((start, end))
                elif start < tip:
                    kept.append((start, tip - 1))
            self.conn.execute("DELETE FROM coverage WHERE address=?", (address,))
            self.conn.executemany(
                "INSERT INTO coverage(address, start_block, end_block) VALUES (?,?,?)",
                [(address, left, right) for left, right in kept],
            )
            self.conn.commit()

    def iter_range(self, address: str, start: int, end: int):
        # Caller must hold the scan lock so this cursor is the only reader.
        return self.conn.execute(
            """
            SELECT hash, block, tx_index, timestamp, from_addr, to_addr,
                   value_wei, gas_used, gas_price, fee_wei, method_id, function_name, is_error
            FROM tx
            WHERE address=? AND block>=? AND block<=?
            """,
            (address, start, end),
        )

    def clear(self) -> None:
        with self.lock:
            self.conn.execute("DELETE FROM tx")
            self.conn.execute("DELETE FROM coverage")
            self.conn.execute("DELETE FROM incomplete")
            self.conn.commit()


def normalize_tx(address: str, raw: dict) -> tuple | None:
    try:
        tx_hash = str(raw["hash"])
        block = int(raw["blockNumber"])
        gas_used = int(raw["gasUsed"])
        gas_price = int(raw["gasPrice"])
        value = int(raw.get("value") or 0)
        timestamp = int(raw.get("timeStamp") or 0)
        tx_index = int(raw.get("transactionIndex") or 0)
    except (KeyError, TypeError, ValueError):
        return None
    if not tx_hash.startswith("0x") or gas_used < 0 or gas_price < 0:
        return None
    fee = gas_used * gas_price
    return (
        address,
        tx_hash,
        block,
        tx_index,
        timestamp,
        str(raw.get("from") or ""),
        str(raw.get("to") or ""),
        str(value),
        str(gas_used),
        str(gas_price),
        str(fee),
        str(raw.get("methodId") or ""),
        str(raw.get("functionName") or ""),
        1 if str(raw.get("isError") or "0") == "1" else 0,
    )


# --- Etherscan client ---

class EtherscanClient:
    def __init__(self, keys: list[str], rps_per_key: float) -> None:
        self.keys = keys
        self.interval = 1.0 / (rps_per_key * len(keys))
        self.next_time = 0.0
        self.lock = threading.Lock()
        self.requests = 0
        self._index = 0

    def _acquire(self) -> str:
        with self.lock:
            now = time.monotonic()
            wait = max(0.0, self.next_time - now)
            self.next_time = max(now, self.next_time) + self.interval
            key = self.keys[self._index % len(self.keys)]
            self._index += 1
            self.requests += 1
        if wait:
            time.sleep(wait)
        return key

    def slow_down(self) -> None:
        with self.lock:
            self.interval = min(1.0, self.interval * 1.5)

    def txlist(self, address: str, start: int, end: int, page: int, offset: int) -> list[dict]:
        last_error = "Etherscan request failed."
        for attempt in range(8):
            key = self._acquire()
            params = {
                "chainid": "1",
                "module": "account",
                "action": "txlist",
                "address": address,
                "startblock": str(start),
                "endblock": str(end),
                "page": str(page),
                "offset": str(offset),
                "sort": "asc",
                "apikey": key,
            }
            url = API_URL + "?" + urllib.parse.urlencode(params)
            try:
                return _parse_txlist(_http_get(url))
            except RateLimit as exc:
                last_error = str(exc)
                self.slow_down()
                time.sleep(0.35 * (attempt + 1))
            except ApiError:
                raise
            except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exc:
                last_error = str(exc)
                time.sleep(0.35 * (attempt + 1))
        raise ApiError(last_error)


def _http_get(url: str) -> dict:
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "TxnFeeSum/1.0", "Accept": "application/json"},
    )
    try:
        with urllib.request.urlopen(request, timeout=40) as response:
            body = response.read()
    except urllib.error.HTTPError as exc:
        payload = exc.read().decode("utf-8", "replace")
        if exc.code == 429 or "rate limit" in payload.lower():
            raise RateLimit("Etherscan rate limit reached.") from exc
        raise ApiError(f"Etherscan HTTP {exc.code}: {payload[:240]}") from exc
    data = json.loads(body)
    if not isinstance(data, dict):
        raise ApiError("Etherscan returned a response that was not JSON.")
    return data


def _parse_txlist(data: dict) -> list[dict]:
    message = str(data.get("message") or "")
    result = data.get("result")
    if isinstance(result, str):
        low = result.lower()
        if "no transactions found" in low or "no records found" in low:
            return []
        if "rate limit" in low or "max calls per sec" in low:
            raise RateLimit(result)
        raise ApiError(result)
    if isinstance(result, list):
        return result
    low = message.lower()
    if "no transactions found" in low or "no records found" in low:
        return []
    if "rate limit" in low:
        raise RateLimit(message)
    raise ApiError(message or "Unexpected Etherscan response.")


def get_head() -> int:
    payload = json.dumps(
        {"jsonrpc": "2.0", "method": "eth_blockNumber", "params": [], "id": 1}
    ).encode()
    last = "Could not read the latest block."
    for url in RPCS:
        request = urllib.request.Request(
            url,
            data=payload,
            headers={"Content-Type": "application/json", "User-Agent": "TxnFeeSum/1.0"},
        )
        try:
            with urllib.request.urlopen(request, timeout=12) as response:
                data = json.loads(response.read())
            return int(data["result"], 16)
        except (urllib.error.URLError, TimeoutError, KeyError, ValueError, json.JSONDecodeError) as exc:
            last = str(exc)
    raise ApiError(last)


# --- scanner ---

class Scanner:
    def __init__(
        self,
        fetch,
        db: Database,
        address: str,
        page_size: int,
        window: int,
        workers: int,
        cancel: threading.Event,
        intervals: IntervalSet,
        progress: dict,
    ) -> None:
        self.fetch = fetch
        self.db = db
        self.address = address
        self.page_size = page_size
        self.window = window
        self.workers = max(1, workers)
        self.cancel = cancel
        self.intervals = intervals
        self.progress = progress
        self.warnings: list[str] = []
        self._warns: set[str] = set()
        self.error: Exception | None = None
        self.seen: set[str] = set()
        self.buffer: list[tuple] = []
        self.q: queue.Queue = queue.Queue()
        self.cv = threading.Condition()
        self.in_flight = 0
        self.lock = threading.Lock()
        self.range_start = 0
        self.range_end = 0

    def scan(self, gaps: list[tuple[int, int]], range_start: int, range_end: int) -> None:
        self.range_start = range_start
        self.range_end = range_end
        slices = max(1, min(self.workers, 16))
        for start, end in gaps:
            for piece in split_range(start, end, slices):
                self.submit(piece)
        threads = [
            threading.Thread(target=self._worker, name=f"scan-{i}", daemon=True)
            for i in range(self.workers)
        ]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()
        self.flush()
        if self.error and not isinstance(self.error, Cancelled):
            raise self.error

    def submit(self, item: tuple[int, int]) -> None:
        with self.cv:
            if self.cancel.is_set():
                return
            self.q.put(item)
            self.cv.notify()

    def _worker(self) -> None:
        while True:
            with self.cv:
                if self.cancel.is_set():
                    self.cv.notify_all()
                    return
                while self.q.empty() and self.in_flight > 0 and not self.cancel.is_set():
                    self.cv.wait()
                if self.cancel.is_set() or self.q.empty():
                    self.cv.notify_all()
                    return
                item = self.q.get()
                self.in_flight += 1
            try:
                self.scan_range(*item)
            except Cancelled:
                self.cancel.set()
            except Exception as exc:
                with self.cv:
                    if self.error is None:
                        self.error = exc
                    self.cancel.set()
                    self.cv.notify_all()
                traceback.print_exc()
            finally:
                with self.cv:
                    self.in_flight -= 1
                    self.cv.notify_all()

    def scan_range(self, start: int, end: int) -> None:
        cursor = start
        limit = end
        while cursor <= limit:
            if self.cancel.is_set():
                raise Cancelled()
            batch, full = self.get_page(cursor, limit, 1)
            self.save(batch)
            if not full:
                self.cover(cursor, limit)
                return
            last = int(batch[-1]["blockNumber"])
            if last < cursor:
                raise ApiError("Etherscan returned transactions out of block order.")
            if last == cursor:
                self.paginate_block(cursor)
                self.cover(cursor, cursor)
                cursor += 1
                continue
            if last - 1 >= cursor:
                self.cover(cursor, last - 1)
            if limit - last >= 20_000:
                mid = last + (limit - last) // 2
                if mid <= limit:
                    self.submit((mid, limit))
                    limit = mid - 1
            cursor = last

    def paginate_block(self, block: int) -> None:
        page = 1
        while True:
            if self.cancel.is_set():
                raise Cancelled()
            offset = self.current_page_size()
            if page * offset > self.window:
                note = (
                    f"Block {block:,} hit Etherscan's {self.window:,}-transaction API limit. "
                    "Any transactions beyond that limit are missing from the total."
                )
                self.db.mark_incomplete(self.address, block, note)
                self.warn(note)
                return
            batch, full = self.get_page(block, block, page)
            self.save(batch)
            if not full:
                return
            page += 1

    def get_page(self, start: int, end: int, page: int) -> tuple[list[dict], bool]:
        offset = self.current_page_size()
        batch = self._in_range(self.fetch(self.address, start, end, page, offset), start, end)
        if (
            batch
            and len(batch) < offset
            and len(batch) % 100 == 0
            and (page + 1) * len(batch) <= self.window
        ):
            probe = self._in_range(
                self.fetch(self.address, start, end, page + 1, len(batch)),
                start,
                end,
            )
            known = {str(row.get("hash")) for row in batch}
            fresh = [row for row in probe if str(row.get("hash")) not in known]
            if fresh:
                self._shrink_page_size(len(batch))
                self.warn(
                    "Etherscan capped this key at "
                    f"{len(batch):,} rows per call. Continuing at that size so no rows are skipped."
                )
                return batch, True
        return batch, len(batch) >= offset and len(batch) > 0

    def _in_range(self, rows: list[dict], start: int, end: int) -> list[dict]:
        kept = []
        for row in rows:
            try:
                block = int(row["blockNumber"])
            except (KeyError, TypeError, ValueError):
                continue
            if start <= block <= end:
                kept.append(row)
        return kept

    def current_page_size(self) -> int:
        with self.lock:
            return self.page_size

    def _shrink_page_size(self, size: int) -> None:
        with self.lock:
            if size < self.page_size:
                self.page_size = size

    def save(self, rows: list[dict]) -> None:
        prepared = []
        new_count = 0
        for raw in rows:
            item = normalize_tx(self.address, raw)
            if item is None:
                self.warn("Skipped a transaction that did not include gas price and gas used.")
                continue
            tx_hash = item[1]
            with self.lock:
                if tx_hash in self.seen:
                    continue
                self.seen.add(tx_hash)
            prepared.append(item)
            new_count += 1
        if not prepared:
            return
        with self.lock:
            self.buffer.extend(prepared)
            self.progress["fetched"] = self.progress.get("fetched", 0) + new_count
            should_flush = len(self.buffer) >= 400
        if should_flush:
            self.flush()

    def flush(self) -> None:
        with self.lock:
            rows = self.buffer
            self.buffer = []
        self.db.insert_many(rows)

    def cover(self, start: int, end: int) -> None:
        self.flush()
        self.db.add_coverage(self.address, start, end)
        self.intervals.add(start, end)
        done = self.intervals.count_within(self.range_start, self.range_end)
        with self.lock:
            self.progress["done"] = done

    def warn(self, message: str) -> None:
        with self.lock:
            if message in self._warns:
                return
            self._warns.add(message)
            self.warnings.append(message)


def aggregate(db: Database, address: str, start: int, end: int, direction: str, max_count: int, min_count: int) -> dict:
    total = 0
    count = 0
    max_heap: list[tuple] = []
    min_heap: list[tuple] = []
    seq = 0
    for row in db.iter_range(address, start, end):
        (
            tx_hash, block, tx_index, timestamp, from_addr, to_addr,
            value_wei, gas_used, gas_price, fee_wei, method_id, function_name, is_error,
        ) = row
        way = _direction(address, from_addr, to_addr)
        if direction == "out" and way not in ("out", "self"):
            continue
        if direction == "in" and way not in ("in", "self"):
            continue
        fee = int(fee_wei)
        count += 1
        total += fee
        record = _record(
            tx_hash, block, tx_index, timestamp, from_addr, to_addr, way,
            int(value_wei), int(gas_used), int(gas_price), fee, method_id, function_name, is_error,
        )
        seq += 1
        if max_count > 0:
            heap_push_max(max_heap, max_count, (fee, block, tx_index, seq, record))
        if min_count > 0:
            heap_push_min(min_heap, min_count, (fee, block, tx_index, seq, record))
    highest = [item[4] for item in sorted(max_heap, key=lambda item: (item[0], item[1], item[2]), reverse=True)]
    lowest = [item[4] for item in sorted(min_heap, key=lambda item: (-item[0], -item[1], -item[2]))]
    return {
        "count": count,
        "feeWei": str(total),
        "feeExact": format_exact(total),
        "max": highest,
        "min": lowest,
    }


def heap_push_max(heap: list, limit: int, item: tuple) -> None:
    import heapq
    heapq.heappush(heap, item)
    if len(heap) > limit:
        heapq.heappop(heap)


def heap_push_min(heap: list, limit: int, item: tuple) -> None:
    import heapq
    fee, block, tx_index, seq, record = item
    heapq.heappush(heap, (-fee, -block, -tx_index, seq, record))
    if len(heap) > limit:
        heapq.heappop(heap)


def _direction(address: str, from_addr: str, to_addr: str) -> str:
    source = from_addr.lower()
    dest = to_addr.lower()
    if source == address and dest == address:
        return "self"
    if source == address:
        return "out"
    return "in"


def _record(
    tx_hash, block, tx_index, timestamp, from_addr, to_addr, direction,
    value, gas_used, gas_price, fee, method_id, function_name, is_error,
) -> dict:
    label, title = pretty_method(function_name, method_id)
    creation = not to_addr
    if creation and label == "Transfer":
        label, title = "Contract Creation", "Contract Creation"
    return {
        "hash": tx_hash,
        "method": label,
        "methodTitle": title,
        "block": block,
        "txIndex": tx_index,
        "timestamp": timestamp,
        "from": from_addr,
        "to": to_addr,
        "toLabel": "Contract Creation" if creation else to_addr,
        "direction": direction,
        "amount": format_amount_list(value),
        "amountExact": format_exact(value) + " ETH",
        "fee": format_fee_list(fee),
        "feeExact": format_exact(fee),
        "feeWei": str(fee),
        "gasUsed": str(gas_used),
        "gasPrice": str(gas_price),
        "failed": bool(is_error),
    }


# --- calculation ---

def run_calculation(body: dict, db: Database, progress: dict, cancel: threading.Event) -> dict:
    demo = bool(body.get("demo"))
    direction = body.get("direction") or "all"
    if direction not in ("all", "out", "in"):
        raise ApiError("Choose all, outgoing, or incoming transactions.")
    max_count = _count(body.get("maxCount"), 5)
    min_count = _count(body.get("minCount"), 3)
    started = time.perf_counter()
    warnings: list[str] = []

    if demo:
        address = "0x" + "11" * 20
        txs = build_demo_txs()
        blocks = [int(tx["blockNumber"]) for tx in txs]
        start, end = min(blocks), max(blocks)
        memory = Database(":memory:")
        fetcher = ListFetcher(txs, delay=0.1)
        page_size, workers = 25, 1
        target = memory
        requests_counter = fetcher
    else:
        address = str(body.get("address") or "").strip()
        if not ADDR_RE.match(address):
            raise ApiError("Enter the address as 0x followed by 40 hex characters.")
        address = address.lower()
        start = _block(body.get("startBlock"), "start")
        end_raw = body.get("endBlock")
        if end_raw in (None, "") or str(end_raw).strip().lower() == "latest":
            end = get_head()
        else:
            end = _block(end_raw, "end")
        if end < start:
            raise ApiError("End block must be the same or later than the start block.")
        plan = str(body.get("plan") or "free")
        if plan not in PLANS:
            raise ApiError("Choose an API plan.")
        keys = _keys(body.get("apiKey"))
        page_size, rps = PLANS[plan]
        client = EtherscanClient(keys, rps)
        target = db
        requests_counter = client
        workers = min(12, max(2, math.ceil(rps)))
        try:
            head = get_head()
        except ApiError:
            head = None
            if db.load_coverage(address):
                warnings.append("Couldn't read the chain head, so cached blocks were kept as stored.")
        if head is not None:
            db.invalidate_tip(address, max(0, head - REORG_DEPTH))
        fetcher = client.txlist

    intervals = IntervalSet()
    intervals.load(target.load_coverage(address))
    progress["total"] = end - start + 1
    progress["done"] = intervals.count_within(start, end)
    progress["fetched"] = 0
    progress["phase"] = "scan"
    gaps = intervals.gaps(start, end)
    if gaps:
        scanner = Scanner(
            fetcher, target, address, page_size, WINDOW_LIMIT, workers,
            cancel, intervals, progress,
        )
        scanner.scan(gaps, start, end)
        warnings.extend(scanner.warnings)
    if cancel.is_set():
        raise Cancelled()
    progress["phase"] = "sum"
    progress["done"] = progress["total"]
    summary = aggregate(target, address, start, end, direction, max_count, min_count)
    for block, note in target.incomplete_in(address, start, end):
        if note not in warnings:
            warnings.append(note)
    elapsed_ms = int((time.perf_counter() - started) * 1000)
    requests = getattr(requests_counter, "requests", getattr(requests_counter, "calls", 0))
    summary.update(
        {
            "address": address,
            "startBlock": start,
            "endBlock": end,
            "direction": direction,
            "maxCount": max_count,
            "minCount": min_count,
            "requests": requests,
            "elapsedMs": elapsed_ms,
            "cached": requests == 0,
            "warnings": warnings,
            "demo": demo,
        }
    )
    return summary


def _count(value, default: int) -> int:
    if value in (None, ""):
        return default
    try:
        number = int(value)
    except (TypeError, ValueError):
        raise ApiError("Max and min counts must be whole numbers from 0 to 100.") from None
    if number < 0 or number > 100:
        raise ApiError("Max and min counts must be whole numbers from 0 to 100.")
    return number


def _block(value, which: str) -> int:
    text = str(value if value is not None else "").strip().replace(",", "").replace("_", "")
    if not text.isdigit():
        raise ApiError(f"Enter the {which} block number.")
    number = int(text)
    if number > 10**15:
        raise ApiError(f"The {which} block number is too large.")
    return number


def _keys(value) -> list[str]:
    parts = [part.strip() for part in re.split(r"[\s,]+", str(value or "")) if part.strip()]
    if not parts or any(len(part) < 10 for part in parts):
        raise ApiError("Paste your Etherscan API key. A free key is created at etherscan.io/apidashboard.")
    return parts


class ListFetcher:
    def __init__(self, txs: list[dict], delay: float = 0) -> None:
        self.txs = sorted(txs, key=lambda tx: (int(tx["blockNumber"]), int(tx["transactionIndex"])))
        self.delay = delay
        self.calls = 0
        self.requests = 0
        self.lock = threading.Lock()

    def __call__(self, address: str, start: int, end: int, page: int, offset: int) -> list[dict]:
        del address
        if self.delay:
            time.sleep(self.delay)
        with self.lock:
            self.calls += 1
            self.requests += 1
        rows = [tx for tx in self.txs if start <= int(tx["blockNumber"]) <= end]
        begin = (page - 1) * offset
        return rows[begin:begin + offset]


def build_demo_txs() -> list[dict]:
    address = "0x" + "11" * 20
    other = "0x" + "22" * 20
    sender = "0x" + "33" * 20
    now = int(time.time()) - 4 * 3600
    txs = []
    block = 2_640_0000

    def add(gas_used, gas_price, value, source, dest, function_name="", failed=False, method_id=""):
        nonlocal block
        fee_check = gas_used * gas_price
        txs.append(
            {
                "blockNumber": str(block),
                "transactionIndex": "0",
                "timeStamp": str(now - (len(txs) * 12)),
                "hash": "0x" + f"{block:016x}{len(txs):016x}".ljust(64, "0"),
                "from": source,
                "to": dest,
                "value": str(value),
                "gasUsed": str(gas_used),
                "gasPrice": str(gas_price),
                "methodId": method_id or ("0x" if not function_name else "0xa1903eab"),
                "functionName": function_name,
                "isError": "1" if failed else "0",
                "_fee": fee_check,
            }
        )
        block += 1

    # Extremes are far from the bulk so the top/bottom tables are stable.
    add(21_000, 1, 0, address, other)  # smallest: list fee 0
    add(21_055, 1_977_785_975, 1_158_472_284_774_840, address, other)  # 0.00004164
    add(10_000, 4_180_000_000, 0, address, other)  # 0.0000418
    add(20_000, 3_000_000_000, 0, address, other)
    add(20_000, 4_000_000_000, 0, address, other)
    for _ in range(740):
        add(100_000, 10**10, 50_000_000_000_000_000, address, other)
    add(100_000, 10**10, 0, sender, address, failed=True)
    for _ in range(19):
        add(100_000, 10**10, 10**16, sender, address)
    add(500_000, 100 * 10**9, 306_253_682_582_288, address, other, "depositEther()")
    add(400_000, 90 * 10**9, 0, address, other, "swapExactETHForTokens(uint256,address[])")
    add(300_000, 80 * 10**9, 10**18, address, other)
    add(250_000, 70 * 10**9, 0, address, "")
    add(220_000, 60 * 10**9, 0, address, address, "transfer(address,uint256)")
    return txs


# --- http ---

DB = Database(DB_PATH)


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def do_GET(self) -> None:
        path = urllib.parse.urlsplit(self.path).path
        if path in ("/", "/index.html"):
            data = STATIC.read_bytes()
            self._bytes(200, "text/html; charset=utf-8", data)
            return
        if path == "/api/head":
            try:
                self._json(200, {"block": get_head()})
            except ApiError as exc:
                self._json(502, {"error": str(exc)})
            return
        self._json(404, {"error": "Not found."})

    def do_POST(self) -> None:
        path = urllib.parse.urlsplit(self.path).path
        try:
            length = int(self.headers.get("Content-Length") or 0)
            raw = self.rfile.read(length) if length else b"{}"
            body = json.loads(raw.decode("utf-8") or "{}")
        except (ValueError, json.JSONDecodeError):
            self._json(400, {"error": "The request was not valid JSON."})
            return
        if path == "/api/cache/clear":
            if not scan_lock.acquire(blocking=False):
                self._json(409, {"error": "A calculation is running. Cancel it before clearing the cache."})
                return
            try:
                DB.clear()
            finally:
                scan_lock.release()
            self._json(200, {"ok": True})
            return
        if path != "/api/calculate":
            self._json(404, {"error": "Not found."})
            return
        if not scan_lock.acquire(blocking=False):
            self._json(409, {"error": "A calculation is already running."})
            return
        cancel = threading.Event()
        progress = {"done": 0, "total": 0, "fetched": 0, "phase": "start"}
        state: dict = {}

        def runner() -> None:
            try:
                state["result"] = run_calculation(body, DB, progress, cancel)
            except Cancelled:
                state["cancelled"] = True
            except Exception as exc:
                traceback.print_exc()
                state["error"] = str(exc)
            finally:
                state["finished"] = True

        worker = threading.Thread(target=runner, daemon=True)
        try:
            self.send_response(200)
            self.send_header("Content-Type", "application/x-ndjson; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Transfer-Encoding", "chunked")
            self.end_headers()
            worker.start()
            last = None
            while not state.get("finished"):
                snap = (
                    progress["done"], progress["total"], progress["fetched"], progress["phase"]
                )
                if snap != last:
                    self._chunk({
                        "type": "progress",
                        "done": snap[0],
                        "total": snap[1],
                        "fetched": snap[2],
                        "phase": snap[3],
                    })
                    last = snap
                time.sleep(0.15)
            if state.get("error"):
                self._chunk({"type": "error", "message": state["error"]})
            elif state.get("result"):
                done = progress["total"]
                self._chunk({
                    "type": "progress",
                    "done": done,
                    "total": done,
                    "fetched": progress["fetched"],
                    "phase": "sum",
                })
                self._chunk({"type": "result", "data": state["result"]})
            self._chunk_end()
        except OSError:
            cancel.set()
        finally:
            cancel.set()
            if worker.ident is not None:
                worker.join(timeout=45)
            scan_lock.release()

    def _chunk(self, payload: dict) -> None:
        data = (json.dumps(payload, separators=(",", ":")) + "\n").encode()
        self.wfile.write(f"{len(data):X}\r\n".encode())
        self.wfile.write(data)
        self.wfile.write(b"\r\n")
        self.wfile.flush()

    def _chunk_end(self) -> None:
        self.wfile.write(b"0\r\n\r\n")
        self.wfile.flush()

    def _json(self, code: int, payload: dict) -> None:
        data = json.dumps(payload).encode()
        self._bytes(code, "application/json; charset=utf-8", data)

    def _bytes(self, code: int, content_type: str, data: bytes) -> None:
        self.send_response(code)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def log_message(self, fmt: str, *args) -> None:
        print(f"[{self.log_date_time_string()}] {fmt % args}", flush=True)


def serve(open_browser: bool) -> None:
    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    server.daemon_threads = True
    host, port = server.server_address
    url = f"http://{host}:{port}"
    print(f"Txn Fee Sum is running at {url}", flush=True)
    print("Leave this window open while you use the calculator.", flush=True)
    if open_browser:
        threading.Timer(0.35, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.", flush=True)
    finally:
        server.server_close()


# --- self test ---

def self_test() -> None:
    assert format_exact(41_642_283_703_625) == "0.000041642283703625"
    assert format_exact(1_158_472_284_774_840) == "0.00115847228477484"
    assert format_exact(351_817_640_299_910) == "0.00035181764029991"
    assert format_exact(10**18 + 1) == "1.000000000000000001"
    assert format_exact(0) == "0"
    assert format_fee_list(41_642_283_703_625) == "0.00004164"
    assert format_fee_list(41_800_000_000_000) == "0.0000418"
    assert format_fee_list(21_000) == "0"
    assert format_fee_list(0) == "0"
    assert format_amount_list(1_158_472_284_774_840) == "0.001158472 ETH"
    assert format_amount_list(306_253_682_582_288) == "0.0₃3062 ETH"
    assert format_amount_list(351_817_640_299_910) == "0.0₃3518 ETH"
    assert format_amount_list(1_589_383_000_000_000_000) == "1.589383 ETH"
    assert format_amount_list(0) == "0 ETH"
    assert pretty_method("", "0x")[0] == "Transfer"
    assert pretty_method("depositEther()", "0xa1903eab")[0] == "Deposit Ether"
    assert pretty_method("swapExactETHForTokens(uint256,address[])", "0x12345678")[0] == "Swap Exact ETH For Tokens"
    assert pretty_method("transfer(address,uint256)", "0xa9059cbb")[0] == "Transfer"
    assert age_text(1_000, 1_016) == "16 secs ago"
    assert age_text(1_000, 1_001) == "1 sec ago"
    assert age_text(1_000, 1_084) == "1 min ago"
    assert age_text(1_000, 1_300) == "5 mins ago"
    assert age_text(1_000, 1_000 + 4 * 3600) == "4 hrs ago"
    assert age_title(1_794_584_771) == "2026-11-13 15:46:11"

    spans = IntervalSet()
    spans.add(1, 5)
    spans.add(6, 10)
    spans.add(20, 25)
    assert spans.gaps(1, 25) == [(11, 19)]
    assert spans.gaps(4, 22) == [(11, 19)]
    assert spans.count_within(1, 25) == 16

    txs = build_demo_txs()
    expected = sum(tx["_fee"] for tx in txs)
    db = Database(":memory:")
    fetcher = ListFetcher([{k: v for k, v in tx.items() if k != "_fee"} for tx in txs])
    address = "0x" + "11" * 20
    blocks = [int(tx["blockNumber"]) for tx in txs]
    start, end = min(blocks), max(blocks)
    intervals = IntervalSet()
    progress: dict = {"done": 0, "fetched": 0}
    cancel = threading.Event()
    scanner = Scanner(fetcher, db, address, 25, WINDOW_LIMIT, 2, cancel, intervals, progress)
    scanner.scan([(start, end)], start, end)
    summary = aggregate(db, address, start, end, "all", 5, 3)
    assert summary["count"] == len(txs), summary["count"]
    assert int(summary["feeWei"]) == expected
    fees = [row["fee"] for row in summary["min"]]
    assert fees[0] == "0"
    assert "0.00004164" in fees
    assert "0.0000418" in fees
    assert any(row["amount"] == "0.001158472 ETH" for row in summary["min"])
    assert any(row["amount"] == "0.0₃3062 ETH" and row["method"] == "Deposit Ether" for row in summary["max"])
    assert any(row["method"] == "Swap Exact ETH For Tokens" for row in summary["max"])
    assert any(row["toLabel"] == "Contract Creation" for row in summary["max"])
    outgoing = aggregate(db, address, start, end, "out", 1, 1)
    incoming = aggregate(db, address, start, end, "in", 1, 1)
    assert outgoing["count"] + incoming["count"] > summary["count"]  # self is in both
    assert outgoing["count"] < summary["count"]
    assert int(outgoing["feeWei"]) + int(incoming["feeWei"]) > int(summary["feeWei"])

    intervals2 = IntervalSet()
    intervals2.load(db.load_coverage(address))
    assert intervals2.gaps(start, end) == []
    fetcher2 = ListFetcher([{k: v for k, v in tx.items() if k != "_fee"} for tx in txs])
    progress2: dict = {"done": 0, "fetched": 0}
    scanner2 = Scanner(fetcher2, db, address, 25, WINDOW_LIMIT, 2, threading.Event(), intervals2, progress2)
    assert intervals2.gaps(start, end) == []
    assert fetcher2.calls == 0

    # Silent 100-row cap plus a block that fills the API window.
    dense: list[dict] = []
    for index in range(250):
        dense.append(_raw_tx(1, index, 21_000, 1_000 + index))
    for index in range(1_000):
        dense.append(_raw_tx(2, index, 21_000, 5_000))
    cap = CapFetcher(dense, 100)
    db2 = Database(":memory:")
    addr2 = "0x" + "ab" * 20
    intervals3 = IntervalSet()
    progress3: dict = {"done": 0, "fetched": 0}
    scanner3 = Scanner(cap, db2, addr2, 1_000, 1_000, 2, threading.Event(), intervals3, progress3)
    scanner3.scan([(1, 5)], 1, 5)
    dense_sum = aggregate(db2, addr2, 1, 5, "all", 1, 1)
    assert dense_sum["count"] == 1_250, dense_sum["count"]
    assert scanner3.page_size == 100
    assert any("API limit" in note for _, note in db2.incomplete_in(addr2, 1, 5))
    assert any("capped" in warning.lower() for warning in scanner3.warnings)
    manual = sum(21_000 * (1_000 + i) for i in range(250)) + 1_000 * 21_000 * 5_000
    assert int(dense_sum["feeWei"]) == manual
    print("self-test passed")


def _raw_tx(block: int, index: int, gas_used: int, gas_price: int) -> dict:
    return {
        "blockNumber": str(block),
        "transactionIndex": str(index),
        "timeStamp": "1700000000",
        "hash": "0x" + f"{block:08x}{index:08x}".ljust(64, "c"),
        "from": "0x" + "ab" * 20,
        "to": "0x" + "cd" * 20,
        "value": "0",
        "gasUsed": str(gas_used),
        "gasPrice": str(gas_price),
        "methodId": "0x",
        "functionName": "",
        "isError": "0",
    }


class CapFetcher:
    def __init__(self, txs: list[dict], cap: int) -> None:
        self.txs = sorted(txs, key=lambda tx: (int(tx["blockNumber"]), int(tx["transactionIndex"])))
        self.cap = cap
        self.calls = 0

    def __call__(self, address: str, start: int, end: int, page: int, offset: int) -> list[dict]:
        del address
        self.calls += 1
        offset = min(offset, self.cap)
        rows = [tx for tx in self.txs if start <= int(tx["blockNumber"]) <= end]
        begin = (page - 1) * offset
        return rows[begin:begin + offset]


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact Etherscan transaction-fee calculator")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--no-browser", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    serve(open_browser=not args.no_browser)


if __name__ == "__main__":
    main()
