# inventory_tracker.py
# Single-file Tkinter + SQLite inventory POS with:
# - Inventory, categories, coupons, discounts (line + order), taxes
# - Cart with inline qty/line-discount editing
# - Sales + receipt storage, TXT/PDF export (PDF via reportlab if installed)
# - Returns/refunds (restock inventory)
# - Reports: daily/monthly, top items/customers, by category, tax export
# - Users + roles (admin/clerk), store/receipt settings, backup/restore
# - Add Item dialog supports scanning:
#     * UPC/EAN barcode -> auto lookup item/brand (UPCItemDB trial, needs internet)
#     * Price-only sticker (digits like 1299) -> parse price
#
# NOTE:
# - If you have an existing old DB schema, this file includes a best-effort migration
#   for an older sales schema that had sales.book_id. If migration cannot be applied,
#   you may need to delete inventory_tracker.db and re-run.
#
# Tested for logical correctness, but I cannot run this on your machine.

import os
import re
import csv
import json
import shutil
import sqlite3
import hashlib
import hmac
import secrets
import time
import urllib.error
import urllib.request
import urllib.parse
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from datetime import datetime, date, timedelta
from typing import Optional, Dict, Any, List, Tuple


DB_PATH = "inventory_tracker.db"
USER_AGENT = "InventoryPOS/1.0 (+https://openai.com)"
CONDITION_OPTIONS = ["New", "Like New", "Good", "Fair", "Poor"]
PLATFORM_OPTIONS = ["Facebook", "eBay", "Other"]
PLATFORM_SALE_STATUSES = ["Paid", "Pending", "Partial", "Unpaid"]
AVAILABILITY_STATUSES = {
    "Available": "available",
    "Pending": "pending",
    "Pickup/Ship": "pickup_ship",
}
AVAILABILITY_LABELS = {v: k for k, v in AVAILABILITY_STATUSES.items()}


# -------------------------- Money helpers (integer cents) --------------------------
def dollars_to_cents(s: str) -> int:
    s = (s or "").strip()
    if not s:
        raise ValueError("empty")
    if s.startswith("$"):
        s = s[1:].strip()
    if s.count(".") > 1:
        raise ValueError("bad format")
    if "." in s:
        left, right = s.split(".", 1)
        left = left.strip() or "0"
        right = (right.strip() + "00")[:2]
    else:
        left, right = s, "00"
    if not left.isdigit() or not right.isdigit():
        raise ValueError("bad digits")
    return int(left) * 100 + int(right)


def cents_to_money(cents: int) -> str:
    return f"${cents / 100:,.2f}"


def now_ts() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def format_measure(value: Optional[float]) -> str:
    if value is None:
        return ""
    if float(value).is_integer():
        return str(int(value))
    return f"{value:g}"


def format_dimensions(length: Optional[float], width: Optional[float], height: Optional[float]) -> str:
    if length is None and width is None and height is None:
        return ""
    if length is not None and width is not None and height is not None:
        return f"{format_measure(length)} x {format_measure(width)} x {format_measure(height)} in"
    parts = []
    if length is not None:
        parts.append(f"L {format_measure(length)}")
    if width is not None:
        parts.append(f"W {format_measure(width)}")
    if height is not None:
        parts.append(f"H {format_measure(height)}")
    return f"{' '.join(parts)} in"


def format_weight(weight_lb: Optional[float], weight_oz: Optional[float]) -> str:
    if weight_lb is None and weight_oz is None:
        return ""
    parts = []
    if weight_lb is not None:
        parts.append(f"{format_measure(weight_lb)} lb")
    if weight_oz is not None:
        parts.append(f"{format_measure(weight_oz)} oz")
    return " ".join(parts)


def today_ymd() -> str:
    return date.today().strftime("%Y-%m-%d")


# -------------------------- Password hashing (PBKDF2) --------------------------
def pbkdf2_hash(password: str, salt: Optional[bytes] = None) -> Tuple[bytes, bytes]:
    if salt is None:
        salt = secrets.token_bytes(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 200_000)
    return salt, dk


def pbkdf2_verify(password: str, salt: bytes, digest: bytes) -> bool:
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 200_000)
    return hmac.compare_digest(dk, digest)


# -------------------------- PDF receipts (optional) --------------------------
def export_pdf_text(text: str, path: str, title: str = "Receipt") -> None:
    try:
        from reportlab.lib.pagesizes import letter
        from reportlab.pdfgen import canvas
    except Exception as e:
        raise RuntimeError("reportlab not installed") from e

    c = canvas.Canvas(path, pagesize=letter)
    w, h = letter
    c.setTitle(title)

    x, y = 50, h - 50
    line_h = 12

    for line in text.splitlines():
        if y < 50:
            c.showPage()
            y = h - 50
        c.drawString(x, y, line)
        y -= line_h

    c.save()


# -------------------------- Barcode / scan helpers --------------------------
BARCODE_RE = re.compile(r"\d{8,14}")

def normalize_barcode(raw: str) -> Optional[str]:
    """
    Normalize any scan containing a UPC/EAN-style barcode.
    - Extracts the first 8-14 digit run
    Returns the barcode string or None if not found.
    """
    if not raw:
        return None
    s = raw.strip()
    if s.isdigit() and 8 <= len(s) <= 14:
        return s
    match = BARCODE_RE.search(s)
    if match:
        return match.group(0)
    return None

def parse_price_from_scan(raw: str) -> Optional[str]:
    """
    Parse a price from a scan string (heuristics).
    Supports:
      - "$12.99" or "12.99"
      - digits-only like "1299" => $12.99 (treat as cents)
    """
    if not raw:
        return None
    s = raw.strip()

    # Direct dollar format
    if re.fullmatch(r"\$?\d+(\.\d{1,2})?", s):
        val = float(s.replace("$", ""))
        return f"{val:.2f}"

    digits = re.sub(r"\D", "", s)
    if not digits:
        return None

    # Price-only stickers often 3-6 digits representing cents
    if 3 <= len(digits) <= 6:
        cents = int(digits)
        return f"{cents / 100:.2f}"

    return None


def parse_scan_barcode_and_price(raw: str) -> Tuple[Optional[str], Optional[str]]:
    """
    Extract barcode and optional price from:
    - UPC/EAN barcode (8-14 digits)
    - Mixed scans that include price stickers
    """
    if not raw:
        return None, None

    digits = re.sub(r"\D", "", raw)
    barcode = normalize_barcode(raw)
    price = None

    # If no price parsed, try price parsing heuristics unless raw is just barcode digits
    if price is None:
        if barcode and digits and digits.isdigit() and len(digits) in (8, 12, 13, 14):
            price = None
        else:
            price = parse_price_from_scan(raw)

    return barcode, price


def parse_locations(raw: Optional[str]) -> List[str]:
    if not raw:
        return []
    parts = re.split(r"[,;\n]+", raw)
    seen = set()
    locations = []
    for part in parts:
        loc = part.strip()
        if not loc:
            continue
        key = loc.lower()
        if key in seen:
            continue
        seen.add(key)
        locations.append(loc)
    return locations


def parse_optional_float(raw: str, field: str) -> Optional[float]:
    s = (raw or "").strip()
    if not s:
        return None
    try:
        value = float(s)
    except ValueError as exc:
        raise ValueError(f"Invalid {field}.") from exc
    if value < 0:
        raise ValueError(f"{field} cannot be negative.")
    return value


def parse_optional_int(raw: str, field: str) -> Optional[int]:
    s = (raw or "").strip()
    if not s:
        return None
    try:
        value = int(s)
    except ValueError as exc:
        raise ValueError(f"Invalid {field}.") from exc
    if value < 0:
        raise ValueError(f"{field} cannot be negative.")
    return value


def normalize_locations(raw: Optional[str]) -> Optional[str]:
    locations = parse_locations(raw)
    return ", ".join(locations) if locations else None


def merge_locations(existing: Optional[str], incoming: Optional[str]) -> Optional[str]:
    combined = parse_locations(existing) + parse_locations(incoming)
    if not combined:
        return None
    seen = set()
    merged = []
    for loc in combined:
        key = loc.lower()
        if key in seen:
            continue
        seen.add(key)
        merged.append(loc)
    return ", ".join(merged)



def fetch_json_with_retry(url: str, timeout: int = 8, retries: int = 2) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    last_error = None
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return json.loads(resp.read().decode("utf-8")), None
        except urllib.error.HTTPError as err:
            last_error = f"HTTP {err.code}"
            if err.code in (429, 500, 502, 503, 504) and attempt < retries:
                retry_after = err.headers.get("Retry-After")
                try:
                    delay = int(retry_after) if retry_after else 1 + attempt * 2
                except ValueError:
                    delay = 1 + attempt * 2
                time.sleep(delay)
                continue
            return None, last_error
        except Exception:
            last_error = "request failed"
            return None, last_error
    return None, last_error


def fetch_title_info_upcitemdb(barcode: str) -> Optional[Dict[str, str]]:
    """
    Lookup item/brand via UPCItemDB trial API.
    Requires internet access. Returns {"title":..., "studio":...} or None.
    """
    if not barcode:
        return None
    url = "https://api.upcitemdb.com/prod/trial/lookup?" + urllib.parse.urlencode({
        "upc": barcode,
    })
    data, _error = fetch_json_with_retry(url)
    if not data:
        return None

    items = data.get("items") or []
    if not items:
        return None

    item = items[0] or {}
    title = (item.get("title") or "").strip()
    studio = (item.get("brand") or item.get("manufacturer") or "").strip()
    if not title:
        return None
    return {"title": title, "studio": studio}


# -------------------------- DB Layer --------------------------
class DB:
    def __init__(self, path: str = DB_PATH):
        self.path = path
        self._conn: Optional[sqlite3.Connection] = None
        self.fts_enabled = False
        self._init_db()

    def _connect(self):
        if self._conn is None:
            conn = sqlite3.connect(self.path, check_same_thread=False)
            conn.execute("PRAGMA foreign_keys = ON;")
            conn.execute("PRAGMA journal_mode = WAL;")
            conn.execute("PRAGMA synchronous = NORMAL;")
            conn.execute("PRAGMA busy_timeout = 5000;")
            self._conn = conn
        return self._conn

    def _table_exists(self, conn, name: str) -> bool:
        cur = conn.cursor()
        cur.execute("SELECT name FROM sqlite_master WHERE type='table' AND name=?;", (name,))
        return cur.fetchone() is not None

    def _columns(self, conn, table: str) -> List[str]:
        cur = conn.cursor()
        cur.execute(f"PRAGMA table_info({table});")
        return [r[1] for r in cur.fetchall()]

    def _try_migrate_old_sales_schema(self, conn) -> None:
        """
        If an old schema exists where sales has book_id (single-item sales),
        migrate to new schema (sales header + sale_items).
        This is best-effort for the known old column set.
        """
        if not self._table_exists(conn, "sales"):
            return
        cols = self._columns(conn, "sales")
        if "book_id" not in cols:
            return  # already new schema

        # Known old columns we expect
        expected = {"id", "created_at", "customer_id", "book_id", "quantity",
                    "unit_price_cents", "subtotal_cents", "tax_rate", "tax_cents",
                    "total_cents", "receipt_text"}
        if not expected.issubset(set(cols)):
            # Unknown old schema; safest is to stop and ask user to reset DB
            raise RuntimeError(
                "Detected an older 'sales' table with book_id but unknown columns. "
                "Please delete inventory_tracker.db and re-run, or provide your sales schema for a custom migration."
            )

        cur = conn.cursor()

        # Create new tables with temporary names
        cur.execute("""
            CREATE TABLE IF NOT EXISTS sales_new (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                receipt_no TEXT NOT NULL UNIQUE,
                created_at TEXT NOT NULL,
                customer_id INTEGER NOT NULL,
                platform TEXT NOT NULL DEFAULT 'In-store',
                subtotal_cents INTEGER NOT NULL,
                discount_cents INTEGER NOT NULL DEFAULT 0,
                coupon_code TEXT,
                tax_rate REAL NOT NULL,
                tax_cents INTEGER NOT NULL,
                total_cents INTEGER NOT NULL,
                payment_method TEXT NOT NULL DEFAULT 'cash',
                payment_status TEXT NOT NULL DEFAULT 'paid',
                note TEXT,
                receipt_text TEXT NOT NULL,
                is_void INTEGER NOT NULL DEFAULT 0,
                FOREIGN KEY(customer_id) REFERENCES customers(id) ON DELETE RESTRICT
            );
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS sale_items_new (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                sale_id INTEGER NOT NULL,
                book_id INTEGER NOT NULL,
                quantity INTEGER NOT NULL CHECK(quantity > 0),
                unit_price_cents INTEGER NOT NULL,
                unit_cost_cents INTEGER NOT NULL DEFAULT 0,
                line_subtotal_cents INTEGER NOT NULL,
                line_discount_cents INTEGER NOT NULL DEFAULT 0,
                line_total_cents INTEGER NOT NULL,
                FOREIGN KEY(sale_id) REFERENCES sales_new(id) ON DELETE CASCADE,
                FOREIGN KEY(book_id) REFERENCES books(id) ON DELETE RESTRICT
            );
        """)

        # Copy old sales -> sales_new, create a simple receipt_no sequence
        prefix = "R"
        cur.execute("SELECT IFNULL(MAX(id),0) FROM sales;")
        max_id = int(cur.fetchone()[0])

        cur.execute("""
            SELECT id, created_at, customer_id, book_id, quantity, unit_price_cents,
                   subtotal_cents, tax_rate, tax_cents, total_cents, receipt_text
            FROM sales;
        """)
        rows = cur.fetchall()

        for (sid, created_at, customer_id, book_id, qty, unit_price, subtotal, tax_rate, tax_cents, total, receipt_text) in rows:
            receipt_no = f"{prefix}{int(sid):06d}"
            cur.execute("""
                INSERT INTO sales_new(
                    id, receipt_no, created_at, customer_id, platform,
                    subtotal_cents, discount_cents, coupon_code,
                    tax_rate, tax_cents, total_cents,
                    payment_method, payment_status, note, receipt_text, is_void
                )
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,0);
            """, (
                int(sid), receipt_no, created_at, int(customer_id), "In-store",
                int(subtotal), 0, None,
                float(tax_rate), int(tax_cents), int(total),
                "cash", "paid", "", receipt_text
            ))

            line_sub = int(unit_price) * int(qty)
            line_total = int(subtotal)  # old subtotal was line total for single item
            cur.execute("""
                INSERT INTO sale_items_new(
                    sale_id, book_id, quantity, unit_price_cents, unit_cost_cents,
                    line_subtotal_cents, line_discount_cents, line_total_cents
                )
                VALUES(?,?,?,?,?,?,?,?);
            """, (int(sid), int(book_id), int(qty), int(unit_price), 0, int(line_sub), 0, int(line_total)))

        # Replace old tables
        cur.execute("DROP TABLE sales;")
        cur.execute("ALTER TABLE sales_new RENAME TO sales;")
        cur.execute("ALTER TABLE sale_items_new RENAME TO sale_items;")

        conn.commit()

    def _init_db(self):
        conn = self._connect()
        cur = conn.cursor()

        # Minimal prerequisites for migration (customers/books must exist or old schema won't be workable)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS customers (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                email TEXT NOT NULL,
                is_active INTEGER NOT NULL DEFAULT 1,
                UNIQUE(name, email)
            );
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS books (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                isbn TEXT UNIQUE,
                barcode TEXT UNIQUE,
                title TEXT NOT NULL,
                author TEXT NOT NULL,
                category_id INTEGER,
                location TEXT,
                length_in REAL,
                width_in REAL,
                height_in REAL,
                weight_lb REAL,
                weight_oz REAL,
                condition TEXT NOT NULL DEFAULT 'Good',
                price_cents INTEGER NOT NULL DEFAULT 0,
                cost_cents INTEGER NOT NULL DEFAULT 0,
                stock_qty INTEGER NOT NULL DEFAULT 0,
                reorder_point INTEGER NOT NULL DEFAULT 0,
                reorder_qty INTEGER NOT NULL DEFAULT 0,
                is_active INTEGER NOT NULL DEFAULT 1,
                uploaded_facebook INTEGER NOT NULL DEFAULT 0,
                uploaded_ebay INTEGER NOT NULL DEFAULT 0,
                availability_status TEXT NOT NULL DEFAULT 'available'
            );
        """)
        conn.commit()

        # Migration if needed
        self._try_migrate_old_sales_schema(conn)

        # Full schema
        cur.execute("""
                CREATE TABLE IF NOT EXISTS settings (
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL
                );
        """)

        cur.execute("""
                CREATE TABLE IF NOT EXISTS users (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    username TEXT NOT NULL UNIQUE,
                    salt BLOB NOT NULL,
                    digest BLOB NOT NULL,
                    role TEXT NOT NULL CHECK(role IN ('admin','clerk')),
                    is_active INTEGER NOT NULL DEFAULT 1
                );
        """)

        cur.execute("""
                CREATE TABLE IF NOT EXISTS categories (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL UNIQUE,
                    is_active INTEGER NOT NULL DEFAULT 1
                );
        """)

        # Add missing FK on books.category_id if old books table lacks it (SQLite can't add FK; we just keep column)
        cur.execute("""
                CREATE TABLE IF NOT EXISTS coupons (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    code TEXT NOT NULL UNIQUE,
                    kind TEXT NOT NULL CHECK(kind IN ('percent','fixed')),
                    value REAL NOT NULL CHECK(value >= 0),
                    is_active INTEGER NOT NULL DEFAULT 1,
                    expires_on TEXT
                );
        """)

        cur.execute("""
                CREATE TABLE IF NOT EXISTS sales (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    receipt_no TEXT NOT NULL UNIQUE,
                    created_at TEXT NOT NULL,
                    customer_id INTEGER NOT NULL,
                    platform TEXT NOT NULL DEFAULT 'In-store',
                    subtotal_cents INTEGER NOT NULL,
                    discount_cents INTEGER NOT NULL DEFAULT 0,
                    coupon_code TEXT,
                    tax_rate REAL NOT NULL,
                    tax_cents INTEGER NOT NULL,
                    total_cents INTEGER NOT NULL,
                    payment_method TEXT NOT NULL CHECK(payment_method IN ('cash','card','other')),
                    payment_status TEXT NOT NULL CHECK(payment_status IN ('paid','unpaid','partial')),
                    note TEXT,
                    receipt_text TEXT NOT NULL,
                    is_void INTEGER NOT NULL DEFAULT 0,
                    FOREIGN KEY(customer_id) REFERENCES customers(id) ON DELETE RESTRICT
                );
        """)

        cur.execute("""
                CREATE TABLE IF NOT EXISTS sale_items (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    sale_id INTEGER NOT NULL,
                    book_id INTEGER NOT NULL,
                    quantity INTEGER NOT NULL CHECK(quantity > 0),
                    unit_price_cents INTEGER NOT NULL,
                    unit_cost_cents INTEGER NOT NULL,
                    line_subtotal_cents INTEGER NOT NULL,
                    line_discount_cents INTEGER NOT NULL DEFAULT 0,
                    line_total_cents INTEGER NOT NULL,
                    FOREIGN KEY(sale_id) REFERENCES sales(id) ON DELETE CASCADE,
                    FOREIGN KEY(book_id) REFERENCES books(id) ON DELETE RESTRICT
                );
        """)

        cur.execute("""
                CREATE TABLE IF NOT EXISTS returns (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    created_at TEXT NOT NULL,
                    sale_id INTEGER NOT NULL,
                    reason TEXT,
                    refund_method TEXT NOT NULL CHECK(refund_method IN ('cash','card','other')),
                    refund_cents INTEGER NOT NULL CHECK(refund_cents >= 0),
                    refund_tax_cents INTEGER NOT NULL DEFAULT 0,
                    receipt_text TEXT NOT NULL,
                    FOREIGN KEY(sale_id) REFERENCES sales(id) ON DELETE RESTRICT
                );
        """)

        cur.execute("""
                CREATE TABLE IF NOT EXISTS return_items (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    return_id INTEGER NOT NULL,
                    book_id INTEGER NOT NULL,
                    quantity INTEGER NOT NULL CHECK(quantity > 0),
                    unit_price_cents INTEGER NOT NULL,
                    line_total_cents INTEGER NOT NULL,
                    FOREIGN KEY(return_id) REFERENCES returns(id) ON DELETE CASCADE,
                    FOREIGN KEY(book_id) REFERENCES books(id) ON DELETE RESTRICT
                );
        """)

        cur.execute("""
                CREATE TABLE IF NOT EXISTS platform_sales (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    created_at TEXT NOT NULL,
                    book_id INTEGER NOT NULL,
                    platform TEXT NOT NULL,
                    listed_price_cents INTEGER NOT NULL,
                    final_price_cents INTEGER NOT NULL,
                    amount_paid_cents INTEGER NOT NULL DEFAULT 0,
                    status TEXT NOT NULL CHECK(status IN ('paid','pending','partial','unpaid')),
                    note TEXT,
                    FOREIGN KEY(book_id) REFERENCES books(id) ON DELETE RESTRICT
                );
        """)

        cur.execute("""
                CREATE TABLE IF NOT EXISTS inventory_adjustments (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    created_at TEXT NOT NULL,
                    book_id INTEGER NOT NULL,
                    delta_qty INTEGER NOT NULL,
                    reason TEXT NOT NULL,
                    note TEXT,
                    user_id INTEGER,
                    FOREIGN KEY(book_id) REFERENCES books(id) ON DELETE RESTRICT,
                    FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE SET NULL
                );
        """)

        conn.commit()

        if "refund_tax_cents" not in self._columns(conn, "returns"):
            cur.execute("ALTER TABLE returns ADD COLUMN refund_tax_cents INTEGER NOT NULL DEFAULT 0;")
            conn.commit()

        if "platform" not in self._columns(conn, "sales"):
            cur.execute("ALTER TABLE sales ADD COLUMN platform TEXT NOT NULL DEFAULT 'In-store';")
            conn.commit()
            cur.execute("UPDATE sales SET platform='In-store' WHERE platform IS NULL OR platform='';")
            conn.commit()

        if "amount_paid_cents" not in self._columns(conn, "platform_sales"):
            cur.execute("ALTER TABLE platform_sales ADD COLUMN amount_paid_cents INTEGER NOT NULL DEFAULT 0;")
            conn.commit()

        if "location" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN location TEXT;")
            conn.commit()

        if "barcode" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN barcode TEXT;")
            conn.commit()

        if "length_in" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN length_in REAL;")
            conn.commit()

        if "width_in" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN width_in REAL;")
            conn.commit()

        if "height_in" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN height_in REAL;")
            conn.commit()

        if "weight_lb" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN weight_lb REAL;")
            conn.commit()

        if "weight_oz" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN weight_oz REAL;")
            conn.commit()

        if "uploaded_facebook" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN uploaded_facebook INTEGER NOT NULL DEFAULT 0;")
            conn.commit()

        if "uploaded_ebay" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN uploaded_ebay INTEGER NOT NULL DEFAULT 0;")
            conn.commit()

        if "must_change_password" not in self._columns(conn, "users"):
            cur.execute("ALTER TABLE users ADD COLUMN must_change_password INTEGER NOT NULL DEFAULT 0;")
            conn.commit()

        if "condition" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN condition TEXT NOT NULL DEFAULT 'Good';")
            conn.commit()

        if "availability_status" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN availability_status TEXT NOT NULL DEFAULT 'available';")
            conn.commit()

        if "reorder_point" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN reorder_point INTEGER NOT NULL DEFAULT 0;")
            conn.commit()

        if "reorder_qty" not in self._columns(conn, "books"):
            cur.execute("ALTER TABLE books ADD COLUMN reorder_qty INTEGER NOT NULL DEFAULT 0;")
            conn.commit()

        if "barcode" in self._columns(conn, "books"):
            cur.execute("""
                UPDATE books
                SET barcode = isbn
                WHERE barcode IS NULL
                  AND isbn IS NOT NULL
                  AND isbn GLOB '[0-9]*'
                  AND LENGTH(isbn) BETWEEN 8 AND 14;
            """)
            conn.commit()

        cur.execute("CREATE INDEX IF NOT EXISTS idx_sales_created_at ON sales(created_at);")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_sale_items_sale_id ON sale_items(sale_id);")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_sale_items_book_id ON sale_items(book_id);")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_returns_sale_id ON returns(sale_id);")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_platform_sales_book_id ON platform_sales(book_id);")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_books_category_id ON books(category_id);")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_customers_name ON customers(name);")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_inventory_adjustments_book_id ON inventory_adjustments(book_id);")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_inventory_adjustments_created_at ON inventory_adjustments(created_at);")
        conn.commit()

        # Seed settings
        defaults = {
            "store_name": "My Resale Store",
            "store_address": "123 Main St",
            "store_phone": "(000) 000-0000",
            "receipt_footer": "Thank you! Returns with receipt within 14 days.",
            "receipt_prefix": "R",
            "tax_rate_default": "0.00",
        }
        for k, v in defaults.items():
            cur.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?);", (k, v))

        # Seed admin if no users
        cur.execute("SELECT COUNT(*) FROM users;")
        if int(cur.fetchone()[0]) == 0:
            temp_password = secrets.token_urlsafe(12)
            salt, dg = pbkdf2_hash(temp_password)
            cur.execute(
                "INSERT INTO users(username,salt,digest,role,is_active,must_change_password) VALUES(?,?,?,?,1,1);",
                ("admin", salt, dg, "admin"),
            )
            cur.execute(
                "INSERT OR REPLACE INTO settings(key,value) VALUES(?,?);",
                ("admin_temp_password", temp_password),
            )
            cur.execute(
                "INSERT OR REPLACE INTO settings(key,value) VALUES(?,?);",
                ("admin_temp_password_created_at", now_ts()),
            )
        conn.commit()

        self._ensure_books_fts(conn)

    def _ensure_books_fts(self, conn: sqlite3.Connection) -> None:
        cur = conn.cursor()
        try:
            cur.execute("""
                CREATE VIRTUAL TABLE IF NOT EXISTS books_fts USING fts5(
                    title, author, isbn, barcode,
                    content='books', content_rowid='id'
                );
            """)
            cur.execute("""
                CREATE TRIGGER IF NOT EXISTS books_ai AFTER INSERT ON books BEGIN
                    INSERT INTO books_fts(rowid, title, author, isbn, barcode)
                    VALUES (new.id, new.title, new.author, new.isbn, new.barcode);
                END;
            """)
            cur.execute("""
                CREATE TRIGGER IF NOT EXISTS books_ad AFTER DELETE ON books BEGIN
                    INSERT INTO books_fts(books_fts, rowid, title, author, isbn, barcode)
                    VALUES('delete', old.id, old.title, old.author, old.isbn, old.barcode);
                END;
            """)
            cur.execute("""
                CREATE TRIGGER IF NOT EXISTS books_au AFTER UPDATE ON books BEGIN
                    INSERT INTO books_fts(books_fts, rowid, title, author, isbn, barcode)
                    VALUES('delete', old.id, old.title, old.author, old.isbn, old.barcode);
                    INSERT INTO books_fts(rowid, title, author, isbn, barcode)
                    VALUES (new.id, new.title, new.author, new.isbn, new.barcode);
                END;
            """)
            cur.execute("INSERT INTO books_fts(books_fts) VALUES('rebuild');")
            conn.commit()
            self.fts_enabled = True
        except sqlite3.OperationalError:
            self.fts_enabled = False

    # -------- Settings --------
    def get_setting(self, key: str) -> str:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT value FROM settings WHERE key=?;", (key,))
            r = cur.fetchone()
            return r[0] if r else ""

    def set_setting(self, key: str, value: str) -> None:
        with self._connect() as conn:
            conn.execute(
                "INSERT INTO settings(key,value) VALUES(?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value;",
                (key, value),
            )
            conn.commit()

    def delete_setting(self, key: str) -> None:
        with self._connect() as conn:
            conn.execute("DELETE FROM settings WHERE key=?;", (key,))
            conn.commit()

    # -------- Auth / users --------
    def auth_user(self, username: str, password: str) -> Optional[Dict[str, Any]]:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute(
                "SELECT id, salt, digest, role, is_active, must_change_password FROM users WHERE username=?;",
                (username,),
            )
            row = cur.fetchone()
            if not row:
                return None
            uid, salt, dg, role, active, must_change = row
            if not int(active):
                return None
            if not pbkdf2_verify(password, salt, dg):
                return None
            return {"id": int(uid), "username": username, "role": role, "must_change_password": int(must_change)}

    def list_users(self) -> List[Tuple[int, str, str, int]]:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, username, role, is_active FROM users ORDER BY username;")
            return [(int(a), b, c, int(d)) for (a, b, c, d) in cur.fetchall()]

    def add_user(self, username: str, password: str, role: str) -> None:
        salt, dg = pbkdf2_hash(password)
        with self._connect() as conn:
            conn.execute(
                "INSERT INTO users(username,salt,digest,role,is_active) VALUES(?,?,?,?,1);",
                (username.strip(), salt, dg, role),
            )
            conn.commit()

    def set_user_active(self, user_id: int, active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE users SET is_active=? WHERE id=?;", (int(active), int(user_id)))
            conn.commit()

    def reset_password(self, user_id: int, new_password: str) -> None:
        salt, dg = pbkdf2_hash(new_password)
        with self._connect() as conn:
            conn.execute(
                "UPDATE users SET salt=?, digest=?, must_change_password=0 WHERE id=?;",
                (salt, dg, int(user_id)),
            )
            conn.commit()

    def set_user_must_change_password(self, user_id: int, must_change: int) -> None:
        with self._connect() as conn:
            conn.execute(
                "UPDATE users SET must_change_password=? WHERE id=?;",
                (int(must_change), int(user_id)),
            )
            conn.commit()

    # -------- Categories --------
    def list_categories(self, include_inactive: bool = False) -> List[Tuple[int, str, int]]:
        with self._connect() as conn:
            cur = conn.cursor()
            if include_inactive:
                cur.execute("SELECT id, name, is_active FROM categories ORDER BY name;")
            else:
                cur.execute("SELECT id, name, is_active FROM categories WHERE is_active=1 ORDER BY name;")
            return [(int(a), b, int(c)) for (a, b, c) in cur.fetchall()]

    def add_category(self, name: str) -> None:
        with self._connect() as conn:
            conn.execute("INSERT INTO categories(name,is_active) VALUES(?,1);", (name.strip(),))
            conn.commit()

    def set_category_active(self, cat_id: int, active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE categories SET is_active=? WHERE id=?;", (int(active), int(cat_id)))
            conn.commit()

    # -------- Items --------
    def list_books(
        self,
        search: str = "",
        in_stock_only: bool = False,
        include_inactive: bool = False,
        low_stock_only: bool = False,
        category_id: Optional[int] = None,
        condition: Optional[str] = None,
        availability_status: Optional[str] = None,
        uploaded_platform: Optional[str] = None,
    ) -> List[
        Tuple[
            int,
            Optional[str],
            Optional[str],
            str,
            str,
            Optional[str],
            Optional[float],
            Optional[float],
            Optional[float],
            Optional[int],
            Optional[int],
            str,
            int,
            int,
            int,
            int,
            int,
            int,
            int,
            str,
            Optional[str],
        ]
    ]:
        """
        Returns:
          (id, barcode, isbn, title, author, location, length_in, width_in, height_in, weight_lb, weight_oz,
           condition, price_cents, cost_cents, stock_qty, reorder_point, is_active, uploaded_facebook, uploaded_ebay,
           availability_status, category_name)
        """
        s = (search or "").strip()
        where = []
        params: List[Any] = []
        join_fts = ""

        if s:
            if self.fts_enabled:
                tokens = re.findall(r"[\w]+", s)
                fts_query = " ".join(f"{t}*" for t in tokens) if tokens else s
                join_fts = "JOIN books_fts fts ON fts.rowid = b.id"
                where.append("fts MATCH ?")
                params.append(fts_query)
            else:
                where.append("(b.title LIKE ? OR b.author LIKE ? OR IFNULL(b.barcode,'') LIKE ? OR IFNULL(b.isbn,'') LIKE ?)")
                like = f"%{s}%"
                params += [like, like, like, like]

        if in_stock_only:
            where.append("b.stock_qty > 0")

        if low_stock_only:
            where.append("b.reorder_point > 0 AND b.stock_qty <= b.reorder_point")

        if not include_inactive:
            where.append("b.is_active = 1")  # FIX: qualified

        if category_id is not None:
            where.append("b.category_id = ?")
            params.append(int(category_id))

        if condition:
            where.append("b.condition = ?")
            params.append(condition)

        if availability_status:
            where.append("b.availability_status = ?")
            params.append(availability_status)

        if uploaded_platform == "facebook":
            where.append("b.uploaded_facebook = 1")
        elif uploaded_platform == "ebay":
            where.append("b.uploaded_ebay = 1")

        wsql = ("WHERE " + " AND ".join(where)) if where else ""

        sql = f"""
            SELECT
                b.id, b.barcode, b.isbn, b.title, b.author, b.location,
                b.length_in, b.width_in, b.height_in, b.weight_lb, b.weight_oz,
                b.condition, b.price_cents, b.cost_cents, b.stock_qty, b.reorder_point, b.is_active,
                b.uploaded_facebook, b.uploaded_ebay, b.availability_status,
                c.name
            FROM books b
            {join_fts}
            LEFT JOIN categories c ON c.id = b.category_id
            {wsql}
            ORDER BY b.title;
        """
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute(sql, params)
            rows = cur.fetchall()
            out = []
            for r in rows:
                out.append((
                    int(r[0]),
                    r[1],
                    r[2],
                    str(r[3]),
                    str(r[4]),
                    r[5],
                    r[6],
                    r[7],
                    r[8],
                    int(r[9]) if r[9] is not None else None,
                    int(r[10]) if r[10] is not None else None,
                    str(r[11]),
                    int(r[12]),
                    int(r[13]),
                    int(r[14]),
                    int(r[15]),
                    int(r[16]),
                    int(r[17]),
                    int(r[18]),
                    str(r[19]),
                    r[20]
                ))
            return out

    def get_book(self, book_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT id, barcode, isbn, title, author, category_id, location,
                       length_in, width_in, height_in, weight_lb, weight_oz,
                       condition, price_cents, cost_cents, stock_qty, reorder_point, reorder_qty, is_active,
                       uploaded_facebook, uploaded_ebay, availability_status
                FROM books WHERE id=?;
            """, (int(book_id),))
            return cur.fetchone()

    def get_book_by_barcode(self, barcode: str):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT id, barcode, isbn, title, author, category_id, location,
                       length_in, width_in, height_in, weight_lb, weight_oz,
                       condition, price_cents, cost_cents, stock_qty, reorder_point, reorder_qty, is_active,
                       uploaded_facebook, uploaded_ebay, availability_status
                FROM books WHERE barcode=?;
            """, (barcode,))
            return cur.fetchone()

    def add_book(
        self,
        barcode,
        isbn,
        title,
        author,
        category_id,
        location,
        length_in,
        width_in,
        height_in,
        weight_lb,
        weight_oz,
        condition,
        price_cents,
        cost_cents,
        stock_qty,
        reorder_point=0,
        reorder_qty=0,
        is_active=1,
        uploaded_facebook=0,
        uploaded_ebay=0,
        availability_status="available",
    ):
        with self._connect() as conn:
            conn.execute("""
                INSERT INTO books(
                    barcode, isbn, title, author, category_id, location,
                    length_in, width_in, height_in, weight_lb, weight_oz,
                    condition,
                    price_cents, cost_cents, stock_qty, reorder_point, reorder_qty, is_active,
                    uploaded_facebook, uploaded_ebay, availability_status
                )
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?);
            """, (
                barcode or None,
                isbn or None,
                title.strip(),
                author.strip(),
                category_id,
                location,
                length_in,
                width_in,
                height_in,
                weight_lb,
                weight_oz,
                condition,
                int(price_cents),
                int(cost_cents),
                int(stock_qty),
                int(reorder_point),
                int(reorder_qty),
                int(is_active),
                int(uploaded_facebook),
                int(uploaded_ebay),
                availability_status,
            ))
            conn.commit()

    def update_book(
        self,
        book_id,
        barcode,
        isbn,
        title,
        author,
        category_id,
        location,
        length_in,
        width_in,
        height_in,
        weight_lb,
        weight_oz,
        condition,
        price_cents,
        cost_cents,
        stock_qty,
        reorder_point,
        reorder_qty,
        is_active,
        uploaded_facebook,
        uploaded_ebay,
        availability_status,
        user_id: Optional[int] = None,
    ):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT stock_qty FROM books WHERE id=?;", (int(book_id),))
            row = cur.fetchone()
            prev_stock = int(row[0]) if row else None
            conn.execute("""
                UPDATE books
                SET barcode=?, isbn=?, title=?, author=?, category_id=?, location=?,
                    length_in=?, width_in=?, height_in=?, weight_lb=?, weight_oz=?,
                    condition=?,
                    price_cents=?, cost_cents=?, stock_qty=?, reorder_point=?, reorder_qty=?, is_active=?,
                    uploaded_facebook=?, uploaded_ebay=?, availability_status=?
                WHERE id=?;
            """, (
                barcode or None,
                isbn or None,
                title.strip(),
                author.strip(),
                category_id,
                location,
                length_in,
                width_in,
                height_in,
                weight_lb,
                weight_oz,
                condition,
                int(price_cents),
                int(cost_cents),
                int(stock_qty),
                int(reorder_point),
                int(reorder_qty),
                int(is_active),
                int(uploaded_facebook),
                int(uploaded_ebay),
                availability_status,
                int(book_id),
            ))
            if prev_stock is not None and int(stock_qty) != prev_stock:
                delta = int(stock_qty) - prev_stock
                self._log_inventory_adjustment(
                    conn,
                    int(book_id),
                    delta,
                    "manual_edit",
                    "Edit item stock",
                    user_id,
                )
            conn.commit()

    def set_book_location(self, book_id: int, location: Optional[str]) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE books SET location=? WHERE id=?;", (location, int(book_id)))
            conn.commit()

    def delete_book(self, book_id: int) -> None:
        with self._connect() as conn:
            conn.execute("DELETE FROM books WHERE id=?;", (int(book_id),))
            conn.commit()

    def _log_inventory_adjustment(
        self,
        conn: sqlite3.Connection,
        book_id: int,
        delta: int,
        reason: str,
        note: Optional[str],
        user_id: Optional[int],
    ) -> None:
        conn.execute(
            """
            INSERT INTO inventory_adjustments(
                created_at, book_id, delta_qty, reason, note, user_id
            ) VALUES(?,?,?,?,?,?);
            """,
            (
                now_ts(),
                int(book_id),
                int(delta),
                reason.strip(),
                note.strip() if note else None,
                int(user_id) if user_id is not None else None,
            ),
        )

    def adjust_stock(self, book_id: int, delta: int, reason: str, note: Optional[str], user_id: Optional[int]) -> None:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT stock_qty FROM books WHERE id=?;", (int(book_id),))
            row = cur.fetchone()
            if not row:
                raise ValueError("item missing")
            new_qty = int(row[0]) + int(delta)
            if new_qty < 0:
                raise ValueError("insufficient stock")
            cur.execute("UPDATE books SET stock_qty=? WHERE id=?;", (new_qty, int(book_id)))
            self._log_inventory_adjustment(conn, book_id, delta, reason, note, user_id)
            conn.commit()

    def set_book_active(self, book_id: int, active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE books SET is_active=? WHERE id=?;", (int(active), int(book_id)))
            conn.commit()

    def set_book_availability(self, book_id: int, availability_status: str) -> None:
        with self._connect() as conn:
            conn.execute(
                "UPDATE books SET availability_status=? WHERE id=?;",
                (availability_status, int(book_id)),
            )
            conn.commit()

    # -------- Platform sales --------
    def add_platform_sale(
        self,
        book_id: int,
        platform: str,
        listed_price_cents: int,
        final_price_cents: int,
        amount_paid_cents: int,
        status: str,
        note: str,
    ) -> None:
        created_at = now_ts()
        status_norm = status.strip().lower()
        if status_norm not in ("paid", "pending", "partial", "unpaid"):
            raise ValueError("invalid status")
        with self._connect() as conn:
            conn.execute(
                """
                INSERT INTO platform_sales(
                    created_at, book_id, platform, listed_price_cents, final_price_cents, amount_paid_cents, status, note
                ) VALUES(?,?,?,?,?,?,?,?);
                """,
                (
                    created_at,
                    int(book_id),
                    platform.strip(),
                    int(listed_price_cents),
                    int(final_price_cents),
                    int(amount_paid_cents),
                    status_norm,
                    note.strip() or None,
                ),
            )
            conn.commit()

        new_availability = "pickup_ship" if status_norm == "paid" else "pending"
        self.set_book_availability(book_id, new_availability)

    def update_platform_sale(
        self,
        sale_id: int,
        final_price_cents: int,
        status: str,
        note: str,
    ) -> None:
        status_norm = status.strip().lower()
        if status_norm not in ("paid", "pending", "partial", "unpaid"):
            raise ValueError("invalid status")
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT book_id, amount_paid_cents FROM platform_sales WHERE id=?;", (int(sale_id),))
            row = cur.fetchone()
            if not row:
                raise ValueError("sale missing")
            book_id = int(row[0])
            amount_paid_cents = int(row[1])
            if status_norm == "paid":
                amount_paid_cents = int(final_price_cents)
            conn.execute(
                "UPDATE platform_sales SET final_price_cents=?, amount_paid_cents=?, status=?, note=? WHERE id=?;",
                (int(final_price_cents), int(amount_paid_cents), status_norm, note.strip() or None, int(sale_id)),
            )
            conn.commit()

        new_availability = "pickup_ship" if status_norm == "paid" else "pending"
        self.set_book_availability(book_id, new_availability)

    def update_platform_payment(
        self,
        sale_id: int,
        final_price_cents: int,
        amount_paid_cents: int,
        note: Optional[str] = None,
    ) -> None:
        if int(final_price_cents) <= 0:
            raise ValueError("final price must be positive")
        if int(amount_paid_cents) < 0:
            raise ValueError("amount paid cannot be negative")
        amount_paid_cents = min(int(amount_paid_cents), int(final_price_cents))
        if amount_paid_cents >= int(final_price_cents):
            status_norm = "paid"
        elif amount_paid_cents > 0:
            status_norm = "partial"
        else:
            status_norm = "pending"
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT book_id FROM platform_sales WHERE id=?;", (int(sale_id),))
            row = cur.fetchone()
            if not row:
                raise ValueError("sale missing")
            book_id = int(row[0])
            conn.execute(
                "UPDATE platform_sales SET final_price_cents=?, amount_paid_cents=?, status=?, note=COALESCE(?, note) WHERE id=?;",
                (int(final_price_cents), int(amount_paid_cents), status_norm, note, int(sale_id)),
            )
            conn.commit()

        new_availability = "pickup_ship" if status_norm == "paid" else "pending"
        self.set_book_availability(book_id, new_availability)

    def delete_platform_sale(self, sale_id: int) -> None:
        with self._connect() as conn:
            conn.execute("DELETE FROM platform_sales WHERE id=?;", (int(sale_id),))
            conn.commit()

    def finalize_platform_sale(self, sale_id: int) -> Tuple[int, str, str]:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT ps.book_id, ps.platform, ps.final_price_cents, ps.status
                FROM platform_sales ps
                WHERE ps.id=?;
            """, (int(sale_id),))
            row = cur.fetchone()
            if not row:
                raise ValueError("platform sale missing")
            book_id, platform, final_price_cents, status = row

        if str(status).lower() != "paid":
            raise ValueError("only paid platform sales can be completed")

        platform_sale_id = int(sale_id)
        platform_name = str(platform).strip() or "Platform"
        customer_name = f"Platform - {platform_name}"
        safe_platform = re.sub(r"[^a-z0-9]+", "-", platform_name.strip().lower()).strip("-") or "platform"
        customer_email = f"platform+{safe_platform}@local"
        customer_id = self.get_or_create_customer(customer_name, customer_email)

        sale_id, receipt_no, receipt_text = self.create_sale(
            customer_id=customer_id,
            cart_items=[{
                "book_id": int(book_id),
                "qty": 1,
                "unit_price_cents": int(final_price_cents),
            }],
            tax_rate=0.0,
            order_discount_cents=0,
            coupon_code=None,
            payment_method="other",
            payment_status="paid",
            note=f"Platform sale via {platform_name}",
            platform=platform_name,
            user_id=None,
        )

        self.delete_platform_sale(platform_sale_id)
        self.set_book_availability(int(book_id), "available")
        return sale_id, receipt_no, receipt_text

    def list_platform_sales(
        self,
        statuses: Optional[List[str]] = None,
        search: str = "",
    ) -> List[Tuple[int, str, int, str, str, int, int, int, str, Optional[str]]]:
        params: List[Any] = []
        where = []
        s = (search or "").strip()
        if s:
            where.append("(b.title LIKE ? OR b.author LIKE ? OR IFNULL(b.barcode,'') LIKE ? OR IFNULL(b.isbn,'') LIKE ?)")
            like = f"%{s}%"
            params += [like, like, like, like]
        if statuses:
            st = [st.strip().lower() for st in statuses]
            where.append("ps.status IN ({})".format(",".join("?" for _ in st)))
            params += st
        wsql = ("WHERE " + " AND ".join(where)) if where else ""
        sql = f"""
            SELECT
                ps.id,
                ps.created_at,
                ps.book_id,
                b.title,
                ps.platform,
                ps.listed_price_cents,
                ps.final_price_cents,
                ps.amount_paid_cents,
                ps.status,
                ps.note
            FROM platform_sales ps
            JOIN books b ON b.id = ps.book_id
            {wsql}
            ORDER BY ps.created_at DESC;
        """
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute(sql, params)
            rows = cur.fetchall()
            return [
                (
                    int(r[0]),
                    r[1],
                    int(r[2]),
                    str(r[3]),
                    str(r[4]),
                    int(r[5]),
                    int(r[6]),
                    int(r[7]),
                    str(r[8]),
                    r[9],
                )
                for r in rows
            ]

    # -------- Customers --------
    def list_customers(self, search: str = "", include_inactive: bool = False):
        s = (search or "").strip()
        where = []
        params: List[Any] = []

        if s:
            where.append("(name LIKE ? OR email LIKE ?)")
            like = f"%{s}%"
            params += [like, like]

        if not include_inactive:
            where.append("is_active = 1")

        wsql = ("WHERE " + " AND ".join(where)) if where else ""
        sql = f"SELECT id, name, email, is_active FROM customers {wsql} ORDER BY name;"

        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute(sql, params)
            return [(int(a), b, c, int(d)) for (a, b, c, d) in cur.fetchall()]

    def get_customer(self, customer_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, name, email, is_active FROM customers WHERE id=?;", (int(customer_id),))
            return cur.fetchone()

    def add_customer(self, name: str, email: str, is_active: int = 1) -> None:
        with self._connect() as conn:
            conn.execute("INSERT INTO customers(name,email,is_active) VALUES(?,?,?);", (name.strip(), email.strip(), int(is_active)))
            conn.commit()

    def _get_or_create_customer(self, conn, name: str, email: str) -> int:
        cur = conn.cursor()
        cur.execute("SELECT id FROM customers WHERE name=? AND email=?;", (name.strip(), email.strip()))
        row = cur.fetchone()
        if row:
            return int(row[0])
        cur.execute(
            "INSERT INTO customers(name,email,is_active) VALUES(?,?,1);",
            (name.strip(), email.strip()),
        )
        return int(cur.lastrowid)

    def get_or_create_customer(self, name: str, email: str) -> int:
        with self._connect() as conn:
            cid = self._get_or_create_customer(conn, name, email)
            conn.commit()
            return cid

    def update_customer(self, customer_id: int, name: str, email: str, is_active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE customers SET name=?, email=?, is_active=? WHERE id=?;",
                         (name.strip(), email.strip(), int(is_active), int(customer_id)))
            conn.commit()

    def set_customer_active(self, customer_id: int, active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE customers SET is_active=? WHERE id=?;", (int(active), int(customer_id)))
            conn.commit()

    # -------- Coupons --------
    def list_coupons(self):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, code, kind, value, is_active, expires_on FROM coupons ORDER BY code;")
            return [(int(a), b, c, float(d), int(e), f) for (a, b, c, d, e, f) in cur.fetchall()]

    def add_coupon(self, code, kind, value, is_active, expires_on):
        with self._connect() as conn:
            conn.execute("""
                INSERT INTO coupons(code,kind,value,is_active,expires_on)
                VALUES(?,?,?,?,?);
            """, (code.strip().upper(), kind, float(value), int(is_active), expires_on or None))
            conn.commit()

    def update_coupon(self, coupon_id, code, kind, value, is_active, expires_on):
        with self._connect() as conn:
            conn.execute("""
                UPDATE coupons SET code=?, kind=?, value=?, is_active=?, expires_on=? WHERE id=?;
            """, (code.strip().upper(), kind, float(value), int(is_active), expires_on or None, int(coupon_id)))
            conn.commit()

    def get_coupon_by_code(self, code: str) -> Optional[Dict[str, Any]]:
        code = (code or "").strip().upper()
        if not code:
            return None
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, code, kind, value, is_active, expires_on FROM coupons WHERE code=?;", (code,))
            row = cur.fetchone()
            if not row:
                return None
            cid, ccode, kind, val, active, expires_on = row
            if not int(active):
                return None
            if expires_on:
                try:
                    exp = datetime.strptime(expires_on, "%Y-%m-%d").date()
                    if date.today() > exp:
                        return None
                except Exception:
                    pass
            return {"id": int(cid), "code": ccode, "kind": kind, "value": float(val)}

    # -------- Sales / Returns / Receipts --------
    def next_receipt_no(self) -> str:
        prefix = self.get_setting("receipt_prefix") or "R"
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT receipt_no FROM sales ORDER BY id DESC LIMIT 1;")
            row = cur.fetchone()
            if not row:
                return f"{prefix}000001"
            last = str(row[0])
            digits = "".join(ch for ch in last if ch.isdigit())
            n = int(digits) + 1 if digits else 1
            return f"{prefix}{n:06d}"

    def _build_sale_receipt_text(
        self,
        receipt_no: str,
        created_at: str,
        customer_name: str,
        customer_email: str,
        lines: List[Dict[str, Any]],
        item_total_before_order_discount: int,
        order_discount_cents: int,
        coupon_code: Optional[str],
        coupon_discount_cents: int,
        discounted_subtotal_cents: int,
        tax_rate: float,
        tax_cents: int,
        total_cents: int,
        payment_method: str,
        payment_status: str,
        note: str
    ) -> str:
        store = self.get_setting("store_name")
        addr = self.get_setting("store_address")
        phone = self.get_setting("store_phone")
        footer = self.get_setting("receipt_footer")

        out = []
        out.append(store)
        out.append(addr)
        out.append(phone)
        out.append("=" * 64)
        out.append(f"Receipt: {receipt_no}")
        out.append(f"Date:    {created_at}")
        out.append(f"Customer:{customer_name}  <{customer_email}>")
        out.append("-" * 64)
        out.append(f"{'Item':34} {'Qty':>3} {'Unit':>10} {'Line':>10}")
        out.append("-" * 64)

        for r in lines:
            t = r["title"]
            if len(t) > 34:
                t = t[:33] + "…"
            out.append(f"{t:34} {r['qty']:>3} {cents_to_money(r['unit_price']):>10} {cents_to_money(r['line_total']):>10}")
            if r.get("line_disc", 0) > 0:
                out.append(f"{'  line discount':34} {'':>3} {'':>10} -{cents_to_money(r['line_disc']):>9}")

        out.append("-" * 64)
        if order_discount_cents > 0:
            out.append(f"{'Order discount:':>52} -{cents_to_money(order_discount_cents):>10}")
        if coupon_code and coupon_discount_cents > 0:
            out.append(f"{('Coupon ' + coupon_code + ':'):>52} -{cents_to_money(coupon_discount_cents):>10}")

        out.append(f"{'Subtotal (items):':>52} {cents_to_money(item_total_before_order_discount):>10}")
        out.append(f"{'Subtotal (after discounts):':>52} {cents_to_money(discounted_subtotal_cents):>10}")
        out.append(f"{('Tax @ ' + str(tax_rate)):>52} {cents_to_money(tax_cents):>10}")
        out.append(f"{'TOTAL:':>52} {cents_to_money(total_cents):>10}")
        out.append("-" * 64)
        out.append(f"Payment: {payment_method} / {payment_status}")
        if note:
            out.append(f"Note: {note}")
        out.append("=" * 64)
        out.append(footer)
        return "\n".join(out)

    def create_sale(
        self,
        customer_id: int,
        cart_items: List[Dict[str, Any]],
        tax_rate: float,
        order_discount_cents: int,
        coupon_code: Optional[str],
        payment_method: str,
        payment_status: str,
        note: str,
        platform: str = "In-store",
        user_id: Optional[int] = None,
    ) -> Tuple[int, str, str]:
        if not cart_items:
            raise ValueError("cart empty")
        if tax_rate < 0:
            raise ValueError("tax rate < 0")
        if order_discount_cents < 0:
            raise ValueError("order discount < 0")

        created_at = now_ts()
        receipt_no = self.next_receipt_no()

        with self._connect() as conn:
            cur = conn.cursor()

            # customer
            cur.execute("SELECT id, name, email FROM customers WHERE id=? AND is_active=1;", (int(customer_id),))
            cust = cur.fetchone()
            if not cust:
                raise ValueError("customer missing/inactive")
            _, cust_name, cust_email = cust

            # Build line items, validate stock
            lines = []
            item_total = 0
            for it in cart_items:
                book_id = int(it["book_id"])
                qty = int(it["qty"])
                if qty <= 0:
                    raise ValueError("bad qty")

                cur.execute("""
                    SELECT title, author, price_cents, cost_cents, stock_qty, is_active
                    FROM books WHERE id=?;
                """, (book_id,))
                b = cur.fetchone()
                if not b:
                    raise ValueError("item missing")
                title, author, price_cents, cost_cents, stock_qty, is_active = b
                if not int(is_active):
                    raise ValueError(f"item archived: {title}")
                if int(stock_qty) < qty:
                    raise ValueError(f"insufficient stock for item '{title}' (have {stock_qty}, need {qty})")

                unit_price = int(it.get("unit_price_cents", price_cents))
                unit_cost = int(it.get("unit_cost_cents", cost_cents))

                line_sub = unit_price * qty
                line_disc = int(it.get("line_discount_cents", 0))
                if line_disc < 0 or line_disc > line_sub:
                    raise ValueError(f"bad line discount for item '{title}'")
                line_total = line_sub - line_disc

                item_total += line_total
                lines.append({
                    "book_id": book_id,
                    "title": str(title),
                    "qty": qty,
                    "unit_price": unit_price,
                    "unit_cost": unit_cost,
                    "line_sub": line_sub,
                    "line_disc": line_disc,
                    "line_total": line_total,
                })

            # coupon
            coupon_discount = 0
            applied_coupon = None
            if coupon_code:
                cpn = self.get_coupon_by_code(coupon_code)
                if cpn and item_total > 0:
                    applied_coupon = cpn["code"]
                    if cpn["kind"] == "percent":
                        coupon_discount = int(round(item_total * (cpn["value"] / 100.0)))
                    else:
                        # fixed: treat as dollars if small
                        coupon_discount = int(round(cpn["value"] * 100.0)) if cpn["value"] < 1000 else int(cpn["value"])
                    coupon_discount = min(coupon_discount, item_total)

            total_order_discount = min(order_discount_cents + coupon_discount, item_total)
            discounted_subtotal = item_total - total_order_discount

            # distribute order-level discount across lines proportionally
            distributed = [0] * len(lines)
            if item_total > 0 and total_order_discount > 0:
                for i, ln in enumerate(lines):
                    share = ln["line_total"] / item_total
                    distributed[i] = int(round(total_order_discount * share))
                drift = total_order_discount - sum(distributed)
                if distributed:
                    distributed[-1] += drift

            # tax/total
            tax_cents = int(round(discounted_subtotal * float(tax_rate)))
            total_cents = discounted_subtotal + tax_cents

            receipt_text = self._build_sale_receipt_text(
                receipt_no=receipt_no,
                created_at=created_at,
                customer_name=cust_name,
                customer_email=cust_email,
                lines=lines,
                item_total_before_order_discount=item_total,
                order_discount_cents=order_discount_cents,
                coupon_code=applied_coupon,
                coupon_discount_cents=coupon_discount,
                discounted_subtotal_cents=discounted_subtotal,
                tax_rate=float(tax_rate),
                tax_cents=tax_cents,
                total_cents=total_cents,
                payment_method=payment_method,
                payment_status=payment_status,
                note=note or "",
            )

            # insert sale header
            cur.execute("""
                INSERT INTO sales(
                    receipt_no, created_at, customer_id, platform,
                    subtotal_cents, discount_cents, coupon_code,
                    tax_rate, tax_cents, total_cents,
                    payment_method, payment_status, note, receipt_text, is_void
                )
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,0);
            """, (
                receipt_no, created_at, int(customer_id), platform,
                int(discounted_subtotal), int(total_order_discount), applied_coupon,
                float(tax_rate), int(tax_cents), int(total_cents),
                payment_method, payment_status, note or "", receipt_text
            ))
            sale_id = int(cur.lastrowid)

            # insert items + decrement stock
            for i, ln in enumerate(lines):
                od = distributed[i]
                line_sub = ln["unit_price"] * ln["qty"]
                line_disc = ln["line_disc"] + od
                if line_disc > line_sub:
                    line_disc = line_sub
                line_total = line_sub - line_disc

                cur.execute("""
                    INSERT INTO sale_items(
                        sale_id, book_id, quantity,
                        unit_price_cents, unit_cost_cents,
                        line_subtotal_cents, line_discount_cents, line_total_cents
                    )
                    VALUES(?,?,?,?,?,?,?,?);
                """, (
                    sale_id, int(ln["book_id"]), int(ln["qty"]),
                    int(ln["unit_price"]), int(ln["unit_cost"]),
                    int(line_sub), int(line_disc), int(line_total)
                ))

                cur.execute("UPDATE books SET stock_qty = stock_qty - ? WHERE id=?;", (int(ln["qty"]), int(ln["book_id"])))
                self._log_inventory_adjustment(
                    conn,
                    int(ln["book_id"]),
                    -int(ln["qty"]),
                    "sale",
                    f"Receipt {receipt_no}",
                    user_id,
                )

            conn.commit()
            return sale_id, receipt_no, receipt_text

    def list_sales(self, limit: int = 300):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT s.id, s.receipt_no, s.created_at, s.platform, s.total_cents, s.payment_status, s.is_void
                FROM sales s
                ORDER BY s.id DESC
                LIMIT ?;
            """, (int(limit),))
            return [(int(a), b, c, d, int(e), f, int(g)) for (a, b, c, d, e, f, g) in cur.fetchall()]

    def get_sale_receipt(self, sale_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT receipt_text, receipt_no, created_at FROM sales WHERE id=?;", (int(sale_id),))
            return cur.fetchone()

    def get_sale_items(self, sale_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT si.book_id, b.title, si.quantity, si.unit_price_cents, si.line_total_cents
                FROM sale_items si
                JOIN books b ON b.id = si.book_id
                WHERE si.sale_id=?
                ORDER BY si.id;
            """, (int(sale_id),))
            return [(int(a), b, int(c), int(d), int(e)) for (a, b, c, d, e) in cur.fetchall()]

    def update_sale_payment_status(self, sale_id: int, payment_status: str) -> None:
        status_norm = payment_status.strip().lower()
        if status_norm not in ("paid", "unpaid", "partial"):
            raise ValueError("invalid payment status")
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id FROM sales WHERE id=?;", (int(sale_id),))
            if not cur.fetchone():
                raise ValueError("sale missing")
            conn.execute("UPDATE sales SET payment_status=? WHERE id=?;", (status_norm, int(sale_id)))
            conn.commit()

    def void_sale(self, sale_id: int, user_id: Optional[int] = None) -> None:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT is_void FROM sales WHERE id=?;", (int(sale_id),))
            row = cur.fetchone()
            if not row:
                raise ValueError("sale missing")
            if int(row[0]):
                return
            cur.execute("SELECT COUNT(*) FROM returns WHERE sale_id=?;", (int(sale_id),))
            if int(cur.fetchone()[0]) > 0:
                raise ValueError("cannot void sale with returns")
            cur.execute("SELECT receipt_no FROM sales WHERE id=?;", (int(sale_id),))
            rno_row = cur.fetchone()
            receipt_no = rno_row[0] if rno_row else str(sale_id)
            cur.execute("SELECT book_id, quantity FROM sale_items WHERE sale_id=?;", (int(sale_id),))
            items = cur.fetchall()
            for book_id, qty in items:
                cur.execute("UPDATE books SET stock_qty = stock_qty + ? WHERE id=?;", (int(qty), int(book_id)))
                self._log_inventory_adjustment(
                    conn,
                    int(book_id),
                    int(qty),
                    "void_sale",
                    f"Receipt {receipt_no}",
                    user_id,
                )
            cur.execute("UPDATE sales SET is_void=1 WHERE id=?;", (int(sale_id),))
            conn.commit()

    def delete_sale(self, sale_id: int, user_id: Optional[int] = None) -> None:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT is_void FROM sales WHERE id=?;", (int(sale_id),))
            row = cur.fetchone()
            if not row:
                raise ValueError("sale missing")
            is_void = int(row[0])
            cur.execute("SELECT COUNT(*) FROM returns WHERE sale_id=?;", (int(sale_id),))
            if int(cur.fetchone()[0]) > 0:
                raise ValueError("delete returns first")
            if not is_void:
                cur.execute("SELECT receipt_no FROM sales WHERE id=?;", (int(sale_id),))
                rno_row = cur.fetchone()
                receipt_no = rno_row[0] if rno_row else str(sale_id)
                cur.execute("SELECT book_id, quantity FROM sale_items WHERE sale_id=?;", (int(sale_id),))
                items = cur.fetchall()
                for book_id, qty in items:
                    cur.execute("UPDATE books SET stock_qty = stock_qty + ? WHERE id=?;", (int(qty), int(book_id)))
                    self._log_inventory_adjustment(
                        conn,
                        int(book_id),
                        int(qty),
                        "delete_sale",
                        f"Receipt {receipt_no}",
                        user_id,
                    )
            cur.execute("DELETE FROM sales WHERE id=?;", (int(sale_id),))
            conn.commit()

    def customer_history(self, customer_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT id, receipt_no, created_at, total_cents, payment_status
                FROM sales
                WHERE customer_id=?
                ORDER BY id DESC;
            """, (int(customer_id),))
            return [(int(a), b, c, int(d), e) for (a, b, c, d, e) in cur.fetchall()]

    def create_return(
        self,
        sale_id: int,
        items: List[Tuple[int, int]],
        reason: str,
        refund_method: str,
        user_id: Optional[int] = None,
    ):
        if not items:
            raise ValueError("no return items")

        created_at = now_ts()

        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, receipt_no, is_void, tax_rate FROM sales WHERE id=?;", (int(sale_id),))
            s = cur.fetchone()
            if not s:
                raise ValueError("sale missing")
            _, receipt_no, is_void, tax_rate = s
            if int(is_void):
                raise ValueError("cannot return voided sale")

            cur.execute("""
                SELECT book_id, quantity, unit_price_cents
                FROM sale_items
                WHERE sale_id=?;
            """, (int(sale_id),))
            orig = cur.fetchall()
            orig_map = {int(bid): {"qty": int(q), "unit": int(u)} for (bid, q, u) in orig}

            refund_subtotal_cents = 0
            receipt_lines = []
            for book_id, qty in items:
                book_id = int(book_id)
                qty = int(qty)
                if qty <= 0:
                    raise ValueError("bad qty")
                if book_id not in orig_map:
                    raise ValueError("item not in original sale")
                if qty > orig_map[book_id]["qty"]:
                    raise ValueError("return qty exceeds sold qty")
                unit = orig_map[book_id]["unit"]
                line_total = unit * qty
                refund_subtotal_cents += line_total
                receipt_lines.append((book_id, qty, unit, line_total))

            refund_tax_cents = int(round(refund_subtotal_cents * float(tax_rate)))
            refund_total_cents = refund_subtotal_cents + refund_tax_cents

            header = []
            store = self.get_setting("store_name")
            header.append(store)
            header.append("=" * 64)
            header.append(f"RETURN RECEIPT (original {receipt_no})")
            header.append(f"Date: {created_at}")
            header.append(f"Reason: {reason or ''}")
            header.append("-" * 64)
            header.append(f"{'Item':34} {'Qty':>3} {'Unit':>10} {'Line':>10}")
            header.append("-" * 64)

            for (book_id, qty, unit, line_total) in receipt_lines:
                cur.execute("SELECT title FROM books WHERE id=?;", (int(book_id),))
                t = cur.fetchone()
                title = t[0] if t else f"Item #{book_id}"
                if len(title) > 34:
                    title = title[:33] + "…"
                header.append(f"{title:34} {qty:>3} {cents_to_money(unit):>10} {cents_to_money(line_total):>10}")

            header.append("-" * 64)
            header.append(f"{'Subtotal:':>52} {cents_to_money(refund_subtotal_cents):>10}")
            header.append(f"{('Tax @ ' + str(tax_rate)):>52} {cents_to_money(refund_tax_cents):>10}")
            header.append(f"{'REFUND:':>52} {cents_to_money(refund_total_cents):>10}")
            header.append(f"Refund method: {refund_method}")
            header.append("=" * 64)
            receipt_text = "\n".join(header)

            cur.execute("""
                INSERT INTO returns(created_at, sale_id, reason, refund_method, refund_cents, refund_tax_cents, receipt_text)
                VALUES(?,?,?,?,?,?,?);
            """, (created_at, int(sale_id), reason or "", refund_method, int(refund_total_cents), int(refund_tax_cents), receipt_text))
            return_id = int(cur.lastrowid)

            for (book_id, qty, unit, line_total) in receipt_lines:
                cur.execute("""
                    INSERT INTO return_items(return_id, book_id, quantity, unit_price_cents, line_total_cents)
                    VALUES(?,?,?,?,?);
                """, (return_id, int(book_id), int(qty), int(unit), int(line_total)))

                cur.execute("UPDATE books SET stock_qty = stock_qty + ? WHERE id=?;", (int(qty), int(book_id)))
                self._log_inventory_adjustment(
                    conn,
                    int(book_id),
                    int(qty),
                    "return",
                    f"Return {return_id} (receipt {receipt_no})",
                    user_id,
                )

            conn.commit()
            return return_id, receipt_text

    def list_returns(self, limit: int = 200):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT r.id, r.created_at, s.receipt_no, r.refund_cents, r.refund_method
                FROM returns r
                JOIN sales s ON s.id = r.sale_id
                ORDER BY r.id DESC
                LIMIT ?;
            """, (int(limit),))
            return [(int(a), b, c, int(d), e) for (a, b, c, d, e) in cur.fetchall()]

    def list_inventory_adjustments(self, limit: int = 200):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT ia.created_at, b.title, ia.delta_qty, ia.reason, ia.note, u.username
                FROM inventory_adjustments ia
                JOIN books b ON b.id = ia.book_id
                LEFT JOIN users u ON u.id = ia.user_id
                ORDER BY ia.id DESC
                LIMIT ?;
            """, (int(limit),))
            rows = cur.fetchall()
            return [
                (ts, title, int(delta), reason, note or "", username or "")
                for (ts, title, delta, reason, note, username) in rows
            ]

    def delete_return(self, return_id: int, user_id: Optional[int] = None) -> None:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id FROM returns WHERE id=?;", (int(return_id),))
            if not cur.fetchone():
                raise ValueError("return missing")
            cur.execute("SELECT sale_id FROM returns WHERE id=?;", (int(return_id),))
            sale_row = cur.fetchone()
            sale_id = sale_row[0] if sale_row else None
            receipt_no = None
            if sale_id is not None:
                cur.execute("SELECT receipt_no FROM sales WHERE id=?;", (int(sale_id),))
                rno_row = cur.fetchone()
                receipt_no = rno_row[0] if rno_row else None
            cur.execute("SELECT book_id, quantity FROM return_items WHERE return_id=?;", (int(return_id),))
            items = cur.fetchall()
            for book_id, qty in items:
                cur.execute("UPDATE books SET stock_qty = stock_qty - ? WHERE id=?;", (int(qty), int(book_id)))
                note = f"Delete return {return_id}"
                if receipt_no:
                    note = f"{note} (receipt {receipt_no})"
                self._log_inventory_adjustment(
                    conn,
                    int(book_id),
                    -int(qty),
                    "delete_return",
                    note,
                    user_id,
                )
            cur.execute("DELETE FROM returns WHERE id=?;", (int(return_id),))
            conn.commit()

    def get_return_receipt(self, return_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT receipt_text, created_at FROM returns WHERE id=?;", (int(return_id),))
            return cur.fetchone()

    # -------- CSV Export helper --------
    def export_table_to_csv(self, query: str, headers: List[str], path: str, params: Tuple = ()) -> None:
        with self._connect() as conn, open(path, "w", newline="", encoding="utf-8") as f:
            cur = conn.cursor()
            cur.execute(query, params)
            rows = cur.fetchall()
            w = csv.writer(f)
            w.writerow(headers)
            w.writerows(rows)

    # -------- Reports --------
    def report_daily(self, days: int = 30):
        start = (date.today() - timedelta(days=days)).strftime("%Y-%m-%d")
        with self._connect() as conn:
            cur = conn.cursor()
            has_refund_tax = "refund_tax_cents" in self._columns(conn, "returns")
            cur.execute("""
                SELECT substr(created_at,1,10) AS day,
                       SUM(total_cents) AS revenue_cents,
                       SUM(tax_cents) AS tax_cents,
                       COUNT(*) AS sale_count
                FROM sales
                WHERE is_void=0 AND substr(created_at,1,10) >= ?
                GROUP BY day
                ORDER BY day DESC;
            """, (start,))
            sales_rows = cur.fetchall()
            sales = {d: (int(rev or 0), int(tax or 0), int(scnt or 0)) for (d, rev, tax, scnt) in sales_rows}

            if has_refund_tax:
                cur.execute("""
                    SELECT substr(created_at,1,10) AS day,
                           SUM(refund_cents) AS refund_cents,
                           SUM(refund_tax_cents) AS refund_tax_cents,
                           COUNT(*) AS return_count
                    FROM returns
                    WHERE substr(created_at,1,10) >= ?
                    GROUP BY day
                    ORDER BY day DESC;
                """, (start,))
                returns = {d: (int(rc or 0), int(rtax or 0), int(cnt or 0)) for (d, rc, rtax, cnt) in cur.fetchall()}
            else:
                cur.execute("""
                    SELECT substr(created_at,1,10) AS day,
                           SUM(refund_cents) AS refund_cents,
                           COUNT(*) AS return_count
                    FROM returns
                    WHERE substr(created_at,1,10) >= ?
                    GROUP BY day
                    ORDER BY day DESC;
                """, (start,))
                returns = {d: (int(rc or 0), 0, int(cnt or 0)) for (d, rc, cnt) in cur.fetchall()}

            out = []
            all_days = sorted(set(sales.keys()) | set(returns.keys()), reverse=True)
            for d in all_days:
                rev_i, tax_i, scnt = sales.get(d, (0, 0, 0))
                refund, refund_tax, rcnt = returns.get(d, (0, 0, 0))
                net = rev_i - refund
                net_tax = tax_i - refund_tax
                out.append((d, int(scnt or 0), rcnt, rev_i, refund, net, net_tax))
            return out

    def report_monthly(self):
        with self._connect() as conn:
            cur = conn.cursor()
            has_refund_tax = "refund_tax_cents" in self._columns(conn, "returns")
            cur.execute("""
                SELECT substr(created_at,1,7) AS month,
                       SUM(total_cents) AS revenue_cents,
                       SUM(tax_cents) AS tax_cents,
                       COUNT(*) AS sale_count
                FROM sales
                WHERE is_void=0
                GROUP BY month
                ORDER BY month DESC;
            """)
            sales = {a: (int(b or 0), int(c or 0), int(d or 0)) for (a, b, c, d) in cur.fetchall()}

            if has_refund_tax:
                cur.execute("""
                    SELECT substr(created_at,1,7) AS month,
                           SUM(refund_cents) AS refund_cents,
                           SUM(refund_tax_cents) AS refund_tax_cents
                    FROM returns
                    GROUP BY month
                    ORDER BY month DESC;
                """)
                returns = {a: (int(b or 0), int(c or 0)) for (a, b, c) in cur.fetchall()}
            else:
                cur.execute("""
                    SELECT substr(created_at,1,7) AS month,
                           SUM(refund_cents) AS refund_cents
                    FROM returns
                    GROUP BY month
                    ORDER BY month DESC;
                """)
                returns = {a: (int(b or 0), 0) for (a, b) in cur.fetchall()}

            out = []
            all_months = sorted(set(sales.keys()) | set(returns.keys()), reverse=True)
            for month in all_months:
                rev, tax, scnt = sales.get(month, (0, 0, 0))
                refund, refund_tax = returns.get(month, (0, 0))
                net_rev = rev - refund
                net_tax = tax - refund_tax
                out.append((month, net_rev, net_tax, scnt))
            return out

    def report_top_books(self, limit: int = 10):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                WITH sold AS (
                    SELECT b.id AS book_id,
                           b.title AS title,
                           SUM(si.quantity) AS units,
                           SUM(si.line_total_cents) AS revenue_cents,
                           SUM((si.unit_price_cents - si.unit_cost_cents) * si.quantity - si.line_discount_cents) AS profit_cents
                    FROM sale_items si
                    JOIN sales s ON s.id = si.sale_id
                    JOIN books b ON b.id = si.book_id
                    WHERE s.is_void=0
                    GROUP BY b.id
                ),
                sale_cost AS (
                    SELECT sale_id, book_id, MAX(unit_cost_cents) AS unit_cost_cents
                    FROM sale_items
                    GROUP BY sale_id, book_id
                ),
                returned AS (
                    SELECT ri.book_id AS book_id,
                           SUM(ri.quantity) AS units,
                           SUM(ri.line_total_cents) AS revenue_cents,
                           SUM((ri.unit_price_cents - sc.unit_cost_cents) * ri.quantity) AS profit_cents
                    FROM return_items ri
                    JOIN returns r ON r.id = ri.return_id
                    JOIN sale_cost sc ON sc.sale_id = r.sale_id AND sc.book_id = ri.book_id
                    GROUP BY ri.book_id
                )
                SELECT sold.title,
                       sold.units - IFNULL(returned.units, 0) AS units,
                       sold.revenue_cents - IFNULL(returned.revenue_cents, 0) AS revenue_cents,
                       sold.profit_cents - IFNULL(returned.profit_cents, 0) AS profit_cents
                FROM sold
                LEFT JOIN returned ON returned.book_id = sold.book_id
                ORDER BY revenue_cents DESC
                LIMIT ?;
            """, (int(limit),))
            return [(a, int(b or 0), int(c or 0), int(d or 0)) for (a, b, c, d) in cur.fetchall()]

    def report_top_platforms(self, limit: int = 10):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                WITH refunds AS (
                    SELECT s.platform AS platform,
                           SUM(r.refund_cents) AS refund_cents
                    FROM returns r
                    JOIN sales s ON s.id = r.sale_id
                    WHERE s.is_void=0
                    GROUP BY s.platform
                )
                SELECT s.platform,
                       COUNT(*) AS sales,
                       SUM(s.total_cents) - IFNULL(refunds.refund_cents, 0) AS revenue_cents
                FROM sales s
                LEFT JOIN refunds ON refunds.platform = s.platform
                WHERE s.is_void=0
                GROUP BY s.platform
                ORDER BY revenue_cents DESC
                LIMIT ?;
            """, (int(limit),))
            return [(a, int(b or 0), int(c or 0)) for (a, b, c) in cur.fetchall()]

    def report_summary(self, days: int = 30) -> Dict[str, Any]:
        start = (date.today() - timedelta(days=days)).strftime("%Y-%m-%d")
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT COUNT(*),
                       SUM(total_cents),
                       SUM(tax_cents)
                FROM sales
                WHERE is_void=0 AND substr(created_at,1,10) >= ?;
            """, (start,))
            sale_count, revenue_cents, tax_cents = cur.fetchone()

            has_refund_tax = "refund_tax_cents" in self._columns(conn, "returns")
            if has_refund_tax:
                cur.execute("""
                    SELECT COUNT(*),
                           SUM(refund_cents),
                           SUM(refund_tax_cents)
                    FROM returns
                    WHERE substr(created_at,1,10) >= ?;
                """, (start,))
                return_count, refund_cents, refund_tax_cents = cur.fetchone()
            else:
                cur.execute("""
                    SELECT COUNT(*),
                           SUM(refund_cents)
                    FROM returns
                    WHERE substr(created_at,1,10) >= ?;
                """, (start,))
                return_count, refund_cents = cur.fetchone()
                refund_tax_cents = 0

            cur.execute("""
                SELECT SUM((si.unit_price_cents - si.unit_cost_cents) * si.quantity - si.line_discount_cents)
                FROM sale_items si
                JOIN sales s ON s.id = si.sale_id
                WHERE s.is_void=0 AND substr(s.created_at,1,10) >= ?;
            """, (start,))
            profit_cents = cur.fetchone()[0] or 0

            cur.execute("""
                WITH sale_cost AS (
                    SELECT sale_id, book_id, MAX(unit_cost_cents) AS unit_cost_cents
                    FROM sale_items
                    GROUP BY sale_id, book_id
                )
                SELECT SUM((ri.unit_price_cents - sc.unit_cost_cents) * ri.quantity)
                FROM return_items ri
                JOIN returns r ON r.id = ri.return_id
                JOIN sale_cost sc ON sc.sale_id = r.sale_id AND sc.book_id = ri.book_id
                WHERE substr(r.created_at,1,10) >= ?;
            """, (start,))
            return_profit_cents = cur.fetchone()[0] or 0

        sale_count = int(sale_count or 0)
        return_count = int(return_count or 0)
        revenue_cents = int(revenue_cents or 0)
        refund_cents = int(refund_cents or 0)
        tax_cents = int(tax_cents or 0)
        refund_tax_cents = int(refund_tax_cents or 0)
        net_revenue = revenue_cents - refund_cents
        net_tax = tax_cents - refund_tax_cents
        net_profit = int(profit_cents or 0) - int(return_profit_cents or 0)
        avg_order = int(net_revenue / sale_count) if sale_count else 0
        return_rate = (return_count / sale_count) if sale_count else 0.0

        return {
            "sales_count": sale_count,
            "returns_count": return_count,
            "revenue_cents": revenue_cents,
            "refund_cents": refund_cents,
            "net_revenue_cents": net_revenue,
            "tax_cents": tax_cents,
            "refund_tax_cents": refund_tax_cents,
            "net_tax_cents": net_tax,
            "profit_cents": net_profit,
            "avg_order_cents": avg_order,
            "return_rate": return_rate,
        }

    def report_by_category(self):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                WITH sold AS (
                    SELECT IFNULL(cat.name,'Uncategorized') AS category,
                           SUM(si.line_total_cents) AS revenue_cents,
                           SUM((si.unit_price_cents - si.unit_cost_cents) * si.quantity - si.line_discount_cents) AS profit_cents
                    FROM sale_items si
                    JOIN sales s ON s.id = si.sale_id
                    JOIN books b ON b.id = si.book_id
                    LEFT JOIN categories cat ON cat.id = b.category_id
                    WHERE s.is_void=0
                    GROUP BY category
                ),
                sale_cost AS (
                    SELECT sale_id, book_id, MAX(unit_cost_cents) AS unit_cost_cents
                    FROM sale_items
                    GROUP BY sale_id, book_id
                ),
                returned AS (
                    SELECT IFNULL(cat.name,'Uncategorized') AS category,
                           SUM(ri.line_total_cents) AS revenue_cents,
                           SUM((ri.unit_price_cents - sc.unit_cost_cents) * ri.quantity) AS profit_cents
                    FROM return_items ri
                    JOIN returns r ON r.id = ri.return_id
                    JOIN sale_cost sc ON sc.sale_id = r.sale_id AND sc.book_id = ri.book_id
                    JOIN books b ON b.id = ri.book_id
                    LEFT JOIN categories cat ON cat.id = b.category_id
                    GROUP BY category
                )
                SELECT sold.category,
                       sold.revenue_cents - IFNULL(returned.revenue_cents, 0) AS revenue_cents,
                       sold.profit_cents - IFNULL(returned.profit_cents, 0) AS profit_cents
                FROM sold
                LEFT JOIN returned ON returned.category = sold.category
                ORDER BY revenue_cents DESC;
            """)
            return [(a, int(b or 0), int(c or 0)) for (a, b, c) in cur.fetchall()]

    def list_reorder_suggestions(self, limit: int = 200):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT b.id, b.title, b.stock_qty, b.reorder_point, b.reorder_qty,
                       IFNULL(cat.name,'(Uncategorized)') AS category
                FROM books b
                LEFT JOIN categories cat ON cat.id = b.category_id
                WHERE b.is_active=1
                  AND b.reorder_point > 0
                  AND b.stock_qty <= b.reorder_point
                ORDER BY (b.reorder_point - b.stock_qty) DESC, b.title
                LIMIT ?;
            """, (int(limit),))
            return [(int(a), b, int(c), int(d), int(e), f) for (a, b, c, d, e, f) in cur.fetchall()]


# -------------------------- UI: dialogs --------------------------
class Dialog:
    @staticmethod
    def ask_fields(root, title, fields, initial=None, password_keys=None):
        """
        fields: list of (label, key)
        initial: dict key->value
        password_keys: set/list of keys whose entry should show='*'
        """
        dlg = tk.Toplevel(root)
        dlg.title(title)
        dlg.transient(root)
        dlg.grab_set()
        dlg.resizable(False, False)

        frm = ttk.Frame(dlg, padding=12)
        frm.pack(fill="both", expand=True)

        entries = {}
        password_keys = set(password_keys or [])

        for r, (label, key) in enumerate(fields):
            ttk.Label(frm, text=label).grid(row=r, column=0, sticky="w", pady=4)
            show = "*" if key in password_keys else ""
            e = ttk.Entry(frm, width=48, show=show)
            e.grid(row=r, column=1, pady=4)
            if initial and key in initial and initial[key] is not None:
                e.insert(0, str(initial[key]))
            entries[key] = e

        if fields:
            entries[fields[0][1]].focus_set()

        out = {"data": None}

        def ok():
            out["data"] = {k: entries[k].get().strip() for _, k in fields}
            dlg.destroy()

        def cancel():
            dlg.destroy()

        btns = ttk.Frame(frm)
        btns.grid(row=len(fields), column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=cancel).pack(side="right")
        ttk.Button(btns, text="OK", command=ok).pack(side="right", padx=8)

        root.wait_window(dlg)
        return out["data"]

    @staticmethod
    def show_text(root, title, text):
        win = tk.Toplevel(root)
        win.title(title)
        win.geometry("820x620")
        win.transient(root)

        t = tk.Text(win, wrap="none")
        t.pack(fill="both", expand=True, padx=10, pady=10)
        t.insert("1.0", text)
        t.configure(state="disabled")

        ttk.Button(win, text="Close", command=win.destroy).pack(pady=(0, 10))


# -------------------------- App --------------------------
class App:
    def __init__(self):
        self.db = DB(DB_PATH)
        self.user = None  # dict{id,username,role}
        self.cart: Dict[int, Dict[str, Any]] = {}
        self.last_category_choice = ""

        self.root = tk.Tk()
        self.root.title("Inventory POS")
        self.root.geometry("1200x720")

        temp_password = self.db.get_setting("admin_temp_password")
        if temp_password:
            messagebox.showinfo(
                "Temporary admin password",
                "A temporary admin password was generated on first run.\n"
                f"Username: admin\nPassword: {temp_password}\n\n"
                "You will be prompted to change it after login.",
            )

        self._login()

        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True, padx=10, pady=10)

        self._build_books_tab()
        self._build_pos_tab()
        self._build_pending_tab()
        self._build_pickup_tab()
        self._build_sales_tab()
        self._build_reports_tab()
        self._build_admin_tab()

        self.refresh_all()

    # ---------------- Login ----------------
    def _login(self):
        while True:
            data = Dialog.ask_fields(
                self.root,
                "Login",
                [("Username", "u"), ("Password", "p")],
                initial={"u": "admin"},
                password_keys={"p"},
            )
            if data is None:
                raise SystemExit
            u = data["u"]
            p = data["p"]
            auth = self.db.auth_user(u, p)
            if auth:
                if auth.get("must_change_password"):
                    self._force_password_change(auth["id"])
                self.user = auth
                self.root.title(f"Inventory POS — {auth['username']} ({auth['role']})")
                return
            messagebox.showerror("Login failed", "Invalid username/password or inactive user.")

    def _force_password_change(self, user_id: int) -> None:
        while True:
            data = Dialog.ask_fields(
                self.root,
                "Change Password",
                [("New password", "p1"), ("Confirm password", "p2")],
                password_keys={"p1", "p2"},
            )
            if data is None:
                raise SystemExit
            if not data["p1"]:
                messagebox.showerror("Invalid password", "Password cannot be empty.")
                continue
            if data["p1"] != data["p2"]:
                messagebox.showerror("Password mismatch", "Passwords do not match.")
                continue
            self.db.reset_password(user_id, data["p1"])
            self.db.delete_setting("admin_temp_password")
            self.db.delete_setting("admin_temp_password_created_at")
            messagebox.showinfo("Password updated", "Password updated successfully.")
            return

    def _require_admin(self) -> bool:
        if self.user["role"] != "admin":
            messagebox.showerror("Permission denied", "Admin only.")
            return False
        return True

    # ---------------- Items tab ----------------
    def _build_books_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Dashboard")
        self.books_tab = tab

        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(2, weight=1)

        top = ttk.Frame(tab)
        top.grid(row=0, column=0, sticky="ew", padx=10, pady=10)
        top.columnconfigure(0, weight=1)

        self.book_search = tk.StringVar()
        self.book_instock = tk.IntVar(value=0)
        self.book_inactive = tk.IntVar(value=0)
        self.book_low_stock = tk.IntVar(value=0)
        self.book_condition_filter = tk.StringVar(value="All")
        self.book_availability_filter = tk.StringVar(value="Available")
        self.book_uploaded_filter = tk.StringVar(value="Any")

        filters = ttk.Frame(top)
        filters.grid(row=0, column=0, sticky="ew")
        filters.columnconfigure(1, weight=1)

        actions = ttk.Frame(top)
        actions.grid(row=0, column=1, sticky="e", padx=(12, 0))

        ttk.Label(filters, text="Search:").grid(row=0, column=0, sticky="w")
        e = ttk.Entry(filters, textvariable=self.book_search, width=28)
        e.grid(row=0, column=1, sticky="ew", padx=(6, 12))
        e.bind("<KeyRelease>", lambda _e: self.refresh_books())

        ttk.Checkbutton(
            filters,
            text="In stock only",
            variable=self.book_instock,
            command=self.refresh_books,
        ).grid(row=0, column=2, sticky="w")
        ttk.Checkbutton(
            filters,
            text="Include archived",
            variable=self.book_inactive,
            command=self.refresh_books,
        ).grid(row=0, column=3, sticky="w", padx=(10, 0))
        ttk.Checkbutton(
            filters,
            text="Low stock only",
            variable=self.book_low_stock,
            command=self.refresh_books,
        ).grid(row=0, column=4, sticky="w", padx=(10, 0))

        ttk.Label(filters, text="Condition:").grid(row=1, column=0, sticky="w", pady=(6, 0))
        condition_combo = ttk.Combobox(
            filters,
            textvariable=self.book_condition_filter,
            values=["All"] + CONDITION_OPTIONS,
            width=10,
            state="readonly",
        )
        condition_combo.grid(row=1, column=1, sticky="w", padx=(6, 12), pady=(6, 0))
        condition_combo.bind("<<ComboboxSelected>>", lambda _e: self.refresh_books())

        ttk.Label(filters, text="Availability:").grid(row=1, column=2, sticky="w", pady=(6, 0))
        availability_combo = ttk.Combobox(
            filters,
            textvariable=self.book_availability_filter,
            values=["Available", "Pending", "Pickup/Ship", "All"],
            width=12,
            state="readonly",
        )
        availability_combo.grid(row=1, column=3, sticky="w", padx=(6, 12), pady=(6, 0))
        availability_combo.bind("<<ComboboxSelected>>", lambda _e: self.refresh_books())

        ttk.Label(filters, text="Uploaded to:").grid(row=1, column=4, sticky="w", pady=(6, 0))
        uploaded_combo = ttk.Combobox(
            filters,
            textvariable=self.book_uploaded_filter,
            values=["Any", "Facebook", "eBay"],
            width=10,
            state="readonly",
        )
        uploaded_combo.grid(row=1, column=5, sticky="w", padx=(6, 12), pady=(6, 0))
        uploaded_combo.bind("<<ComboboxSelected>>", lambda _e: self.refresh_books())

        ttk.Button(actions, text="Add Item (scan supported)", command=self.add_book).grid(row=0, column=0, sticky="e")
        ttk.Button(actions, text="Edit", command=self.edit_book).grid(row=0, column=1, sticky="e", padx=6)
        ttk.Button(actions, text="Archive/Unarchive", command=self.toggle_book_active).grid(row=0, column=2, sticky="e", padx=6)
        ttk.Button(actions, text="Delete", command=self.delete_book).grid(row=0, column=3, sticky="e", padx=6)
        ttk.Button(actions, text="Restock", command=self.restock_book).grid(row=0, column=4, sticky="e", padx=6)
        ttk.Button(actions, text="Export CSV", command=self.export_books_csv).grid(row=0, column=5, sticky="e", padx=(12, 0))
        ttk.Button(actions, text="Import CSV", command=self.import_books_csv).grid(row=0, column=6, sticky="e", padx=(6, 0))

        customize = ttk.LabelFrame(tab, text="Customize view")
        customize.grid(row=1, column=0, sticky="ew", padx=10, pady=(0, 8))

        self.book_column_vars = {
            "isbn": tk.IntVar(value=1),
            "author": tk.IntVar(value=1),
            "category": tk.IntVar(value=1),
            "location": tk.IntVar(value=1),
            "dimensions": tk.IntVar(value=1),
            "weight": tk.IntVar(value=1),
            "cost": tk.IntVar(value=1),
            "condition": tk.IntVar(value=1),
            "availability": tk.IntVar(value=1),
            "active": tk.IntVar(value=1),
            "facebook": tk.IntVar(value=1),
            "ebay": tk.IntVar(value=1),
        }
        for key, label in [
            ("isbn", "Barcode"),
            ("author", "Brand/Details"),
            ("category", "Category"),
            ("condition", "Condition"),
            ("availability", "Availability"),
            ("location", "Location"),
            ("active", "Active"),
            ("dimensions", "Dimensions"),
            ("weight", "Weight"),
            ("cost", "Cost"),
            ("facebook", "Facebook"),
            ("ebay", "eBay"),
        ]:
            ttk.Checkbutton(
                customize,
                text=label,
                variable=self.book_column_vars[key],
                command=self._apply_book_column_visibility,
            ).pack(side="left", padx=6)

        self.books_tree = ttk.Treeview(
            tab,
            columns=(
                "isbn",
                "title",
                "author",
                "category",
                "condition",
                "availability",
                "location",
                "dimensions",
                "weight",
                "price",
                "cost",
                "stock",
                "active",
                "facebook",
                "ebay",
            ),
            show="headings",
            height=18,
        )
        for col, lbl, w, anchor in [
            ("isbn", "Barcode", 140, "w"),
            ("title", "Item", 300, "w"),
            ("author", "Brand/Details", 180, "w"),
            ("category", "Category", 130, "w"),
            ("condition", "Condition", 110, "w"),
            ("availability", "Availability", 120, "w"),
            ("location", "Locations", 160, "w"),
            ("dimensions", "Dimensions (LxWxH)", 160, "w"),
            ("weight", "Weight (lb/oz)", 120, "w"),
            ("price", "Price", 90, "e"),
            ("cost", "Cost", 90, "e"),
            ("stock", "Stock", 70, "center"),
            ("active", "Active", 70, "center"),
            ("facebook", "Facebook", 80, "center"),
            ("ebay", "eBay", 70, "center"),
        ]:
            self.books_tree.heading(col, text=lbl)
            self.books_tree.column(col, width=w, anchor=anchor)

        self.books_tree.grid(row=2, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.books_tree.bind("<Double-1>", lambda _e: self.edit_book())
        self.books_tree.tag_configure("low_stock", background="#fff3cd")
        self._apply_book_column_visibility()

    def refresh_books(self):
        for i in self.books_tree.get_children():
            self.books_tree.delete(i)

        rows = self.db.list_books(
            search=self.book_search.get(),
            in_stock_only=bool(self.book_instock.get()),
            include_inactive=bool(self.book_inactive.get()),
            low_stock_only=bool(self.book_low_stock.get()),
            condition=None if self.book_condition_filter.get() == "All" else self.book_condition_filter.get(),
            availability_status=None
            if self.book_availability_filter.get() == "All"
            else AVAILABILITY_STATUSES.get(self.book_availability_filter.get(), "available"),
            uploaded_platform={
                "Any": None,
                "Facebook": "facebook",
                "eBay": "ebay",
            }.get(self.book_uploaded_filter.get()),
        )
        for (
            bid,
            barcode,
            _isbn,
            title,
            author,
            location,
            length_in,
            width_in,
            height_in,
            weight_lb,
            weight_oz,
            condition,
            price,
            cost,
            stock,
            reorder_point,
            active,
            uploaded_facebook,
            uploaded_ebay,
            availability_status,
            catname,
        ) in rows:
            tags = ()
            if reorder_point and stock <= reorder_point:
                tags = ("low_stock",)
            self.books_tree.insert(
                "", "end", iid=str(bid),
                values=(
                    barcode or "",
                    title,
                    author,
                    catname or "",
                    condition or "",
                    AVAILABILITY_LABELS.get(availability_status, availability_status),
                    location or "",
                    format_dimensions(length_in, width_in, height_in),
                    format_weight(weight_lb, weight_oz),
                    cents_to_money(price),
                    cents_to_money(cost),
                    stock,
                    "yes" if active else "no",
                    "yes" if uploaded_facebook else "no",
                    "yes" if uploaded_ebay else "no",
                ),
                tags=tags,
            )

        self._refresh_pos_books()

    def _apply_book_column_visibility(self):
        if not hasattr(self, "books_tree"):
            return
        base_cols = [
            "title",
            "price",
            "stock",
        ]
        optional_cols = [
            ("isbn", self.book_column_vars["isbn"]),
            ("author", self.book_column_vars["author"]),
            ("category", self.book_column_vars["category"]),
            ("condition", self.book_column_vars["condition"]),
            ("availability", self.book_column_vars["availability"]),
            ("location", self.book_column_vars["location"]),
            ("dimensions", self.book_column_vars["dimensions"]),
            ("weight", self.book_column_vars["weight"]),
            ("cost", self.book_column_vars["cost"]),
            ("active", self.book_column_vars["active"]),
            ("facebook", self.book_column_vars["facebook"]),
            ("ebay", self.book_column_vars["ebay"]),
        ]
        cols = base_cols + [name for name, var in optional_cols if var.get()]
        self.books_tree["displaycolumns"] = cols

    def _selected_book_id(self) -> Optional[int]:
        sel = self.books_tree.selection()
        return int(sel[0]) if sel else None

    def add_book(self):
        """
        Add item dialog with scan support:
        - scan string can include UPC/EAN barcode or price-only barcode.
        - lookup via UPCItemDB if barcode present.
        """
        dlg = tk.Toplevel(self.root)
        dlg.title("Add Item (scan barcode/price)")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        frame = ttk.Frame(dlg, padding=12)
        frame.pack(fill="both", expand=True)

        scan_var = tk.StringVar(value="")
        barcode_var = tk.StringVar(value="")
        isbn_var = tk.StringVar(value="")
        title_var = tk.StringVar(value="")
        author_var = tk.StringVar(value="")
        cat_var = tk.StringVar(value=self.last_category_choice)
        location_var = tk.StringVar(value="")
        condition_var = tk.StringVar(value="Good")
        length_var = tk.StringVar(value="")
        width_var = tk.StringVar(value="")
        height_var = tk.StringVar(value="")
        weight_lb_var = tk.StringVar(value="")
        weight_oz_var = tk.StringVar(value="")
        price_var = tk.StringVar(value="0.00")
        cost_var = tk.StringVar(value="0.00")
        stock_var = tk.StringVar(value="1")
        reorder_point_var = tk.StringVar(value="0")
        reorder_qty_var = tk.StringVar(value="0")
        uploaded_facebook_var = tk.IntVar(value=0)
        uploaded_ebay_var = tk.IntVar(value=0)
        add_another_var = tk.IntVar(value=0)

        def show_status(msg: str):
            status_lbl.configure(text=msg)

        def do_parse_scan():
            raw = scan_var.get().strip()
            if not raw:
                messagebox.showerror("Scan needed", "Scan something into the Scan field.", parent=dlg)
                return
            barcode, price = parse_scan_barcode_and_price(raw)
            if barcode:
                barcode_var.set(barcode)
            if price:
                price_var.set(price)
            if not barcode and not price:
                messagebox.showerror("Unrecognized", "Could not parse barcode or price from scan.", parent=dlg)
                return
            show_status(f"Parsed scan → Barcode: {barcode or '(none)'}  Price: {price or '(none)'}")

            # auto-lookup if barcode found
            if barcode:
                info = fetch_title_info_upcitemdb(barcode)
                if info:
                    title_var.set(info.get("title", ""))
                    author_var.set(info.get("studio", ""))
                    show_status("Parsed + barcode lookup OK (item/brand filled).")
                else:
                    show_status("Parsed barcode, but lookup failed (enter item/brand manually).")

        def do_lookup_barcode():
            barcode = normalize_barcode(barcode_var.get())
            if not barcode:
                messagebox.showerror("Invalid barcode", "No valid barcode detected in Barcode field.", parent=dlg)
                return
            barcode_var.set(barcode)
            info = fetch_title_info_upcitemdb(barcode)
            if not info:
                messagebox.showerror("Lookup failed", "Could not fetch metadata (no result or no internet).", parent=dlg)
                return
            title_var.set(info.get("title", ""))
            author_var.set(info.get("studio", ""))
            show_status("Barcode lookup OK (item/brand filled).")

        def do_parse_price_field():
            p = parse_price_from_scan(price_var.get())
            if not p:
                messagebox.showerror("Price not recognized", "Could not parse price from Price field.", parent=dlg)
                return
            price_var.set(p)
            show_status("Price parsed/normalized.")

        # Layout
        r = 0
        ttk.Label(frame, text="Scan (barcode or price-only):").grid(row=r, column=0, sticky="w", pady=4)
        scan_entry = ttk.Entry(frame, textvariable=scan_var, width=46)
        scan_entry.grid(row=r, column=1, pady=4, sticky="w")
        ttk.Button(frame, text="Parse Scan", command=do_parse_scan).grid(row=r, column=2, padx=8)
        r += 1

        ttk.Label(frame, text="Barcode:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=barcode_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        ttk.Button(frame, text="Lookup Barcode", command=do_lookup_barcode).grid(row=r, column=2, padx=8)
        r += 1

        ttk.Label(frame, text="ISBN (optional):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=isbn_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Item name:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=title_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Brand/Details:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=author_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Category (optional):").grid(row=r, column=0, sticky="w", pady=4)
        categories = [name for (_cid, name, _active) in self.db.list_categories(include_inactive=True)]
        cat_combo = ttk.Combobox(frame, textvariable=cat_var, values=categories, width=44)
        cat_combo.grid(row=r, column=1, pady=4, sticky="w")

        def update_category_autocomplete(_event=None):
            value = cat_var.get()
            if not value:
                cat_combo["values"] = categories
                return
            matches = [c for c in categories if c.lower().startswith(value.lower())]
            if matches:
                cat_combo["values"] = matches
                if matches[0].lower() != value.lower():
                    cat_combo.set(matches[0])
                    cat_combo.icursor(len(value))
                    cat_combo.select_range(len(value), "end")
            else:
                cat_combo["values"] = categories

        cat_combo.bind("<KeyRelease>", update_category_autocomplete)
        r += 1

        ttk.Label(frame, text="Condition:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Combobox(frame, textvariable=condition_var, values=CONDITION_OPTIONS, width=44, state="readonly").grid(
            row=r, column=1, pady=4, sticky="w"
        )
        r += 1

        ttk.Label(frame, text="Locations (comma-separated, optional):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=location_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Dimensions (inches):").grid(row=r, column=0, sticky="w", pady=4)
        dim_frame = ttk.Frame(frame)
        dim_frame.grid(row=r, column=1, pady=4, sticky="w")
        ttk.Label(dim_frame, text="L").pack(side="left")
        ttk.Entry(dim_frame, textvariable=length_var, width=8).pack(side="left", padx=(4, 10))
        ttk.Label(dim_frame, text="W").pack(side="left")
        ttk.Entry(dim_frame, textvariable=width_var, width=8).pack(side="left", padx=(4, 10))
        ttk.Label(dim_frame, text="H").pack(side="left")
        ttk.Entry(dim_frame, textvariable=height_var, width=8).pack(side="left", padx=(4, 0))
        r += 1

        ttk.Label(frame, text="Weight (optional):").grid(row=r, column=0, sticky="w", pady=4)
        weight_frame = ttk.Frame(frame)
        weight_frame.grid(row=r, column=1, pady=4, sticky="w")
        ttk.Label(weight_frame, text="lb").pack(side="left")
        ttk.Entry(weight_frame, textvariable=weight_lb_var, width=8).pack(side="left", padx=(4, 10))
        ttk.Label(weight_frame, text="oz").pack(side="left")
        ttk.Entry(weight_frame, textvariable=weight_oz_var, width=8).pack(side="left", padx=(4, 0))
        r += 1

        ttk.Label(frame, text="Price (e.g. 12.99):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=price_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        price_btns = ttk.Frame(frame)
        price_btns.grid(row=r, column=2, padx=8, sticky="w")
        ttk.Button(price_btns, text="Parse Price", command=do_parse_price_field).pack(side="left")
        r += 1

        ttk.Label(frame, text="Cost (e.g. 7.50):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=cost_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Stock qty:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=stock_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Reorder point:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=reorder_point_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Reorder qty:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=reorder_qty_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        upload_frame = ttk.Frame(frame)
        upload_frame.grid(row=r, column=0, columnspan=3, sticky="w", pady=4)
        ttk.Label(upload_frame, text="Uploaded to:").pack(side="left")
        ttk.Checkbutton(upload_frame, text="Facebook", variable=uploaded_facebook_var).pack(side="left", padx=(10, 0))
        ttk.Checkbutton(upload_frame, text="eBay", variable=uploaded_ebay_var).pack(side="left", padx=(10, 0))
        r += 1

        ttk.Checkbutton(frame, text="Add another after save", variable=add_another_var).grid(
            row=r, column=0, columnspan=2, sticky="w", pady=(4, 0)
        )
        r += 1

        status_lbl = ttk.Label(frame, text="", foreground="#444")
        status_lbl.grid(row=r, column=0, columnspan=3, sticky="w", pady=(8, 0))
        r += 1

        def on_add():
            barcode = normalize_barcode(barcode_var.get()) or None
            isbn = (isbn_var.get().strip() or None)
            title = title_var.get().strip()
            author = author_var.get().strip()
            cat_name = cat_var.get().strip()
            location = normalize_locations(location_var.get())
            condition = condition_var.get().strip() or "Good"
            length_raw = length_var.get()
            width_raw = width_var.get()
            height_raw = height_var.get()
            weight_lb_raw = weight_lb_var.get()
            weight_oz_raw = weight_oz_var.get()
            price_s = price_var.get().strip()
            cost_s = cost_var.get().strip()
            stock_s = stock_var.get().strip()
            reorder_point_s = reorder_point_var.get().strip()
            reorder_qty_s = reorder_qty_var.get().strip()
            uploaded_facebook = 1 if uploaded_facebook_var.get() else 0
            uploaded_ebay = 1 if uploaded_ebay_var.get() else 0

            if not title:
                messagebox.showerror("Missing data", "Item name is required.", parent=dlg)
                return

            try:
                length_in = parse_optional_float(length_raw, "length")
                width_in = parse_optional_float(width_raw, "width")
                height_in = parse_optional_float(height_raw, "height")
                weight_lb = parse_optional_float(weight_lb_raw, "weight (lb)")
                weight_oz = parse_optional_float(weight_oz_raw, "weight (oz)")
                if weight_oz is not None and weight_oz >= 16:
                    raise ValueError("Weight (oz) must be between 0 and 15.")
                price_cents = dollars_to_cents(price_s)
                cost_cents = dollars_to_cents(cost_s)
                stock = int(stock_s)
                reorder_point = int(reorder_point_s or 0)
                reorder_qty = int(reorder_qty_s or 0)
                if stock < 0:
                    raise ValueError
            except Exception:
                messagebox.showerror("Bad input", "Check dimensions/weight/price/cost/stock/reorder values.", parent=dlg)
                return

            if reorder_point < 0 or reorder_qty < 0:
                messagebox.showerror("Bad input", "Reorder values cannot be negative.", parent=dlg)
                return

            if cat_name:
                self.last_category_choice = cat_name
            else:
                self.last_category_choice = ""

            if condition not in CONDITION_OPTIONS:
                messagebox.showerror("Bad condition", "Choose a valid condition.", parent=dlg)
                return

            # category: auto-create if provided
            cat_id = None
            if cat_name:
                try:
                    self.db.add_category(cat_name)
                except sqlite3.IntegrityError:
                    pass
                cats_all = self.db.list_categories(include_inactive=True)
                for (cid, name, _active) in cats_all:
                    if name == cat_name:
                        cat_id = cid
                        break

            try:
                if barcode:
                    existing = self.db.get_book_by_barcode(barcode)
                    if existing:
                        self.db.adjust_stock(int(existing[0]), stock, "restock", "Add item (merge)", self.user["id"])
                        merged_location = merge_locations(existing[6], location)
                        if merged_location != existing[6]:
                            self.db.set_book_location(int(existing[0]), merged_location)
                    else:
                        self.db.add_book(
                            barcode,
                            isbn,
                            title,
                            author,
                            cat_id,
                            location,
                            length_in,
                            width_in,
                            height_in,
                            weight_lb,
                            weight_oz,
                            condition,
                            price_cents,
                            cost_cents,
                            stock,
                            reorder_point,
                            reorder_qty,
                            1,
                            uploaded_facebook,
                            uploaded_ebay,
                            "available",
                        )
                else:
                    self.db.add_book(
                        barcode,
                        isbn,
                        title,
                        author,
                        cat_id,
                        location,
                        length_in,
                        width_in,
                        height_in,
                        weight_lb,
                        weight_oz,
                        condition,
                        price_cents,
                        cost_cents,
                        stock,
                        reorder_point,
                        reorder_qty,
                        1,
                        uploaded_facebook,
                        uploaded_ebay,
                        "available",
                    )
            except sqlite3.IntegrityError as e:
                messagebox.showerror("DB error", f"Could not add item.\n\n{e}", parent=dlg)
                return

            self.refresh_books()
            self.refresh_reports()
            if add_another_var.get():
                barcode_var.set("")
                isbn_var.set("")
                title_var.set("")
                author_var.set("")
                price_var.set("0.00")
                cost_var.set("0.00")
                stock_var.set("1")
                reorder_point_var.set("0")
                reorder_qty_var.set("0")
                scan_var.set("")
                length_var.set("")
                width_var.set("")
                height_var.set("")
                weight_lb_var.set("")
                weight_oz_var.set("")
                condition_var.set("Good")
                uploaded_facebook_var.set(0)
                uploaded_ebay_var.set(0)
                scan_entry.focus_set()
                show_status("Added. Ready for another item.")
            else:
                dlg.destroy()

        btns = ttk.Frame(frame)
        btns.grid(row=r, column=0, columnspan=3, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=dlg.destroy).pack(side="right")
        add_btn = ttk.Button(btns, text="Add Item", command=on_add)
        add_btn.pack(side="right", padx=8)

        def on_scan_enter(_event):
            do_parse_scan()
            add_btn.focus_set()
            return "break"

        dlg.bind("<Return>", lambda _e: on_add())
        scan_entry.bind("<Return>", on_scan_enter)
        scan_entry.focus_set()
        self.root.wait_window(dlg)

    def edit_book(self):
        bid = self._selected_book_id()
        if not bid:
            messagebox.showerror("No selection", "Select an item.")
            return
        row = self.db.get_book(bid)
        if not row:
            messagebox.showerror("Missing", "Item not found.")
            return

        (
            _id,
            barcode,
            isbn,
            title,
            author,
            cat_id,
            location,
            length_in,
            width_in,
            height_in,
            weight_lb,
            weight_oz,
            condition,
            price,
            cost,
            stock,
            reorder_point,
            reorder_qty,
            active,
            uploaded_facebook,
            uploaded_ebay,
            availability_status,
        ) = row

        catname = ""
        if cat_id:
            for (cid, nm, _ac) in self.db.list_categories(include_inactive=True):
                if cid == cat_id:
                    catname = nm
                    break

        dlg = tk.Toplevel(self.root)
        dlg.title("Edit Item")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        frame = ttk.Frame(dlg, padding=12)
        frame.pack(fill="both", expand=True)

        barcode_var = tk.StringVar(value=barcode or "")
        isbn_var = tk.StringVar(value=isbn or "")
        title_var = tk.StringVar(value=title)
        author_var = tk.StringVar(value=author)
        cat_var = tk.StringVar(value=catname)
        location_var = tk.StringVar(value=location or "")
        condition_var = tk.StringVar(value=condition or "Good")
        availability_var = tk.StringVar(value=AVAILABILITY_LABELS.get(availability_status, "Available"))
        length_var = tk.StringVar(value="" if length_in is None else str(length_in))
        width_var = tk.StringVar(value="" if width_in is None else str(width_in))
        height_var = tk.StringVar(value="" if height_in is None else str(height_in))
        weight_lb_var = tk.StringVar(value="" if weight_lb is None else str(weight_lb))
        weight_oz_var = tk.StringVar(value="" if weight_oz is None else str(weight_oz))
        price_var = tk.StringVar(value=f"{int(price)/100:.2f}")
        cost_var = tk.StringVar(value=f"{int(cost)/100:.2f}")
        stock_var = tk.StringVar(value=str(stock))
        reorder_point_var = tk.StringVar(value=str(reorder_point))
        reorder_qty_var = tk.StringVar(value=str(reorder_qty))
        active_var = tk.IntVar(value=1 if int(active) else 0)
        uploaded_facebook_var = tk.IntVar(value=1 if int(uploaded_facebook) else 0)
        uploaded_ebay_var = tk.IntVar(value=1 if int(uploaded_ebay) else 0)

        def show_status(msg: str):
            status_lbl.configure(text=msg)

        def do_parse_price_field():
            p = parse_price_from_scan(price_var.get())
            if not p:
                messagebox.showerror("Price not recognized", "Could not parse price from Price field.", parent=dlg)
                return
            price_var.set(p)
            show_status("Price parsed/normalized.")

        r = 0
        ttk.Label(frame, text="Barcode (optional):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=barcode_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="ISBN (optional):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=isbn_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Item name:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=title_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Brand/Details:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=author_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Category (optional):").grid(row=r, column=0, sticky="w", pady=4)
        categories = [name for (_cid, name, _active) in self.db.list_categories(include_inactive=True)]
        cat_combo = ttk.Combobox(frame, textvariable=cat_var, values=categories, width=44)
        cat_combo.grid(row=r, column=1, pady=4, sticky="w")

        def update_category_autocomplete(_event=None):
            value = cat_var.get()
            if not value:
                cat_combo["values"] = categories
                return
            matches = [c for c in categories if c.lower().startswith(value.lower())]
            if matches:
                cat_combo["values"] = matches
                if matches[0].lower() != value.lower():
                    cat_combo.set(matches[0])
                    cat_combo.icursor(len(value))
                    cat_combo.select_range(len(value), "end")
            else:
                cat_combo["values"] = categories

        cat_combo.bind("<KeyRelease>", update_category_autocomplete)
        r += 1

        ttk.Label(frame, text="Condition:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Combobox(frame, textvariable=condition_var, values=CONDITION_OPTIONS, width=44, state="readonly").grid(
            row=r, column=1, pady=4, sticky="w"
        )
        r += 1

        ttk.Label(frame, text="Availability:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Combobox(
            frame,
            textvariable=availability_var,
            values=["Available", "Pending", "Pickup/Ship"],
            width=44,
            state="readonly",
        ).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Locations (comma-separated, optional):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=location_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Dimensions (inches):").grid(row=r, column=0, sticky="w", pady=4)
        dim_frame = ttk.Frame(frame)
        dim_frame.grid(row=r, column=1, pady=4, sticky="w")
        ttk.Label(dim_frame, text="L").pack(side="left")
        ttk.Entry(dim_frame, textvariable=length_var, width=8).pack(side="left", padx=(4, 10))
        ttk.Label(dim_frame, text="W").pack(side="left")
        ttk.Entry(dim_frame, textvariable=width_var, width=8).pack(side="left", padx=(4, 10))
        ttk.Label(dim_frame, text="H").pack(side="left")
        ttk.Entry(dim_frame, textvariable=height_var, width=8).pack(side="left", padx=(4, 0))
        r += 1

        ttk.Label(frame, text="Weight (optional):").grid(row=r, column=0, sticky="w", pady=4)
        weight_frame = ttk.Frame(frame)
        weight_frame.grid(row=r, column=1, pady=4, sticky="w")
        ttk.Label(weight_frame, text="lb").pack(side="left")
        ttk.Entry(weight_frame, textvariable=weight_lb_var, width=8).pack(side="left", padx=(4, 10))
        ttk.Label(weight_frame, text="oz").pack(side="left")
        ttk.Entry(weight_frame, textvariable=weight_oz_var, width=8).pack(side="left", padx=(4, 0))
        r += 1

        ttk.Label(frame, text="Price (e.g. 12.99):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=price_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        price_btns = ttk.Frame(frame)
        price_btns.grid(row=r, column=2, padx=8, sticky="w")
        ttk.Button(price_btns, text="Parse Price", command=do_parse_price_field).pack(side="left")
        r += 1

        ttk.Label(frame, text="Cost (e.g. 7.50):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=cost_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Stock qty:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=stock_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Reorder point:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=reorder_point_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Reorder qty:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=reorder_qty_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        upload_frame = ttk.Frame(frame)
        upload_frame.grid(row=r, column=0, columnspan=3, sticky="w", pady=4)
        ttk.Label(upload_frame, text="Uploaded to:").pack(side="left")
        ttk.Checkbutton(upload_frame, text="Facebook", variable=uploaded_facebook_var).pack(side="left", padx=(10, 0))
        ttk.Checkbutton(upload_frame, text="eBay", variable=uploaded_ebay_var).pack(side="left", padx=(10, 0))
        r += 1

        ttk.Checkbutton(frame, text="Active", variable=active_var).grid(row=r, column=1, sticky="w", pady=4)
        r += 1

        status_lbl = ttk.Label(frame, text="", foreground="#444")
        status_lbl.grid(row=r, column=0, columnspan=3, sticky="w", pady=(8, 0))
        r += 1

        def on_save():
            barcode_val = normalize_barcode(barcode_var.get()) or None
            isbn_val = isbn_var.get().strip() or None
            title_val = title_var.get().strip()
            author_val = author_var.get().strip()
            cat_name = cat_var.get().strip()
            location_val = normalize_locations(location_var.get())
            condition_val = condition_var.get().strip() or "Good"
            availability_val = AVAILABILITY_STATUSES.get(availability_var.get(), "available")
            length_raw = length_var.get()
            width_raw = width_var.get()
            height_raw = height_var.get()
            weight_lb_raw = weight_lb_var.get()
            weight_oz_raw = weight_oz_var.get()
            price_s = price_var.get().strip()
            cost_s = cost_var.get().strip()
            stock_s = stock_var.get().strip()
            reorder_point_s = reorder_point_var.get().strip()
            reorder_qty_s = reorder_qty_var.get().strip()
            uploaded_facebook_val = 1 if uploaded_facebook_var.get() else 0
            uploaded_ebay_val = 1 if uploaded_ebay_var.get() else 0

            if not title_val:
                messagebox.showerror("Missing data", "Item name is required.", parent=dlg)
                return
            if condition_val not in CONDITION_OPTIONS:
                messagebox.showerror("Bad condition", "Choose a valid condition.", parent=dlg)
                return

            try:
                length_val = parse_optional_float(length_raw, "length")
                width_val = parse_optional_float(width_raw, "width")
                height_val = parse_optional_float(height_raw, "height")
                weight_lb_val = parse_optional_float(weight_lb_raw, "weight (lb)")
                weight_oz_val = parse_optional_float(weight_oz_raw, "weight (oz)")
                if weight_oz_val is not None and weight_oz_val >= 16:
                    raise ValueError("Weight (oz) must be between 0 and 15.")
                price2 = dollars_to_cents(price_s)
                cost2 = dollars_to_cents(cost_s)
                stock2 = int(stock_s)
                reorder_point2 = int(reorder_point_s or 0)
                reorder_qty2 = int(reorder_qty_s or 0)
                active2 = 1 if active_var.get() else 0
                if stock2 < 0:
                    raise ValueError
            except Exception:
                messagebox.showerror("Bad input", "Check dimensions/weight/price/cost/stock/reorder/active.", parent=dlg)
                return

            if reorder_point2 < 0 or reorder_qty2 < 0:
                messagebox.showerror("Bad input", "Reorder values cannot be negative.", parent=dlg)
                return

            cat_id2 = None
            if cat_name:
                try:
                    self.db.add_category(cat_name)
                except sqlite3.IntegrityError:
                    pass
                cats = self.db.list_categories(include_inactive=True)
                cat_id2 = next((c[0] for c in cats if c[1] == cat_name), None)

            try:
                self.db.update_book(
                    bid,
                    barcode_val,
                    isbn_val,
                    title_val,
                    author_val,
                    cat_id2,
                    location_val,
                    length_val,
                    width_val,
                    height_val,
                    weight_lb_val,
                    weight_oz_val,
                    condition_val,
                    price2,
                    cost2,
                    stock2,
                    reorder_point2,
                    reorder_qty2,
                    active2,
                    uploaded_facebook_val,
                    uploaded_ebay_val,
                    availability_val,
                    self.user["id"],
                )
            except sqlite3.IntegrityError as e:
                messagebox.showerror("DB error", f"Could not update.\n\n{e}", parent=dlg)
                return

            dlg.destroy()
            self.refresh_books()
            self.refresh_reports()

        btns = ttk.Frame(frame)
        btns.grid(row=r, column=0, columnspan=3, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=dlg.destroy).pack(side="right")
        ttk.Button(btns, text="Save", command=on_save).pack(side="right", padx=8)

        self.root.wait_window(dlg)
        return

    def delete_book(self):
        bid = self._selected_book_id()
        if not bid:
            messagebox.showerror("No selection", "Select an item.")
            return
        row = self.db.get_book(bid)
        if not row:
            messagebox.showerror("Missing", "Item not found.")
            return
        title = row[3]
        if not messagebox.askyesno("Delete Item", f"Delete '{title}' permanently?"):
            return
        try:
            self.db.delete_book(bid)
        except sqlite3.IntegrityError:
            messagebox.showerror("Delete failed", "Cannot delete an item with related sales/returns. Archive instead.")
            return
        self.refresh_books()

    def toggle_book_active(self):
        bid = self._selected_book_id()
        if not bid:
            messagebox.showerror("No selection", "Select an item.")
            return
        row = self.db.get_book(bid)
        if not row:
            return
        active = int(row[18])
        self.db.set_book_active(bid, 0 if active else 1)
        self.refresh_books()

    def restock_book(self):
        bid = self._selected_book_id()
        if not bid:
            messagebox.showerror("No selection", "Select an item.")
            return
        data = Dialog.ask_fields(self.root, "Restock Item", [("Add quantity (positive integer)", "qty")], initial={"qty": "1"})
        if not data:
            return
        try:
            qty = int(data["qty"])
            if qty <= 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad qty", "Enter a positive integer.")
            return
        try:
            self.db.adjust_stock(bid, qty, "restock", "Manual restock", self.user["id"])
        except Exception as e:
            messagebox.showerror("Stock error", str(e))
            return
        self.refresh_books()

    def export_books_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Items CSV")
        if not path:
            return
        q = """
            SELECT
                b.id,
                IFNULL(b.barcode,''),
                IFNULL(b.isbn,''),
                b.title,
                b.author,
                IFNULL(cat.name,''),
                IFNULL(b.location,''),
                b.length_in,
                b.width_in,
                b.height_in,
                b.weight_lb,
                b.weight_oz,
                b.condition,
                b.price_cents,
                b.cost_cents,
                b.stock_qty,
                b.reorder_point,
                b.reorder_qty,
                b.is_active,
                b.uploaded_facebook,
                b.uploaded_ebay,
                b.availability_status
            FROM books b
            LEFT JOIN categories cat ON cat.id = b.category_id
            ORDER BY b.title;
        """
        self.db.export_table_to_csv(
            q,
            [
                "book_id",
                "barcode",
                "isbn",
                "item_name",
                "brand_details",
                "category",
                "locations",
                "length_in",
                "width_in",
                "height_in",
                "weight_lb",
                "weight_oz",
                "condition",
                "price_cents",
                "cost_cents",
                "stock_qty",
                "reorder_point",
                "reorder_qty",
                "is_active",
                "uploaded_facebook",
                "uploaded_ebay",
                "availability_status",
            ],
            path,
        )
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    def import_books_csv(self):
        path = filedialog.askopenfilename(filetypes=[("CSV", "*.csv")], title="Import Items CSV")
        if not path:
            return
        required = {
            "barcode",
            "isbn",
            "item_name",
            "brand_details",
            "category",
            "locations",
            "length_in",
            "width_in",
            "height_in",
            "weight_lb",
            "weight_oz",
            "condition",
            "price_cents",
            "cost_cents",
            "stock_qty",
            "reorder_point",
            "reorder_qty",
            "is_active",
            "uploaded_facebook",
            "uploaded_ebay",
            "availability_status",
        }
        inserted = 0
        updated = 0
        errors = []
        with open(path, newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            headers = {h.strip() for h in (reader.fieldnames or [])}
            missing = required - headers
            if missing:
                messagebox.showerror("Import error", f"Missing columns:\n{', '.join(sorted(missing))}")
                return
            conn = self.db._connect()
            cur = conn.cursor()
            cur.execute("SELECT id, name FROM categories;")
            categories = {name: int(cid) for (cid, name) in cur.fetchall()}
            cur.execute("SELECT id, barcode, stock_qty FROM books WHERE barcode IS NOT NULL;")
            barcode_map = {barcode: (int(bid), int(stock_qty or 0)) for (bid, barcode, stock_qty) in cur.fetchall()}

            for idx, row in enumerate(reader, start=2):
                try:
                    barcode = normalize_barcode(row.get("barcode", "").strip()) or None
                    isbn = (row.get("isbn", "").strip() or None)
                    title = (row.get("item_name", "") or "").strip()
                    author = (row.get("brand_details", "") or "").strip()
                    cat_name = (row.get("category", "") or "").strip()
                    location = normalize_locations(row.get("locations", ""))
                    condition = (row.get("condition", "") or "Good").strip()
                    length_in = parse_optional_float(row.get("length_in", ""), "length")
                    width_in = parse_optional_float(row.get("width_in", ""), "width")
                    height_in = parse_optional_float(row.get("height_in", ""), "height")
                    weight_lb = parse_optional_float(row.get("weight_lb", ""), "weight (lb)")
                    weight_oz = parse_optional_float(row.get("weight_oz", ""), "weight (oz)")
                    price_cents = int(row.get("price_cents") or 0)
                    cost_cents = int(row.get("cost_cents") or 0)
                    stock_qty = int(row.get("stock_qty") or 0)
                    reorder_point = int(row.get("reorder_point") or 0)
                    reorder_qty = int(row.get("reorder_qty") or 0)
                    is_active = 1 if str(row.get("is_active", "1")).strip() in ("1", "yes", "true", "y") else 0
                    uploaded_facebook = 1 if str(row.get("uploaded_facebook", "0")).strip() in ("1", "yes", "true", "y") else 0
                    uploaded_ebay = 1 if str(row.get("uploaded_ebay", "0")).strip() in ("1", "yes", "true", "y") else 0
                    availability_status = (row.get("availability_status", "") or "available").strip()

                    if not title:
                        raise ValueError("item_name is required")
                    if condition not in CONDITION_OPTIONS:
                        raise ValueError("invalid condition")
                    if weight_oz is not None and weight_oz >= 16:
                        raise ValueError("weight_oz must be 0-15")
                    if stock_qty < 0 or reorder_point < 0 or reorder_qty < 0:
                        raise ValueError("stock/reorder values cannot be negative")

                    cat_id = None
                    if cat_name:
                        cat_id = categories.get(cat_name)
                        if cat_id is None:
                            cur.execute("INSERT OR IGNORE INTO categories(name, is_active) VALUES(?,1);", (cat_name,))
                            cur.execute("SELECT id FROM categories WHERE name=?;", (cat_name,))
                            row_id = cur.fetchone()
                            if row_id:
                                cat_id = int(row_id[0])
                                categories[cat_name] = cat_id

                    existing = barcode_map.get(barcode) if barcode else None

                    if existing:
                        book_id, prev_stock = existing
                        cur.execute("""
                            UPDATE books
                            SET barcode=?, isbn=?, title=?, author=?, category_id=?, location=?,
                                length_in=?, width_in=?, height_in=?, weight_lb=?, weight_oz=?,
                                condition=?,
                                price_cents=?, cost_cents=?, stock_qty=?, reorder_point=?, reorder_qty=?, is_active=?,
                                uploaded_facebook=?, uploaded_ebay=?, availability_status=?
                            WHERE id=?;
                        """, (
                            barcode or None,
                            isbn or None,
                            title.strip(),
                            author.strip(),
                            cat_id,
                            location,
                            length_in,
                            width_in,
                            height_in,
                            weight_lb,
                            weight_oz,
                            condition,
                            int(price_cents),
                            int(cost_cents),
                            int(stock_qty),
                            int(reorder_point),
                            int(reorder_qty),
                            int(is_active),
                            int(uploaded_facebook),
                            int(uploaded_ebay),
                            availability_status,
                            int(book_id),
                        ))
                        if int(stock_qty) != int(prev_stock):
                            delta = int(stock_qty) - int(prev_stock)
                            self.db._log_inventory_adjustment(
                                conn,
                                int(book_id),
                                delta,
                                "import",
                                "CSV import",
                                self.user["id"],
                            )
                            barcode_map[barcode] = (int(book_id), int(stock_qty))
                        updated += 1
                    else:
                        cur.execute("""
                            INSERT INTO books(
                                barcode, isbn, title, author, category_id, location,
                                length_in, width_in, height_in, weight_lb, weight_oz,
                                condition,
                                price_cents, cost_cents, stock_qty, reorder_point, reorder_qty, is_active,
                                uploaded_facebook, uploaded_ebay, availability_status
                            )
                            VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?);
                        """, (
                            barcode or None,
                            isbn or None,
                            title.strip(),
                            author.strip(),
                            cat_id,
                            location,
                            length_in,
                            width_in,
                            height_in,
                            weight_lb,
                            weight_oz,
                            condition,
                            int(price_cents),
                            int(cost_cents),
                            int(stock_qty),
                            int(reorder_point),
                            int(reorder_qty),
                            int(is_active),
                            int(uploaded_facebook),
                            int(uploaded_ebay),
                            availability_status,
                        ))
                        inserted += 1
                        if barcode:
                            barcode_map[barcode] = (int(cur.lastrowid), int(stock_qty))
                except Exception as exc:
                    errors.append(f"Row {idx}: {exc}")
            conn.commit()

        self.refresh_books()
        self.refresh_reports()
        if errors:
            Dialog.show_text(self.root, "Import completed with errors", "\n".join(errors))
        messagebox.showinfo("Import complete", f"Inserted: {inserted}\nUpdated: {updated}\nErrors: {len(errors)}")

    # ---------------- Customers tab ----------------
    def _build_customers_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Customers")
        self.customers_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)

        self.cust_search = tk.StringVar()
        self.cust_inactive = tk.IntVar(value=0)

        ttk.Label(top, text="Search:").pack(side="left")
        e = ttk.Entry(top, textvariable=self.cust_search, width=28)
        e.pack(side="left", padx=(6, 12))
        e.bind("<KeyRelease>", lambda _e: self.refresh_customers())

        ttk.Checkbutton(top, text="Include archived", variable=self.cust_inactive, command=self.refresh_customers).pack(side="left")

        ttk.Button(top, text="Add", command=self.add_customer).pack(side="left", padx=(20, 0))
        ttk.Button(top, text="Edit", command=self.edit_customer).pack(side="left", padx=6)
        ttk.Button(top, text="Archive/Unarchive", command=self.toggle_customer_active).pack(side="left", padx=6)
        ttk.Button(top, text="History", command=self.view_customer_history).pack(side="left", padx=6)
        ttk.Button(top, text="Import CSV", command=self.import_customers_csv).pack(side="right")
        ttk.Button(top, text="Export CSV", command=self.export_customers_csv).pack(side="right", padx=(0, 8))

        self.customers_tree = ttk.Treeview(tab, columns=("name", "email", "active"), show="headings", height=18)
        self.customers_tree.heading("name", text="Name")
        self.customers_tree.heading("email", text="Email")
        self.customers_tree.heading("active", text="Active")
        self.customers_tree.column("name", width=260)
        self.customers_tree.column("email", width=460)
        self.customers_tree.column("active", width=80, anchor="center")
        self.customers_tree.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        self.customers_tree.bind("<Double-1>", lambda _e: self.edit_customer())

    def refresh_customers(self):
        for i in self.customers_tree.get_children():
            self.customers_tree.delete(i)
        rows = self.db.list_customers(self.cust_search.get(), include_inactive=bool(self.cust_inactive.get()))
        for cid, name, email, active in rows:
            self.customers_tree.insert("", "end", iid=str(cid), values=(name, email, "yes" if active else "no"))
        self._refresh_pos_customers()

    def _selected_customer_id(self) -> Optional[int]:
        sel = self.customers_tree.selection()
        return int(sel[0]) if sel else None

    def add_customer(self):
        data = Dialog.ask_fields(self.root, "Add Customer", [("Name", "name"), ("Email", "email")])
        if not data:
            return
        try:
            self.db.add_customer(data["name"], data["email"], 1)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", f"Could not add customer.\n\n{e}")
            return
        self.refresh_customers()

    def edit_customer(self):
        cid = self._selected_customer_id()
        if not cid:
            messagebox.showerror("No selection", "Select a customer.")
            return
        row = self.db.get_customer(cid)
        if not row:
            return
        _id, name, email, active = row
        data = Dialog.ask_fields(self.root, "Edit Customer", [
            ("Name", "name"),
            ("Email", "email"),
            ("Active? (yes/no)", "active"),
        ], initial={"name": name, "email": email, "active": "yes" if int(active) else "no"})
        if not data:
            return
        active2 = 1 if data["active"].lower() in ("yes", "y", "1", "true") else 0
        try:
            self.db.update_customer(cid, data["name"], data["email"], active2)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", f"Could not update.\n\n{e}")
            return
        self.refresh_customers()

    def toggle_customer_active(self):
        cid = self._selected_customer_id()
        if not cid:
            messagebox.showerror("No selection", "Select a customer.")
            return
        row = self.db.get_customer(cid)
        if not row:
            return
        active = int(row[3])
        self.db.set_customer_active(cid, 0 if active else 1)
        self.refresh_customers()

    def view_customer_history(self):
        cid = self._selected_customer_id()
        if not cid:
            messagebox.showerror("No selection", "Select a customer.")
            return
        row = self.db.get_customer(cid)
        if not row:
            return
        _id, name, email, _a = row
        hist = self.db.customer_history(cid)
        lines = [f"Purchase history for {name} <{email}>", "=" * 60]
        for sid, rno, ts, total, status in hist:
            lines.append(f"{ts}  {rno:10}  {cents_to_money(total):>10}  {status}")
        if not hist:
            lines.append("(no sales)")
        Dialog.show_text(self.root, "Customer History", "\n".join(lines))

    def export_customers_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Customers CSV")
        if not path:
            return
        q = "SELECT name, email, is_active FROM customers ORDER BY name;"
        self.db.export_table_to_csv(q, ["name", "email", "is_active"], path)
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    def import_customers_csv(self):
        path = filedialog.askopenfilename(filetypes=[("CSV", "*.csv")], title="Import Customers CSV")
        if not path:
            return
        required = {"name", "email", "is_active"}
        inserted = 0
        updated = 0
        errors = []
        with open(path, newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            headers = {h.strip() for h in (reader.fieldnames or [])}
            missing = required - headers
            if missing:
                messagebox.showerror("Import error", f"Missing columns:\n{', '.join(sorted(missing))}")
                return
            conn = self.db._connect()
            cur = conn.cursor()
            cur.execute("SELECT id, name, email FROM customers;")
            customer_map = {(name, email): int(cid) for (cid, name, email) in cur.fetchall()}

            for idx, row in enumerate(reader, start=2):
                try:
                    name = (row.get("name", "") or "").strip()
                    email = (row.get("email", "") or "").strip()
                    is_active = 1 if str(row.get("is_active", "1")).strip() in ("1", "yes", "true", "y") else 0
                    if not name or not email:
                        raise ValueError("name and email are required")
                    existing_id = customer_map.get((name, email))
                    if existing_id:
                        cur.execute(
                            "UPDATE customers SET name=?, email=?, is_active=? WHERE id=?;",
                            (name, email, int(is_active), int(existing_id)),
                        )
                        updated += 1
                    else:
                        cur.execute(
                            "INSERT INTO customers(name, email, is_active) VALUES(?,?,?);",
                            (name, email, int(is_active)),
                        )
                        customer_map[(name, email)] = int(cur.lastrowid)
                        inserted += 1
                except Exception as exc:
                    errors.append(f"Row {idx}: {exc}")
            conn.commit()

        self.refresh_customers()
        if errors:
            Dialog.show_text(self.root, "Customer import errors", "\n".join(errors))
        messagebox.showinfo("Import complete", f"Inserted: {inserted}\nUpdated: {updated}\nErrors: {len(errors)}")

    # ---------------- POS tab ----------------
    def _build_pos_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Platform Sales")
        self.pos_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)

        ttk.Label(top, text="Search inventory:").pack(side="left")
        self.platform_search_var = tk.StringVar()
        search_entry = ttk.Entry(top, textvariable=self.platform_search_var, width=36)
        search_entry.pack(side="left", padx=(6, 12))
        search_entry.bind("<KeyRelease>", lambda _e: self._refresh_pos_books())
        ttk.Button(top, text="Refresh", command=self._refresh_pos_books).pack(side="left")

        body = ttk.Frame(tab)
        body.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        left = ttk.Frame(body)
        left.pack(side="left", fill="both", expand=True, padx=(0, 10))
        right = ttk.Frame(body)
        right.pack(side="left", fill="both", expand=True)

        ttk.Label(left, text="Available inventory (double-click to autofill pricing)").pack(anchor="w")
        self.pos_books_tree = ttk.Treeview(
            left,
            columns=("isbn", "title", "condition", "price", "stock"),
            show="headings",
            height=18,
        )
        self.pos_books_tree.heading("isbn", text="Barcode")
        self.pos_books_tree.heading("title", text="Item")
        self.pos_books_tree.heading("condition", text="Condition")
        self.pos_books_tree.heading("price", text="Listed Price")
        self.pos_books_tree.heading("stock", text="Stock")
        self.pos_books_tree.column("isbn", width=140)
        self.pos_books_tree.column("title", width=280)
        self.pos_books_tree.column("condition", width=100)
        self.pos_books_tree.column("price", width=110, anchor="e")
        self.pos_books_tree.column("stock", width=60, anchor="center")
        self.pos_books_tree.pack(fill="both", expand=True, pady=(4, 6))
        self.pos_books_tree.bind("<Double-1>", lambda _e: self._prefill_platform_price())

        form = ttk.LabelFrame(right, text="Log platform sale")
        form.pack(fill="x", pady=(0, 10))

        self.platform_var = tk.StringVar(value=PLATFORM_OPTIONS[0])
        self.platform_listed_var = tk.StringVar(value="0.00")
        self.platform_final_var = tk.StringVar(value="0.00")
        self.platform_status_var = tk.StringVar(value="Pending")
        self.platform_note_var = tk.StringVar(value="")

        row1 = ttk.Frame(form)
        row1.pack(fill="x", padx=10, pady=8)
        ttk.Label(row1, text="Platform:").pack(side="left")
        ttk.Combobox(row1, textvariable=self.platform_var, values=PLATFORM_OPTIONS, width=14).pack(
            side="left", padx=(6, 12)
        )
        ttk.Label(row1, text="Status:").pack(side="left")
        ttk.Combobox(
            row1, textvariable=self.platform_status_var, values=PLATFORM_SALE_STATUSES, width=12, state="readonly"
        ).pack(side="left", padx=(6, 12))

        row2 = ttk.Frame(form)
        row2.pack(fill="x", padx=10, pady=(0, 8))
        ttk.Label(row2, text="Listed price ($):").pack(side="left")
        ttk.Entry(row2, textvariable=self.platform_listed_var, width=12).pack(side="left", padx=(6, 12))
        ttk.Label(row2, text="Final price ($):").pack(side="left")
        ttk.Entry(row2, textvariable=self.platform_final_var, width=12).pack(side="left", padx=(6, 12))

        row3 = ttk.Frame(form)
        row3.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Label(row3, text="Note:").pack(side="left")
        ttk.Entry(row3, textvariable=self.platform_note_var, width=36).pack(side="left", padx=(6, 12))
        ttk.Button(row3, text="Log Sale", command=self.log_platform_sale).pack(side="right")

        sales = ttk.LabelFrame(right, text="Recent platform sales")
        sales.pack(fill="both", expand=True)
        self.platform_sales_tree = ttk.Treeview(
            sales,
            columns=("date", "item", "platform", "listed", "final", "status"),
            show="headings",
            height=10,
        )
        for col, label, width, anchor in [
            ("date", "Date", 140, "w"),
            ("item", "Item", 220, "w"),
            ("platform", "Platform", 110, "w"),
            ("listed", "Listed", 90, "e"),
            ("final", "Final", 90, "e"),
            ("status", "Status", 90, "center"),
        ]:
            self.platform_sales_tree.heading(col, text=label)
            self.platform_sales_tree.column(col, width=width, anchor=anchor)
        self.platform_sales_tree.pack(fill="both", expand=True, padx=10, pady=10)
        self.platform_sales_tree.bind("<<TreeviewSelect>>", lambda _e: self._load_selected_platform_sale())

        action_row = ttk.Frame(sales)
        action_row.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(action_row, text="Update Selected Sale", command=self.update_platform_sale).pack(side="left")
        ttk.Button(action_row, text="Refresh", command=self.refresh_platform_sales).pack(side="left", padx=6)

    def _refresh_pos_books(self):
        if not hasattr(self, "pos_books_tree"):
            return
        for i in self.pos_books_tree.get_children():
            self.pos_books_tree.delete(i)
        rows = self.db.list_books(
            self.platform_search_var.get(),
            in_stock_only=False,
            include_inactive=False,
            availability_status="available",
        )
        for (
            bid,
            barcode,
            _isbn,
            title,
            _author,
            _location,
            _length_in,
            _width_in,
            _height_in,
            _weight_lb,
            _weight_oz,
            condition,
            price,
            _cost,
            stock,
            _reorder_point,
            _active,
            _uploaded_facebook,
            _uploaded_ebay,
            _availability_status,
            _cat,
        ) in rows:
            self.pos_books_tree.insert(
                "", "end", iid=str(bid), values=(barcode or "", title, condition or "", cents_to_money(price), stock)
            )

    def _prefill_platform_price(self):
        sel = self.pos_books_tree.selection()
        if not sel:
            return
        bid = int(sel[0])
        row = self.db.get_book(bid)
        if not row:
            return
        price_cents = int(row[13])
        price_text = f"{price_cents / 100:.2f}"
        self.platform_listed_var.set(price_text)
        self.platform_final_var.set(price_text)

    def log_platform_sale(self):
        sel = self.pos_books_tree.selection()
        if not sel:
            messagebox.showerror("No selection", "Select an available item first.")
            return
        book_id = int(sel[0])
        platform = self.platform_var.get().strip()
        if not platform:
            messagebox.showerror("Missing data", "Platform is required.")
            return
        status = self.platform_status_var.get().strip()
        try:
            listed_price_cents = dollars_to_cents(self.platform_listed_var.get())
            final_price_cents = dollars_to_cents(self.platform_final_var.get())
        except Exception:
            messagebox.showerror("Bad price", "Enter valid listed/final prices.")
            return
        note = self.platform_note_var.get().strip()
        amount_paid_cents = final_price_cents if status.strip().lower() == "paid" else 0

        try:
            self.db.add_platform_sale(
                book_id=book_id,
                platform=platform,
                listed_price_cents=listed_price_cents,
                final_price_cents=final_price_cents,
                amount_paid_cents=amount_paid_cents,
                status=status,
                note=note,
            )
        except Exception as e:
            messagebox.showerror("Log failed", str(e))
            return

        self.platform_note_var.set("")
        self.platform_status_var.set("Pending")
        self.refresh_books()
        self.refresh_platform_sales()
        self.refresh_pending_products()
        self.refresh_pickup_ship()

    def _load_selected_platform_sale(self):
        sel = self.platform_sales_tree.selection()
        if not sel:
            return
        sale_id = int(sel[0])
        rows = self.db.list_platform_sales()
        row = next((r for r in rows if r[0] == sale_id), None)
        if not row:
            return
        _sid, _created, _book_id, _title, platform, listed, final, _paid, status, note = row
        self.platform_var.set(platform)
        self.platform_listed_var.set(f"{listed / 100:.2f}")
        self.platform_final_var.set(f"{final / 100:.2f}")
        self.platform_status_var.set(status.title())
        self.platform_note_var.set(note or "")

    def update_platform_sale(self):
        sel = self.platform_sales_tree.selection()
        if not sel:
            messagebox.showerror("No selection", "Select a platform sale to update.")
            return
        sale_id = int(sel[0])
        try:
            final_price_cents = dollars_to_cents(self.platform_final_var.get())
        except Exception:
            messagebox.showerror("Bad price", "Enter a valid final price.")
            return
        status = self.platform_status_var.get().strip()
        note = self.platform_note_var.get().strip()
        try:
            self.db.update_platform_sale(sale_id, final_price_cents, status, note)
        except Exception as e:
            messagebox.showerror("Update failed", str(e))
            return
        self.refresh_books()
        self.refresh_platform_sales()
        self.refresh_pending_products()
        self.refresh_pickup_ship()

    def refresh_platform_sales(self):
        if not hasattr(self, "platform_sales_tree"):
            return
        for i in self.platform_sales_tree.get_children():
            self.platform_sales_tree.delete(i)
        for (
            sid,
            created_at,
            _book_id,
            title,
            platform,
            listed_price,
            final_price,
            _paid,
            status,
            _note,
        ) in self.db.list_platform_sales():
            self.platform_sales_tree.insert(
                "", "end", iid=str(sid),
                values=(
                    created_at,
                    title,
                    platform,
                    cents_to_money(listed_price),
                    cents_to_money(final_price),
                    "Paid in full" if status == "paid" else status.title(),
                ),
            )

    # ---------------- Pending products tab ----------------
    def _build_pending_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Pending Products")
        self.pending_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)
        ttk.Button(top, text="Refresh", command=self.refresh_pending_products).pack(side="left")
        ttk.Button(top, text="Mark Selected Available", command=self.mark_pending_available).pack(side="left", padx=6)
        ttk.Button(top, text="Payment", command=self.pending_payment).pack(side="left", padx=6)

        self.pending_tree = ttk.Treeview(
            tab,
            columns=("date", "item", "platform", "listed", "final", "paid", "owed", "status"),
            show="headings",
            height=18,
        )
        for col, label, width, anchor in [
            ("date", "Date", 140, "w"),
            ("item", "Item", 280, "w"),
            ("platform", "Platform", 120, "w"),
            ("listed", "Listed", 90, "e"),
            ("final", "Final", 90, "e"),
            ("paid", "Paid", 90, "e"),
            ("owed", "Owed", 90, "e"),
            ("status", "Status", 110, "center"),
        ]:
            self.pending_tree.heading(col, text=label)
            self.pending_tree.column(col, width=width, anchor=anchor)
        self.pending_tree.pack(fill="both", expand=True, padx=10, pady=(0, 10))

    def refresh_pending_products(self):
        if not hasattr(self, "pending_tree"):
            return
        for i in self.pending_tree.get_children():
            self.pending_tree.delete(i)
        rows = self.db.list_platform_sales(statuses=["pending", "partial", "unpaid"])
        for sid, created_at, _book_id, title, platform, listed, final, paid, status, _note in rows:
            owed = max(0, int(final) - int(paid))
            self.pending_tree.insert(
                "", "end", iid=str(sid),
                values=(
                    created_at,
                    title,
                    platform,
                    cents_to_money(listed),
                    cents_to_money(final),
                    cents_to_money(paid),
                    cents_to_money(owed),
                    "Paid in full" if status == "paid" else status.title(),
                ),
            )

    def mark_pending_available(self):
        sel = self.pending_tree.selection()
        if not sel:
            messagebox.showerror("No selection", "Select a pending item.")
            return
        platform_sale_id = int(sel[0])
        rows = self.db.list_platform_sales()
        row = next((r for r in rows if r[0] == platform_sale_id), None)
        if not row:
            return
        _sid, _created, book_id, _title, _platform, _listed, _final, _paid, _status, _note = row
        self.db.set_book_availability(book_id, "available")
        self.db.delete_platform_sale(platform_sale_id)
        self.refresh_books()
        self.refresh_pending_products()
        self.refresh_platform_sales()

    def pending_payment(self):
        sel = self.pending_tree.selection()
        if not sel:
            messagebox.showerror("No selection", "Select a pending item.")
            return
        platform_sale_id = int(sel[0])
        rows = self.db.list_platform_sales()
        row = next((r for r in rows if r[0] == platform_sale_id), None)
        if not row:
            return
        _sid, _created, _book_id, title, _platform, _listed, final, paid, status, _note = row

        dlg = tk.Toplevel(self.root)
        dlg.title("Record Payment")
        dlg.geometry("420x260")
        dlg.transient(self.root)
        dlg.grab_set()

        ttk.Label(dlg, text=f"Item: {title}").pack(anchor="w", padx=12, pady=(12, 6))

        form = ttk.Frame(dlg, padding=12)
        form.pack(fill="both", expand=True)

        ttk.Label(form, text="Final price ($):").grid(row=0, column=0, sticky="w", pady=6)
        final_var = tk.StringVar(value=f"{final / 100:.2f}")
        ttk.Entry(form, textvariable=final_var, width=12).grid(row=0, column=1, sticky="w", pady=6)

        paid_mode = tk.StringVar(value="full" if status == "paid" else "part")
        ttk.Label(form, text="Payment:").grid(row=1, column=0, sticky="w", pady=6)
        mode_frame = ttk.Frame(form)
        mode_frame.grid(row=1, column=1, sticky="w", pady=6)
        ttk.Radiobutton(mode_frame, text="Paid in full", variable=paid_mode, value="full").pack(anchor="w")
        ttk.Radiobutton(mode_frame, text="Paid in part", variable=paid_mode, value="part").pack(anchor="w")

        ttk.Label(form, text="Amount paid ($):").grid(row=2, column=0, sticky="w", pady=6)
        paid_var = tk.StringVar(value=f"{paid / 100:.2f}" if paid > 0 else "")
        paid_entry = ttk.Entry(form, textvariable=paid_var, width=12)
        paid_entry.grid(row=2, column=1, sticky="w", pady=6)

        def toggle_paid_entry(*_args):
            if paid_mode.get() == "full":
                paid_entry.configure(state="disabled")
            else:
                paid_entry.configure(state="normal")

        paid_mode.trace_add("write", toggle_paid_entry)
        toggle_paid_entry()

        def save_payment():
            try:
                final_price_cents = dollars_to_cents(final_var.get())
            except Exception:
                messagebox.showerror("Bad price", "Enter a valid final price.", parent=dlg)
                return
            if paid_mode.get() == "full":
                amount_paid_cents = final_price_cents
            else:
                try:
                    amount_paid_cents = dollars_to_cents(paid_var.get())
                except Exception:
                    messagebox.showerror("Bad amount", "Enter a valid amount paid.", parent=dlg)
                    return
                if amount_paid_cents <= 0 or amount_paid_cents >= final_price_cents:
                    messagebox.showerror("Bad amount", "Amount paid must be less than final price.", parent=dlg)
                    return
            try:
                self.db.update_platform_payment(
                    platform_sale_id,
                    final_price_cents=final_price_cents,
                    amount_paid_cents=amount_paid_cents,
                )
            except Exception as e:
                messagebox.showerror("Update failed", str(e), parent=dlg)
                return
            dlg.destroy()
            self.refresh_platform_sales()
            self.refresh_pending_products()
            self.refresh_pickup_ship()
            self.refresh_books()

        buttons = ttk.Frame(dlg, padding=12)
        buttons.pack(fill="x")
        ttk.Button(buttons, text="Cancel", command=dlg.destroy).pack(side="right")
        ttk.Button(buttons, text="Save Payment", command=save_payment).pack(side="right", padx=8)

        self.root.wait_window(dlg)

    # ---------------- Pickup/Ship tab ----------------
    def _build_pickup_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Pickup/Ship")
        self.pickup_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)
        ttk.Button(top, text="Refresh", command=self.refresh_pickup_ship).pack(side="left")
        ttk.Button(top, text="Mark Selected Available", command=self.mark_pickup_available).pack(side="left", padx=6)
        ttk.Button(top, text="Done", command=self.mark_pickup_done).pack(side="left", padx=6)

        self.pickup_tree = ttk.Treeview(
            tab,
            columns=("date", "item", "platform", "listed", "final", "status"),
            show="headings",
            height=18,
        )
        for col, label, width, anchor in [
            ("date", "Date", 140, "w"),
            ("item", "Item", 280, "w"),
            ("platform", "Platform", 120, "w"),
            ("listed", "Listed", 90, "e"),
            ("final", "Final", 90, "e"),
            ("status", "Status", 90, "center"),
        ]:
            self.pickup_tree.heading(col, text=label)
            self.pickup_tree.column(col, width=width, anchor=anchor)
        self.pickup_tree.pack(fill="both", expand=True, padx=10, pady=(0, 10))

    def refresh_pickup_ship(self):
        if not hasattr(self, "pickup_tree"):
            return
        for i in self.pickup_tree.get_children():
            self.pickup_tree.delete(i)
        rows = self.db.list_platform_sales(statuses=["paid"])
        for sid, created_at, _book_id, title, platform, listed, final, _paid, status, _note in rows:
            self.pickup_tree.insert(
                "", "end", iid=str(sid),
                values=(created_at, title, platform, cents_to_money(listed), cents_to_money(final), "Paid in full"),
            )

    def mark_pickup_available(self):
        sel = self.pickup_tree.selection()
        if not sel:
            messagebox.showerror("No selection", "Select a pickup/ship item.")
            return
        platform_sale_id = int(sel[0])
        rows = self.db.list_platform_sales()
        row = next((r for r in rows if r[0] == platform_sale_id), None)
        if not row:
            return
        _sid, _created, book_id, _title, _platform, _listed, _final, _paid, _status, _note = row
        self.db.set_book_availability(book_id, "available")
        self.db.delete_platform_sale(platform_sale_id)
        self.refresh_books()
        self.refresh_pickup_ship()
        self.refresh_platform_sales()

    def mark_pickup_done(self):
        sel = self.pickup_tree.selection()
        if not sel:
            messagebox.showerror("No selection", "Select a pickup/ship item.")
            return
        platform_sale_id = int(sel[0])
        try:
            self.db.finalize_platform_sale(platform_sale_id)
        except Exception as e:
            messagebox.showerror("Complete failed", str(e))
            return
        self.refresh_books()
        self.refresh_platform_sales()
        self.refresh_pending_products()
        self.refresh_pickup_ship()
        self.refresh_sales()
        self.refresh_reports()

    # ---------------- Sales & Returns tab ----------------
    def _build_sales_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Sales & Returns")
        self.sales_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)

        ttk.Button(top, text="Refresh", command=self.refresh_sales).pack(side="left")
        ttk.Button(top, text="View Receipt", command=self.view_sale_receipt).pack(side="left", padx=6)
        ttk.Button(top, text="Export Receipt TXT", command=self.export_sale_txt).pack(side="left", padx=6)
        ttk.Button(top, text="Export Receipt PDF", command=self.export_sale_pdf).pack(side="left", padx=6)

        ttk.Separator(top, orient="vertical").pack(side="left", fill="y", padx=10)

        ttk.Button(top, text="Create Return (selected sale)", command=self.create_return_ui).pack(side="left")
        ttk.Button(top, text="Update Payment Status", command=self.update_sale_payment_status_ui).pack(side="left", padx=6)
        ttk.Button(top, text="Void Sale", command=self.void_sale_ui).pack(side="left", padx=6)
        ttk.Button(top, text="Delete Sale", command=self.delete_sale_ui).pack(side="left", padx=6)
        ttk.Button(top, text="View Return Receipt", command=self.view_return_receipt).pack(side="left", padx=6)
        ttk.Button(top, text="Export Return PDF", command=self.export_return_pdf).pack(side="left", padx=6)
        ttk.Button(top, text="Delete Return", command=self.delete_return_ui).pack(side="left", padx=6)

        body = ttk.Frame(tab)
        body.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        left = ttk.Frame(body)
        left.pack(side="left", fill="both", expand=True, padx=(0, 10))
        right = ttk.Frame(body)
        right.pack(side="left", fill="both", expand=True)

        ttk.Label(left, text="Sales").pack(anchor="w")
        self.sales_tree = ttk.Treeview(left, columns=("rno", "ts", "platform", "total", "status", "void"), show="headings", height=18)
        for c, l, w, a in [
            ("rno", "Receipt", 100, "w"),
            ("ts", "Date/Time", 160, "w"),
            ("platform", "Platform", 220, "w"),
            ("total", "Total", 100, "e"),
            ("status", "Pay", 80, "center"),
            ("void", "Void", 60, "center"),
        ]:
            self.sales_tree.heading(c, text=l)
            self.sales_tree.column(c, width=w, anchor=a)
        self.sales_tree.pack(fill="both", expand=True)
        self.sales_tree.bind("<Double-1>", lambda _e: self.view_sale_receipt())

        ttk.Label(right, text="Returns").pack(anchor="w")
        self.returns_tree = ttk.Treeview(right, columns=("ts", "orig", "refund", "method"), show="headings", height=18)
        for c, l, w, a in [
            ("ts", "Date/Time", 160, "w"),
            ("orig", "Original Receipt", 120, "w"),
            ("refund", "Refund", 100, "e"),
            ("method", "Method", 80, "center"),
        ]:
            self.returns_tree.heading(c, text=l)
            self.returns_tree.column(c, width=w, anchor=a)
        self.returns_tree.pack(fill="both", expand=True)
        self.returns_tree.bind("<Double-1>", lambda _e: self.view_return_receipt())

    def refresh_sales(self):
        for i in self.sales_tree.get_children():
            self.sales_tree.delete(i)
        for sid, rno, ts, platform, total, status, is_void in self.db.list_sales(400):
            self.sales_tree.insert(
                "", "end", iid=str(sid),
                values=(rno, ts, platform, cents_to_money(total), status, "yes" if is_void else "no"),
            )

        for i in self.returns_tree.get_children():
            self.returns_tree.delete(i)
        for rid, ts, orig_rno, refund, method in self.db.list_returns(300):
            self.returns_tree.insert("", "end", iid=str(rid), values=(ts, orig_rno, cents_to_money(refund), method))

    def _selected_sale_id(self, tree: Optional[ttk.Treeview] = None) -> Optional[int]:
        tree = tree or self.sales_tree
        sel = tree.selection()
        return int(sel[0]) if sel else None

    def view_sale_receipt(self):
        sid = self._selected_sale_id()
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return
        row = self.db.get_sale_receipt(sid)
        if not row:
            messagebox.showerror("Missing", "Receipt not found.")
            return
        receipt_text, rno, ts = row
        Dialog.show_text(self.root, f"Receipt {rno}", receipt_text)

    def export_sale_txt(self):
        sid = self._selected_sale_id()
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return
        row = self.db.get_sale_receipt(sid)
        if not row:
            return
        receipt_text, rno, _ = row
        path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text", "*.txt")], initialfile=f"{rno}.txt")
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write(receipt_text)
        messagebox.showinfo("Saved", f"Saved:\n{path}")

    def export_sale_pdf(self):
        sid = self._selected_sale_id()
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return
        row = self.db.get_sale_receipt(sid)
        if not row:
            return
        receipt_text, rno, _ = row
        path = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF", "*.pdf")], initialfile=f"{rno}.pdf")
        if not path:
            return
        try:
            export_pdf_text(receipt_text, path, title=rno)
        except Exception as e:
            messagebox.showerror("PDF error", f"{e}\n\nInstall reportlab: pip install reportlab")
            return
        messagebox.showinfo("Saved", f"Saved:\n{path}")

    def update_sale_payment_status_ui(self, tree: Optional[ttk.Treeview] = None):
        sid = self._selected_sale_id(tree)
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return

        dlg = tk.Toplevel(self.root)
        dlg.title("Update Payment Status")
        dlg.geometry("320x180")
        dlg.transient(self.root)
        dlg.grab_set()

        ttk.Label(dlg, text="Payment status:").pack(anchor="w", padx=12, pady=(12, 4))
        status_var = tk.StringVar(value="paid")
        ttk.Combobox(dlg, textvariable=status_var, values=["paid", "partial", "unpaid"], state="readonly").pack(anchor="w", padx=12)

        def save():
            try:
                self.db.update_sale_payment_status(sid, status_var.get())
            except Exception as e:
                messagebox.showerror("Update failed", str(e), parent=dlg)
                return
            dlg.destroy()
            self.refresh_sales()
            self.refresh_reports()

        btns = ttk.Frame(dlg, padding=12)
        btns.pack(fill="x")
        ttk.Button(btns, text="Cancel", command=dlg.destroy).pack(side="right")
        ttk.Button(btns, text="Save", command=save).pack(side="right", padx=8)
        self.root.wait_window(dlg)

    def void_sale_ui(self, tree: Optional[ttk.Treeview] = None):
        sid = self._selected_sale_id(tree)
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return
        if not messagebox.askyesno("Void sale", "Void this sale and restock items?"):
            return
        try:
            self.db.void_sale(sid, self.user["id"])
        except Exception as e:
            messagebox.showerror("Void failed", str(e))
            return
        self.refresh_sales()
        self.refresh_reports()
        self.refresh_books()

    def delete_sale_ui(self, tree: Optional[ttk.Treeview] = None):
        sid = self._selected_sale_id(tree)
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return
        if not messagebox.askyesno("Delete sale", "Delete this sale? This cannot be undone."):
            return
        try:
            self.db.delete_sale(sid, self.user["id"])
        except Exception as e:
            messagebox.showerror("Delete failed", str(e))
            return
        self.refresh_sales()
        self.refresh_reports()
        self.refresh_books()

    def create_return_ui(self, tree: Optional[ttk.Treeview] = None):
        sid = self._selected_sale_id(tree)
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return

        items = self.db.get_sale_items(sid)
        if not items:
            messagebox.showerror("No items", "No sale items found.")
            return

        dlg = tk.Toplevel(self.root)
        dlg.title("Create Return")
        dlg.geometry("720x460")
        dlg.transient(self.root)
        dlg.grab_set()

        ttk.Label(dlg, text="Enter return qty for each item (0 = not returned)").pack(anchor="w", padx=10, pady=(10, 0))

        frame = ttk.Frame(dlg, padding=10)
        frame.pack(fill="both", expand=True)

        rows = []
        for i, (book_id, title, qty, unit, line_total) in enumerate(items):
            ttk.Label(frame, text=title).grid(row=i, column=0, sticky="w", pady=4)
            ttk.Label(frame, text=f"Sold: {qty} @ {cents_to_money(unit)}").grid(row=i, column=1, sticky="w", pady=4)
            var = tk.StringVar(value="0")
            ttk.Entry(frame, textvariable=var, width=6).grid(row=i, column=2, pady=4)
            rows.append((book_id, qty, var))

        reason_var = tk.StringVar(value="")
        method_var = tk.StringVar(value="cash")

        bottom = ttk.Frame(dlg, padding=10)
        bottom.pack(fill="x")
        ttk.Label(bottom, text="Reason:").pack(side="left")
        ttk.Entry(bottom, textvariable=reason_var, width=30).pack(side="left", padx=(6, 12))
        ttk.Label(bottom, text="Refund method:").pack(side="left")
        ttk.Combobox(bottom, textvariable=method_var, values=["cash", "card", "other"], width=10, state="readonly").pack(side="left", padx=(6, 12))

        def do_return():
            pick = []
            for book_id, sold_qty, var in rows:
                try:
                    rq = int(var.get().strip())
                except Exception:
                    rq = 0
                if rq > 0:
                    if rq > sold_qty:
                        messagebox.showerror("Bad qty", "Return qty cannot exceed sold qty.", parent=dlg)
                        return
                    pick.append((book_id, rq))
            if not pick:
                messagebox.showerror("No items", "You must return at least one item.", parent=dlg)
                return
            try:
                rid, receipt_text = self.db.create_return(
                    sid,
                    pick,
                    reason_var.get().strip(),
                    method_var.get(),
                    self.user["id"],
                )
            except Exception as e:
                messagebox.showerror("Return failed", str(e), parent=dlg)
                return
            dlg.destroy()
            self.refresh_sales()
            self.refresh_books()
            self.refresh_reports()
            Dialog.show_text(self.root, f"Return #{rid}", receipt_text)

        ttk.Button(bottom, text="Cancel", command=dlg.destroy).pack(side="right")
        ttk.Button(bottom, text="Create Return", command=do_return).pack(side="right", padx=8)

        self.root.wait_window(dlg)

    def _selected_return_id(self, tree: Optional[ttk.Treeview] = None) -> Optional[int]:
        tree = tree or self.returns_tree
        sel = tree.selection()
        return int(sel[0]) if sel else None

    def view_return_receipt(self):
        rid = self._selected_return_id()
        if not rid:
            messagebox.showerror("No selection", "Select a return.")
            return
        row = self.db.get_return_receipt(rid)
        if not row:
            return
        receipt_text, ts = row
        Dialog.show_text(self.root, f"Return #{rid}", receipt_text)

    def export_return_pdf(self):
        rid = self._selected_return_id()
        if not rid:
            messagebox.showerror("No selection", "Select a return.")
            return
        row = self.db.get_return_receipt(rid)
        if not row:
            return
        receipt_text, _ = row
        path = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF", "*.pdf")], initialfile=f"return_{rid}.pdf")
        if not path:
            return
        try:
            export_pdf_text(receipt_text, path, title=f"Return {rid}")
        except Exception as e:
            messagebox.showerror("PDF error", f"{e}\n\nInstall reportlab: pip install reportlab")
            return
        messagebox.showinfo("Saved", f"Saved:\n{path}")

    def delete_return_ui(self, tree: Optional[ttk.Treeview] = None):
        rid = self._selected_return_id(tree)
        if not rid:
            messagebox.showerror("No selection", "Select a return.")
            return
        if not messagebox.askyesno("Delete return", "Delete this return? This cannot be undone."):
            return
        try:
            self.db.delete_return(rid, self.user["id"])
        except Exception as e:
            messagebox.showerror("Delete failed", str(e))
            return
        self.refresh_sales()
        self.refresh_reports()
        self.refresh_books()

    # ---------------- Reports tab ----------------
    def _build_reports_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Reports")
        self.reports_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)
        ttk.Button(top, text="Refresh", command=self.refresh_reports).pack(side="left")
        ttk.Button(top, text="Export Sales CSV", command=self.export_sales_csv).pack(side="right")
        ttk.Button(top, text="Export Tax CSV", command=self.export_tax_csv).pack(side="right", padx=8)

        body = ttk.Frame(tab)
        body.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        left = ttk.Frame(body)
        left.pack(side="left", fill="both", expand=True, padx=(0, 10))
        right = ttk.Frame(body)
        right.pack(side="left", fill="both", expand=True)

        summary = ttk.LabelFrame(right, text="Summary (last 30 days)")
        summary.pack(fill="x", pady=(0, 10))
        self.report_summary_vars = {
            "sales": tk.StringVar(value="0"),
            "returns": tk.StringVar(value="0"),
            "net_revenue": tk.StringVar(value="$0.00"),
            "net_profit": tk.StringVar(value="$0.00"),
            "avg_order": tk.StringVar(value="$0.00"),
            "return_rate": tk.StringVar(value="0.0%"),
        }
        summary_fields = [
            ("Sales", "sales"),
            ("Returns", "returns"),
            ("Net revenue", "net_revenue"),
            ("Net profit", "net_profit"),
            ("Avg order", "avg_order"),
            ("Return rate", "return_rate"),
        ]
        for idx, (label, key) in enumerate(summary_fields):
            row = idx // 2
            col = (idx % 2) * 2
            ttk.Label(summary, text=f"{label}:").grid(row=row, column=col, sticky="w", padx=8, pady=2)
            ttk.Label(summary, textvariable=self.report_summary_vars[key]).grid(row=row, column=col + 1, sticky="w", padx=(0, 8), pady=2)

        manage = ttk.LabelFrame(right, text="Manage Sales & Returns")
        manage.pack(fill="both", expand=False, pady=(0, 10))

        manage_body = ttk.Frame(manage)
        manage_body.pack(fill="both", expand=True, padx=8, pady=8)

        sales_frame = ttk.Frame(manage_body)
        sales_frame.pack(fill="both", expand=True)
        ttk.Label(sales_frame, text="Recent sales").pack(anchor="w")
        self.reports_sales_tree = ttk.Treeview(
            sales_frame,
            columns=("rno", "ts", "total", "status", "void"),
            show="headings",
            height=6,
        )
        for c, l, w, a in [
            ("rno", "Receipt", 80, "w"),
            ("ts", "Date", 140, "w"),
            ("total", "Total", 80, "e"),
            ("status", "Pay", 70, "center"),
            ("void", "Void", 60, "center"),
        ]:
            self.reports_sales_tree.heading(c, text=l)
            self.reports_sales_tree.column(c, width=w, anchor=a)
        self.reports_sales_tree.pack(fill="x", pady=(0, 6))

        sales_btns = ttk.Frame(sales_frame)
        sales_btns.pack(fill="x", pady=(0, 6))
        ttk.Button(sales_btns, text="Create Return", command=lambda: self.create_return_ui(self.reports_sales_tree)).pack(side="left")
        ttk.Button(sales_btns, text="Update Payment", command=lambda: self.update_sale_payment_status_ui(self.reports_sales_tree)).pack(side="left", padx=6)
        ttk.Button(sales_btns, text="Void Sale", command=lambda: self.void_sale_ui(self.reports_sales_tree)).pack(side="left", padx=6)
        ttk.Button(sales_btns, text="Delete Sale", command=lambda: self.delete_sale_ui(self.reports_sales_tree)).pack(side="left", padx=6)

        returns_frame = ttk.Frame(manage_body)
        returns_frame.pack(fill="both", expand=True)
        ttk.Label(returns_frame, text="Recent returns").pack(anchor="w")
        self.reports_returns_tree = ttk.Treeview(
            returns_frame,
            columns=("ts", "orig", "refund", "method"),
            show="headings",
            height=5,
        )
        for c, l, w, a in [
            ("ts", "Date", 140, "w"),
            ("orig", "Receipt", 90, "w"),
            ("refund", "Refund", 90, "e"),
            ("method", "Method", 70, "center"),
        ]:
            self.reports_returns_tree.heading(c, text=l)
            self.reports_returns_tree.column(c, width=w, anchor=a)
        self.reports_returns_tree.pack(fill="x", pady=(0, 6))

        returns_btns = ttk.Frame(returns_frame)
        returns_btns.pack(fill="x")
        ttk.Button(returns_btns, text="Delete Return", command=lambda: self.delete_return_ui(self.reports_returns_tree)).pack(side="left")

        adjustments = ttk.LabelFrame(right, text="Inventory adjustments (recent)")
        adjustments.pack(fill="both", expand=False, pady=(0, 10))
        self.adjustments_tree = ttk.Treeview(
            adjustments,
            columns=("ts", "item", "delta", "reason", "user", "note"),
            show="headings",
            height=5,
        )
        for c, l, w, a in [
            ("ts", "Date", 140, "w"),
            ("item", "Item", 220, "w"),
            ("delta", "Δ Qty", 60, "center"),
            ("reason", "Reason", 100, "w"),
            ("user", "User", 90, "w"),
            ("note", "Note", 160, "w"),
        ]:
            self.adjustments_tree.heading(c, text=l)
            self.adjustments_tree.column(c, width=w, anchor=a)
        self.adjustments_tree.pack(fill="x", padx=8, pady=8)

        reorder = ttk.LabelFrame(right, text="Reorder suggestions")
        reorder.pack(fill="both", expand=False, pady=(0, 10))
        reorder_actions = ttk.Frame(reorder)
        reorder_actions.pack(fill="x", padx=8, pady=(8, 0))
        ttk.Button(reorder_actions, text="Export Reorder CSV", command=self.export_reorder_csv).pack(side="right")
        self.reorder_tree = ttk.Treeview(
            reorder,
            columns=("item", "category", "stock", "reorder_point", "reorder_qty"),
            show="headings",
            height=6,
        )
        for c, l, w, a in [
            ("item", "Item", 220, "w"),
            ("category", "Category", 140, "w"),
            ("stock", "Stock", 60, "center"),
            ("reorder_point", "Reorder @", 80, "center"),
            ("reorder_qty", "Reorder Qty", 90, "center"),
        ]:
            self.reorder_tree.heading(c, text=l)
            self.reorder_tree.column(c, width=w, anchor=a)
        self.reorder_tree.pack(fill="x", padx=8, pady=8)

        daily = ttk.LabelFrame(left, text="Daily (last 30 days) — revenue, refunds, net, tax")
        daily.pack(fill="both", expand=True, pady=(0, 10))
        self.daily_tree = ttk.Treeview(daily, columns=("day", "sales", "returns", "rev", "refund", "net", "tax"), show="headings", height=10)
        for c, l, w, a in [
            ("day", "Day", 110, "w"),
            ("sales", "Sales", 60, "center"),
            ("returns", "Returns", 70, "center"),
            ("rev", "Revenue", 100, "e"),
            ("refund", "Refunds", 100, "e"),
            ("net", "Net", 100, "e"),
            ("tax", "Tax", 90, "e"),
        ]:
            self.daily_tree.heading(c, text=l)
            self.daily_tree.column(c, width=w, anchor=a)
        self.daily_tree.pack(fill="both", expand=True, padx=10, pady=10)

        monthly = ttk.LabelFrame(left, text="Monthly totals")
        monthly.pack(fill="both", expand=True)
        self.monthly_tree = ttk.Treeview(monthly, columns=("month", "sales", "rev", "tax"), show="headings", height=8)
        for c, l, w, a in [
            ("month", "Month", 110, "w"),
            ("sales", "Sales", 60, "center"),
            ("rev", "Revenue", 120, "e"),
            ("tax", "Tax", 100, "e"),
        ]:
            self.monthly_tree.heading(c, text=l)
            self.monthly_tree.column(c, width=w, anchor=a)
        self.monthly_tree.pack(fill="both", expand=True, padx=10, pady=10)

        topbooks = ttk.LabelFrame(right, text="Top items (revenue + profit)")
        topbooks.pack(fill="both", expand=True, pady=(0, 10))
        self.top_books = ttk.Treeview(topbooks, columns=("title", "units", "rev", "profit"), show="headings", height=8)
        for c, l, w, a in [
            ("title", "Item", 260, "w"),
            ("units", "Units", 70, "center"),
            ("rev", "Revenue", 120, "e"),
            ("profit", "Profit", 120, "e"),
        ]:
            self.top_books.heading(c, text=l)
            self.top_books.column(c, width=w, anchor=a)
        self.top_books.pack(fill="both", expand=True, padx=10, pady=10)

        topcust = ttk.LabelFrame(right, text="Top platforms (revenue)")
        topcust.pack(fill="both", expand=True, pady=(0, 10))
        self.top_customers = ttk.Treeview(topcust, columns=("name", "sales", "rev"), show="headings", height=6)
        for c, l, w, a in [
            ("name", "Platform", 220, "w"),
            ("sales", "Sales", 60, "center"),
            ("rev", "Revenue", 120, "e"),
        ]:
            self.top_customers.heading(c, text=l)
            self.top_customers.column(c, width=w, anchor=a)
        self.top_customers.pack(fill="both", expand=True, padx=10, pady=10)

        bycat = ttk.LabelFrame(right, text="By category (revenue + profit)")
        bycat.pack(fill="both", expand=True)
        self.by_category = ttk.Treeview(bycat, columns=("cat", "rev", "profit"), show="headings", height=6)
        for c, l, w, a in [
            ("cat", "Category", 220, "w"),
            ("rev", "Revenue", 120, "e"),
            ("profit", "Profit", 120, "e"),
        ]:
            self.by_category.heading(c, text=l)
            self.by_category.column(c, width=w, anchor=a)
        self.by_category.pack(fill="both", expand=True, padx=10, pady=10)

    def refresh_reports(self):
        for t in (self.daily_tree, self.monthly_tree, self.top_books, self.top_customers, self.by_category):
            for i in t.get_children():
                t.delete(i)

        summary = self.db.report_summary(30)
        self.report_summary_vars["sales"].set(str(summary["sales_count"]))
        self.report_summary_vars["returns"].set(str(summary["returns_count"]))
        self.report_summary_vars["net_revenue"].set(cents_to_money(summary["net_revenue_cents"]))
        self.report_summary_vars["net_profit"].set(cents_to_money(summary["profit_cents"]))
        self.report_summary_vars["avg_order"].set(cents_to_money(summary["avg_order_cents"]))
        self.report_summary_vars["return_rate"].set(f"{summary['return_rate'] * 100:.1f}%")

        for d, scnt, rcnt, rev, refund, net, tax in self.db.report_daily(30):
            self.daily_tree.insert("", "end", values=(d, scnt, rcnt, cents_to_money(rev), cents_to_money(refund), cents_to_money(net), cents_to_money(tax)))

        for month, rev, tax, scnt in self.db.report_monthly():
            self.monthly_tree.insert("", "end", values=(month, scnt, cents_to_money(rev), cents_to_money(tax)))

        for title, units, rev, profit in self.db.report_top_books(10):
            self.top_books.insert("", "end", values=(title, units, cents_to_money(rev), cents_to_money(profit)))

        for name, sales, rev in self.db.report_top_platforms(10):
            self.top_customers.insert("", "end", values=(name, sales, cents_to_money(rev)))

        for cat, rev, profit in self.db.report_by_category():
            self.by_category.insert("", "end", values=(cat, cents_to_money(rev), cents_to_money(profit)))

        if hasattr(self, "reports_sales_tree"):
            for i in self.reports_sales_tree.get_children():
                self.reports_sales_tree.delete(i)
            for sid, rno, ts, _platform, total, status, is_void in self.db.list_sales(50):
                self.reports_sales_tree.insert(
                    "", "end", iid=str(sid),
                    values=(rno, ts, cents_to_money(total), status, "yes" if is_void else "no"),
                )

        if hasattr(self, "reports_returns_tree"):
            for i in self.reports_returns_tree.get_children():
                self.reports_returns_tree.delete(i)
            for rid, ts, orig_rno, refund, method in self.db.list_returns(50):
                self.reports_returns_tree.insert(
                    "", "end", iid=str(rid),
                    values=(ts, orig_rno, cents_to_money(refund), method),
                )

        if hasattr(self, "adjustments_tree"):
            for i in self.adjustments_tree.get_children():
                self.adjustments_tree.delete(i)
            for ts, title, delta, reason, note, username in self.db.list_inventory_adjustments(50):
                self.adjustments_tree.insert(
                    "", "end",
                    values=(ts, title, f"{delta:+d}", reason, username, note),
                )

        if hasattr(self, "reorder_tree"):
            for i in self.reorder_tree.get_children():
                self.reorder_tree.delete(i)
            for _bid, title, stock, reorder_point, reorder_qty, category in self.db.list_reorder_suggestions(200):
                self.reorder_tree.insert(
                    "", "end",
                    values=(title, category, stock, reorder_point, reorder_qty),
                )

    def export_sales_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Sales CSV")
        if not path:
            return
        q = """
            SELECT receipt_no, created_at, customer_id, platform, subtotal_cents, discount_cents, coupon_code, tax_rate, tax_cents,
                   total_cents, payment_method, payment_status, note, is_void
            FROM sales
            ORDER BY id DESC;
        """
        self.db.export_table_to_csv(q,
            ["receipt_no", "created_at", "customer_id", "platform", "subtotal_cents", "discount_cents", "coupon_code", "tax_rate", "tax_cents",
             "total_cents", "payment_method", "payment_status", "note", "is_void"], path)
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    def export_tax_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Tax CSV")
        if not path:
            return
        with self.db._connect() as conn:
            has_refund_tax = "refund_tax_cents" in self.db._columns(conn, "returns")
        q = """
            WITH sales_daily AS (
                SELECT substr(created_at,1,10) AS day,
                       SUM(tax_cents) AS tax_cents,
                       SUM(total_cents) AS total_cents
                FROM sales
                WHERE is_void=0
                GROUP BY day
            ),
            returns_daily AS (
                SELECT substr(created_at,1,10) AS day,
                       SUM(refund_cents) AS refund_cents,
                       SUM({refund_tax_col}) AS refund_tax_cents
                FROM returns
                GROUP BY day
            )
            SELECT COALESCE(sales_daily.day, returns_daily.day) AS day,
                   IFNULL(sales_daily.tax_cents, 0) - IFNULL(returns_daily.refund_tax_cents, 0) AS tax_cents,
                   IFNULL(sales_daily.total_cents, 0) - IFNULL(returns_daily.refund_cents, 0) AS total_cents
            FROM sales_daily
            LEFT JOIN returns_daily ON returns_daily.day = sales_daily.day
            UNION
            SELECT COALESCE(sales_daily.day, returns_daily.day) AS day,
                   IFNULL(sales_daily.tax_cents, 0) - IFNULL(returns_daily.refund_tax_cents, 0) AS tax_cents,
                   IFNULL(sales_daily.total_cents, 0) - IFNULL(returns_daily.refund_cents, 0) AS total_cents
            FROM returns_daily
            LEFT JOIN sales_daily ON sales_daily.day = returns_daily.day
            ORDER BY day DESC;
        """
        refund_tax_col = "refund_tax_cents" if has_refund_tax else "0"
        q = q.format(refund_tax_col=refund_tax_col)
        self.db.export_table_to_csv(q, ["day", "tax_cents", "total_cents"], path)
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    def export_reorder_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Reorder CSV")
        if not path:
            return
        q = """
            SELECT b.title, IFNULL(cat.name,'(Uncategorized)') AS category,
                   b.stock_qty, b.reorder_point, b.reorder_qty
            FROM books b
            LEFT JOIN categories cat ON cat.id = b.category_id
            WHERE b.is_active=1
              AND b.reorder_point > 0
              AND b.stock_qty <= b.reorder_point
            ORDER BY (b.reorder_point - b.stock_qty) DESC, b.title;
        """
        self.db.export_table_to_csv(q, ["title", "category", "stock_qty", "reorder_point", "reorder_qty"], path)
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    # ---------------- Admin tab ----------------
    def _build_admin_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Admin")
        self.admin_tab = tab

        banner = ttk.Label(tab, text="Admin tools (requires admin role for changes).")
        banner.pack(anchor="w", padx=10, pady=(10, 0))

        body = ttk.Frame(tab)
        body.pack(fill="both", expand=True, padx=10, pady=10)

        left = ttk.Frame(body)
        left.pack(side="left", fill="both", expand=True, padx=(0, 10))
        right = ttk.Frame(body)
        right.pack(side="left", fill="both", expand=True)

        settings = ttk.LabelFrame(left, text="Store / Receipt Settings")
        settings.pack(fill="x", pady=(0, 10))

        self.set_store = tk.StringVar(value=self.db.get_setting("store_name"))
        self.set_addr = tk.StringVar(value=self.db.get_setting("store_address"))
        self.set_phone = tk.StringVar(value=self.db.get_setting("store_phone"))
        self.set_footer = tk.StringVar(value=self.db.get_setting("receipt_footer"))
        self.set_prefix = tk.StringVar(value=self.db.get_setting("receipt_prefix"))
        self.set_taxdef = tk.StringVar(value=self.db.get_setting("tax_rate_default"))

        def row(parent, label, var, show: str = ""):
            r = ttk.Frame(parent)
            r.pack(fill="x", padx=10, pady=4)
            ttk.Label(r, text=label, width=18).pack(side="left")
            ttk.Entry(r, textvariable=var, width=50, show=show).pack(side="left")

        row(settings, "Store name:", self.set_store)
        row(settings, "Address:", self.set_addr)
        row(settings, "Phone:", self.set_phone)
        row(settings, "Footer:", self.set_footer)
        row(settings, "Receipt prefix:", self.set_prefix)
        row(settings, "Default tax:", self.set_taxdef)
        ttk.Button(settings, text="Save Settings", command=self.save_settings).pack(anchor="e", padx=10, pady=(6, 10))

        backup = ttk.LabelFrame(left, text="Backup / Restore")
        backup.pack(fill="x")
        bbtn = ttk.Frame(backup)
        bbtn.pack(fill="x", padx=10, pady=10)
        ttk.Button(bbtn, text="Backup DB", command=self.backup_db).pack(side="left")
        ttk.Button(bbtn, text="Restore DB", command=self.restore_db).pack(side="left", padx=8)

        cats = ttk.LabelFrame(right, text="Categories")
        cats.pack(fill="both", expand=True, pady=(0, 10))

        self.cat_tree = ttk.Treeview(cats, columns=("name", "active"), show="headings", height=6)
        self.cat_tree.heading("name", text="Name")
        self.cat_tree.heading("active", text="Active")
        self.cat_tree.column("name", width=220)
        self.cat_tree.column("active", width=80, anchor="center")
        self.cat_tree.pack(fill="x", padx=10, pady=10)

        catbtn = ttk.Frame(cats)
        catbtn.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(catbtn, text="Add", command=self.add_category).pack(side="left")
        ttk.Button(catbtn, text="Toggle Active", command=self.toggle_category).pack(side="left", padx=8)
        ttk.Button(catbtn, text="Refresh", command=self.refresh_admin_lists).pack(side="right")

        coupons = ttk.LabelFrame(right, text="Coupons")
        coupons.pack(fill="both", expand=True, pady=(0, 10))

        self.coupon_tree = ttk.Treeview(coupons, columns=("code", "kind", "value", "active", "expires"), show="headings", height=6)
        for c, l, w, a in [
            ("code", "Code", 120, "w"),
            ("kind", "Kind", 80, "center"),
            ("value", "Value", 80, "e"),
            ("active", "Active", 70, "center"),
            ("expires", "Expires", 100, "w"),
        ]:
            self.coupon_tree.heading(c, text=l)
            self.coupon_tree.column(c, width=w, anchor=a)
        self.coupon_tree.pack(fill="x", padx=10, pady=10)

        cbtn = ttk.Frame(coupons)
        cbtn.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(cbtn, text="Add", command=self.add_coupon).pack(side="left")
        ttk.Button(cbtn, text="Edit", command=self.edit_coupon).pack(side="left", padx=8)

        users = ttk.LabelFrame(right, text="Users")
        users.pack(fill="both", expand=True)

        self.user_tree = ttk.Treeview(users, columns=("username", "role", "active"), show="headings", height=6)
        for c, l, w, a in [
            ("username", "Username", 140, "w"),
            ("role", "Role", 80, "center"),
            ("active", "Active", 80, "center"),
        ]:
            self.user_tree.heading(c, text=l)
            self.user_tree.column(c, width=w, anchor=a)
        self.user_tree.pack(fill="x", padx=10, pady=10)

        ubtn = ttk.Frame(users)
        ubtn.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(ubtn, text="Add User", command=self.add_user).pack(side="left")
        ttk.Button(ubtn, text="Toggle Active", command=self.toggle_user).pack(side="left", padx=8)
        ttk.Button(ubtn, text="Reset Password", command=self.reset_user_password).pack(side="left", padx=8)

    def refresh_admin_lists(self):
        for t in (self.cat_tree, self.coupon_tree, self.user_tree):
            for i in t.get_children():
                t.delete(i)

        for cid, name, active in self.db.list_categories(include_inactive=True):
            self.cat_tree.insert("", "end", iid=str(cid), values=(name, "yes" if active else "no"))

        for cid, code, kind, value, active, exp in self.db.list_coupons():
            val_str = f"{value:.2f}%" if kind == "percent" else f"${value:.2f}"
            self.coupon_tree.insert("", "end", iid=str(cid), values=(code, kind, val_str, "yes" if active else "no", exp or ""))

        for uid, username, role, active in self.db.list_users():
            self.user_tree.insert("", "end", iid=str(uid), values=(username, role, "yes" if active else "no"))

    def save_settings(self):
        if not self._require_admin():
            return
        self.db.set_setting("store_name", self.set_store.get().strip())
        self.db.set_setting("store_address", self.set_addr.get().strip())
        self.db.set_setting("store_phone", self.set_phone.get().strip())
        self.db.set_setting("receipt_footer", self.set_footer.get().strip())
        self.db.set_setting("receipt_prefix", self.set_prefix.get().strip() or "R")
        self.db.set_setting("tax_rate_default", self.set_taxdef.get().strip() or "0.00")
        if hasattr(self, "tax_var"):
            self.tax_var.set(self.db.get_setting("tax_rate_default") or "0.00")
        messagebox.showinfo("Saved", "Settings saved.")

    def backup_db(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".db",
            filetypes=[("SQLite DB", "*.db")],
            title="Backup DB",
            initialfile=f"inventory_backup_{today_ymd()}.db"
        )
        if not path:
            return
        try:
            shutil.copy2(DB_PATH, path)
        except Exception as e:
            messagebox.showerror("Backup failed", str(e))
            return
        messagebox.showinfo("Backup", f"Backup saved:\n{path}")

    def restore_db(self):
        if not self._require_admin():
            return
        path = filedialog.askopenfilename(filetypes=[("SQLite DB", "*.db"), ("All files", "*.*")], title="Select DB to restore")
        if not path:
            return
        if not messagebox.askyesno("Confirm", "This will overwrite your current DB. Continue?"):
            return
        try:
            shutil.copy2(path, DB_PATH)
        except Exception as e:
            messagebox.showerror("Restore failed", str(e))
            return
        messagebox.showinfo("Restore", "DB restored. Please restart the app.")
        self.root.destroy()

    def add_category(self):
        if not self._require_admin():
            return
        data = Dialog.ask_fields(self.root, "Add Category", [("Name", "name")])
        if not data:
            return
        try:
            self.db.add_category(data["name"])
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", str(e))
            return
        self.refresh_admin_lists()
        self.refresh_books()

    def toggle_category(self):
        if not self._require_admin():
            return
        sel = self.cat_tree.selection()
        if not sel:
            return
        cid = int(sel[0])
        cats = self.db.list_categories(include_inactive=True)
        cur = next((c for c in cats if c[0] == cid), None)
        if not cur:
            return
        active = int(cur[2])
        self.db.set_category_active(cid, 0 if active else 1)
        self.refresh_admin_lists()
        self.refresh_books()

    def add_coupon(self):
        if not self._require_admin():
            return
        data = Dialog.ask_fields(self.root, "Add Coupon", [
            ("Code (no spaces)", "code"),
            ("Kind (percent/fixed)", "kind"),
            ("Value (percent number OR dollars)", "value"),
            ("Active? (yes/no)", "active"),
            ("Expires on (YYYY-MM-DD or blank)", "exp"),
        ], initial={"kind": "percent", "value": "10", "active": "yes", "exp": ""})
        if not data:
            return
        kind = data["kind"].strip().lower()
        if kind not in ("percent", "fixed"):
            messagebox.showerror("Bad kind", "Kind must be percent or fixed.")
            return
        try:
            val = float(data["value"])
            if val < 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad value", "Value must be >= 0.")
            return
        active = 1 if data["active"].lower() in ("yes", "y", "1", "true") else 0
        exp = data["exp"].strip() or None
        try:
            self.db.add_coupon(data["code"], kind, val, active, exp)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", str(e))
            return
        self.refresh_admin_lists()

    def edit_coupon(self):
        if not self._require_admin():
            return
        sel = self.coupon_tree.selection()
        if not sel:
            return
        cid = int(sel[0])
        rows = self.db.list_coupons()
        row = next((r for r in rows if r[0] == cid), None)
        if not row:
            return
        _id, code, kind, value, active, exp = row
        init = {"code": code, "kind": kind, "value": str(value), "active": "yes" if active else "no", "exp": exp or ""}
        data = Dialog.ask_fields(self.root, "Edit Coupon", [
            ("Code", "code"),
            ("Kind (percent/fixed)", "kind"),
            ("Value", "value"),
            ("Active? (yes/no)", "active"),
            ("Expires on (YYYY-MM-DD or blank)", "exp"),
        ], initial=init)
        if not data:
            return
        kind2 = data["kind"].strip().lower()
        if kind2 not in ("percent", "fixed"):
            messagebox.showerror("Bad kind", "Kind must be percent or fixed.")
            return
        try:
            val2 = float(data["value"])
            if val2 < 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad value", "Value must be >= 0.")
            return
        active2 = 1 if data["active"].lower() in ("yes", "y", "1", "true") else 0
        exp2 = data["exp"].strip() or None
        try:
            self.db.update_coupon(cid, data["code"], kind2, val2, active2, exp2)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", str(e))
            return
        self.refresh_admin_lists()

    def add_user(self):
        if not self._require_admin():
            return
        data = Dialog.ask_fields(self.root, "Add User", [
            ("Username", "u"),
            ("Password", "p"),
            ("Role (admin/clerk)", "r"),
        ], initial={"r": "clerk"}, password_keys={"p"})
        if not data:
            return
        role = data["r"].strip().lower()
        if role not in ("admin", "clerk"):
            messagebox.showerror("Bad role", "Role must be admin or clerk.")
            return
        try:
            self.db.add_user(data["u"], data["p"], role)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", str(e))
            return
        self.refresh_admin_lists()

    def toggle_user(self):
        if not self._require_admin():
            return
        sel = self.user_tree.selection()
        if not sel:
            return
        uid = int(sel[0])
        rows = self.db.list_users()
        row = next((r for r in rows if r[0] == uid), None)
        if not row:
            return
        active = int(row[3])
        self.db.set_user_active(uid, 0 if active else 1)
        self.refresh_admin_lists()

    def reset_user_password(self):
        if not self._require_admin():
            return
        sel = self.user_tree.selection()
        if not sel:
            return
        uid = int(sel[0])
        data = Dialog.ask_fields(self.root, "Reset Password", [("New password", "p")], password_keys={"p"})
        if not data:
            return
        self.db.reset_password(uid, data["p"])
        messagebox.showinfo("Done", "Password reset.")

    # ---------------- Global refresh ----------------
    def refresh_all(self):
        self.refresh_books()
        self.refresh_platform_sales()
        self.refresh_pending_products()
        self.refresh_pickup_ship()
        self.refresh_sales()
        self.refresh_reports()
        self.refresh_admin_lists()

    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    App().run()
