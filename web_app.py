import csv
import io
import os
import secrets
import shutil
from functools import wraps
from typing import List, Dict, Any, Optional, Tuple

from flask import (
    Flask,
    render_template,
    redirect,
    request,
    session,
    url_for,
    flash,
    Response,
    send_file,
    jsonify,
)

from app import (
    DB,
    DB_PATH,
    cents_to_money,
    dollars_to_cents,
    CONDITION_OPTIONS,
    AVAILABILITY_LABELS,
    AVAILABILITY_STATUSES,
    PLATFORM_OPTIONS,
    PLATFORM_SALE_STATUSES,
    normalize_barcode,
    normalize_locations,
    parse_optional_float,
    parse_optional_int,
    parse_scan_barcode_and_price,
    export_pdf_text,
    fetch_title_info_upcitemdb,
)


app = Flask(__name__)
app.secret_key = os.environ.get("FLASK_SECRET_KEY", secrets.token_hex(16))
app.config["MAX_CONTENT_LENGTH"] = 10 * 1024 * 1024

db = DB()


PAYMENT_METHODS = ["cash", "card", "other"]
PAYMENT_STATUSES = ["paid", "partial", "unpaid"]


def login_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not session.get("user_id"):
            return redirect(url_for("login"))
        return view(*args, **kwargs)
    return wrapped


def admin_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not session.get("user_id"):
            return redirect(url_for("login"))
        if session.get("role") != "admin":
            flash("Admin access required.", "danger")
            return redirect(url_for("inventory"))
        return view(*args, **kwargs)
    return wrapped


def parse_money(value: str, default: int = 0) -> int:
    value = (value or "").strip()
    if not value:
        return default
    return dollars_to_cents(value)


def parse_cart_lines(raw: str) -> List[Dict[str, Any]]:
    lines = []
    for idx, line in enumerate((raw or "").splitlines(), start=1):
        if not line.strip():
            continue
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 2:
            raise ValueError(f"Line {idx}: expected book_id,qty[,unit_price][,line_discount]")
        book_id = int(parts[0])
        qty = int(parts[1])
        unit_price_cents = parse_money(parts[2]) if len(parts) > 2 and parts[2] else None
        line_discount_cents = parse_money(parts[3]) if len(parts) > 3 and parts[3] else None
        item = {"book_id": book_id, "qty": qty}
        if unit_price_cents is not None:
            item["unit_price_cents"] = unit_price_cents
        if line_discount_cents is not None:
            item["line_discount_cents"] = line_discount_cents
        lines.append(item)
    return lines


def parse_return_lines(raw: str) -> List[Tuple[int, int]]:
    items = []
    for idx, line in enumerate((raw or "").splitlines(), start=1):
        if not line.strip():
            continue
        parts = [p.strip() for p in line.split(",")]
        if len(parts) < 2:
            raise ValueError(f"Line {idx}: expected book_id,qty")
        items.append((int(parts[0]), int(parts[1])))
    return items


def load_book_form(form: Dict[str, str]) -> Dict[str, Any]:
    barcode = normalize_barcode(form.get("barcode", "").strip()) or None
    isbn = form.get("isbn", "").strip() or None
    title = form.get("title", "").strip()
    author = form.get("author", "").strip()
    category_id = parse_optional_int(form.get("category_id", ""), "category")
    location = normalize_locations(form.get("location", ""))
    condition = form.get("condition", "Good").strip() or "Good"
    length_in = parse_optional_float(form.get("length_in", ""), "length")
    width_in = parse_optional_float(form.get("width_in", ""), "width")
    height_in = parse_optional_float(form.get("height_in", ""), "height")
    weight_lb = parse_optional_float(form.get("weight_lb", ""), "weight lb")
    weight_oz = parse_optional_float(form.get("weight_oz", ""), "weight oz")
    price_cents = parse_money(form.get("price", ""))
    cost_cents = parse_money(form.get("cost", ""))
    stock_qty = int(form.get("stock_qty", "0") or 0)
    reorder_point = int(form.get("reorder_point", "0") or 0)
    reorder_qty = int(form.get("reorder_qty", "0") or 0)
    is_active = 1 if form.get("is_active") == "1" else 0
    uploaded_facebook = 1 if form.get("uploaded_facebook") == "1" else 0
    uploaded_ebay = 1 if form.get("uploaded_ebay") == "1" else 0
    availability_status = form.get("availability_status", "available").strip() or "available"

    if not title:
        raise ValueError("Title is required.")
    if condition not in CONDITION_OPTIONS:
        raise ValueError("Invalid condition.")
    if weight_oz is not None and weight_oz >= 16:
        raise ValueError("Weight oz must be 0-15.")
    if stock_qty < 0 or reorder_point < 0 or reorder_qty < 0:
        raise ValueError("Stock and reorder values cannot be negative.")

    return {
        "isbn": isbn,
        "barcode": barcode,
        "title": title,
        "author": author,
        "category_id": category_id,
        "location": location,
        "length_in": length_in,
        "width_in": width_in,
        "height_in": height_in,
        "weight_lb": weight_lb,
        "weight_oz": weight_oz,
        "condition": condition,
        "price_cents": price_cents,
        "cost_cents": cost_cents,
        "stock_qty": stock_qty,
        "reorder_point": reorder_point,
        "reorder_qty": reorder_qty,
        "is_active": is_active,
        "uploaded_facebook": uploaded_facebook,
        "uploaded_ebay": uploaded_ebay,
        "availability_status": availability_status,
    }


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        password = request.form.get("password", "").strip()
        auth = db.auth_user(username, password)
        if not auth:
            flash("Invalid username or password.", "danger")
            return render_template("login.html")
        session.clear()
        session["user_id"] = auth["id"]
        session["username"] = auth["username"]
        session["role"] = auth["role"]
        if auth.get("must_change_password"):
            session["must_change_password"] = True
            return redirect(url_for("change_password"))
        return redirect(url_for("inventory"))
    return render_template("login.html")


@app.route("/change-password", methods=["GET", "POST"])
def change_password():
    if not session.get("user_id"):
        return redirect(url_for("login"))
    if request.method == "POST":
        p1 = request.form.get("password", "")
        p2 = request.form.get("password_confirm", "")
        if not p1:
            flash("Password cannot be empty.", "danger")
        elif p1 != p2:
            flash("Passwords do not match.", "danger")
        else:
            db.reset_password(session["user_id"], p1)
            db.delete_setting("admin_temp_password")
            db.delete_setting("admin_temp_password_created_at")
            session.pop("must_change_password", None)
            flash("Password updated.", "success")
            return redirect(url_for("inventory"))
    return render_template("change_password.html")


@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))


@app.route("/")
@app.route("/inventory")
@login_required
def inventory():
    search = request.args.get("search", "")
    in_stock = request.args.get("in_stock") == "1"
    low_stock = request.args.get("low_stock") == "1"
    condition = request.args.get("condition") or None
    availability = request.args.get("availability") or "All"
    categories = db.list_categories(include_inactive=False)
    category_id = request.args.get("category_id") or None
    category_id_int = int(category_id) if category_id else None
    books = db.list_books(
        search=search,
        in_stock_only=in_stock,
        low_stock_only=low_stock,
        include_inactive=True,
        category_id=category_id_int,
        condition=None if condition == "All" else condition,
        availability_status=None if availability == "All" else availability,
    )
    availability_options = [("All", "All")] + [(value, label) for label, value in AVAILABILITY_STATUSES.items()]
    rows = [
        {
            "id": b[0],
            "barcode": b[1],
            "isbn": b[2],
            "title": b[3],
            "author": b[4],
            "location": b[5],
            "condition": b[11],
            "price": cents_to_money(b[12]),
            "stock": b[14],
            "reorder_point": b[15],
            "availability": AVAILABILITY_LABELS.get(b[19], b[19]),
            "category": b[20] or "(Uncategorized)",
            "active": bool(b[18]),
        }
        for b in books
    ]
    return render_template(
        "inventory.html",
        rows=rows,
        search=search,
        in_stock=in_stock,
        low_stock=low_stock,
        categories=categories,
        category_id=category_id_int,
        conditions=["All"] + CONDITION_OPTIONS,
        condition=condition or "All",
        availability=availability or "All",
        availability_options=availability_options,
    )


@app.route("/books/new", methods=["GET", "POST"])
@login_required
def book_new():
    categories = db.list_categories(include_inactive=True)
    if request.method == "POST":
        try:
            payload = load_book_form(request.form)
            db.add_book(**payload)
            flash("Item added.", "success")
            return redirect(url_for("inventory"))
        except Exception as exc:
            flash(str(exc), "danger")
    return render_template(
        "book_form.html",
        title="Add Item",
        book=None,
        show_scan=True,
        categories=categories,
        conditions=CONDITION_OPTIONS,
        availability=list(AVAILABILITY_STATUSES.values()),
        cents_to_money=cents_to_money,
    )


@app.route("/books/<int:book_id>/edit", methods=["GET", "POST"])
@login_required
def book_edit(book_id: int):
    categories = db.list_categories(include_inactive=True)
    book = db.get_book(book_id)
    if not book:
        flash("Item not found.", "danger")
        return redirect(url_for("inventory"))
    if request.method == "POST":
        try:
            payload = load_book_form(request.form)
            db.update_book(book_id, **payload)
            flash("Item updated.", "success")
            return redirect(url_for("inventory"))
        except Exception as exc:
            flash(str(exc), "danger")
    return render_template(
        "book_form.html",
        title="Edit Item",
        book=book,
        show_scan=False,
        categories=categories,
        conditions=CONDITION_OPTIONS,
        availability=list(AVAILABILITY_STATUSES.values()),
        cents_to_money=cents_to_money,
    )


@app.post("/books/scan")
@login_required
def book_scan():
    payload = request.get_json(silent=True) or {}
    raw = (payload.get("scan") or "").strip()
    if not raw:
        return jsonify({"error": "Scan value is required."}), 400
    barcode, price = parse_scan_barcode_and_price(raw)
    if not barcode and not price:
        return jsonify({"error": "Could not parse barcode or price from scan."}), 400

    title = None
    author = None
    if barcode:
        info = fetch_title_info_upcitemdb(barcode)
        if info:
            title = info.get("title") or None
            author = info.get("studio") or None

    return jsonify(
        {
            "barcode": barcode,
            "price": price,
            "title": title,
            "author": author,
        }
    )


@app.route("/books/<int:book_id>/toggle", methods=["POST"])
@login_required
def book_toggle(book_id: int):
    book = db.get_book(book_id)
    if not book:
        flash("Item not found.", "danger")
    else:
        db.set_book_active(book_id, 0 if int(book[18]) else 1)
        flash("Item status updated.", "success")
    return redirect(url_for("inventory"))


@app.route("/books/<int:book_id>/delete", methods=["POST"])
@admin_required
def book_delete(book_id: int):
    try:
        db.delete_book(book_id)
        flash("Item deleted.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("inventory"))


@app.route("/books/<int:book_id>/adjust", methods=["POST"])
@login_required
def book_adjust(book_id: int):
    delta = int(request.form.get("delta", "0") or 0)
    reason = request.form.get("reason", "adjustment")
    note = request.form.get("note", "")
    try:
        db.adjust_stock(book_id, delta, reason, note, session.get("user_id"))
        flash("Stock adjusted.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("inventory"))


@app.route("/books.csv")
@login_required
def books_csv():
    output = io.StringIO()
    writer = csv.writer(output)
    headers = [
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
    ]
    writer.writerow(headers)
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
    with db._connect() as conn:
        cur = conn.cursor()
        cur.execute(q)
        for row in cur.fetchall():
            writer.writerow(row)
    output.seek(0)
    return Response(
        output.getvalue(),
        mimetype="text/csv",
        headers={"Content-Disposition": "attachment; filename=inventory_items.csv"},
    )


@app.route("/books/import", methods=["POST"])
@admin_required
def books_import():
    file = request.files.get("file")
    if not file or not file.filename:
        flash("Select a CSV file to import.", "danger")
        return redirect(url_for("inventory"))
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
    content = io.StringIO(file.stream.read().decode("utf-8"))
    reader = csv.DictReader(content)
    headers = {h.strip() for h in (reader.fieldnames or [])}
    missing = required - headers
    if missing:
        flash(f"Missing columns: {', '.join(sorted(missing))}", "danger")
        return redirect(url_for("inventory"))

    with db._connect() as conn:
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

                category_id = None
                if cat_name:
                    if cat_name in categories:
                        category_id = categories[cat_name]
                    else:
                        cur.execute("INSERT INTO categories(name, is_active) VALUES(?,1);", (cat_name,))
                        category_id = int(cur.lastrowid)
                        categories[cat_name] = category_id

                if barcode and barcode in barcode_map:
                    book_id, existing_stock = barcode_map[barcode]
                    cur.execute(
                        """
                        UPDATE books
                        SET isbn=?, title=?, author=?, category_id=?, location=?, length_in=?, width_in=?, height_in=?,
                            weight_lb=?, weight_oz=?, condition=?, price_cents=?, cost_cents=?,
                            stock_qty=?, reorder_point=?, reorder_qty=?, is_active=?, uploaded_facebook=?,
                            uploaded_ebay=?, availability_status=?
                        WHERE id=?;
                        """,
                        (
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
                            stock_qty or existing_stock,
                            reorder_point,
                            reorder_qty,
                            is_active,
                            uploaded_facebook,
                            uploaded_ebay,
                            availability_status,
                            book_id,
                        ),
                    )
                    updated += 1
                else:
                    cur.execute(
                        """
                        INSERT INTO books(
                            isbn, barcode, title, author, category_id, location,
                            length_in, width_in, height_in, weight_lb, weight_oz,
                            condition, price_cents, cost_cents, stock_qty,
                            reorder_point, reorder_qty, is_active,
                            uploaded_facebook, uploaded_ebay, availability_status
                        ) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?);
                        """,
                        (
                            isbn,
                            barcode,
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
                        ),
                    )
                    inserted += 1
            except Exception as exc:
                errors.append(f"Row {idx}: {exc}")

        conn.commit()

    if errors:
        flash("Import completed with errors: " + "; ".join(errors[:5]), "warning")
    flash(f"Import done. Inserted {inserted}, updated {updated}.", "success")
    return redirect(url_for("inventory"))


@app.route("/reorder")
@login_required
def reorder():
    suggestions = db.list_reorder_suggestions(500)
    rows = [
        {
            "title": title,
            "category": category,
            "stock": stock,
            "reorder_point": reorder_point,
            "reorder_qty": reorder_qty,
        }
        for _bid, title, stock, reorder_point, reorder_qty, category in suggestions
    ]
    return render_template("reorder.html", rows=rows)


@app.route("/reorder.csv")
@login_required
def reorder_csv():
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(["title", "category", "stock_qty", "reorder_point", "reorder_qty"])
    for _bid, title, stock, reorder_point, reorder_qty, category in db.list_reorder_suggestions(1000):
        writer.writerow([title, category, stock, reorder_point, reorder_qty])
    output.seek(0)
    return Response(
        output.getvalue(),
        mimetype="text/csv",
        headers={"Content-Disposition": "attachment; filename=reorder_suggestions.csv"},
    )


@app.route("/customers")
@login_required
def customers():
    search = request.args.get("search", "")
    rows = db.list_customers(search=search, include_inactive=True)
    return render_template("customers.html", rows=rows, search=search)


@app.route("/customers/new", methods=["GET", "POST"])
@login_required
def customer_new():
    if request.method == "POST":
        name = request.form.get("name", "").strip()
        email = request.form.get("email", "").strip()
        is_active = 1 if request.form.get("is_active") == "1" else 0
        if not name or not email:
            flash("Name and email are required.", "danger")
        else:
            try:
                db.add_customer(name, email, is_active)
                flash("Customer added.", "success")
                return redirect(url_for("customers"))
            except Exception as exc:
                flash(str(exc), "danger")
    return render_template("customer_form.html", customer=None)


@app.route("/customers/<int:customer_id>/edit", methods=["GET", "POST"])
@login_required
def customer_edit(customer_id: int):
    customer = db.get_customer(customer_id)
    if not customer:
        flash("Customer not found.", "danger")
        return redirect(url_for("customers"))
    if request.method == "POST":
        name = request.form.get("name", "").strip()
        email = request.form.get("email", "").strip()
        is_active = 1 if request.form.get("is_active") == "1" else 0
        if not name or not email:
            flash("Name and email are required.", "danger")
        else:
            try:
                db.update_customer(customer_id, name, email, is_active)
                flash("Customer updated.", "success")
                return redirect(url_for("customers"))
            except Exception as exc:
                flash(str(exc), "danger")
    return render_template("customer_form.html", customer=customer)


@app.route("/customers/<int:customer_id>/toggle", methods=["POST"])
@login_required
def customer_toggle(customer_id: int):
    customer = db.get_customer(customer_id)
    if not customer:
        flash("Customer not found.", "danger")
    else:
        db.set_customer_active(customer_id, 0 if int(customer[3]) else 1)
        flash("Customer status updated.", "success")
    return redirect(url_for("customers"))


@app.route("/customers/<int:customer_id>/history")
@login_required
def customer_history(customer_id: int):
    customer = db.get_customer(customer_id)
    if not customer:
        flash("Customer not found.", "danger")
        return redirect(url_for("customers"))
    history = db.customer_history(customer_id)
    return render_template("customer_history.html", customer=customer, history=history, cents_to_money=cents_to_money)


@app.route("/sales")
@login_required
def sales():
    rows = db.list_sales(300)
    return render_template(
        "sales.html",
        rows=rows,
        cents_to_money=cents_to_money,
        payment_statuses=PAYMENT_STATUSES,
    )


@app.route("/sales/new", methods=["GET", "POST"])
@login_required
def sale_new():
    customers = db.list_customers(include_inactive=False)
    default_tax = db.get_setting("tax_rate_default") or "0.00"
    if request.method == "POST":
        try:
            customer_id = int(request.form.get("customer_id", "0") or 0)
            tax_rate = float(request.form.get("tax_rate", default_tax) or 0)
            order_discount = parse_money(request.form.get("order_discount", ""))
            coupon_code = request.form.get("coupon_code", "").strip() or None
            payment_method = request.form.get("payment_method", "cash")
            payment_status = request.form.get("payment_status", "paid")
            platform = request.form.get("platform", "In-store")
            note = request.form.get("note", "")
            cart_items = parse_cart_lines(request.form.get("cart_lines", ""))
            sale_id, receipt_no, _receipt = db.create_sale(
                customer_id=customer_id,
                cart_items=cart_items,
                tax_rate=tax_rate,
                order_discount_cents=order_discount,
                coupon_code=coupon_code,
                payment_method=payment_method,
                payment_status=payment_status,
                note=note,
                platform=platform,
                user_id=session.get("user_id"),
            )
            flash(f"Sale {receipt_no} created.", "success")
            return redirect(url_for("sale_receipt", sale_id=sale_id))
        except Exception as exc:
            flash(str(exc), "danger")
    return render_template(
        "sale_form.html",
        customers=customers,
        default_tax=default_tax,
        payment_methods=PAYMENT_METHODS,
        payment_statuses=PAYMENT_STATUSES,
        platforms=["In-store"] + PLATFORM_OPTIONS,
    )


@app.route("/sales/<int:sale_id>")
@login_required
def sale_receipt(sale_id: int):
    receipt = db.get_sale_receipt(sale_id)
    if not receipt:
        flash("Sale not found.", "danger")
        return redirect(url_for("sales"))
    items = db.get_sale_items(sale_id)
    return render_template("sale_receipt.html", receipt=receipt, items=items, cents_to_money=cents_to_money)


@app.route("/sales/<int:sale_id>/payment", methods=["POST"])
@login_required
def sale_payment(sale_id: int):
    status = request.form.get("payment_status", "paid")
    try:
        db.update_sale_payment_status(sale_id, status)
        flash("Payment status updated.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("sales"))


@app.route("/sales/<int:sale_id>/void", methods=["POST"])
@login_required
def sale_void(sale_id: int):
    try:
        db.void_sale(sale_id, session.get("user_id"))
        flash("Sale voided.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("sales"))


@app.route("/sales/<int:sale_id>/delete", methods=["POST"])
@admin_required
def sale_delete(sale_id: int):
    try:
        db.delete_sale(sale_id, session.get("user_id"))
        flash("Sale deleted.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("sales"))


@app.route("/sales/<int:sale_id>.txt")
@login_required
def sale_txt(sale_id: int):
    receipt = db.get_sale_receipt(sale_id)
    if not receipt:
        flash("Sale not found.", "danger")
        return redirect(url_for("sales"))
    content = receipt[1]
    return Response(
        content,
        mimetype="text/plain",
        headers={"Content-Disposition": f"attachment; filename=sale_{sale_id}.txt"},
    )


@app.route("/sales/<int:sale_id>.pdf")
@login_required
def sale_pdf(sale_id: int):
    receipt = db.get_sale_receipt(sale_id)
    if not receipt:
        flash("Sale not found.", "danger")
        return redirect(url_for("sales"))
    content = receipt[1]
    tmp_path = f"/tmp/sale_{sale_id}.pdf"
    try:
        export_pdf_text(content, tmp_path, title=f"Sale {sale_id}")
    except Exception as exc:
        flash(str(exc), "danger")
        return redirect(url_for("sale_receipt", sale_id=sale_id))
    return send_file(tmp_path, as_attachment=True, download_name=f"sale_{sale_id}.pdf")


@app.route("/returns")
@login_required
def returns():
    rows = db.list_returns(200)
    return render_template("returns.html", rows=rows, cents_to_money=cents_to_money)


@app.route("/returns/new", methods=["GET", "POST"])
@login_required
def return_new():
    if request.method == "POST":
        try:
            sale_id = int(request.form.get("sale_id", "0") or 0)
            reason = request.form.get("reason", "")
            refund_method = request.form.get("refund_method", "cash")
            items = parse_return_lines(request.form.get("return_lines", ""))
            return_id, _receipt = db.create_return(
                sale_id=sale_id,
                items=items,
                reason=reason,
                refund_method=refund_method,
                user_id=session.get("user_id"),
            )
            flash(f"Return {return_id} created.", "success")
            return redirect(url_for("return_receipt", return_id=return_id))
        except Exception as exc:
            flash(str(exc), "danger")
    return render_template("return_form.html")


@app.route("/returns/<int:return_id>")
@login_required
def return_receipt(return_id: int):
    receipt = db.get_return_receipt(return_id)
    if not receipt:
        flash("Return not found.", "danger")
        return redirect(url_for("returns"))
    return render_template("return_receipt.html", receipt=receipt)


@app.route("/returns/<int:return_id>/delete", methods=["POST"])
@admin_required
def return_delete(return_id: int):
    try:
        db.delete_return(return_id, session.get("user_id"))
        flash("Return deleted.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("returns"))


@app.route("/reports")
@login_required
def reports():
    daily = db.report_daily(30)
    monthly = db.report_monthly()
    top_books = db.report_top_books(10)
    top_platforms = db.report_top_platforms(10)
    summary = db.report_summary(30)
    by_category = db.report_by_category()
    returns_list = db.list_returns(50)
    adjustments = db.list_inventory_adjustments(50)
    return render_template(
        "reports.html",
        daily=daily,
        monthly=monthly,
        top_books=top_books,
        top_platforms=top_platforms,
        summary=summary,
        by_category=by_category,
        returns_list=returns_list,
        adjustments=adjustments,
        cents_to_money=cents_to_money,
    )


@app.route("/reports/sales.csv")
@login_required
def sales_csv():
    output = io.StringIO()
    writer = csv.writer(output)
    headers = [
        "receipt_no",
        "created_at",
        "customer_id",
        "platform",
        "subtotal_cents",
        "discount_cents",
        "coupon_code",
        "tax_rate",
        "tax_cents",
        "total_cents",
        "payment_method",
        "payment_status",
        "note",
        "is_void",
    ]
    writer.writerow(headers)
    q = """
        SELECT receipt_no, created_at, customer_id, platform, subtotal_cents, discount_cents, coupon_code, tax_rate, tax_cents,
               total_cents, payment_method, payment_status, note, is_void
        FROM sales
        ORDER BY id DESC;
    """
    with db._connect() as conn:
        cur = conn.cursor()
        cur.execute(q)
        for row in cur.fetchall():
            writer.writerow(row)
    output.seek(0)
    return Response(
        output.getvalue(),
        mimetype="text/csv",
        headers={"Content-Disposition": "attachment; filename=sales.csv"},
    )


@app.route("/reports/tax.csv")
@login_required
def tax_csv():
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(["day", "tax_cents", "total_cents"])
    with db._connect() as conn:
        refund_tax_col = "refund_tax_cents" if "refund_tax_cents" in db._columns(conn, "returns") else "refund_cents"
        q = f"""
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
        cur = conn.cursor()
        cur.execute(q)
        for row in cur.fetchall():
            writer.writerow(row)
    output.seek(0)
    return Response(
        output.getvalue(),
        mimetype="text/csv",
        headers={"Content-Disposition": "attachment; filename=tax.csv"},
    )


@app.route("/platform-sales", methods=["GET", "POST"])
@login_required
def platform_sales():
    if request.method == "POST":
        try:
            book_id = int(request.form.get("book_id", "0") or 0)
            platform = request.form.get("platform", "Other")
            listed_price = parse_money(request.form.get("listed_price", ""))
            final_price = parse_money(request.form.get("final_price", ""))
            amount_paid = parse_money(request.form.get("amount_paid", ""))
            status = request.form.get("status", "pending")
            note = request.form.get("note", "")
            db.add_platform_sale(
                book_id=book_id,
                platform=platform,
                listed_price_cents=listed_price,
                final_price_cents=final_price,
                amount_paid_cents=amount_paid,
                status=status,
                note=note,
            )
            flash("Platform sale logged.", "success")
        except Exception as exc:
            flash(str(exc), "danger")
    search = request.args.get("search", "")
    status_filter = request.args.getlist("status")
    rows = db.list_platform_sales(statuses=status_filter or None, search=search)
    return render_template(
        "platform_sales.html",
        rows=rows,
        search=search,
        statuses=PLATFORM_SALE_STATUSES,
        status_filter=status_filter,
        platforms=PLATFORM_OPTIONS,
        cents_to_money=cents_to_money,
    )


@app.route("/platform-sales/<int:sale_id>/update", methods=["POST"])
@login_required
def platform_sale_update(sale_id: int):
    try:
        final_price = parse_money(request.form.get("final_price", ""))
        status = request.form.get("status", "pending")
        note = request.form.get("note", "")
        db.update_platform_sale(sale_id, final_price, status, note)
        flash("Platform sale updated.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("platform_sales"))


@app.route("/platform-sales/<int:sale_id>/payment", methods=["POST"])
@login_required
def platform_sale_payment(sale_id: int):
    try:
        final_price = parse_money(request.form.get("final_price", ""))
        amount_paid = parse_money(request.form.get("amount_paid", ""))
        db.update_platform_payment(sale_id, final_price, amount_paid, request.form.get("note", ""))
        flash("Platform payment updated.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("platform_sales"))


@app.route("/platform-sales/<int:sale_id>/finalize", methods=["POST"])
@login_required
def platform_sale_finalize(sale_id: int):
    try:
        sale_id, receipt_no, _receipt = db.finalize_platform_sale(sale_id)
        flash(f"Platform sale finalized into receipt {receipt_no}.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("platform_sales"))


@app.route("/platform-sales/<int:sale_id>/delete", methods=["POST"])
@admin_required
def platform_sale_delete(sale_id: int):
    try:
        db.delete_platform_sale(sale_id)
        flash("Platform sale deleted.", "success")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("platform_sales"))


@app.route("/availability/<status>")
@login_required
def availability(status: str):
    label = AVAILABILITY_LABELS.get(status, status)
    books = db.list_books(availability_status=status, include_inactive=True)
    rows = [
        {
            "id": b[0],
            "title": b[3],
            "author": b[4],
            "stock": b[14],
            "availability": AVAILABILITY_LABELS.get(b[19], b[19]),
            "category": b[20] or "(Uncategorized)",
        }
        for b in books
    ]
    return render_template("availability.html", rows=rows, label=label)


@app.route("/admin", methods=["GET", "POST"])
@admin_required
def admin():
    if request.method == "POST":
        action = request.form.get("action")
        try:
            if action == "settings":
                db.set_setting("store_name", request.form.get("store_name", "").strip())
                db.set_setting("store_address", request.form.get("store_address", "").strip())
                db.set_setting("store_phone", request.form.get("store_phone", "").strip())
                db.set_setting("receipt_footer", request.form.get("receipt_footer", "").strip())
                db.set_setting("receipt_prefix", request.form.get("receipt_prefix", "").strip() or "R")
                db.set_setting("tax_rate_default", request.form.get("tax_rate_default", "").strip() or "0.00")
                flash("Settings saved.", "success")
            elif action == "category_add":
                db.add_category(request.form.get("name", "").strip())
                flash("Category added.", "success")
            elif action == "category_toggle":
                db.set_category_active(int(request.form.get("category_id", "0")), int(request.form.get("active", "1")))
                flash("Category updated.", "success")
            elif action == "coupon_add":
                db.add_coupon(
                    request.form.get("code", "").strip(),
                    request.form.get("kind", "percent"),
                    float(request.form.get("value", "0") or 0),
                    int(request.form.get("is_active", "1")),
                    request.form.get("expires_on", "") or None,
                )
                flash("Coupon added.", "success")
            elif action == "coupon_edit":
                db.update_coupon(
                    int(request.form.get("coupon_id", "0")),
                    request.form.get("code", "").strip(),
                    request.form.get("kind", "percent"),
                    float(request.form.get("value", "0") or 0),
                    int(request.form.get("is_active", "1")),
                    request.form.get("expires_on", "") or None,
                )
                flash("Coupon updated.", "success")
            elif action == "user_add":
                db.add_user(
                    request.form.get("username", "").strip(),
                    request.form.get("password", ""),
                    request.form.get("role", "clerk"),
                )
                flash("User added.", "success")
            elif action == "user_toggle":
                db.set_user_active(int(request.form.get("user_id", "0")), int(request.form.get("active", "1")))
                flash("User updated.", "success")
            elif action == "user_reset":
                db.reset_password(int(request.form.get("user_id", "0")), request.form.get("password", ""))
                flash("Password reset.", "success")
            else:
                flash("Unknown admin action.", "danger")
        except Exception as exc:
            flash(str(exc), "danger")
        return redirect(url_for("admin"))

    settings = {
        "store_name": db.get_setting("store_name"),
        "store_address": db.get_setting("store_address"),
        "store_phone": db.get_setting("store_phone"),
        "receipt_footer": db.get_setting("receipt_footer"),
        "receipt_prefix": db.get_setting("receipt_prefix"),
        "tax_rate_default": db.get_setting("tax_rate_default"),
    }
    categories = db.list_categories(include_inactive=True)
    coupons = db.list_coupons()
    users = db.list_users()
    return render_template(
        "admin.html",
        settings=settings,
        categories=categories,
        coupons=coupons,
        users=users,
    )


@app.route("/admin/backup")
@admin_required
def admin_backup():
    return send_file(DB_PATH, as_attachment=True, download_name="inventory_backup.db")


@app.route("/admin/restore", methods=["POST"])
@admin_required
def admin_restore():
    file = request.files.get("file")
    if not file or not file.filename:
        flash("Select a DB file to restore.", "danger")
        return redirect(url_for("admin"))
    try:
        temp_path = "/tmp/inventory_restore.db"
        file.save(temp_path)
        shutil.copy2(temp_path, DB_PATH)
        flash("Database restored. Restart the app.", "warning")
    except Exception as exc:
        flash(str(exc), "danger")
    return redirect(url_for("admin"))


@app.route("/adjustments")
@login_required
def adjustments():
    rows = db.list_inventory_adjustments(200)
    return render_template("adjustments.html", rows=rows)


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=True)
