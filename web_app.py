import csv
import io
import os
import secrets
from functools import wraps

from flask import Flask, render_template, redirect, request, session, url_for, flash, Response

from app import DB, cents_to_money, CONDITION_OPTIONS, AVAILABILITY_LABELS, AVAILABILITY_STATUSES


app = Flask(__name__)
app.secret_key = os.environ.get("FLASK_SECRET_KEY", secrets.token_hex(16))
db = DB()


def login_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not session.get("user_id"):
            return redirect(url_for("login"))
        return view(*args, **kwargs)
    return wrapped


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
        include_inactive=False,
        category_id=category_id_int,
        condition=None if condition == "All" else condition,
        availability_status=None if availability == "All" else availability,
    )
    availability_options = [("All", "All")] + [(value, label) for label, value in AVAILABILITY_STATUSES.items()]
    rows = [
        {
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


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=True)
