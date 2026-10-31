# -*- coding: utf-8 -*-
"""
Akıl ve Zeka Oyunları Yönetim ve Takip Paneli
=============================================
Çalıştırma:
    pip install streamlit pandas openpyxl
    streamlit run app.py

- Veriler aynı klasördeki `akil_oyunlari.db` (SQLite) dosyasında saklanır (veritabanı şeması değişmedi).
- Varsayılan yönetici PIN'i: 6991 (Yönetici Paneli > PIN Değiştir'den değiştirilebilir).
- Gereken Streamlit sürümü: 1.30 veya üzeri. Excel (.xlsx) dışa aktarma için openpyxl gerekir.
- Tasarım: "Warm Minimalist" (krem zemin, koyu kahve sidebar, taba vurgu) korunmuştur.

Yeni eklenenler:
- Karşılama ekranı (landing): "Demoyu İncele", "Bekleme Listesine Katıl" ve "Mevcut kullanıcı girişi" akışları.
- Demo modu: oturuma özel, geçici bir SQLite dosyasında kurgusal verilerle çalışır; gerçek veritabanına dokunmaz.
- Bekleme listesi: gerçek veritabanındaki `waitlist` tablosuna kaydedilir (Yönetici Paneli > Bekleme Listesi).
- KVKK Aydınlatma Metni (footer) ve yönetici "PIN'imi unuttum" akışı (kurtarma anahtarı / sunucu doğrulama kodu).

Yetki modeli (Güçlendirilmiş Salt Okunur):
------------------------------------------
- Yönetici girişi YOKKEN yalnızca görüntüleme, listeleri inceleme, şube/karne/sıralama bakma yapılabilir.
- Maç girişi, bireysel ilerleme kaydetme, grup oluşturma, skor girişi, silme, düzenleme ve Excel yükleme
  işlemleri YALNIZCA yönetici modunda çalışır. Giriş yapılmadıysa bu alanlar kilitli veya salt okunur görünür.
"""

import hashlib
import hmac
import html
import io
import math
import os
import random
import re
import secrets
import shutil
import sqlite3
import tempfile
import time
from contextlib import contextmanager
from datetime import date, datetime, timedelta

import pandas as pd
import streamlit as st

# ----------------------------------------------------------------------------
# SABİTLER
# ----------------------------------------------------------------------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "akil_oyunlari.db")
DEFAULT_PIN = "6991"
PAIR_CATEGORY = "İkili Oyunlar"
INDIV_CATEGORY = "Bireysel Oyunlar"
GROUP_CATEGORY = "Toplu Oyunlar"

GAME_LIBRARY = {
    "İkili Oyunlar": ["Mangala", "Goon", "9 Taş", "Küre", "Pentego", "Abluka", "Surakarta", "Renk Kat"],
    "Bireysel Oyunlar": ["Şakuli", "Motif", "Equilibrio", "9/24"],
    "Toplu Oyunlar": ["The Road Game", "Renkli Bardaklar", "Baybak", "Dik Go"],
}
CATEGORY_ICONS = {"İkili Oyunlar": "⚔️", "Bireysel Oyunlar": "🧩", "Toplu Oyunlar": "👥"}

THEME_TOML = """[theme]
base = "light"
primaryColor = "#A9794F"
backgroundColor = "#F8F5F0"
secondaryBackgroundColor = "#F1EADF"
textColor = "#3A2E27"
font = "sans serif"
"""

OLD_THEME_TOML = """[theme]
base = "light"
primaryColor = "#B07D4F"
backgroundColor = "#FBF7F0"
secondaryBackgroundColor = "#F3EADC"
textColor = "#3B2A20"
font = "sans serif"
"""

PG_HOME = "Genel Bakış"
PG_BRANCH = "Şube Paneli"
PG_MATCH = "Maç Girişi"
PG_BOARD = "Sıralama ve Geçmiş"
PG_INDIV = "Bireysel Oyunlar"
PG_GROUP = "Grup ve Turnuva"
PG_LIB = "Oyun Kütüphanesi"
PG_ADMIN = "Yönetici Paneli"

PAGE_ICONS = {
    PG_HOME: "home", PG_BRANCH: "school", PG_MATCH: "swords", PG_BOARD: "trophy",
    PG_INDIV: "puzzle", PG_GROUP: "users", PG_LIB: "dice", PG_ADMIN: "lock",
}

esc = html.escape

XLSX_MIME = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
NO_AUTH_MSG = "Bu işlem için yönetici girişi gerekir."
MAX_PIN_FAILS = 5      
LOCK_SECONDS = 300     
PAGE_SIZE = 20         

# NOT: Orijinal dosyada karne/ilerleme tablolarında kullanılıyordu ancak tanımsızdı (NameError); eklendi.
PROG_KAYNAK = {"manuel": "Manuel giriş", "gecis": "Geçen yıldan aktarım"}

# Demo / bekleme listesi / PIN kurtarma sabitleri
DEMO_DIR = os.path.join(tempfile.gettempdir(), "akil_oyunlari_demo")
DEMO_MAX_AGE = 24 * 3600
WAITLIST_SESSION_LIMIT = 3
EMAIL_RE = re.compile(r"^[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}$")
RESET_CODE_FILE = os.path.join(BASE_DIR, "pin_sifirlama_kodu.txt")
RESET_CODE_TTL = 15 * 60
RESET_CODE_COOLDOWN = 60
RESET_MAX_FAILS = 5
RESET_LOCK_SECONDS = 600

# KVKK metnindeki kurum bilgileri: yayına almadan önce kendi bilgilerinizle değiştirin.
KVKK_CONTROLLER = "Akıl ve Zeka Oyunları Yönetim ve Takip Paneli işletmecisi"
KVKK_CONTACT = "kvkk@ornek-kurum.com"
KVKK_RETENTION = "24 ay"


# ----------------------------------------------------------------------------
# YARDIMCI FONKSİYONLAR
# ----------------------------------------------------------------------------
def ensure_theme_config():
    try:
        cfg_dir = os.path.join(BASE_DIR, ".streamlit")
        cfg = os.path.join(cfg_dir, "config.toml")
        if not os.path.exists(cfg):
            os.makedirs(cfg_dir, exist_ok=True)
            with open(cfg, "w", encoding="utf-8") as f:
                f.write(THEME_TOML)
        else:
            with open(cfg, "r", encoding="utf-8") as f:
                current = f.read()
            if current.strip() == OLD_THEME_TOML.strip():
                with open(cfg, "w", encoding="utf-8") as f:
                    f.write(THEME_TOML)
    except OSError:
        pass


def tr_upper(s):
    return str(s).replace("i", "İ").replace("ı", "I").upper()


_TR_ALPHA = "ABCÇDEFGHIİJKLMNOÖPRSŞTUÜVYZ"


def tr_key(s):
    return tuple(_TR_ALPHA.find(c) if c in _TR_ALPHA else 100 + ord(c) for c in tr_upper(s))


def _nz(v):
    if v is None:
        return None
    try:
        if pd.isna(v):
            return None
    except (TypeError, ValueError):
        pass
    if isinstance(v, str):
        v = v.strip()
        return v or None
    return v


def _to_int(v):
    v = _nz(v)
    if v is None:
        return None
    try:
        return int(float(v))
    except (TypeError, ValueError):
        return None


def prev_school_year():
    t = date.today()
    start = t.year if t.month >= 9 else t.year - 1
    return f"{start - 1}-{start}"


def _norm(s):
    s = str(s).strip()
    for a, b in (("İ", "i"), ("I", "i"), ("ı", "i")):
        s = s.replace(a, b)
    s = s.lower()
    for a, b in zip("şğüöç", "sguoc"):
        s = s.replace(a, b)
    return re.sub(r"[^a-z0-9]", "", s)


# ----------------------------------------------------------------------------
# VERİTABANI
# ----------------------------------------------------------------------------
def _demo_token():
    tok = st.session_state.get("demo_token")
    if not tok:
        tok = secrets.token_hex(8)
        st.session_state["demo_token"] = tok
    return tok


def _demo_path():
    try:
        os.makedirs(DEMO_DIR, exist_ok=True)
    except OSError:
        pass
    return os.path.join(DEMO_DIR, f"demo_{_demo_token()}.db")


def active_db_path():
    return _demo_path() if st.session_state.get("mode") == "demo" else DB_PATH


@contextmanager
def db(path=None):
    conn = sqlite3.connect(path or active_db_path())
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def _backup_before_migration():
    if active_db_path() != DB_PATH or not os.path.exists(DB_PATH):
        return
    try:
        conn = sqlite3.connect(DB_PATH)
        try:
            cols = [r[1] for r in conn.execute("PRAGMA table_info(students)")]
        finally:
            conn.close()
        if cols and "arsiv" not in cols:
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            shutil.copy2(DB_PATH, os.path.join(BASE_DIR, f"akil_oyunlari_yedek_{stamp}.db"))
    except (OSError, sqlite3.Error):
        pass


def _migrate(c):
    cols = {r["name"] for r in c.execute("PRAGMA table_info(students)")}
    if "arsiv" not in cols:
        c.execute("ALTER TABLE students ADD COLUMN arsiv INTEGER NOT NULL DEFAULT 0")
    if "arsiv_tarih" not in cols:
        c.execute("ALTER TABLE students ADD COLUMN arsiv_tarih TEXT")
    if "arsiv_notu" not in cols:
        c.execute("ALTER TABLE students ADD COLUMN arsiv_notu TEXT")
    c.execute("CREATE INDEX IF NOT EXISTS idx_students_arsiv ON students(arsiv)")


def init_db():
    _backup_before_migration()
    with db() as c:
        c.executescript(
            """
            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY, value TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS students (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ogrenci_no TEXT UNIQUE,
                ad_soyad TEXT NOT NULL,
                sinif INTEGER NOT NULL,
                sube TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS games (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ad TEXT NOT NULL UNIQUE,
                kategori TEXT NOT NULL,
                varsayilan INTEGER NOT NULL DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS matches (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                tarih TEXT NOT NULL,
                game_id INTEGER NOT NULL REFERENCES games(id) ON DELETE CASCADE,
                p1_id INTEGER NOT NULL REFERENCES students(id) ON DELETE CASCADE,
                p2_id INTEGER NOT NULL REFERENCES students(id) ON DELETE CASCADE,
                sonuc TEXT NOT NULL CHECK (sonuc IN ('1','2','D')),
                CHECK (p1_id <> p2_id)
            );
            CREATE INDEX IF NOT EXISTS idx_matches_game ON matches(game_id);
            CREATE INDEX IF NOT EXISTS idx_students_sb ON students(sinif, sube);

            CREATE TABLE IF NOT EXISTS progress (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                student_id INTEGER NOT NULL REFERENCES students(id) ON DELETE CASCADE,
                game_id INTEGER NOT NULL REFERENCES games(id) ON DELETE CASCADE,
                kart INTEGER,
                seviye TEXT,
                tarih TEXT NOT NULL,
                kaynak TEXT NOT NULL DEFAULT 'manuel',
                donem TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_progress_sg ON progress(student_id, game_id);

            CREATE TABLE IF NOT EXISTS game_groups (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ad TEXT NOT NULL,
                game_id INTEGER NOT NULL REFERENCES games(id) ON DELETE CASCADE,
                turnuva TEXT NOT NULL DEFAULT '',
                tarih TEXT NOT NULL,
                UNIQUE (game_id, turnuva, ad)
            );
            CREATE TABLE IF NOT EXISTS group_members (
                group_id INTEGER NOT NULL REFERENCES game_groups(id) ON DELETE CASCADE,
                student_id INTEGER NOT NULL REFERENCES students(id) ON DELETE CASCADE,
                PRIMARY KEY (group_id, student_id)
            );
            CREATE TABLE IF NOT EXISTS group_scores (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                group_id INTEGER NOT NULL REFERENCES game_groups(id) ON DELETE CASCADE,
                student_id INTEGER NOT NULL REFERENCES students(id) ON DELETE CASCADE,
                tarih TEXT NOT NULL,
                tur TEXT NOT NULL DEFAULT '',
                kart INTEGER NOT NULL DEFAULT 0,
                puan INTEGER NOT NULL DEFAULT 0
            );
            CREATE INDEX IF NOT EXISTS idx_gscores_group ON group_scores(group_id);
            CREATE INDEX IF NOT EXISTS idx_gscores_student ON group_scores(student_id);

            CREATE TABLE IF NOT EXISTS waitlist (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ad_soyad TEXT NOT NULL,
                eposta TEXT NOT NULL UNIQUE,
                kurum TEXT NOT NULL,
                kvkk_onay INTEGER NOT NULL DEFAULT 0,
                kayit_tarihi TEXT NOT NULL
            );
            """
        )
        _migrate(c)
        for kategori, oyunlar in GAME_LIBRARY.items():
            for ad in oyunlar:
                c.execute(
                    "INSERT OR IGNORE INTO games (ad, kategori, varsayilan) VALUES (?,?,1)",
                    (ad, kategori),
                )
    if _get_setting("admin_pin") is None:
        _store_pin(DEFAULT_PIN)


def _get_setting(key):
    with db() as c:
        row = c.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
    return row["value"] if row else None


def _set_setting(key, value):
    with db() as c:
        c.execute(
            "INSERT INTO settings (key, value) VALUES (?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, value),
        )


def is_admin():
    return bool(st.session_state.get("admin"))


def require_admin():
    if not is_admin():
        raise PermissionError(NO_AUTH_MSG)


def admin_logout():
    st.session_state["admin"] = False
    st.session_state.pop("del_pending", None)


def _hash_pin(pin, salt_hex):
    return hashlib.pbkdf2_hmac("sha256", pin.encode("utf-8"), bytes.fromhex(salt_hex), 120_000).hex()


def _store_pin(pin):
    salt = secrets.token_hex(16)
    _set_setting("admin_pin", f"{salt}${_hash_pin(pin, salt)}")


def set_pin(pin):
    require_admin()
    _store_pin(pin)


def verify_pin(pin):
    stored = _get_setting("admin_pin")
    if not stored or "$" not in stored:
        return False
    salt, h = stored.split("$", 1)
    return hmac.compare_digest(_hash_pin(pin, salt), h)


def _int_setting(key):
    try:
        return int(float(_get_setting(key) or 0))
    except (TypeError, ValueError):
        return 0


def lock_remaining():
    return max(0, _int_setting("pin_lock_until") - int(time.time()))


def register_pin_failure():
    n = _int_setting("pin_fail_count") + 1
    if n >= MAX_PIN_FAILS:
        _set_setting("pin_lock_until", str(int(time.time()) + LOCK_SECONDS))
        n = 0
    _set_setting("pin_fail_count", str(n))
    return n


def reset_pin_failures():
    _set_setting("pin_fail_count", "0")
    _set_setting("pin_lock_until", "0")


def _sort_students(df):
    if df.empty:
        return df
    order = sorted(range(len(df)), key=lambda i: (int(df.sinif.iloc[i]), df.sube.iloc[i], tr_key(df.ad_soyad.iloc[i])))
    return df.iloc[order].reset_index(drop=True)


def load_students(durum="aktif"):
    where = {"aktif": "WHERE arsiv=0", "arsiv": "WHERE arsiv=1"}.get(durum, "")
    with db() as c:
        df = pd.read_sql_query(
            "SELECT id, ogrenci_no, ad_soyad, sinif, sube, arsiv, arsiv_tarih, arsiv_notu "
            f"FROM students {where}", c
        )
    return _sort_students(df)


def _dup_no_message(no):
    with db() as c:
        row = c.execute("SELECT arsiv FROM students WHERE ogrenci_no=?", (no,)).fetchone()
    if row and row["arsiv"]:
        return "Bu numara arşivdeki bir öğrenciye ait. Yönetici Paneli > Arşiv bölümünden geri alabilirsiniz."
    return None


def add_student(ogrenci_no, ad_soyad, sinif, sube):
    require_admin()
    ad_soyad = re.sub(r"\s+", " ", ad_soyad).strip()
    sube = sube.strip().upper()
    if not ad_soyad or not sube:
        return False, "Ad Soyad ve Şube boş bırakılamaz."
    try:
        with db() as c:
            cur = c.execute(
                "INSERT INTO students (ogrenci_no, ad_soyad, sinif, sube) VALUES (?,?,?,?)",
                (ogrenci_no.strip() or None, ad_soyad, int(sinif), sube),
            )
            if not ogrenci_no.strip():
                c.execute("UPDATE students SET ogrenci_no=? WHERE id=?", (f"OG{cur.lastrowid:04d}", cur.lastrowid))
        return True, f"{ad_soyad} eklendi."
    except sqlite3.IntegrityError:
        return False, _dup_no_message(ogrenci_no.strip()) or "Bu öğrenci numarası zaten kayıtlı."


def update_student(sid, ogrenci_no, ad_soyad, sinif, sube):
    require_admin()
    ad_soyad = re.sub(r"\s+", " ", ad_soyad).strip()
    sube = sube.strip().upper()
    if not ad_soyad or not sube or not ogrenci_no.strip():
        return False, "Tüm alanlar doldurulmalıdır."
    try:
        with db() as c:
            c.execute(
                "UPDATE students SET ogrenci_no=?, ad_soyad=?, sinif=?, sube=? WHERE id=?",
                (ogrenci_no.strip(), ad_soyad, int(sinif), sube, int(sid)),
            )
        return True, "Öğrenci bilgileri güncellendi."
    except sqlite3.IntegrityError:
        return False, _dup_no_message(ogrenci_no.strip()) or "Bu öğrenci numarası başka bir öğrenciye ait."


def delete_student(sid):
    require_admin()
    with db() as c:
        c.execute("DELETE FROM students WHERE id=?", (int(sid),))


_ALIAS_ID = {"ogrenciid", "ogrencino", "ogrno", "okulno", "no", "id", "numara", "ogrencinumarasi"}
_ALIAS_NAME = {"adsoyad", "adisoyadi", "adsoyadi", "adisoyad", "isim", "ogrenci", "ogrenciadi", "adivesoyadi",
               "ogrenciadisoyadi", "ogrenciadsoyad", "ogrenciadsoyadi"}
_ALIAS_SINIF = {"sinif", "sinifi", "sinifduzeyi", "seviye"}
_ALIAS_SUBE = {"sube", "subesi"}


def _read_uploaded_table(uploaded):
    name = uploaded.name.lower()
    data = uploaded.getvalue()
    raw = None
    try:
        if name.endswith(".csv"):
            for enc in ("utf-8-sig", "cp1254", "latin-1"):
                try:
                    raw = pd.read_csv(io.BytesIO(data), sep=None, engine="python", encoding=enc, dtype=str)
                    break
                except (UnicodeDecodeError, pd.errors.ParserError):
                    continue
        else:
            raw = pd.read_excel(io.BytesIO(data), dtype=str)
    except Exception as e:
        raise ValueError(f"Dosya okunamadı: {e}")
    if raw is None or raw.empty:
        raise ValueError("Dosya boş veya okunamadı.")
    return raw


def parse_student_file(uploaded):
    raw = _read_uploaded_table(uploaded)
    cols = {}
    for col in raw.columns:
        n = _norm(col)
        for key, alias in (("id", _ALIAS_ID), ("name", _ALIAS_NAME), ("sinif", _ALIAS_SINIF), ("sube", _ALIAS_SUBE)):
            if n in alias and key not in cols:
                cols[key] = col
    missing = [lbl for k, lbl in (("name", "Ad_Soyad"), ("sinif", "Sınıf"), ("sube", "Şube")) if k not in cols]
    if missing:
        raise ValueError(
            "Gerekli sütun(lar) bulunamadı: " + ", ".join(missing)
            + f". Dosyadaki sütunlar: {', '.join(map(str, raw.columns))}"
        )

    out = pd.DataFrame()
    out["ad_soyad"] = raw[cols["name"]].fillna("").astype(str).str.replace(r"\s+", " ", regex=True).str.strip()
    out["sinif"] = pd.to_numeric(raw[cols["sinif"]].astype(str).str.extract(r"(\d+)")[0], errors="coerce")
    out["sube"] = raw[cols["sube"]].fillna("").astype(str).str.strip().map(tr_upper)
    if "id" in cols:
        out["ogrenci_no"] = raw[cols["id"]].fillna("").astype(str).str.strip().replace("nan", "")
    else:
        out["ogrenci_no"] = ""

    notes = []
    total = len(out)
    valid = (out.ad_soyad != "") & out.sinif.notna() & (out.sube != "")
    if (~valid).sum():
        notes.append(f"{int((~valid).sum())} satır eksik bilgi nedeniyle atlandı.")
    out = out[valid].copy()
    out["sinif"] = out.sinif.astype(int)
    out = out[["ogrenci_no", "ad_soyad", "sinif", "sube"]]

    before = len(out)
    has_id = out.ogrenci_no != ""
    dup_id = out[has_id].duplicated("ogrenci_no", keep="first")
    out = out.drop(index=dup_id[dup_id].index)
    out = out.drop_duplicates(subset=["ad_soyad", "sinif", "sube"], keep="first")
    if before - len(out):
        notes.append(f"{before - len(out)} tekrar eden satır birleştirildi.")
    if "id" not in cols:
        notes.append("Dosyada öğrenci numarası sütunu yok; numaralar otomatik üretilecek (OG0001, OG0002...).")
    if total and out.empty:
        raise ValueError("Geçerli öğrenci satırı bulunamadı.")
    return out.reset_index(drop=True), notes


def import_students(df, replace=False):
    require_admin()
    added = updated = skipped = arch = 0
    with db() as c:
        if replace:
            c.execute("DELETE FROM students")
        for r in df.itertuples(index=False):
            no = (r.ogrenci_no or "").strip()
            if no:
                row = c.execute("SELECT id, arsiv FROM students WHERE ogrenci_no=?", (no,)).fetchone()
                if row:
                    arch += int(row["arsiv"] or 0)
                    c.execute(
                        "UPDATE students SET ad_soyad=?, sinif=?, sube=? WHERE id=?",
                        (r.ad_soyad, int(r.sinif), r.sube, row["id"]),
                    )
                    updated += 1
                    continue
                c.execute(
                    "INSERT INTO students (ogrenci_no, ad_soyad, sinif, sube) VALUES (?,?,?,?)",
                    (no, r.ad_soyad, int(r.sinif), r.sube),
                )
                added += 1
            else:
                row = c.execute(
                    "SELECT id, arsiv FROM students WHERE ad_soyad=? AND sinif=? AND sube=?",
                    (r.ad_soyad, int(r.sinif), r.sube),
                ).fetchone()
                if row:
                    arch += int(row["arsiv"] or 0)
                    skipped += 1
                    continue
                cur = c.execute(
                    "INSERT INTO students (ad_soyad, sinif, sube) VALUES (?,?,?)",
                    (r.ad_soyad, int(r.sinif), r.sube),
                )
                c.execute("UPDATE students SET ogrenci_no=? WHERE id=?", (f"OG{cur.lastrowid:04d}", cur.lastrowid))
                added += 1
    return added, updated, skipped, arch


def load_games():
    with db() as c:
        return pd.read_sql_query("SELECT id, ad, kategori, varsayilan FROM games ORDER BY kategori, id", c)


def add_game(ad, kategori):
    require_admin()
    ad = ad.strip()
    if not ad:
        return False, "Oyun adı boş olamaz."
    try:
        with db() as c:
            c.execute("INSERT INTO games (ad, kategori, varsayilan) VALUES (?,?,0)", (ad, kategori))
        return True, f"'{ad}' kütüphaneye eklendi."
    except sqlite3.IntegrityError:
        return False, "Bu isimde bir oyun zaten var."


def delete_game(gid):
    require_admin()
    with db() as c:
        c.execute("DELETE FROM games WHERE id=? AND varsayilan=0", (int(gid),))


def add_match(game_id, p1, p2, sonuc, tarih=None):
    require_admin()
    if game_id is None:
        return False, "Lütfen bir oyun seçin."
    if p1 is None or p2 is None:
        return False, "Lütfen iki öğrenciyi de seçin."
    if int(p1) == int(p2):
        return False, "Bir öğrenci kendisiyle eşleştirilemez."
    if sonuc not in ("1", "2", "D"):
        return False, "Geçersiz sonuç."
    if tarih is None:
        tarih = date.today()
    if isinstance(tarih, datetime):
        tarih = tarih.date()
    if not isinstance(tarih, date):
        return False, "Lütfen geçerli bir maç tarihi seçin."
    if tarih > date.today():
        return False, "Maç tarihi bugünden sonra olamaz."
    with db() as c:
        c.execute(
            "INSERT INTO matches (tarih, game_id, p1_id, p2_id, sonuc) VALUES (?,?,?,?,?)",
            (tarih.strftime("%Y-%m-%d"), int(game_id), int(p1), int(p2), sonuc),
        )
    return True, "Maç kaydedildi."


def fmt_tarih(v):
    try:
        return datetime.strptime(str(v)[:10], "%Y-%m-%d").strftime("%d.%m.%Y")
    except (ValueError, TypeError):
        return str(v) if v else "—"


def delete_match(mid):
    require_admin()
    with db() as c:
        cur = c.execute("DELETE FROM matches WHERE id=?", (int(mid),))
        return cur.rowcount > 0


def delete_all_matches():
    require_admin()
    with db() as c:
        c.execute("DELETE FROM matches")


def load_matches(game_id=None, active_only=False):
    sql = "SELECT id, tarih, game_id, p1_id, p2_id, sonuc FROM matches"
    conds, params = [], []
    if game_id is not None:
        conds.append("game_id=?")
        params.append(int(game_id))
    if active_only:
        conds.append("(p1_id IN (SELECT id FROM students WHERE arsiv=0) OR p2_id IN (SELECT id FROM students WHERE arsiv=0))")
    if conds:
        sql += " WHERE " + " AND ".join(conds)
    with db() as c:
        return pd.read_sql_query(sql + " ORDER BY id DESC", c, params=params)


def match_history(game_id=None, newest_first=True, include_archived=False):
    sql = (
        "SELECT m.id AS id, m.tarih AS tarih, g.ad AS oyun, "
        "s1.ad_soyad || CASE WHEN s1.arsiv=1 THEN ' (arşiv)' ELSE '' END AS oyuncu1, "
        "(s1.sinif || '-' || s1.sube) AS sube1, "
        "s2.ad_soyad || CASE WHEN s2.arsiv=1 THEN ' (arşiv)' ELSE '' END AS oyuncu2, "
        "(s2.sinif || '-' || s2.sube) AS sube2, m.sonuc AS sonuc "
        "FROM matches m JOIN games g ON g.id=m.game_id "
        "JOIN students s1 ON s1.id=m.p1_id JOIN students s2 ON s2.id=m.p2_id"
    )
    conds, params = [], []
    if game_id is not None:
        conds.append("m.game_id=?")
        params.append(int(game_id))
    if not include_archived:
        conds.append("(s1.arsiv=0 OR s2.arsiv=0)")
    if conds:
        sql += " WHERE " + " AND ".join(conds)
    direction = "DESC" if newest_first else "ASC"
    with db() as c:
        return pd.read_sql_query(
            sql + f" ORDER BY substr(m.tarih, 1, 10) {direction}, m.id {direction}", c, params=params
        )


def played_pairs(game_id):
    m = load_matches(game_id)
    return {frozenset((int(a), int(b))) for a, b in zip(m.p1_id, m.p2_id)}


def archive_students(ids, note=""):
    require_admin()
    ids = sorted({int(i) for i in ids})
    if not ids:
        return 0
    stamp = date.today().strftime("%Y-%m-%d")
    note = (note or "").strip() or None
    with db() as c:
        cur = c.executemany(
            "UPDATE students SET arsiv=1, arsiv_tarih=?, arsiv_notu=? WHERE id=? AND arsiv=0",
            [(stamp, note, i) for i in ids],
        )
        return cur.rowcount


def restore_students(ids):
    require_admin()
    ids = sorted({int(i) for i in ids})
    if not ids:
        return 0
    with db() as c:
        cur = c.executemany(
            "UPDATE students SET arsiv=0, arsiv_tarih=NULL, arsiv_notu=NULL WHERE id=? AND arsiv=1",
            [(i,) for i in ids],
        )
        return cur.rowcount


def count_archived():
    with db() as c:
        return int(c.execute("SELECT COUNT(*) FROM students WHERE arsiv=1").fetchone()[0])


def archived_data_summary():
    with db() as c:
        return pd.read_sql_query(
            "SELECT s.id AS id, "
            "(SELECT COUNT(*) FROM matches m WHERE m.p1_id=s.id OR m.p2_id=s.id) AS mac, "
            "(SELECT COUNT(*) FROM progress p WHERE p.student_id=s.id) AS ilerleme, "
            "(SELECT COUNT(*) FROM group_scores g WHERE g.student_id=s.id) AS grup_skoru "
            "FROM students s WHERE s.arsiv=1", c,
        )


def save_progress(student_id, game_id, kart, seviye, tarih=None, kaynak="manuel", donem=None):
    require_admin()
    kart, seviye = _to_int(kart), _nz(seviye)
    if kart is not None and kart < 0:
        return False, "Kart sayısı negatif olamaz."
    if tarih is None:
        tarih = date.today()
    if isinstance(tarih, datetime):
        tarih = tarih.date()
    if not isinstance(tarih, date):
        return False, "Geçerli bir tarih seçin."
    if tarih > date.today():
        return False, "Tarih bugünden sonra olamaz."
    with db() as c:
        c.execute(
            "INSERT INTO progress (student_id, game_id, kart, seviye, tarih, kaynak, donem) VALUES (?,?,?,?,?,?,?)",
            (int(student_id), int(game_id), kart, str(seviye) if seviye is not None else None,
             tarih.strftime("%Y-%m-%d"), kaynak, donem),
        )
    return True, "Kaydedildi."


def load_progress(game_id=None, student_id=None):
    sql = (
        "SELECT p.id AS id, p.student_id AS student_id, p.game_id AS game_id, g.ad AS oyun, g.kategori AS kategori, "
        "p.kart AS kart, p.seviye AS seviye, p.tarih AS tarih, p.kaynak AS kaynak, p.donem AS donem "
        "FROM progress p JOIN games g ON g.id=p.game_id"
    )
    conds, params = [], []
    if game_id is not None:
        conds.append("p.game_id=?")
        params.append(int(game_id))
    if student_id is not None:
        conds.append("p.student_id=?")
        params.append(int(student_id))
    if conds:
        sql += " WHERE " + " AND ".join(conds)
    with db() as c:
        return pd.read_sql_query(sql, c, params=params)


def latest_progress(df):
    if df.empty:
        return df
    d = df.sort_values(["tarih", "id"], ascending=[False, False])
    return d.drop_duplicates(["student_id", "game_id"], keep="first").reset_index(drop=True)


def import_progress(records, tarih, donem):
    require_admin()
    if isinstance(tarih, datetime):
        tarih = tarih.date()
    stamp = tarih.strftime("%Y-%m-%d")
    n = 0
    with db() as c:
        for r in records:
            c.execute(
                "DELETE FROM progress WHERE student_id=? AND game_id=? AND kaynak='gecis' AND COALESCE(donem,'')=?",
                (r["student_id"], r["game_id"], donem or ""),
            )
            c.execute(
                "INSERT INTO progress (student_id, game_id, kart, seviye, tarih, kaynak, donem) "
                "VALUES (?,?,?,?,?, 'gecis', ?)",
                (r["student_id"], r["game_id"], r["kart"], r["seviye"], stamp, donem or ""),
            )
            n += 1
    return n


_ALIAS_TIME = {"zamandamgasi", "tarih", "zaman", "timestamp"}


def read_progress_file(uploaded):
    raw = _read_uploaded_table(uploaded)
    cols = {}
    for col in raw.columns:
        n = _norm(col)
        for key, alias in (("id", _ALIAS_ID), ("name", _ALIAS_NAME), ("time", _ALIAS_TIME)):
            if n in alias and key not in cols:
                cols[key] = col
    if "id" not in cols and "name" not in cols:
        raise ValueError(
            "Öğrenciyi belirleyecek sütun bulunamadı: dosyada Ogrenci_ID (veya Ad_Soyad) sütunu olmalıdır. "
            f"Dosyadaki sütunlar: {', '.join(map(str, raw.columns))}"
        )
    return raw, cols


def auto_map_columns(raw, cols, games):
    keyed = set(cols.values())
    gkeys = [(int(r.id), _norm(r.ad)) for r in games.itertuples()]
    out = {}
    for col in raw.columns:
        if col in keyed:
            continue
        n = _norm(col)
        out[col] = [gid for gid, gk in gkeys if gk and gk in n]
    return out


def _norm_no(v):
    s = "" if v is None else str(v).strip()
    if s.lower() in ("nan", "none"):
        return ""
    if re.fullmatch(r"\d+\.0+", s):
        s = s.split(".")[0]
    return s.upper()


def _norm_name(s):
    return re.sub(r"\s+", " ", tr_upper(str(s))).strip()


def build_progress_records(raw, cols, mapping):
    all_st = load_students("tumu")
    no_map, name_map, info, arch = {}, {}, {}, set()
    for r in all_st.itertuples():
        sid = int(r.id)
        if r.ogrenci_no:
            no_map[_norm_no(r.ogrenci_no)] = sid
        name_map.setdefault(_norm_name(r.ad_soyad), []).append(sid)
        info[sid] = (r.ad_soyad, f"{r.sinif}-{r.sube}" + (" (arşiv)" if int(r.arsiv) else ""))
        if int(r.arsiv):
            arch.add(sid)
    id_col, name_col, time_col = cols.get("id"), cols.get("name"), cols.get("time")
    ts = pd.to_datetime(raw[time_col], errors="coerce") if time_col else None

    row_sid, unmatched, blank = {}, [], 0
    for idx in raw.index:
        raw_id = _norm_no(raw.at[idx, id_col]) if id_col else ""
        raw_name = _nz(raw.at[idx, name_col]) if name_col else None
        if not raw_id and not raw_name:
            blank += 1
            continue
        sid = no_map.get(raw_id) if raw_id else None
        if sid is None and raw_name:
            cand = name_map.get(_norm_name(raw_name), [])
            if len(cand) == 1:
                sid = cand[0]
        if sid is None:
            unmatched.append(f"{raw_id or '—'} · {raw_name or '—'}")
        else:
            row_sid[idx] = sid

    order = list(row_sid.keys())
    if ts is not None:
        order.sort(key=lambda i: ts.at[i] if pd.notna(ts.at[i]) else pd.Timestamp.min)
    final, dup = {}, 0
    for i in order:
        if row_sid[i] in final:
            dup += 1
        final[row_sid[i]] = i  

    recs = {}
    for sid, i in final.items():
        for col, gids in mapping.items():
            v = _nz(raw.at[i, col])
            if v is None or str(v).strip().lower() in ("nan", "none", "-"):
                continue
            s = str(v).strip()
            kart = seviye = None
            try:
                f = float(s.replace(",", "."))
                if f >= 0 and f == int(f):
                    kart = int(f)
                else:
                    seviye = s
            except (ValueError, OverflowError):
                seviye = s
            for gid in gids:
                d = recs.setdefault((sid, int(gid)), {"kart": None, "seviye": None})
                if kart is not None and d["kart"] is None:
                    d["kart"] = kart
                if seviye is not None and d["seviye"] is None:
                    d["seviye"] = seviye
    records = [{"student_id": s, "game_id": g, **d} for (s, g), d in recs.items()]
    return records, {
        "matched": len(final), "unmatched": unmatched, "dup": dup, "blank": blank,
        "archived": len([s for s in final if s in arch]), "info": info,
        "ts_max": (ts.max().date() if ts is not None and ts.notna().any() else None),
    }


def progress_template_xlsx():
    games = load_games()
    indiv = games[games.kategori == INDIV_CATEGORY].ad.tolist()
    example = pd.DataFrame(
        [["OG0001", "Örnek Öğrenci 1"] + [20 + 5 * i for i in range(len(indiv))],
         ["OG0002", "Örnek Öğrenci 2"] + [10 + 3 * i for i in range(len(indiv))]],
        columns=["Ogrenci_ID", "Ad_Soyad"] + indiv,
    )
    help_df = pd.DataFrame({"Açıklama": [
        "Ogrenci_ID sütunu zorunludur (uygulamadaki öğrenci numarası ile aynı olmalı). Ad_Soyad isteğe bağlıdır; ID bulunamazsa yedek olarak kullanılır.",
        "Her oyun ayrı bir sütundur. Başlıkta oyun adı geçmesi yeterlidir (örn. 'Şakuli Oyunu Seviyesi').",
        "Hücre bir SAYI ise kart sayısı, METİN ise seviye adı (örn. 'Usta') olarak kaydedilir.",
        "İsterseniz aynı oyun için iki sütun kullanın: 'Şakuli Kart' (sayı) ve 'Şakuli Seviye' (metin).",
        "Boş hücreler atlanır. Aynı öğrenci birden çok satırdaysa en güncel satır alınır.",
    ]})
    return to_xlsx_bytes({"Geçiş Verisi": example, "Açıklama": help_df})


def _clean(s):
    return re.sub(r"\s+", " ", s or "").strip()


def _as_date(tarih):
    if tarih is None:
        return date.today()
    if isinstance(tarih, datetime):
        return tarih.date()
    return tarih if isinstance(tarih, date) else None


def create_group(ad, game_id, turnuva, member_ids, tarih=None):
    require_admin()
    ad, turnuva = _clean(ad), _clean(turnuva)
    if game_id is None:
        return False, "Lütfen bir toplu oyun seçin."
    if not ad:
        return False, "Grup adı boş bırakılamaz."
    member_ids = sorted({int(i) for i in (member_ids or [])})
    if not member_ids:
        return False, "Gruba en az bir oyuncu ekleyin."
    tarih = _as_date(tarih)
    if tarih is None or tarih > date.today():
        return False, "Geçerli bir tarih seçin (bugünden sonrası olamaz)."
    try:
        with db() as c:
            kat = c.execute("SELECT kategori FROM games WHERE id=?", (int(game_id),)).fetchone()
            if not kat or kat["kategori"] != GROUP_CATEGORY:
                return False, "Gruplar yalnızca toplu oyunlar için oluşturulabilir."
            cur = c.execute(
                "INSERT INTO game_groups (ad, game_id, turnuva, tarih) VALUES (?,?,?,?)",
                (ad, int(game_id), turnuva, tarih.strftime("%Y-%m-%d")),
            )
            c.executemany(
                "INSERT OR IGNORE INTO group_members (group_id, student_id) VALUES (?,?)",
                [(cur.lastrowid, i) for i in member_ids],
            )
        return True, f"'{ad}' grubu {len(member_ids)} oyuncu ile oluşturuldu."
    except sqlite3.IntegrityError:
        return False, "Bu oyunda, aynı turnuva altında bu isimde bir grup zaten var."


def update_group(gid, ad, turnuva, member_ids):
    require_admin()
    ad, turnuva = _clean(ad), _clean(turnuva)
    if not ad:
        return False, "Grup adı boş bırakılamaz."
    want = {int(i) for i in (member_ids or [])}
    try:
        with db() as c:
            c.execute("UPDATE game_groups SET ad=?, turnuva=? WHERE id=?", (ad, turnuva, int(gid)))
            current = {r[0] for r in c.execute("SELECT student_id FROM group_members WHERE group_id=?", (int(gid),))}
            active = {r[0] for r in c.execute(
                "SELECT s.id FROM group_members gm JOIN students s ON s.id=gm.student_id "
                "WHERE gm.group_id=? AND s.arsiv=0", (int(gid),))}
            c.executemany("DELETE FROM group_members WHERE group_id=? AND student_id=?",
                          [(int(gid), i) for i in active - want])
            c.executemany("INSERT OR IGNORE INTO group_members (group_id, student_id) VALUES (?,?)",
                          [(int(gid), i) for i in want - current])
        return True, "Grup güncellendi."
    except sqlite3.IntegrityError:
        return False, "Bu oyunda, aynı turnuva altında bu isimde başka bir grup zaten var."


def delete_group(gid):
    require_admin()
    with db() as c:
        c.execute("DELETE FROM game_groups WHERE id=?", (int(gid),))


def load_groups():
    with db() as c:
        return pd.read_sql_query(
            "SELECT gg.id AS id, gg.ad AS ad, gg.turnuva AS turnuva, gg.tarih AS tarih, gg.game_id AS game_id, "
            "g.ad AS oyun, "
            "(SELECT COUNT(*) FROM group_members gm JOIN students s ON s.id=gm.student_id "
            " WHERE gm.group_id=gg.id AND s.arsiv=0) AS uye "
            "FROM game_groups gg JOIN games g ON g.id=gg.game_id ORDER BY gg.tarih DESC, gg.id DESC", c)


def group_label(r):
    return f"{r.oyun} · " + (f"{r.turnuva} · " if r.turnuva else "") + f"{r.ad}"


def group_members_df(gid):
    with db() as c:
        df = pd.read_sql_query(
            "SELECT s.id AS id, s.ogrenci_no AS ogrenci_no, s.ad_soyad AS ad_soyad, s.sinif AS sinif, s.sube AS sube "
            "FROM group_members gm JOIN students s ON s.id=gm.student_id "
            "WHERE gm.group_id=? AND s.arsiv=0", c, params=[int(gid)])
    return _sort_students(df)


def save_group_scores(gid, rows, tarih=None, tur=""):
    require_admin()
    tarih = _as_date(tarih)
    if tarih is None or tarih > date.today():
        return False, "Geçerli bir tarih seçin (bugünden sonrası olamaz)."
    clean = []
    for sid, kart, puan in rows:
        k, p = _to_int(kart), _to_int(puan)
        if k is None and p is None:
            continue
        if (k or 0) < 0 or (p or 0) < 0:
            return False, "Kart ve puan negatif olamaz."
        clean.append((int(sid), k or 0, p or 0))
    if not clean:
        return False, "Kaydedilecek skor girilmedi."
    with db() as c:
        members = {r[0] for r in c.execute("SELECT student_id FROM group_members WHERE group_id=?", (int(gid),))}
        if any(s not in members for s, _, _ in clean):
            return False, "Skor girilen oyunculardan biri bu grubun üyesi değil."
        c.executemany(
            "INSERT INTO group_scores (group_id, student_id, tarih, tur, kart, puan) VALUES (?,?,?,?,?,?)",
            [(int(gid), s, tarih.strftime("%Y-%m-%d"), _clean(tur), k, p) for s, k, p in clean],
        )
    return True, f"{len(clean)} oyuncunun skoru kaydedildi."


def delete_group_score(sid):
    require_admin()
    with db() as c:
        c.execute("DELETE FROM group_scores WHERE id=?", (int(sid),))


def group_scores_df():
    with db() as c:
        return pd.read_sql_query(
            "SELECT sc.id AS id, sc.tarih AS tarih, sc.tur AS tur, sc.kart AS kart, sc.puan AS puan, "
            "sc.student_id AS student_id, sc.group_id AS group_id, gg.ad AS grup, gg.turnuva AS turnuva, "
            "gg.game_id AS game_id, g.ad AS oyun, s.ad_soyad AS ad_soyad, s.sinif AS sinif, s.sube AS sube, "
            "s.arsiv AS arsiv "
            "FROM group_scores sc JOIN game_groups gg ON gg.id=sc.group_id JOIN games g ON g.id=gg.game_id "
            "JOIN students s ON s.id=sc.student_id ORDER BY sc.tarih DESC, sc.id DESC", c)


def player_standings(sc, key="puan"):
    cols = ["Sıra", "Ad Soyad", "Sınıf", "Şube", "Kayıt", "Kart", "Puan"]
    if sc.empty:
        return pd.DataFrame(columns=cols)
    g = sc.groupby(["student_id", "ad_soyad", "sinif", "sube"], as_index=False).agg(
        kayit=("id", "count"), kart=("kart", "sum"), puan=("puan", "sum"))
    other = "kart" if key == "puan" else "puan"
    g = g.sort_values([key, other, "ad_soyad"], ascending=[False, False, True]).reset_index(drop=True)
    g.insert(0, "Sıra", range(1, len(g) + 1))
    return g.rename(columns={"ad_soyad": "Ad Soyad", "sinif": "Sınıf", "sube": "Şube", "kayit": "Kayıt",
                             "kart": "Kart", "puan": "Puan"})[cols]


def group_totals(sc, key="puan"):
    cols = ["Sıra", "Oyun", "Turnuva", "Grup", "Oyuncu", "Kart", "Puan"]
    if sc.empty:
        return pd.DataFrame(columns=cols)
    g = sc.groupby(["group_id", "oyun", "turnuva", "grup"], as_index=False).agg(
        oyuncu=("student_id", "nunique"), kart=("kart", "sum"), puan=("puan", "sum"))
    other = "kart" if key == "puan" else "puan"
    g = g.sort_values([key, other], ascending=False).reset_index(drop=True)
    g.insert(0, "Sıra", range(1, len(g) + 1))
    g["turnuva"] = g.turnuva.replace("", "—")
    return g.rename(columns={"oyun": "Oyun", "turnuva": "Turnuva", "grup": "Grup", "oyuncu": "Oyuncu",
                             "kart": "Kart", "puan": "Puan"})[cols]


def compute_stats(students, matches):
    df = students.copy()
    cols = ["galibiyet", "beraberlik", "maglubiyet"]
    if matches.empty:
        for c in cols:
            df[c] = 0
    else:
        a = pd.DataFrame({
            "id": matches.p1_id,
            "galibiyet": (matches.sonuc == "1").astype(int),
            "beraberlik": (matches.sonuc == "D").astype(int),
            "maglubiyet": (matches.sonuc == "2").astype(int),
        })
        b = pd.DataFrame({
            "id": matches.p2_id,
            "galibiyet": (matches.sonuc == "2").astype(int),
            "beraberlik": (matches.sonuc == "D").astype(int),
            "maglubiyet": (matches.sonuc == "1").astype(int),
        })
        agg = pd.concat([a, b]).groupby("id", as_index=False).sum()
        df = df.merge(agg, on="id", how="left")
        df[cols] = df[cols].fillna(0).astype(int)
    df["mac"] = df[cols].sum(axis=1)
    df["puan"] = df.galibiyet * 3 + df.beraberlik
    df["basari"] = ((df.galibiyet + 0.5 * df.beraberlik) / df.mac.where(df.mac > 0) * 100).fillna(0).round(1)
    df["seviye"] = ((df.galibiyet + 0.5 * df.beraberlik + 1) / (df.mac + 2)).round(3)
    return df


def branch_summary(stats):
    if stats.empty:
        return pd.DataFrame(columns=["sinif", "sube", "mevcut", "aktif", "galibiyet", "beraberlik", "mac", "basari"])
    g = (
        stats.groupby(["sinif", "sube"])
        .agg(
            mevcut=("id", "count"),
            aktif=("mac", lambda s: int((s > 0).sum())),
            galibiyet=("galibiyet", "sum"),
            beraberlik=("beraberlik", "sum"),
            mac=("mac", "sum"),
        )
        .reset_index()
    )
    g["basari"] = ((g.galibiyet + 0.5 * g.beraberlik) / g.mac.where(g.mac > 0) * 100).fillna(0).round(1)
    return g.sort_values(["sinif", "sube"]).reset_index(drop=True)


def auto_pair(ids, rating, already):
    ordered = sorted(ids, key=lambda i: (-rating[i], i))
    pairs, remaining = [], list(ordered)
    while len(remaining) >= 2:
        a = remaining.pop(0)
        best = min(
            range(len(remaining)),
            key=lambda k: (frozenset((a, remaining[k])) in already, abs(rating[a] - rating[remaining[k]]), k),
        )
        b = remaining.pop(best)
        pairs.append((a, b))
    return pairs, remaining


_ICON_PATHS = {
    "home": '<path d="M3 11l9-8 9 8"/><path d="M5 10v10h14V10"/>',
    "school": '<path d="M2 10l10-5 10 5-10 5z"/><path d="M6 12v5c3 2 9 2 12 0v-5"/>',
    "swords": '<path d="M14 4l6-1-1 6-9 9-4-4z"/><path d="M5 15l-2 2 4 4 2-2"/>',
    "trophy": '<path d="M8 21h8M12 17v4M7 4h10v5a5 5 0 0 1-10 0z"/><path d="M7 6H4v2a3 3 0 0 0 3 3M17 6h3v2a3 3 0 0 1-3 3"/>',
    "dice": '<rect x="4" y="4" width="16" height="16" rx="3"/><circle cx="9" cy="9" r="1"/><circle cx="15" cy="15" r="1"/><circle cx="15" cy="9" r="1"/><circle cx="9" cy="15" r="1"/>',
    "lock": '<rect x="5" y="11" width="14" height="9" rx="2"/><path d="M8 11V8a4 4 0 0 1 8 0v3"/>',
    "users": '<circle cx="9" cy="8" r="3"/><path d="M3 20c0-3 3-5 6-5s6 2 6 5"/><path d="M16 5a3 3 0 0 1 0 6M18 15c2 .5 3 2.2 3 4"/>',
    "chart": '<path d="M4 20V10M10 20V4M16 20v-7M22 20H2"/>',
    "scale": '<path d="M12 3v18M5 21h14M5 7h14"/><path d="M5 7l-3 7a3 3 0 0 0 6 0zM19 7l-3 7a3 3 0 0 0 6 0z"/>',
    "target": '<circle cx="12" cy="12" r="9"/><circle cx="12" cy="12" r="4"/>',
    "puzzle": '<path d="M10 4a2 2 0 1 1 4 0v2h4v4h-2a2 2 0 1 0 0 4h2v6H4v-6h2a2 2 0 1 0 0-4H4V6h6z"/>',
    "brain": '<path d="M9 4a3 3 0 0 0-3 3 3 3 0 0 0-2 5 3 3 0 0 0 2 5 3 3 0 0 0 6 1V4a3 3 0 0 0-3 0zM15 4a3 3 0 0 1 3 3 3 3 0 0 1 2 5 3 3 0 0 1-2 5 3 3 0 0 1-6 1"/>',
    "archive": '<rect x="3" y="4" width="18" height="4" rx="1"/><path d="M5 8v11h14V8M10 12h4"/>',
    "calendar": '<rect x="3" y="5" width="18" height="16" rx="2"/><path d="M3 10h18M8 3v4M16 3v4"/>',
}

_EMOJI_TO_ICON = {
    "⚔️": "swords", "⚖️": "scale", "👩‍🎓": "users", "📈": "chart", "🏫": "school", "🏆": "trophy",
    "🎲": "dice", "🔐": "lock", "👥": "users", "🎯": "target", "📊": "chart", "🧠": "brain", "🧩": "puzzle",
}


def icon(name, size=22):
    return (
        f'<svg width="{size}" height="{size}" viewBox="0 0 24 24" fill="none" stroke="currentColor" '
        f'stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">'
        f'{_ICON_PATHS[name]}</svg>'
    )


def _ico(x, size=22):
    name = _EMOJI_TO_ICON.get(x, x)
    return icon(name, size) if name in _ICON_PATHS else x


CSS = """
<style>
@import url('https://fonts.googleapis.com/css2?family=DM+Serif+Display&family=Nunito:wght@400;600;700;800&display=swap');
:root{
  --bg:#F8F5F0; --card:#FFFDFA; --line:#E6DCD0; --milk:#F1EADF; --latte:#E2D3BF;
  --side:#45372F; --side-hi:#54443A;
  --taba:#A9794F; --taba-d:#8A5E3E; --mocha:#6F5443; --espresso:#3A2E27; --muted:#85766A;
  --shadow:0 4px 12px rgba(0,0,0,.03); --shadow-h:0 10px 24px rgba(69,55,47,.10);
}
html, body, .stApp{font-family:'Nunito',system-ui,-apple-system,'Segoe UI',sans-serif;}
.stApp{background:var(--bg);color:var(--espresso);}
.stApp p, .stApp label, .stApp li, .stApp span, .stApp div[data-testid="stMarkdownContainer"]{color:var(--espresso);}
header[data-testid="stHeader"]{background:transparent;}
.block-container{padding-top:2rem;max-width:1200px;}
h1,h2,h3,h4{font-family:'DM Serif Display',Georgia,serif !important;color:var(--espresso) !important;letter-spacing:.2px;}
hr{border-color:var(--line);}

section[data-testid="stSidebar"], section[data-testid="stSidebar"] > div{background:var(--side) !important;}
section[data-testid="stSidebar"]{border-right:none;}
section[data-testid="stSidebar"] .block-container{padding-top:1.5rem;}
section[data-testid="stSidebar"] p, section[data-testid="stSidebar"] span,
section[data-testid="stSidebar"] label, section[data-testid="stSidebar"] div{color:#EFE6DA;}
[data-testid="stSidebarCollapseButton"] button, [data-testid="stSidebarCollapseButton"] span,
[data-testid="stSidebarCollapseButton"] svg{color:#E9DFD2 !important;fill:#E9DFD2 !important;}
.brand{display:flex;align-items:center;gap:.8rem;padding:.2rem .3rem 1.2rem .3rem;margin-bottom:.9rem;border-bottom:1px solid rgba(255,255,255,.10);}
.brand-logo{width:44px;height:44px;border-radius:12px;background:linear-gradient(135deg,#B98B5F,#8A5E3E);display:flex;align-items:center;justify-content:center;font-size:1.45rem;box-shadow:0 6px 14px rgba(0,0,0,.28);}
section[data-testid="stSidebar"] .brand-t{font-family:'DM Serif Display',Georgia,serif;font-size:1.1rem;line-height:1.15;color:#FBF4EA;}
section[data-testid="stSidebar"] .brand-s{font-size:.7rem;color:#BBA896;letter-spacing:.1em;text-transform:uppercase;margin-top:3px;}
section[data-testid="stSidebar"] .side-label{font-size:.68rem;font-weight:800;letter-spacing:.14em;text-transform:uppercase;color:#A8957F;margin:0 0 .5rem .4rem;}
section[data-testid="stSidebar"] div[role="radiogroup"]{display:flex;flex-direction:column;gap:.3rem;}
section[data-testid="stSidebar"] div[role="radiogroup"] > label{background:transparent;border:1px solid transparent;border-radius:10px;padding:.65rem .9rem;width:100%;cursor:pointer;transition:background .2s ease, transform .2s ease;}
section[data-testid="stSidebar"] div[role="radiogroup"] > label:hover{background:rgba(255,255,255,.07);transform:translateX(3px);}
section[data-testid="stSidebar"] div[role="radiogroup"] > label:has(input:checked){background:linear-gradient(135deg,#B5855A 0%,#8F6342 100%);box-shadow:0 6px 14px rgba(0,0,0,.25);}
section[data-testid="stSidebar"] div[role="radiogroup"] > label > div:first-child{display:none;}
section[data-testid="stSidebar"] div[role="radiogroup"] > label p{font-weight:700;font-size:.96rem;margin:0;color:#EFE6DA;}
section[data-testid="stSidebar"] div[role="radiogroup"] > label:has(input:checked) p,
section[data-testid="stSidebar"] div[role="radiogroup"] > label:has(input:checked) div{color:#FFF9F0 !important;}
section[data-testid="stSidebar"] .side-note{margin-top:1.4rem;padding:.75rem .95rem;border-radius:10px;background:rgba(255,255,255,.06);border:1px solid rgba(255,255,255,.10);font-size:.8rem;color:#D9CBBA;}

.welcome{position:relative;overflow:hidden;display:flex;align-items:center;justify-content:space-between;gap:1.2rem;padding:2rem 2.2rem;margin-bottom:1.3rem;border-radius:12px;background:linear-gradient(120deg,#F1E6D5 0%,#E4D0B4 100%);border:1px solid var(--line);box-shadow:var(--shadow);}
.welcome:before{content:"";position:absolute;right:-60px;top:-80px;width:260px;height:260px;border-radius:50%;background:rgba(255,253,250,.35);}
.welcome:after{content:"";position:absolute;right:120px;bottom:-110px;width:200px;height:200px;border-radius:50%;background:rgba(169,121,79,.10);}
.welcome-main{position:relative;z-index:1;}
.welcome-eyebrow{font-size:.72rem;font-weight:800;letter-spacing:.14em;text-transform:uppercase;color:var(--taba-d);margin-bottom:.45rem;}
.welcome-t{font-family:'DM Serif Display',Georgia,serif;font-size:2.15rem;line-height:1.15;color:var(--espresso);}
.welcome-s{margin-top:.5rem;font-size:1.02rem;color:var(--mocha);max-width:560px;}
.welcome-art{position:relative;z-index:1;font-size:3.4rem;letter-spacing:.35rem;opacity:.92;}

.hero{display:flex;align-items:center;gap:1rem;padding:1.15rem 1.4rem;margin-bottom:1.3rem;border-radius:12px;background:var(--card);border:1px solid var(--line);box-shadow:var(--shadow);}
.hero-icon{font-size:1.8rem;width:54px;height:54px;border-radius:12px;background:var(--milk);display:flex;align-items:center;justify-content:center;flex-shrink:0;}
.hero-t{font-family:'DM Serif Display',Georgia,serif;font-size:1.65rem;line-height:1.15;color:var(--espresso);}
.hero-s{margin-top:.2rem;color:var(--muted);font-size:.95rem;}
.sec-t{font-family:'DM Serif Display',Georgia,serif;font-size:1.3rem;color:var(--espresso);margin:1.4rem 0 .8rem 0;}

.stat{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:1.1rem 1.25rem;box-shadow:var(--shadow);transition:transform .2s ease, box-shadow .2s ease;height:100%;}
.stat:hover{transform:translateY(-2px);box-shadow:var(--shadow-h);}
.stat-top{display:flex;align-items:center;justify-content:space-between;gap:.5rem;}
.stat-label{font-size:.74rem;color:var(--muted);text-transform:uppercase;letter-spacing:.08em;font-weight:700;}
.stat-icon{width:32px;height:32px;border-radius:9px;background:var(--milk);display:flex;align-items:center;justify-content:center;font-size:1rem;flex-shrink:0;}
.stat-val{font-size:2.3rem;font-weight:800;color:var(--espresso);line-height:1.1;margin-top:.55rem;}
.stat-sub{font-size:.78rem;color:var(--muted);margin-top:.3rem;}

[data-testid$="olumn"]:has(.qa-body){position:relative;box-sizing:border-box;background:var(--card);border:1px solid var(--line);border-radius:12px;box-shadow:var(--shadow);padding:1.2rem 1.3rem !important;cursor:pointer;transition:transform .2s ease, box-shadow .2s ease, border-color .2s ease, background .2s ease;}
[data-testid$="olumn"]:has(.qa-body):hover{transform:translateY(-2px);box-shadow:var(--shadow-h);border-color:var(--taba);background:#FFFEFB;}
[data-testid$="olumn"]:has(.qa-body):has(button:focus-visible){outline:2px solid var(--taba);outline-offset:2px;}
[data-testid$="olumn"]:has(.qa-body) .element-container:has(.stButton),
[data-testid$="olumn"]:has(.qa-body) [data-testid="stElementContainer"]:has(.stButton){position:absolute;inset:0;width:100% !important;height:100%;margin:0;z-index:3;}
[data-testid$="olumn"]:has(.qa-body) .stButton{width:100%;height:100%;}
[data-testid$="olumn"]:has(.qa-body) .stButton > button{width:100%;height:100%;min-height:0;opacity:0;cursor:pointer;border-radius:12px;}
.qa-body{display:flex;align-items:center;gap:1rem;min-height:74px;}
.qa-ico{width:52px;height:52px;border-radius:12px;background:var(--milk);border:1px solid var(--line);display:flex;align-items:center;justify-content:center;font-size:1.55rem;flex-shrink:0;transition:background .2s ease;}
[data-testid$="olumn"]:has(.qa-body):hover .qa-ico{background:linear-gradient(135deg,#EBD9C0,#E0C8A6);}
.qa-txt{flex:1;min-width:0;}
.qa-t{font-weight:800;font-size:1.05rem;color:var(--espresso);}
.qa-d{font-size:.85rem;color:var(--muted);margin-top:.15rem;line-height:1.35;}
.qa-go{font-size:1.25rem;color:var(--taba);font-weight:800;transition:transform .2s ease;}
[data-testid$="olumn"]:has(.qa-body):hover .qa-go{transform:translateX(4px);}

.bcard{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:1.05rem 1.15rem;margin-bottom:1rem;box-shadow:var(--shadow);transition:all .2s ease;}
.bcard:hover{transform:translateY(-2px);box-shadow:var(--shadow-h);border-color:var(--latte);}
.bhead{display:flex;justify-content:space-between;align-items:center;margin-bottom:.45rem;}
.btag{font-family:'DM Serif Display',Georgia,serif;font-size:1.45rem;color:var(--espresso);}
.bpct{font-weight:800;color:var(--taba);font-size:1.05rem;}
.bmeta{font-size:.83rem;color:var(--mocha);margin-bottom:.6rem;}
.bar{height:8px;border-radius:99px;background:var(--milk);overflow:hidden;}
.bar > div{height:100%;border-radius:99px;background:linear-gradient(90deg,#C9A27A,#A9794F);transition:width .6s ease;}
.row{display:flex;align-items:center;gap:.8rem;padding:.65rem .9rem;margin-bottom:.5rem;background:var(--card);border:1px solid var(--line);border-radius:12px;box-shadow:var(--shadow);}
.row .medal{width:34px;height:34px;border-radius:50%;background:var(--milk);display:flex;align-items:center;justify-content:center;font-weight:800;color:var(--mocha);flex-shrink:0;}
.row .nm{font-weight:700;flex:1;}
.row .sb{font-size:.8rem;color:var(--muted);}
.row .pt{font-weight:800;color:var(--taba);}
.vs{display:flex;align-items:center;justify-content:space-between;gap:1rem;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:1.1rem 1.4rem;margin:.6rem 0 1rem 0;}
.vs .pl{flex:1;text-align:center;}
.vs .pl b{font-family:'DM Serif Display',Georgia,serif;font-size:1.25rem;}
.vs .pl span{display:block;font-size:.8rem;color:var(--muted);}
.vs .x{font-weight:800;color:var(--taba);font-size:1.2rem;}
.chip{display:inline-block;margin:.2rem .3rem .2rem 0;padding:.38rem .85rem;border-radius:99px;background:var(--milk);border:1px solid var(--latte);color:var(--mocha);font-weight:700;font-size:.88rem;}
.chip i{font-style:normal;color:var(--taba);margin-left:.35rem;font-size:.78rem;}
.lib{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:1.2rem 1.3rem;box-shadow:var(--shadow);height:100%;}
.lib h3{margin:0 0 .7rem 0;font-size:1.3rem;}

.stButton > button, .stDownloadButton > button, [data-testid="stFormSubmitButton"] > button{border-radius:10px;border:1px solid var(--line);background:var(--card);color:var(--espresso);font-weight:700;transition:all .2s ease;}
.stButton > button:hover, .stDownloadButton > button:hover, [data-testid="stFormSubmitButton"] > button:hover{border-color:var(--taba);color:var(--taba-d);transform:translateY(-1px);box-shadow:0 6px 14px rgba(69,55,47,.10);}
.stButton > button[kind="primary"], [data-testid="stBaseButton-primary"], [data-testid="stFormSubmitButton"] > button[kind="primary"], [data-testid="stBaseButton-primaryFormSubmit"]{background:linear-gradient(135deg,#B5855A,#8F6342) !important;color:#FFF9F0 !important;border:none !important;}
.stButton > button[kind="primary"] p, [data-testid="stBaseButton-primary"] p, [data-testid="stBaseButton-primaryFormSubmit"] p{color:#FFF9F0 !important;}

[data-testid="stWidgetLabel"] p, .stApp label p{font-weight:700;font-size:.86rem;color:var(--mocha) !important;}
[data-baseweb="input"], [data-baseweb="textarea"]{background:var(--card) !important;border:1px solid var(--line) !important;border-radius:10px !important;box-shadow:none !important;transition:border-color .18s ease, box-shadow .18s ease;}
[data-baseweb="base-input"]{background:transparent !important;border:none !important;}
[data-baseweb="input"] input, [data-baseweb="textarea"] textarea, .stTextInput input, .stNumberInput input{background:transparent !important;color:var(--espresso) !important;caret-color:var(--taba);}
[data-baseweb="input"] input::placeholder, [data-baseweb="textarea"] textarea::placeholder{color:#B3A598 !important;opacity:1;}
[data-baseweb="input"]:hover, [data-baseweb="textarea"]:hover, [data-baseweb="select"] > div:hover{border-color:var(--latte) !important;}
[data-baseweb="input"]:focus-within, [data-baseweb="textarea"]:focus-within{border-color:var(--taba) !important;box-shadow:0 0 0 3px rgba(169,121,79,.16) !important;}
[data-baseweb="select"] > div{background:var(--card) !important;border:1px solid var(--line) !important;border-radius:10px !important;min-height:44px;color:var(--espresso) !important;box-shadow:none !important;transition:border-color .18s ease, box-shadow .18s ease;}
[data-baseweb="select"] > div:focus-within{border-color:var(--taba) !important;box-shadow:0 0 0 3px rgba(169,121,79,.16) !important;}
[data-baseweb="select"] input, [data-baseweb="select"] div, [data-baseweb="select"] span{color:var(--espresso);}
[data-baseweb="select"] svg{fill:var(--taba-d);}
[data-baseweb="popover"] > div, [data-baseweb="popover"] ul, [data-baseweb="menu"]{background:var(--card) !important;border-radius:10px !important;}
[data-baseweb="popover"] li{color:var(--espresso) !important;}
[data-baseweb="popover"] li:hover, [data-baseweb="popover"] li[aria-selected="true"]{background:var(--milk) !important;}
[data-testid="stNumberInput"] button{background:var(--milk) !important;border:none !important;color:var(--mocha) !important;}
[data-testid="stNumberInput"] button:hover{background:var(--latte) !important;}

.stTabs [data-baseweb="tab-list"]{gap:.4rem;border-bottom:1px solid var(--line);}
.stTabs [data-baseweb="tab"]{border-radius:10px 10px 0 0;padding:.6rem 1.1rem;font-weight:700;color:var(--mocha);}
.stTabs [aria-selected="true"]{color:var(--taba-d) !important;}
.stTabs [data-baseweb="tab-highlight"]{background-color:var(--taba) !important;}
[data-testid="stVerticalBlockBorderWrapper"]{border-radius:12px;}
[data-testid="stExpander"]{border:1px solid var(--line);border-radius:12px;background:var(--card);}
[data-testid="stFileUploader"] section{background:var(--card);border:1.5px dashed var(--latte);border-radius:12px;}
[data-testid="stDataFrame"]{border:1px solid var(--line);border-radius:12px;overflow:hidden;}
[data-testid="stAlert"]{border-radius:12px;}

.hero-icon svg, .stat-icon svg, .qa-ico svg{color:var(--taba-d);display:block;}
.brand-logo svg{color:#FFF6EA;display:block;}
.welcome-art{display:flex;gap:1rem;color:var(--taba-d);opacity:.85;}
.welcome-art svg{display:block;}
.vs .pl, .row .nm{min-width:0;overflow-wrap:anywhere;}
/*MENU_ICONS*/

section[data-testid="stSidebar"] .side-note b{color:#FBF4EA;font-weight:800;}
section[data-testid="stSidebar"] .side-note small{display:block;margin-top:.3rem;color:#BBA896;font-size:.74rem;line-height:1.4;}
section[data-testid="stSidebar"] .side-note .dot{display:inline-block;width:9px;height:9px;border-radius:50%;margin-right:.5rem;}
section[data-testid="stSidebar"] .side-note.admin-on{border-color:rgba(143,191,138,.50);background:rgba(143,191,138,.11);}
section[data-testid="stSidebar"] .side-note.admin-on .dot{background:#8FBF8A;box-shadow:0 0 0 3px rgba(143,191,138,.22);}
section[data-testid="stSidebar"] .side-note.admin-off .dot{background:#D9A066;}
section[data-testid="stSidebar"] .stButton > button{background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.20);}
section[data-testid="stSidebar"] .stButton > button:hover{background:rgba(255,255,255,.14);border-color:#D9B48A;}
section[data-testid="stSidebar"] .stButton > button p{color:#EFE6DA !important;}

.mrow{display:flex;flex-wrap:wrap;align-items:center;gap:.35rem .9rem;min-height:44px;padding:.5rem .9rem;margin-bottom:.45rem;background:var(--card);border:1px solid var(--line);border-radius:12px;box-shadow:var(--shadow);}
.mrow .md{font-size:.8rem;font-weight:700;color:var(--muted);min-width:76px;}
.mrow .mg{font-size:.76rem;font-weight:800;color:var(--mocha);background:var(--milk);border:1px solid var(--latte);border-radius:99px;padding:.12rem .65rem;}
.mrow .mp{flex:1;min-width:200px;font-weight:700;color:var(--espresso);overflow-wrap:anywhere;}
.mrow .mp i{font-style:normal;font-weight:600;font-size:.78rem;color:var(--muted);}
.mrow .mp .vsx{color:var(--taba);font-size:.74rem;margin:0 .3rem;}
.mrow .mr{font-size:.82rem;font-weight:800;color:var(--taba-d);}
.confirm-del{padding:.9rem 1.1rem;margin:.4rem 0 .6rem 0;border-radius:12px;background:#FBEDE6;border:1px solid #E4B7A5;color:#7A2E1B;line-height:1.55;}
.confirm-del b{color:#7A2E1B;}
[class*="st-key-delm_"] .stButton > button:hover{border-color:#B5523B;color:#9C3D28;}
[class*="st-key-confirm_del"] .stButton > button{background:linear-gradient(135deg,#C4593F,#9C3D28) !important;color:#FFF9F0 !important;border:none !important;}
[class*="st-key-confirm_del"] .stButton > button p{color:#FFF9F0 !important;}

[data-testid="stDataFrame"], [data-testid="stTable"]{max-width:100%;overflow-x:auto;}
[data-testid="stDateInput"] input{min-height:44px;}
@media (max-width: 768px){
  .block-container{padding:1rem .85rem 3rem .85rem !important;}
  .welcome{flex-direction:column;align-items:flex-start;padding:1.3rem 1.2rem;}
  .welcome-t{font-size:1.6rem;}
  .welcome-art svg{width:44px;height:44px;}
  .hero{padding:.9rem 1rem;}
  .hero-t{font-size:1.3rem;}
  .stat-val{font-size:1.8rem;}
  .qa-body{min-height:64px;}
  .vs{flex-direction:column;gap:.4rem;padding:.9rem 1rem;}
  .stButton > button, .stDownloadButton > button, [data-testid="stFormSubmitButton"] > button{min-height:46px;}
  [data-baseweb="select"] > div, [data-baseweb="input"]{min-height:46px;}
  .stTabs [data-baseweb="tab"]{padding:.5rem .7rem;font-size:.9rem;}
  div[data-testid="stHorizontalBlock"]{flex-wrap:wrap !important;row-gap:.6rem;}
  div[data-testid="stHorizontalBlock"] > div[data-testid$="olumn"]{min-width:100% !important;flex:1 1 100% !important;}
}
</style>
"""


def menu_icon_css():
    rules = []
    for i, name in enumerate((PAGE_ICONS[p] for p in PAGES), start=1):
        svg = ("<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='black' "
               "stroke-width='1.8' stroke-linecap='round' stroke-linejoin='round'>"
               + _ICON_PATHS[name].replace('"', "'") + "</svg>")
        uri = "data:image/svg+xml;utf8," + svg.replace("<", "%3C").replace(">", "%3E")
        rules.append(
            'section[data-testid="stSidebar"] div[role="radiogroup"] > label:nth-child(%d) p::before{content:"";'
            'display:inline-block;width:18px;height:18px;margin-right:.7rem;vertical-align:-3px;background:currentColor;'
            '-webkit-mask:url("%s") center/contain no-repeat;mask:url("%s") center/contain no-repeat;}' % (i, uri, uri)
        )
    return "\n".join(rules)


def inject_css():
    st.markdown(CSS.replace("/*MENU_ICONS*/", menu_icon_css()), unsafe_allow_html=True)


def hero(title, subtitle, icon_name):
    st.markdown(
        f'<div class="hero"><div class="hero-icon">{_ico(icon_name, 26)}</div>'
        f'<div><div class="hero-t">{esc(title)}</div><div class="hero-s">{esc(subtitle)}</div></div></div>',
        unsafe_allow_html=True,
    )


def welcome_banner():
    st.markdown(
        '<div class="welcome"><div class="welcome-main">'
        '<div class="welcome-eyebrow">Akıl ve Zeka Oyunları · Yönetim ve Takip</div>'
        '<div class="welcome-t">Hoş Geldiniz, Öğretmenim</div>'
        '<div class="welcome-s">Akıl ve zeka oyunlarıyla öğrencilerinizin potansiyelini keşfedin.</div>'
        '</div><div class="welcome-art">' + icon("puzzle", 64) + icon("dice", 64) + '</div></div>',
        unsafe_allow_html=True,
    )


def stat_cards(items):
    cols = st.columns(len(items))
    for col, item in zip(cols, items):
        icn, label, value = item[0], item[1], item[2]
        sub = item[3] if len(item) > 3 else ""
        col.markdown(
            f'<div class="stat"><div class="stat-top"><div class="stat-label">{esc(label)}</div>'
            f'<div class="stat-icon">{_ico(icn, 18)}</div></div>'
            f'<div class="stat-val">{esc(str(value))}</div>'
            + (f'<div class="stat-sub">{esc(sub)}</div>' if sub else "")
            + "</div>",
            unsafe_allow_html=True,
        )


def goto(page, match_tab=None):
    st.session_state["nav"] = page
    if match_tab:
        st.session_state["match_tab"] = match_tab


def reset_match_tab():
    st.session_state["match_tab"] = "manual"


def quick_action(col, key, icn, title, desc, page, match_tab=None):
    with col:
        st.markdown(
            f'<div class="qa-body"><div class="qa-ico">{_ico(icn, 26)}</div>'
            f'<div class="qa-txt"><div class="qa-t">{esc(title)}</div><div class="qa-d">{esc(desc)}</div></div>'
            f'<div class="qa-go">→</div></div>',
            unsafe_allow_html=True,
        )
        st.button(title, key=key, on_click=goto, args=(page, match_tab), use_container_width=True)


def bar_html(pct):
    return f'<div class="bar"><div style="width:{max(0, min(100, pct))}%"></div></div>'


def flash(kind, msg):
    st.session_state["flash"] = (kind, msg)


def show_flash():
    f = st.session_state.pop("flash", None)
    if f:
        kind, msg = f
        {"success": st.success, "error": st.error, "warning": st.warning}.get(kind, st.info)(msg)


def empty_state():
    st.info("Henüz öğrenci listesi yüklenmemiş. Yönetici Paneli'nden giriş yaparak Excel/CSV yükleyebilirsiniz.")


def student_labels(df):
    return {int(r.id): f"{r.ad_soyad}  ·  {r.sinif}-{r.sube}" for r in df.itertuples()}


def class_branch_filter(df, key):
    c1, c2 = st.columns(2)
    siniflar = ["Tümü"] + sorted(int(x) for x in df.sinif.unique())
    sel_s = c1.selectbox(
        "Sınıf", siniflar, key=f"{key}_sinif",
        format_func=lambda x: x if x == "Tümü" else f"{x}. Sınıf",
    )
    base = df if sel_s == "Tümü" else df[df.sinif == sel_s]
    subeler = ["Tümü"] + sorted(base.sube.unique().tolist(), key=tr_key)
    sel_b = c2.selectbox("Şube", subeler, key=f"{key}_sube", format_func=lambda x: x if x == "Tümü" else f"{x} Şubesi")
    return base if sel_b == "Tümü" else base[base.sube == sel_b]


def _sanitize_df(df):
    out = df.copy()
    def fix(v):
        return "'" + v if isinstance(v, str) and v[:1] in ("=", "+", "-", "@", "\t", "\r") else v
    for col in out.columns:
        if not pd.api.types.is_numeric_dtype(out[col]):
            out[col] = out[col].map(fix)
    return out


def to_csv_bytes(df):
    return _sanitize_df(df).to_csv(index=False, sep=";", decimal=",").encode("utf-8-sig")


def to_xlsx_bytes(sheets):
    try:
        from openpyxl.styles import Alignment, Font, PatternFill
        from openpyxl.utils import get_column_letter
    except ImportError:
        return None
    buf = io.BytesIO()
    try:
        with pd.ExcelWriter(buf, engine="openpyxl") as xw:
            for name, df in sheets.items():
                name = name[:31]
                safe = _sanitize_df(df)
                safe.to_excel(xw, sheet_name=name, index=False)
                ws = xw.sheets[name]
                ws.freeze_panes = "A2"
                for cell in ws[1]:
                    cell.fill = PatternFill("solid", fgColor="A9794F")
                    cell.font = Font(bold=True, color="FFFFFF")
                    cell.alignment = Alignment(horizontal="center", vertical="center")
                for i, col in enumerate(safe.columns, start=1):
                    longest = max([len(str(col))] + [len(str(v)) for v in safe[col].head(500)])
                    ws.column_dimensions[get_column_letter(i)].width = min(max(longest + 3, 8), 45)
    except Exception:
        return None
    return buf.getvalue()


def export_buttons(df, base_name, key, sheet="Veri"):
    stamp = date.today().strftime("%Y%m%d")
    c1, c2, _ = st.columns([1.3, 1.3, 3])
    xlsx = to_xlsx_bytes({sheet: df})
    if xlsx is not None:
        c1.download_button("Excel indir (.xlsx)", xlsx, file_name=f"{base_name}_{stamp}.xlsx",
                           mime=XLSX_MIME, key=f"{key}_xlsx", use_container_width=True)
    else:
        c1.caption("Excel için openpyxl gerekli")
    c2.download_button("CSV indir (.csv)", to_csv_bytes(df), file_name=f"{base_name}_{stamp}.csv",
                       mime="text/csv", key=f"{key}_csv", use_container_width=True)


def page_dashboard():
    welcome_banner()
    students = load_students()
    matches = load_matches(active_only=True)

    if students.empty:
        st.markdown("### Öğrenci listenizi yükleyin")
        st.info("Henüz öğrenci listesi yüklenmemiş. Veri girişi ve yükleme işlemleri için sol menüden **Yönetici Paneli**'ne giderek giriş yapın.")
        if st.button("Yönetici Paneline Git", type="primary"):
            goto(PG_ADMIN)
        return

    stats = compute_stats(students, matches)
    summary = branch_summary(stats)

    active = stats[stats.mac > 0]
    avg_txt = f"%{active.basari.mean():.0f}" if len(active) else "—"
    ranked = summary[summary.mac > 0].sort_values(["basari", "mac"], ascending=False)
    if ranked.empty:
        best_txt, best_sub = "—", "Henüz maç kaydı yok"
    else:
        b = ranked.iloc[0]
        best_txt, best_sub = f"{int(b.sinif)}-{b.sube}", f"%{b.basari:.0f} başarı oranı"
    stat_cards([
        ("👩‍🎓", "Toplam Öğrenci", len(students),
         f"{len(summary)} şubede" + (f" · {count_archived()} arşivde" if count_archived() else "")),
        ("⚔️", "Toplam Maç", len(matches), "kayıtlı karşılaşma"),
        ("📊", "Ortalama Başarı", avg_txt, f"{len(active)} aktif öğrenci"),
        ("🏆", "En Başarılı Sınıf", best_txt, best_sub),
    ])

    st.markdown('<div class="sec-t">Hızlı Menü & İnceleme</div>', unsafe_allow_html=True)
    r1a, r1b = st.columns(2)
    quick_action(r1a, "qa_match", "⚔️", "Maç Girişi & Eşleştirme",
                 "Yönetici girişiyle yeni maç kaydedin veya otomatik eşleştirin.", PG_MATCH, "manual")
    quick_action(r1b, "qa_auto", "⚖️", "Sıralama ve Geçmiş",
                 "Tüm maç geçmişini, puanları ve liderlik tablosunu inceleyin.", PG_BOARD)
    r2a, r2b = st.columns(2)
    quick_action(r2a, "qa_students", "👩‍🎓", "Şube Paneli",
                 "Sınıf ve şubelere göre başarıları ve öğrenci listelerini görüntüleyin.", PG_BRANCH)
    quick_action(r2b, "qa_reports", "📈", "Bireysel Oyunlar",
                 "Kart ve seviye takiplerini inceleyin ya da karne görüntüleyin.", PG_INDIV)
    r3a, r3b = st.columns(2)
    quick_action(r3a, "qa_indiv", "puzzle", "Grup ve Turnuva",
                 "Toplu oyun gruplarını ve turnuva skor tablolarını görüntüleyin.", PG_GROUP)
    quick_action(r3b, "qa_group", "users", "Oyun Kütüphanesi",
                 "Kategorilere göre akıl ve zeka oyunları arşivini inceleyin.", PG_LIB)


def page_branch():
    hero("Şube Kontrol Paneli", "Sınıf mevcudu, öğrenci listesi ve şube başarısı tek ekranda", "🏫")
    students = load_students()
    if students.empty:
        empty_state()
        return
    stats = compute_stats(students, load_matches(active_only=True))
    f = class_branch_filter(stats, "br")
    if f.empty:
        st.warning("Seçilen filtreye uygun öğrenci yok.")
        return

    summary = branch_summary(f)
    played = int((f.mac > 0).sum())
    wins, draws, macs = f.galibiyet.sum(), f.beraberlik.sum(), f.mac.sum()
    avg = round((wins + 0.5 * draws) / macs * 100, 1) if macs else 0
    stat_cards([
        ("👥", "Sınıf Mevcudu", len(f)),
        ("🎯", "Maça Katılan", played),
        ("📊", "Genel Başarı", f"%{avg:.0f}"),
    ])
    st.write("")

    st.markdown("### Şube Kartları")
    for i in range(0, len(summary), 4):
        cols = st.columns(4)
        for col, r in zip(cols, summary.iloc[i:i + 4].itertuples()):
            col.markdown(
                f'<div class="bcard"><div class="bhead"><span class="btag">{r.sinif}-{esc(r.sube)}</span>'
                f'<span class="bpct">%{r.basari:.0f}</span></div>'
                f'<div class="bmeta">{r.mevcut} öğrenci · {r.aktif} aktif</div>{bar_html(r.basari)}</div>',
                unsafe_allow_html=True,
            )

    st.markdown("### Öğrenci Listesi")
    q = st.text_input("Öğrenci ara", key="br_q", placeholder="Ad veya soyad yazın...")
    table = f
    if q.strip():
        table = f[f.ad_soyad.map(tr_upper).str.contains(re.escape(tr_upper(q.strip())), regex=True)]
    show = table.rename(columns={
        "ogrenci_no": "No", "ad_soyad": "Ad Soyad", "sinif": "Sınıf", "sube": "Şube",
        "mac": "Maç", "galibiyet": "G", "beraberlik": "B", "maglubiyet": "M", "puan": "Puan", "basari": "Başarı %",
    })[["No", "Ad Soyad", "Sınıf", "Şube", "Maç", "G", "B", "M", "Puan", "Başarı %"]]
    st.dataframe(
        show, hide_index=True, use_container_width=True,
        column_config={"Başarı %": st.column_config.ProgressColumn("Başarı %", min_value=0, max_value=100, format="%.0f%%")},
    )
    if show.empty:
        st.caption("Aramanızla eşleşen öğrenci yok.")
    else:
        export_buttons(show, "ogrenci_listesi", "br", sheet="Öğrenci Listesi")


def save_manual(sonuc):
    if not is_admin():
        flash("error", "Veri girişi için Yönetici Paneli'nden giriş yapmalısınız.")
        return
    ok, msg = add_match(
        st.session_state.get("match_game"),
        st.session_state.get("man_p1"),
        st.session_state.get("man_p2"),
        sonuc,
        st.session_state.get("match_date"),
    )
    if ok:
        st.session_state["man_p1"] = None
        st.session_state["man_p2"] = None
        flash("success", "Maç sonucu kaydedildi.")
    else:
        flash("error", msg)


def save_auto(p1, p2, sonuc):
    if not is_admin():
        flash("error", "Veri girişi için Yönetici Paneli'nden giriş yapmalısınız.")
        return
    ok, msg = add_match(st.session_state.get("match_game"), p1, p2, sonuc, st.session_state.get("match_date"))
    if ok:
        st.session_state["auto_pairs"] = [
            p for p in st.session_state.get("auto_pairs", []) if (p["p1"], p["p2"]) != (p1, p2)
        ]
        st.toast("Maç kaydedildi")
    else:
        flash("error", msg)


def skip_auto(p1, p2):
    st.session_state["auto_pairs"] = [
        p for p in st.session_state.get("auto_pairs", []) if (p["p1"], p["p2"]) != (p1, p2)
    ]


def clear_auto():
    st.session_state["auto_pairs"] = []
    st.session_state["auto_rest"] = []


def page_match():
    hero("Maç Girişi", "Yönetici şifresiyle maç kaydedin veya otomatik eşleştirme yapın", "⚔️")
    students = load_students()
    if students.empty:
        empty_state()
        return

    if not is_admin():
        st.warning("🔒 **Salt Okunur Mod:** Maç kaydetmek ve yeni veri girişi yapmak için sol menüden **Yönetici Paneli**'ne girerek oturum açmalısınız. Aşağıdan mevcut maçları ve eşleştirmeleri inceleyebilirsiniz.")

    games = load_games()
    pair_games = games[games.kategori == PAIR_CATEGORY]
    gname = dict(zip(pair_games.id, pair_games.ad))
    g_col, d_col = st.columns([3, 2])
    g_col.selectbox("Oyun", list(gname.keys()), key="match_game", format_func=lambda i: gname[i])
    d_col.date_input(
        "Maç Tarihi", value=date.today(), max_value=date.today(),
        format="DD.MM.YYYY", key="match_date",
    )

    stats = compute_stats(students, load_matches(active_only=True))
    labels = student_labels(students)
    info = {int(r.id): r for r in stats.itertuples()}
    t_manual, t_auto = "Manuel Eşleştirme", "Otomatik Akıllı Eşleştirme"
    if st.session_state.get("match_tab") == "auto":
        tab_auto, tab_manual = st.tabs([t_auto, t_manual])
    else:
        tab_manual, tab_auto = st.tabs([t_manual, t_auto])

    with tab_manual:
        pool = class_branch_filter(students, "man")
        ids = [int(i) for i in pool.id]
        p1 = st.selectbox(
            "1. Oyuncu", ids, index=None, key="man_p1", placeholder="İsim yazarak arayın...",
            format_func=lambda i: labels[i],
        )
        ids2 = [i for i in ids if i != p1]
        p2 = st.selectbox(
            "2. Oyuncu", ids2, index=None, key="man_p2", placeholder="İsim yazarak arayın...",
            format_func=lambda i: labels[i],
        )
        if p1 is not None and p2 is not None:
            a, b = info[p1], info[p2]
            st.markdown(
                f'<div class="vs"><div class="pl"><b>{esc(a.ad_soyad)}</b><span>{a.sinif}-{esc(a.sube)} · seviye %{a.seviye*100:.0f}</span></div>'
                f'<div class="x">VS</div>'
                f'<div class="pl"><b>{esc(b.ad_soyad)}</b><span>{b.sinif}-{esc(b.sube)} · seviye %{b.seviye*100:.0f}</span></div></div>',
                unsafe_allow_html=True,
            )
        st.caption("Yönetici girişi yapıldıysa kazananı işaretlediğiniz anda maç kaydedilir.")
        ready = p1 is not None and p2 is not None and is_admin()
        c1, c2, c3 = st.columns(3)
        c1.button("1. Oyuncu Kazandı", key="m_w1", disabled=not ready, use_container_width=True, on_click=save_manual, args=("1",))
        c2.button("Berabere", key="m_d", disabled=not ready, use_container_width=True, on_click=save_manual, args=("D",))
        c3.button("2. Oyuncu Kazandı", key="m_w2", disabled=not ready, use_container_width=True, on_click=save_manual, args=("2",))
        if not is_admin() and p1 and p2:
            st.info("Maç kaydetmek için Yönetici Paneli'nden giriş yapmalısınız.")

    with tab_auto:
        st.write("Seçilen şube/sınıftaki öğrencilerin başarı oranlarına bakılır; benzer seviyedekiler birbiriyle eşleştirilir.")
        pool = class_branch_filter(students, "auto")
        same_class = st.checkbox("Sadece aynı sınıftakileri eşleştir", value=True, key="auto_same")
        if st.button("Aynı Seviyedekileri Otomatik Eşleştir", type="primary", key="auto_go"):
            rating = {int(r.id): float(info[int(r.id)].seviye) for r in pool.itertuples()}
            already = played_pairs(st.session_state.get("match_game"))
            groups = [pool] if not same_class else [g for _, g in pool.groupby("sinif")]
            pairs, rest = [], []
            for g in groups:
                p, r = auto_pair([int(i) for i in g.id], rating, already)
                pairs += p
                rest += r
            st.session_state["auto_pairs"] = [
                {"p1": a, "p2": b, "gap": abs(rating[a] - rating[b])} for a, b in pairs
            ]
            st.session_state["auto_rest"] = rest
            if not pairs:
                flash("warning", "Eşleştirme için en az iki öğrenci gerekir.")
                st.rerun()

        pairs = st.session_state.get("auto_pairs", [])
        rest = st.session_state.get("auto_rest", [])
        if pairs:
            head, btn = st.columns([4, 1])
            head.markdown(f"#### Önerilen Maçlar ({len(pairs)})")
            btn.button("Listeyi temizle", key="auto_clear", on_click=clear_auto, use_container_width=True)
            for p in pairs:
                a, b = info[p["p1"]], info[p["p2"]]
                with st.container(border=True):
                    st.markdown(
                        f'<div class="vs" style="margin:0;border:none;padding:.2rem 0 .4rem 0;background:transparent">'
                        f'<div class="pl"><b>{esc(a.ad_soyad)}</b><span>{a.sinif}-{esc(a.sube)} · seviye %{a.seviye*100:.0f}</span></div>'
                        f'<div class="x">VS</div>'
                        f'<div class="pl"><b>{esc(b.ad_soyad)}</b><span>{b.sinif}-{esc(b.sube)} · seviye %{b.seviye*100:.0f}</span></div></div>',
                        unsafe_allow_html=True,
                    )
                    k = f"{p['p1']}_{p['p2']}"
                    c1, c2, c3, c4 = st.columns(4)
                    can_save = is_admin()
                    c1.button("1. Kazandı", key=f"a1_{k}", disabled=not can_save, use_container_width=True, on_click=save_auto, args=(p["p1"], p["p2"], "1"))
                    c2.button("Berabere", key=f"ad_{k}", disabled=not can_save, use_container_width=True, on_click=save_auto, args=(p["p1"], p["p2"], "D"))
                    c3.button("2. Kazandı", key=f"a2_{k}", disabled=not can_save, use_container_width=True, on_click=save_auto, args=(p["p1"], p["p2"], "2"))
                    c4.button("Atla", key=f"as_{k}", use_container_width=True, on_click=skip_auto, args=(p["p1"], p["p2"]))
        if rest:
            names = ", ".join(info[i].ad_soyad for i in rest if i in info)
            st.caption(f"Eşleşemeyen (tek kalan) öğrenci(ler): {names}")


RANK_COLS = ["Sıra", "Ad Soyad", "Sınıf", "Şube", "Maç", "G", "B", "M", "Puan", "Başarı %"]
RANK_RENAME = {
    "ad_soyad": "Ad Soyad", "sinif": "Sınıf", "sube": "Şube", "mac": "Maç",
    "galibiyet": "G", "beraberlik": "B", "maglubiyet": "M", "puan": "Puan", "basari": "Başarı %",
}
HIST_COLS = ["Kayıt", "Tarih", "Oyun", "1. Oyuncu", "Şube 1", "2. Oyuncu", "Şube 2", "Sonuç"]


def ranking_frame(stats):
    rank = stats[stats.mac > 0].sort_values(["puan", "basari", "mac"], ascending=False).reset_index(drop=True)
    if rank.empty:
        return pd.DataFrame(columns=RANK_COLS)
    rank.insert(0, "Sıra", range(1, len(rank) + 1))
    return rank.rename(columns=RANK_RENAME)[RANK_COLS]


def branch_frame(stats):
    s = branch_summary(stats)
    return s.rename(columns={
        "sinif": "Sınıf", "sube": "Şube", "mevcut": "Mevcut", "aktif": "Aktif", "galibiyet": "G",
        "beraberlik": "B", "mac": "Maç", "basari": "Başarı %",
    })


def result_text(r):
    return {"1": f"{r.oyuncu1} kazandı", "2": f"{r.oyuncu2} kazandı", "D": "Berabere"}[r.sonuc]


def history_frame(hist):
    if hist.empty:
        return pd.DataFrame(columns=HIST_COLS)
    h = hist.copy()
    h["tarih"] = h["tarih"].map(fmt_tarih)
    h["Sonuç"] = [result_text(r) for r in hist.itertuples()]
    return h.rename(columns={
        "id": "Kayıt", "tarih": "Tarih", "oyun": "Oyun", "oyuncu1": "1. Oyuncu", "sube1": "Şube 1",
        "oyuncu2": "2. Oyuncu", "sube2": "Şube 2",
    })[HIST_COLS]


def full_report_xlsx(students, game_id):
    stats = compute_stats(students, load_matches(game_id, active_only=True))
    return to_xlsx_bytes({
        "Sıralama": ranking_frame(stats),
        "Şube Özeti": branch_frame(stats),
        "Maç Geçmişi": history_frame(match_history(game_id)),
    })


def ask_delete_match(mid):
    st.session_state["del_pending"] = int(mid)


def cancel_delete_match():
    st.session_state.pop("del_pending", None)


def confirm_delete_match(mid):
    st.session_state.pop("del_pending", None)
    try:
        removed = delete_match(mid)
    except PermissionError as e:
        flash("error", str(e))
        return
    if removed:
        flash("success", "Maç kaydı kalıcı olarak silindi; sıralama ve istatistikler güncellendi.")
    else:
        flash("warning", "Kayıt bulunamadı.")


def history_tab(gsel):
    order_sel = st.radio(
        "Sıralama", ["Tarihe göre: yeniden eskiye", "Tarihe göre: eskiden yeniye"],
        horizontal=True, key="hist_order",
    )
    show_arch = st.checkbox("Arşivdeki öğrencilerin geçmiş maçlarını da göster", key="hist_arch",
                            help="İşaretlenmezse, iki oyuncusu da arşivde olan maçlar listelenmez.")
    hist = match_history(gsel, newest_first="yeniden eskiye" in order_sel, include_archived=show_arch)
    if hist.empty:
        st.caption("Henüz maç kaydı yok.")
        return
    show = history_frame(hist)
    export_buttons(show, "mac_gecmisi", "lb_hist", sheet="Maç Geçmişi")

    if not is_admin():
        st.dataframe(show, hide_index=True, use_container_width=True)
        return

    st.caption(f"Yönetici modu · {len(hist)} kayıt. Yanlış girilen maçı 🗑️ Sil ile kalıcı olarak silebilirsiniz.")
    pend = st.session_state.get("del_pending")
    if pend is not None:
        row = hist[hist.id == pend]
        if row.empty:
            st.session_state.pop("del_pending", None)
        else:
            r = row.iloc[0]
            st.markdown(
                '<div class="confirm-del"><b>Bu maç kalıcı olarak silinecek:</b><br>'
                f'#{int(r["id"])} · {esc(fmt_tarih(r["tarih"]))} · {esc(r["oyun"])} · '
                f'{esc(r["oyuncu1"])} ({esc(r["sube1"])}) – {esc(r["oyuncu2"])} ({esc(r["sube2"])}) · '
                f'{esc(result_text(r))}<br>Bu işlem geri alınamaz.</div>',
                unsafe_allow_html=True,
            )
            b1, b2, _ = st.columns([1.5, 1, 3])
            b1.button("Evet, kalıcı olarak sil", key="confirm_del_btn", type="primary",
                      on_click=confirm_delete_match, args=(int(r["id"]),), use_container_width=True)
            b2.button("Vazgeç", key="cancel_del_btn", on_click=cancel_delete_match, use_container_width=True)

    pages = max(1, math.ceil(len(hist) / PAGE_SIZE))
    page_no = 1
    if pages > 1:
        page_no = int(st.number_input(f"Sayfa (1-{pages})", min_value=1, max_value=pages, value=1, step=1,
                                      key=f"hist_pg_{pages}"))
    chunk = hist.iloc[(page_no - 1) * PAGE_SIZE: page_no * PAGE_SIZE]
    for r in chunk.itertuples():
        left, right = st.columns([8, 1.4])
        left.markdown(
            f'<div class="mrow"><span class="md">{esc(fmt_tarih(r.tarih))}</span>'
            f'<span class="mg">{esc(r.oyun)}</span>'
            f'<span class="mp">{esc(r.oyuncu1)} <i>({esc(r.sube1)})</i><b class="vsx">VS</b>'
            f'{esc(r.oyuncu2)} <i>({esc(r.sube2)})</i></span>'
            f'<span class="mr">{esc(result_text(r))}</span></div>',
            unsafe_allow_html=True,
        )
        right.button("🗑️ Sil", key=f"delm_{int(r.id)}", help="Bu maçı kalıcı olarak sil",
                     on_click=ask_delete_match, args=(int(r.id),), use_container_width=True)


def page_leaderboard():
    hero("Sıralama & Maç Geçmişi", "Puan: galibiyet 3, beraberlik 1, mağlubiyet 0", "🏆")
    students = load_students()
    if students.empty:
        empty_state()
        return
    games = load_games()
    pair_games = games[games.kategori == PAIR_CATEGORY]
    gname = {None: "Tüm Oyunlar", **dict(zip(pair_games.id, pair_games.ad))}
    gsel = st.selectbox("Oyun", list(gname.keys()), format_func=lambda i: gname[i], key="lb_game")

    report = full_report_xlsx(students, gsel)
    if report is not None:
        st.download_button(
            "Tam Raporu Excel İndir (Sıralama + Şube Özeti + Maç Geçmişi)", report,
            file_name=f"rapor_{date.today().strftime('%Y%m%d')}.xlsx", mime=XLSX_MIME, key="lb_full_report",
        )

    tab1, tab2 = st.tabs(["Sıralama", "Maç Geçmişi"])
    with tab1:
        stats = compute_stats(students, load_matches(gsel, active_only=True))
        f = class_branch_filter(stats, "lb")
        show = ranking_frame(f)
        if show.empty:
            st.caption("Bu filtre için henüz maç kaydı yok.")
        else:
            st.dataframe(
                show, hide_index=True, use_container_width=True,
                column_config={"Başarı %": st.column_config.ProgressColumn("Başarı %", min_value=0, max_value=100, format="%.0f%%")},
            )
            export_buttons(show, "siralama", "lb_rank", sheet="Sıralama")
    with tab2:
        history_tab(gsel)


def page_library():
    hero("Oyun Kütüphanesi", "Kategorilere göre akıl ve zeka oyunları", "🎲")
    games = load_games()
    with db() as c:
        cnt = dict(c.execute(
            "SELECT game_id, COUNT(*) FROM matches WHERE p1_id IN (SELECT id FROM students WHERE arsiv=0) "
            "OR p2_id IN (SELECT id FROM students WHERE arsiv=0) GROUP BY game_id").fetchall())
        pcnt = dict(c.execute(
            "SELECT p.game_id, COUNT(DISTINCT p.student_id) FROM progress p JOIN students s ON s.id=p.student_id "
            "WHERE s.arsiv=0 GROUP BY p.game_id").fetchall())
        gcnt = dict(c.execute("SELECT game_id, COUNT(*) FROM game_groups GROUP BY game_id").fetchall())
    cols = st.columns(3)
    for col, kategori in zip(cols, GAME_LIBRARY.keys()):
        sub = games[games.kategori == kategori]
        chips = "".join(
            f'<span class="chip">{esc(r.ad)}' + (f'<i>{cnt.get(r.id, 0)} maç</i>' if kategori == PAIR_CATEGORY
                                       else f'<i>{pcnt.get(r.id, 0)} öğrenci</i>' if kategori == INDIV_CATEGORY
                                       else f'<i>{gcnt.get(r.id, 0)} grup</i>' if kategori == GROUP_CATEGORY else "") + "</span>"
            for r in sub.itertuples()
        )
        col.markdown(
            f'<div class="lib"><h3>{CATEGORY_ICONS[kategori]} {esc(kategori)}</h3>{chips}'
            f'<div class="bmeta" style="margin-top:.8rem">{len(sub)} oyun</div></div>',
            unsafe_allow_html=True,
        )
    extra = [k for k in games.kategori.unique() if k not in GAME_LIBRARY]
    for k in extra:
        st.markdown(f"#### {esc(k)}")
        st.markdown("".join(f'<span class="chip">{esc(r.ad)}</span>' for r in games[games.kategori == k].itertuples()),
                    unsafe_allow_html=True)
    st.caption("İkili oyunlar maç girişiyle, bireysel oyunlar kart/seviye ilerlemesiyle, toplu oyunlar grup ve turnuva skorlarıyla takip edilir.")


def _game_label_map(games):
    order = {INDIV_CATEGORY: 0, GROUP_CATEGORY: 1}
    suffix = {INDIV_CATEGORY: "", GROUP_CATEGORY: " (Toplu)", PAIR_CATEGORY: " (İkili)"}
    g = games.assign(_o=games.kategori.map(lambda k: order.get(k, 2))).sort_values(["_o", "id"])
    return {int(r.id): r.ad + suffix.get(r.kategori, f" ({r.kategori})") for r in g.itertuples()}


def bump(key):
    st.session_state[key] = st.session_state.get(key, 0) + 1


def progress_entry_tab(students, games):
    if not is_admin():
        st.warning("🔒 **Salt Okunur Mod:** Bireysel ilerleme verisi girmek için sol menüden **Yönetici Paneli**'ne girerek oturum açmalısınız.")
        return
    labels = _game_label_map(games)
    c1, c2 = st.columns([3, 2])
    gid = c1.selectbox("Oyun", list(labels.keys()), format_func=lambda i: labels[i], key="pe_game")
    tarih = c2.date_input("Kayıt tarihi", value=date.today(), max_value=date.today(),
                          format="DD.MM.YYYY", key="pe_date")
    pool = class_branch_filter(students, "pe")
    if pool.empty:
        st.warning("Seçilen filtreye uygun öğrenci yok.")
        return
    cur = latest_progress(load_progress(game_id=gid))
    kart_map = dict(zip(cur.student_id, cur.kart)) if not cur.empty else {}
    sev_map = dict(zip(cur.student_id, cur.seviye)) if not cur.empty else {}
    ids = [int(i) for i in pool.id]
    base = pd.DataFrame({
        "Ad Soyad": pool.ad_soyad.values,
        "Sınıf-Şube": (pool.sinif.astype(str) + "-" + pool.sube).values,
        "Kart": pd.array([_to_int(kart_map.get(i)) for i in ids], dtype="Int64"),
        "Seviye": [_nz(sev_map.get(i)) or "" for i in ids],
    }, index=ids)
    ekey = f"pe_ed_{gid}_{st.session_state.get('pe_sinif')}_{st.session_state.get('pe_sube')}_{st.session_state.get('pe_ver', 0)}"
    st.caption("Kart ve/veya seviye hücresini düzenleyin; yalnızca değiştirdiğiniz satırlar yeni kayıt olarak eklenir.")
    edited = st.data_editor(
        base, key=ekey, hide_index=True, use_container_width=True, disabled=["Ad Soyad", "Sınıf-Şube"],
        column_config={
            "Kart": st.column_config.NumberColumn("Kart", min_value=0, step=1, format="%d"),
            "Seviye": st.column_config.TextColumn("Seviye", max_chars=40),
        },
    )
    changes = []
    for sid in base.index:
        ok, nk = _to_int(base.at[sid, "Kart"]), _to_int(edited.at[sid, "Kart"])
        os_, ns = base.at[sid, "Seviye"] or "", _nz(edited.at[sid, "Seviye"]) or ""
        if ok != nk or os_ != ns:
            changes.append((sid, nk, ns))
    if st.button(f"Değişiklikleri Kaydet ({len(changes)})", type="primary", key="pe_save", disabled=not changes):
        errors = 0
        for sid, nk, ns in changes:
            ok, _ = save_progress(sid, gid, nk, ns, tarih)
            errors += 0 if ok else 1
        flash("success" if not errors else "warning",
              f"{len(changes) - errors} öğrencinin ilerlemesi kaydedildi." + (f" {errors} kayıt hatalıydı." if errors else ""))
        bump("pe_ver")
        st.rerun()


def progress_table_tab(students, games):
    labels = _game_label_map(games)
    gid = st.selectbox("Oyun", list(labels.keys()), format_func=lambda i: labels[i], key="pt_game")
    pool = class_branch_filter(students, "pt")
    only = st.checkbox("Yalnızca kaydı olan öğrenciler", value=True, key="pt_only")
    prog = load_progress(game_id=gid)
    cur = latest_progress(prog).rename(columns={"student_id": "id"})
    t = pool[["id", "ad_soyad", "sinif", "sube"]].copy()
    if not cur.empty and "id" in cur.columns:
        cur = cur.loc[:, ~cur.columns.duplicated()]

    t = t.merge(cur[["id", "kart", "seviye", "tarih", "kaynak"]], on="id", how="left") if not cur.empty else t.assign(
        kart=None, seviye=None, tarih=None, kaynak=None)
    base = latest_progress(prog[prog.kaynak == "gecis"]).rename(columns={"student_id": "id", "kart": "kart_gecis"}) \
        if not prog.empty else pd.DataFrame()

    if not base.empty and "id" in base.columns and "kart_gecis" in base.columns:
        base_clean = base[["id", "kart_gecis"]].drop_duplicates(subset=["id"]).copy()
        if base_clean.columns.duplicated().any():
            base_clean = base_clean.loc[:, ~base_clean.columns.duplicated()]
        t = t.merge(base_clean, on="id", how="left", validate="many_to_one")
    else:
        t["kart_gecis"] = None

    t["kart"] = pd.to_numeric(t["kart"], errors="coerce").astype("Int64")
    t["kart_gecis"] = pd.to_numeric(t["kart_gecis"], errors="coerce").astype("Int64")
    t["fark"] = (t.kart - t.kart_gecis).where(t.kaynak != "gecis")
    t["has"] = t.kart.notna() | t.seviye.map(lambda v: _nz(v) is not None)
    shown = t[t.has] if only else t
    if shown.empty:
        st.caption("Bu filtre için ilerleme kaydı yok.")
        return
    with_kart = shown.kart.dropna()
    stat_cards([
        ("👥", "Kayıtlı Öğrenci", int(shown.has.sum())),
        ("📊", "Ortalama Kart", f"{with_kart.mean():.1f}" if len(with_kart) else "—"),
        ("🏆", "En Yüksek Kart", int(with_kart.max()) if len(with_kart) else "—"),
        ("📈", "Bu Yıl İlerleyen", int((shown.fark.fillna(0) > 0).sum()), "geçen yıla göre kartı artan"),
    ])
    st.write("")
    out = shown.sort_values(["kart", "ad_soyad"], ascending=[False, True], na_position="last")
    out = pd.DataFrame({
        "Ad Soyad": out.ad_soyad, "Sınıf": out.sinif, "Şube": out.sube, "Kart": out.kart, "Seviye": out.seviye.map(lambda v: _nz(v) or ""),
        "Geçen Yıl Kartı": out.kart_gecis, "Fark": out.fark,
        "Son Güncelleme": out.tarih.map(lambda v: fmt_tarih(v) if _nz(v) else "—"),
        "Kaynak": out.kaynak.map(lambda v: PROG_KAYNAK.get(v, "—")),
    })
    st.dataframe(out, hide_index=True, use_container_width=True)
    export_buttons(out, "bireysel_ilerleme", "pt", sheet="İlerleme")


def karne_tab(students, games):
    st.caption("Karnede yalnızca aktif öğrenciler listelenir.")
    pool = class_branch_filter(students, "kr")
    labels = student_labels(pool)
    sid = st.selectbox("Öğrenci", list(labels.keys()), index=None, key="kr_sel",
                       format_func=lambda i: labels[i], placeholder="İsim yazarak arayın...")
    if sid is None:
        return
    stats = compute_stats(students, load_matches(active_only=True))
    me = stats[stats.id == sid].iloc[0]
    sc = group_scores_df()
    mine = sc[(sc.student_id == sid)]
    st.markdown(f'<div class="sec-t">{esc(me.ad_soyad)} · {int(me.sinif)}-{esc(me.sube)}</div>', unsafe_allow_html=True)
    stat_cards([
        ("⚔️", "İkili Maç", int(me.mac), f"{int(me.galibiyet)} G · {int(me.beraberlik)} B · {int(me.maglubiyet)} M"),
        ("📊", "Başarı", f"%{me.basari:.0f}"),
        ("🎯", "Grup Kartı", int(mine.kart.sum()) if not mine.empty else 0),
        ("🏆", "Grup Puanı", int(mine.puan.sum()) if not mine.empty else 0),
    ])
    prog = load_progress(student_id=sid)
    cur = latest_progress(prog)
    st.markdown('<div class="sec-t">Oyun İlerlemesi (Kart / Seviye)</div>', unsafe_allow_html=True)
    cur_df = pd.DataFrame(columns=["Oyun", "Kart", "Seviye", "Geçen Yıl Kartı", "Fark", "Son Güncelleme"])
    hist_df = pd.DataFrame(columns=["Tarih", "Oyun", "Kart", "Seviye", "Kaynak", "Dönem"])
    if cur.empty:
        st.caption("Bu öğrenci için ilerleme kaydı yok.")
    else:
        gecis = latest_progress(prog[prog.kaynak == "gecis"])
        gk = dict(zip(gecis.game_id, gecis.kart)) if not gecis.empty else {}
        rows = []
        for r in cur.sort_values("oyun").itertuples():
            kg = _to_int(gk.get(r.game_id))
            kk = _to_int(r.kart)
            rows.append({
                "Oyun": r.oyun, "Kart": kk, "Seviye": _nz(r.seviye) or "", "Geçen Yıl Kartı": kg,
                "Fark": (kk - kg) if (kk is not None and kg is not None and r.kaynak != "gecis") else None,
                "Son Güncelleme": fmt_tarih(r.tarih),
            })
        cur_df = pd.DataFrame(rows)
        st.dataframe(cur_df, hide_index=True, use_container_width=True)
        h = prog.sort_values(["tarih", "id"], ascending=[False, False])
        hist_df = pd.DataFrame({
            "Tarih": h.tarih.map(fmt_tarih), "Oyun": h.oyun, "Kart": h.kart.map(_to_int),
            "Seviye": h.seviye.map(lambda v: _nz(v) or ""), "Kaynak": h.kaynak.map(lambda v: PROG_KAYNAK.get(v, "—")),
            "Dönem": h.donem.map(lambda v: _nz(v) or ""),
        })
        with st.expander("İlerleme geçmişi"):
            st.dataframe(hist_df, hide_index=True, use_container_width=True)
    st.markdown('<div class="sec-t">Grup ve Turnuva Skorları</div>', unsafe_allow_html=True)
    grp_df = pd.DataFrame(columns=["Oyun", "Turnuva", "Grup", "Kayıt", "Kart", "Puan"])
    if mine.empty:
        st.caption("Bu öğrenci için grup skoru kaydı yok.")
    else:
        g = mine.groupby(["oyun", "turnuva", "grup"], as_index=False).agg(
            Kayıt=("id", "count"), Kart=("kart", "sum"), Puan=("puan", "sum"))
        g["turnuva"] = g.turnuva.replace("", "—")
        grp_df = g.rename(columns={"oyun": "Oyun", "turnuva": "Turnuva", "grup": "Grup"})
        st.dataframe(grp_df, hide_index=True, use_container_width=True)
    xl = to_xlsx_bytes({"Oyun İlerlemesi": cur_df, "İlerleme Geçmişi": hist_df, "Grup Skorları": grp_df})
    if xl is not None:
        st.download_button("Karneyi Excel indir", xl, file_name=f"karne_{me.ogrenci_no}_{date.today().strftime('%Y%m%d')}.xlsx",
                           mime=XLSX_MIME, key="kr_xlsx")


def render_progress_import():
    if not is_admin():
        st.warning("🔒 **Salt Okunur Mod:** Geçiş verisi yüklemek için sol menüden **Yönetici Paneli**'ne girerek oturum açmalısınız.")
        return
    st.markdown(
        "Geçen yıldan kalan kart/seviye verilerini **Ogrenci_ID** bazlı Excel veya CSV ile toplu yükleyin."
    )
    tpl = progress_template_xlsx()
    if tpl is not None:
        st.download_button("Örnek şablonu indir (.xlsx)", tpl, file_name="gecis_verisi_sablonu.xlsx",
                           mime=XLSX_MIME, key="prg_tpl")
    up = st.file_uploader("Excel (.xlsx) veya CSV dosyası seçin", type=["xlsx", "xlsm", "csv"], key="prg_up")
    if up is None:
        return
    try:
        raw, cols = read_progress_file(up)
    except ValueError as e:
        st.error(str(e))
        return
    games = load_games()
    gname = _game_label_map(games)
    auto = auto_map_columns(raw, cols, games)
    sig = f"{up.name}_{up.size}"

    cand = []
    for col in raw.columns:
        if col in cols.values():
            continue
        vals = raw[col].dropna().astype(str)
        if vals.empty:
            continue
        if auto.get(col) or vals.str.len().mean() <= 40:
            cand.append(col)
    skipped = [str(c) for c in raw.columns if c not in cols.values() and c not in cand]

    st.markdown("**Sütun → Oyun eşleştirmesi**")
    mapping = {}
    with st.expander("Eşleştirmeyi göster / düzenle", expanded=True):
        for i, col in enumerate(cand):
            default = [g for g in auto.get(col, []) if g in gname]
            sel = st.multiselect(str(col).strip(), list(gname.keys()), default=default,
                                 format_func=lambda g: gname[g], key=f"prgmap_{sig}_{i}",
                                 placeholder="Aktarılmayacak")
            if sel:
                mapping[col] = sel

    if not mapping:
        st.info("Aktarılacak oyun sütunu seçilmedi.")
        return

    records, rep = build_progress_records(raw, cols, mapping)
    if not records:
        st.error("Eşleşen öğrenci veya aktarılacak değer bulunamadı.")
        return
    st.success(f"{rep['matched']} öğrenci eşleşti · {len(records)} oyun kaydı aktarıma hazır.")

    gmap = {int(r.id): r.ad for r in games.itertuples()}
    prev = pd.DataFrame([{
        "Öğrenci": rep["info"][r["student_id"]][0], "Sınıf-Şube": rep["info"][r["student_id"]][1],
        "Oyun": gmap[r["game_id"]], "Kart": r["kart"], "Seviye": r["seviye"] or "",
    } for r in records[:200]])
    st.dataframe(prev.head(15), hide_index=True, use_container_width=True)

    d1, d2 = st.columns(2)
    default_date = min(rep["ts_max"], date.today()) if rep["ts_max"] else date.today()
    tarih = d1.date_input("Verinin tarihi", value=default_date, max_value=date.today(), format="DD.MM.YYYY",
                          key=f"prg_date_{sig}")
    donem = d2.text_input("Dönem etiketi", value=prev_school_year(), key=f"prg_donem_{sig}")
    if st.button("Geçiş Verisini Aktar", type="primary", key=f"prg_go_{sig}"):
        n = import_progress(records, tarih, _clean(donem))
        flash("success", f"{n} ilerleme kaydı aktarıldı ({rep['matched']} öğrenci).")
        st.rerun()


def page_individual():
    hero("Bireysel Oyunlar", "Kart / seviye ilerleme takibi ve öğrenci karneleri", "🧩")
    students = load_students()
    games = load_games()
    t1, t2, t3, t4 = st.tabs(["İlerleme Girişi", "İlerleme Tablosu", "Öğrenci Karnesi", "Geçiş Verisi Yükle"])
    with t1:
        progress_entry_tab(students, games)
    with t2:
        if students.empty:
            empty_state()
        else:
            progress_table_tab(students, games)
    with t3:
        if students.empty:
            empty_state()
        else:
            karne_tab(students, games)
    with t4:
        render_progress_import()


def _add_branch(key, sinif, sube):
    df = load_students()
    ids = [int(i) for i in df[(df.sinif == sinif) & (df.sube == sube)].id]
    cur = list(st.session_state.get(key, []))
    st.session_state[key] = cur + [i for i in ids if i not in cur]


def member_picker(key, students, default_ids=None):
    labels = student_labels(students)
    if key not in st.session_state:
        st.session_state[key] = [int(i) for i in (default_ids or []) if int(i) in labels]
    st.session_state[key] = [i for i in st.session_state[key] if i in labels]
    c1, c2, c3 = st.columns([1, 1, 1.4])
    siniflar = sorted(int(x) for x in students.sinif.unique())
    s_sel = c1.selectbox("Hızlı ekle: Sınıf", siniflar, key=f"{key}_qs", format_func=lambda x: f"{x}. Sınıf")
    subeler = sorted(students[students.sinif == s_sel].sube.unique().tolist(), key=tr_key)
    b_sel = c2.selectbox("Şube", subeler, key=f"{key}_qb", format_func=lambda x: f"{x} Şubesi")
    c3.markdown('<div style="height:1.7rem"></div>', unsafe_allow_html=True)
    c3.button("Bu şubeyi ekle", key=f"{key}_qa", use_container_width=True, on_click=_add_branch, args=(key, s_sel, b_sel))
    return st.multiselect("Oyuncular", list(labels.keys()), key=key, format_func=lambda i: labels[i],
                          placeholder="İsim yazarak arayın...")


def create_group_cb():
    if not is_admin():
        flash("error", "Grup oluşturmak için Yönetici Paneli'nden giriş yapmalısınız.")
        return
    ok, msg = create_group(
        st.session_state.get("gc_name"), st.session_state.get("gc_game"), st.session_state.get("gc_turn"),
        st.session_state.get("gc_members", []), st.session_state.get("gc_date"),
    )
    if ok:
        st.session_state["gc_name"] = ""
        st.session_state["gc_members"] = []
    flash("success" if ok else "error", msg)


def group_create_tab(students, toplu):
    if not is_admin():
        st.warning("🔒 **Salt Okunur Mod:** Grup oluşturmak için sol menüden **Yönetici Paneli**'ne girerek oturum açmalısınız.")
        return
    gname = dict(zip(toplu.id, toplu.ad))
    c1, c2 = st.columns(2)
    c1.selectbox("Toplu oyun", list(gname.keys()), key="gc_game", format_func=lambda i: gname[i])
    c2.text_input("Grup adı", key="gc_name", placeholder="Örn. Kırmızı Takım", max_chars=60)
    c3, c4 = st.columns(2)
    c3.text_input("Turnuva adı (isteğe bağlı)", key="gc_turn", placeholder="Örn. Bahar Turnuvası", max_chars=60)
    c4.date_input("Oluşturma tarihi", value=date.today(), max_value=date.today(), format="DD.MM.YYYY", key="gc_date")
    n = len(member_picker("gc_members", students))
    st.button(f"Grubu Oluştur ({n} oyuncu)", type="primary", key="gc_go", on_click=create_group_cb)


def group_score_tab(students):
    if not is_admin():
        st.warning("🔒 **Salt Okunur Mod:** Grup skoru girmek için sol menüden **Yönetici Paneli**'ne girerek oturum açmalısınız.")
        groups = load_groups()
        if not groups.empty:
            labels = {int(r.id): group_label(r) + f"  ({r.uye} oyuncu)" for r in groups.itertuples()}
            gid = st.selectbox("Grup", list(labels.keys()), format_func=lambda i: labels[i], key="gs_group_view")
            sc = group_scores_df()
            sc = sc[(sc.group_id == gid) & (sc.arsiv == 0)]
            if not sc.empty:
                st.markdown("#### Grubun Mevcut Durumu")
                st.dataframe(player_standings(sc), hide_index=True, use_container_width=True)
        return

    groups = load_groups()
    if groups.empty:
        st.info("Henüz grup yok. Yönetici girişi yaparak 'Grup Oluştur' sekmesinden bir grup kurabilirsiniz.")
        return
    labels = {int(r.id): group_label(r) + f"  ({r.uye} oyuncu)" for r in groups.itertuples()}
    gid = st.selectbox("Grup", list(labels.keys()), format_func=lambda i: labels[i], key="gs_group")
    c1, c2 = st.columns([2, 3])
    tarih = c1.date_input("Tarih", value=date.today(), max_value=date.today(), format="DD.MM.YYYY", key="gs_date")
    tur = c2.text_input("Tur / oturum adı (isteğe bağlı)", key="gs_tur", placeholder="Örn. 1. Tur", max_chars=40)
    mem = group_members_df(gid)
    if mem.empty:
        st.warning("Bu grubun aktif oyuncusu yok.")
        return
    ids = [int(i) for i in mem.id]
    base = pd.DataFrame({
        "Ad Soyad": mem.ad_soyad.values,
        "Sınıf-Şube": (mem.sinif.astype(str) + "-" + mem.sube).values,
        "Kart": pd.array([None] * len(ids), dtype="Int64"),
        "Puan": pd.array([None] * len(ids), dtype="Int64"),
    }, index=ids)
    edited = st.data_editor(
        base, key=f"gs_ed_{gid}_{st.session_state.get('gs_ver', 0)}", hide_index=True, use_container_width=True,
        disabled=["Ad Soyad", "Sınıf-Şube"],
        column_config={
            "Kart": st.column_config.NumberColumn("Kart", min_value=0, step=1, format="%d"),
            "Puan": st.column_config.NumberColumn("Puan", min_value=0, step=1, format="%d"),
        },
    )
    filled = [(sid, edited.at[sid, "Kart"], edited.at[sid, "Puan"]) for sid in ids]
    n = sum(1 for _, k, p in filled if _to_int(k) is not None or _to_int(p) is not None)
    if st.button(f"Skorları Kaydet ({n} oyuncu)", type="primary", key="gs_save", disabled=n == 0):
        ok, msg = save_group_scores(gid, filled, tarih, tur)
        flash("success" if ok else "error", msg)
        if ok:
            bump("gs_ver")
        st.rerun()

    sc = group_scores_df()
    sc = sc[(sc.group_id == gid) & (sc.arsiv == 0)]
    if not sc.empty:
        st.markdown("#### Grubun Mevcut Durumu")
        st.dataframe(player_standings(sc), hide_index=True, use_container_width=True)


def group_board_tab(toplu):
    sc_all = group_scores_df()
    if sc_all.empty:
        st.caption("Henüz grup skoru kaydı yok.")
        return
    f1, f2, f3 = st.columns(3)
    oyunlar = {None: "Tüm toplu oyunlar", **dict(zip(toplu.id, toplu.ad))}
    gsel = f1.selectbox("Oyun", list(oyunlar.keys()), format_func=lambda i: oyunlar[i], key="gb_game")
    sub = sc_all if gsel is None else sc_all[sc_all.game_id == gsel]
    turs = ["Tümü"] + sorted(t for t in sub.turnuva.unique() if t) + (["(Turnuvasız)"] if (sub.turnuva == "").any() else [])
    tsel = f2.selectbox("Turnuva", turs, key=f"gb_turn_{gsel}")
    if tsel == "(Turnuvasız)":
        sub = sub[sub.turnuva == ""]
    elif tsel != "Tümü":
        sub = sub[sub.turnuva == tsel]
    key = {"Puan": "puan", "Kart": "kart"}[f3.selectbox("Sıralama ölçütü", ["Puan", "Kart"], key="gb_key")]
    if sub.empty:
        st.caption("Bu filtre için kayıt yok.")
        return
    st.markdown("#### Grup Sıralaması")
    gt = group_totals(sub, key)
    st.dataframe(gt, hide_index=True, use_container_width=True)
    export_buttons(gt, "grup_siralamasi", "gb_g", sheet="Grup Sıralaması")
    act = sub[sub.arsiv == 0]
    st.markdown("#### Oyuncu Sıralaması")
    ps = player_standings(act, key)
    st.dataframe(ps, hide_index=True, use_container_width=True)
    if not ps.empty:
        export_buttons(ps, "oyuncu_siralamasi", "gb_p", sheet="Oyuncu Sıralaması")
    st.markdown("#### Skor Geçmişi")
    h = act.sort_values(["tarih", "id"], ascending=[False, False])
    hist = pd.DataFrame({
        "Kayıt": h.id, "Tarih": h.tarih.map(fmt_tarih), "Oyun": h.oyun, "Turnuva": h.turnuva.replace("", "—"),
        "Grup": h.grup, "Tur": h.tur.replace("", "—"), "Oyuncu": h.ad_soyad, "Kart": h.kart, "Puan": h.puan,
    })
    st.dataframe(hist, hide_index=True, use_container_width=True)
    if not hist.empty:
        export_buttons(hist, "grup_skor_gecmisi", "gb_h", sheet="Skor Geçmişi")
    if is_admin() and not h.empty:
        with st.expander("Yönetici: yanlış girilen skor kaydını sil"):
            opts = {int(r.id): f"#{r.id} · {fmt_tarih(r.tarih)} · {r.grup} · {r.ad_soyad} · {r.kart} kart / {r.puan} puan"
                    for r in h.head(100).itertuples()}
            rid = st.selectbox("Kayıt", list(opts.keys()), format_func=lambda i: opts[i], key="gb_del_sel")
            conf = st.checkbox("Bu skor kaydını kalıcı olarak silmek istiyorum.", key="gb_del_conf")
            if st.button("Skor Kaydını Sil", disabled=not conf, key="gb_del_btn"):
                delete_group_score(rid)
                flash("success", "Skor kaydı silindi.")
                st.rerun()


def group_edit_tab(students):
    if not is_admin():
        st.warning("🔒 **Salt Okunur Mod:** Grup düzenlemek için sol menüden **Yönetici Paneli**'ne girerek oturum açmalısınız.")
        return
    groups = load_groups()
    if groups.empty:
        st.info("Henüz grup yok.")
        return
    labels = {int(r.id): group_label(r) for r in groups.itertuples()}
    gid = st.selectbox("Grup", list(labels.keys()), format_func=lambda i: labels[i], key="ge_group")
    row = groups[groups.id == gid].iloc[0]
    c1, c2 = st.columns(2)
    ad = c1.text_input("Grup adı", value=row.ad, key=f"ge_name_{gid}", max_chars=60)
    tur = c2.text_input("Turnuva adı", value=row.turnuva, key=f"ge_turn_{gid}", max_chars=60)
    mem = group_members_df(gid)
    picked = member_picker(f"ge_mem_{gid}", students, [int(i) for i in mem.id])
    if st.button("Grubu Güncelle", type="primary", key=f"ge_save_{gid}"):
        ok, msg = update_group(gid, ad, tur, picked)
        flash("success" if ok else "error", msg)
        st.rerun()
    st.markdown("#### Grubu Sil")
    conf = st.checkbox("Bu grubu ve tüm skor kayıtlarını silmek istiyorum.", key=f"ge_del_conf_{gid}")
    if st.button("Grubu Sil", disabled=not conf, key=f"ge_del_{gid}"):
        delete_group(gid)
        flash("success", "Grup silindi.")
        st.rerun()


def page_groups():
    hero("Grup ve Turnuva Yönetimi", "Toplu oyunlar için grupları görüntüleyin ve yönetin", "👥")
    students = load_students()
    if students.empty:
        empty_state()
        return
    games = load_games()
    toplu = games[games.kategori == GROUP_CATEGORY]
    if toplu.empty:
        st.info("Kütüphanede toplu oyun yok.")
        return
    t1, t2, t3, t4 = st.tabs(["Grup Oluştur", "Skor Girişi", "Sıralama ve Geçmiş", "Grup Düzenle"])
    with t1:
        group_create_tab(students, toplu)
    with t2:
        group_score_tab(students)
    with t3:
        group_board_tab(toplu)
    with t4:
        group_edit_tab(students)


# ----------------------------------------------------------------------------
# DEMO MODU (örnek verilerle, gerçek veritabanından tamamen yalıtılmış)
# ----------------------------------------------------------------------------
_KEEP_KEYS = ("mode", "admin", "demo_token", "nav")


def _reset_session_state():
    for k in list(st.session_state.keys()):
        if k in _KEEP_KEYS or str(k).startswith("lp_") or str(k).startswith("FormSubmitter"):
            continue
        try:
            del st.session_state[k]
        except Exception:
            pass


def _drop_demo_db():
    tok = st.session_state.get("demo_token")
    if not tok:
        return
    for suffix in ("", "-wal", "-shm", "-journal"):
        try:
            os.remove(os.path.join(DEMO_DIR, f"demo_{tok}.db{suffix}"))
        except OSError:
            pass


def _cleanup_old_demo_files():
    try:
        now = time.time()
        for name in os.listdir(DEMO_DIR):
            p = os.path.join(DEMO_DIR, name)
            if name.startswith("demo_") and now - os.path.getmtime(p) > DEMO_MAX_AGE:
                os.remove(p)
    except OSError:
        pass


def enter_demo():
    _cleanup_old_demo_files()
    _reset_session_state()
    st.session_state["mode"] = "demo"
    st.session_state["admin"] = True      # yalnızca demo veritabanında geçerlidir
    st.session_state["nav"] = PG_HOME


def enter_live():
    _reset_session_state()
    st.session_state["mode"] = "live"
    st.session_state["admin"] = False
    st.session_state["nav"] = PG_HOME


def back_to_landing():
    _drop_demo_db()
    _reset_session_state()
    st.session_state.pop("demo_token", None)
    st.session_state["mode"] = None
    st.session_state["admin"] = False


def demo_to_waitlist():
    back_to_landing()
    st.session_state["lp_show_wait"] = True


def reset_demo():
    _drop_demo_db()
    _reset_session_state()
    st.session_state["nav"] = PG_HOME


def open_waitlist():
    st.session_state["lp_show_wait"] = True


_DEMO_ADLAR = [
    "Ahmet", "Ayşe", "Mehmet", "Zeynep", "Ali", "Elif", "Mustafa", "Defne", "Emre", "Ecrin", "Yusuf", "Nehir",
    "Kerem", "Azra", "Burak", "İpek", "Efe", "Asya", "Arda", "Mira", "Kaan", "Duru", "Eren", "Ela", "Can", "Lina",
    "Barış", "Sena", "Ege", "Nisa", "Onur", "Ada", "Berk", "Melis", "Tuna", "Çınar",
]
_DEMO_SOYADLAR = [
    "Yılmaz", "Kaya", "Demir", "Şahin", "Çelik", "Yıldız", "Aydın", "Özdemir", "Arslan", "Doğan",
    "Kılıç", "Aslan", "Çetin", "Koç", "Kurt", "Özkan", "Polat", "Erdoğan", "Güneş", "Aksoy",
]


def seed_demo_data():
    """Demo veritabanını (yalnızca boşsa) kurgusal örnek verilerle doldurur."""
    with db() as c:
        if c.execute("SELECT COUNT(*) FROM students").fetchone()[0] > 0:
            return
        rnd = random.Random(20260)
        today = date.today()
        fmt = "%Y-%m-%d"
        gid = {r["ad"]: r["id"] for r in c.execute("SELECT id, ad FROM games")}

        kadro = [(5, "A"), (5, "B"), (6, "A"), (6, "B")]
        ids_by_class = {k: [] for k in kadro}
        skill = {}
        for i, ad in enumerate(_DEMO_ADLAR):
            sinif, sube = kadro[i // 9]
            cur = c.execute(
                "INSERT INTO students (ogrenci_no, ad_soyad, sinif, sube) VALUES (?,?,?,?)",
                (str(1001 + i), f"{ad} {rnd.choice(_DEMO_SOYADLAR)}", sinif, sube),
            )
            ids_by_class[(sinif, sube)].append(cur.lastrowid)
            skill[cur.lastrowid] = rnd.uniform(0.25, 0.95)

        # İkili oyunlar: aynı sınıf düzeyindeki öğrenciler arasında maçlar
        ikili = [g for g in GAME_LIBRARY[PAIR_CATEGORY] if g in gid]
        havuz_sinif = {
            5: ids_by_class[(5, "A")] + ids_by_class[(5, "B")],
            6: ids_by_class[(6, "A")] + ids_by_class[(6, "B")],
        }
        for _ in range(150):
            a, b = rnd.sample(havuz_sinif[rnd.choice((5, 6))], 2)
            if rnd.random() < 0.12:
                sonuc = "D"
            else:
                sonuc = "1" if rnd.random() < skill[a] / (skill[a] + skill[b]) else "2"
            gun = today - timedelta(days=rnd.randint(0, 75))
            c.execute(
                "INSERT INTO matches (tarih, game_id, p1_id, p2_id, sonuc) VALUES (?,?,?,?,?)",
                (gun.strftime(fmt), gid[rnd.choice(ikili)], a, b, sonuc),
            )

        # Bireysel oyunlar: her öğrenci için iki oyunda, iki zaman noktalı ilerleme kaydı
        bireysel = [g for g in GAME_LIBRARY[INDIV_CATEGORY] if g in gid]

        def seviye_of(k):
            return "Başlangıç" if k < 6 else "Orta" if k < 11 else "İleri" if k < 16 else "Usta"

        for sid in skill:
            for oyun in rnd.sample(bireysel, 2):
                k1 = rnd.randint(2, 9)
                k2 = k1 + rnd.randint(1, 8)
                for kart, gun_once in ((k1, rnd.randint(40, 70)), (k2, rnd.randint(2, 25))):
                    c.execute(
                        "INSERT INTO progress (student_id, game_id, kart, seviye, tarih, kaynak, donem) "
                        "VALUES (?,?,?,?,?,?,?)",
                        (sid, gid[oyun], kart, seviye_of(kart),
                         (today - timedelta(days=gun_once)).strftime(fmt), "manuel", None),
                    )

        # Toplu oyunlar: gruplar ve turnuva skorları
        toplu = [g for g in GAME_LIBRARY[GROUP_CATEGORY] if g in gid]
        a5, a6 = ids_by_class[(5, "A")], ids_by_class[(6, "A")]
        plan = [
            (toplu[0], "Kartallar", a5[:4]), (toplu[0], "Şahinler", a5[4:8]),
            (toplu[1], "Mavi Takım", a6[:4]), (toplu[1], "Kırmızı Takım", a6[4:8]),
        ]
        for oyun, ad, uyeler in plan:
            cur = c.execute(
                "INSERT INTO game_groups (ad, game_id, turnuva, tarih) VALUES (?,?,?,?)",
                (ad, gid[oyun], "Bahar Turnuvası", (today - timedelta(days=30)).strftime(fmt)),
            )
            grp_id = cur.lastrowid
            c.executemany(
                "INSERT OR IGNORE INTO group_members (group_id, student_id) VALUES (?,?)",
                [(grp_id, s) for s in uyeler],
            )
            for tur in (1, 2, 3):
                gun = (today - timedelta(days=35 - 7 * tur)).strftime(fmt)
                for sid in uyeler:
                    c.execute(
                        "INSERT INTO group_scores (group_id, student_id, tarih, tur, kart, puan) VALUES (?,?,?,?,?,?)",
                        (grp_id, sid, gun, f"{tur}. Tur", rnd.randint(1, 6), rnd.randint(5, 30)),
                    )


def demo_banner():
    c1, c2 = st.columns([5, 1.6])
    c1.markdown(
        '<div class="demo-bar"><b>DEMO MODU</b>Örnek (kurgusal) verilerle çalışıyorsunuz. '
        'Yaptığınız değişiklikler gerçek verilerinize yansımaz ve demo kapatıldığında silinir.</div>',
        unsafe_allow_html=True,
    )
    c2.button("Bekleme Listesine Katıl", key="demo_wait", on_click=demo_to_waitlist, use_container_width=True)


# ----------------------------------------------------------------------------
# BEKLEME LİSTESİ (her zaman GERÇEK veritabanına yazılır)
# ----------------------------------------------------------------------------
def add_waitlist(ad_soyad, eposta, kurum, kvkk_onay):
    ad = _clean(ad_soyad)
    mail = _clean(eposta).lower()
    kur = _clean(kurum)
    if len(ad.split()) < 2 or not re.search(r"[^\W\d_]", ad):
        return False, "Lütfen adınızı ve soyadınızı birlikte girin."
    if len(mail) > 120 or not EMAIL_RE.match(mail):
        return False, "Lütfen geçerli bir e-posta adresi girin."
    if len(kur) < 2:
        return False, "Lütfen kurum bilgisini girin."
    if not kvkk_onay:
        return False, "Devam etmek için KVKK Aydınlatma Metni'ni okuduğunuzu onaylamanız gerekir."
    try:
        with db(DB_PATH) as c:
            c.execute(
                "INSERT INTO waitlist (ad_soyad, eposta, kurum, kvkk_onay, kayit_tarihi) VALUES (?,?,?,?,?)",
                (ad[:80], mail, kur[:120], 1, datetime.now().strftime("%Y-%m-%d %H:%M:%S")),
            )
        return True, "Kaydınız alındı. Yayına açıldığımızda sizinle e-posta yoluyla iletişime geçeceğiz."
    except sqlite3.IntegrityError:
        return False, "Bu e-posta adresiyle zaten bekleme listesine kayıt yapılmış."
    except sqlite3.Error:
        return False, "Kayıt sırasında bir sorun oluştu. Lütfen daha sonra tekrar deneyin."


def load_waitlist():
    require_admin()
    with db() as c:
        return pd.read_sql_query(
            "SELECT id, ad_soyad, eposta, kurum, kayit_tarihi FROM waitlist ORDER BY id DESC", c
        )


def delete_waitlist(wid):
    require_admin()
    with db() as c:
        c.execute("DELETE FROM waitlist WHERE id=?", (int(wid),))


def admin_waitlist_tab():
    st.markdown("#### Bekleme Listesi")
    df = load_waitlist()
    if df.empty:
        st.caption("Bekleme listesinde henüz kayıt yok.")
        return
    view = df.rename(columns={
        "id": "No", "ad_soyad": "Ad Soyad", "eposta": "E-Posta", "kurum": "Kurum", "kayit_tarihi": "Kayıt Tarihi",
    })
    st.dataframe(view, hide_index=True, use_container_width=True)
    export_buttons(view, "bekleme_listesi", "wl_exp", sheet="Bekleme Listesi")
    st.markdown("#### Kayıt Sil (KVKK silme talebi)")
    labels = {int(r.id): f"{r.ad_soyad}  ·  {r.eposta}" for r in df.itertuples()}
    wid = st.selectbox("Kayıt seçin", list(labels.keys()), index=None, format_func=lambda i: labels[i],
                       key="wl_del_sel", placeholder="İsim veya e-posta yazarak arayın...")
    if wid is not None:
        conf = st.checkbox("Bu kaydı kalıcı olarak silmek istiyorum.", key=f"wl_del_conf_{wid}")
        if st.button("Kaydı Sil", disabled=not conf, key=f"wl_del_btn_{wid}"):
            delete_waitlist(wid)
            flash("success", "Kayıt silindi.")
            st.rerun()


# ----------------------------------------------------------------------------
# KVKK AYDINLATMA METNİ VE FOOTER
# ----------------------------------------------------------------------------
def kvkk_text():
    return f"""**6698 Sayılı Kişisel Verilerin Korunması Kanunu (KVKK) Kapsamında Aydınlatma Metni**

**1. Veri Sorumlusu**

{KVKK_CONTROLLER}, kişisel verilerinizi 6698 sayılı Kişisel Verilerin Korunması Kanunu ("KVKK") ve ilgili mevzuata uygun olarak işlemektedir. İletişim: {KVKK_CONTACT}

**2. İşlenen Kişisel Veriler**

- *Bekleme listesi formu:* ad soyad, e-posta adresi, kurum bilgisi, aydınlatma metnini okuduğunuza dair onay kaydı ve kayıt tarihi.
- *Panel kullanımı (kurum kullanıcıları):* kurumunuz tarafından sisteme yüklenen veya girilen öğrenci numarası, ad soyad, sınıf/şube bilgileri ile maç, bireysel ilerleme ve turnuva sonuçları.
- *Demo ortamı:* yalnızca kurgusal örnek veriler kullanılır; gerçek kişilere ait veri içermez ve demo kapatıldığında silinir.

**3. Kişisel Verilerin İşlenme Amaçları**

- Bekleme listesine kayıt olan kişilerle hizmetin yayına alınması, erken erişim ve bilgilendirme konularında iletişim kurmak,
- Panelin sunulması, yetkilendirilmesi, güvenliğinin sağlanması ve teknik destek verilmesi,
- Yasal yükümlülüklerin yerine getirilmesi ve olası hukuki uyuşmazlıklarda hakların korunması.

**4. Hukuki Sebep**

Bekleme listesi verileriniz KVKK m.5/1 uyarınca **açık rızanıza**, bilgi güvenliğine ilişkin kayıtlar ise veri sorumlusunun **meşru menfaatine** (m.5/2-f) dayanılarak işlenir. Rızanızı dilediğiniz zaman geri çekebilirsiniz; geri çekme, öncesinde yapılan işlemlerin hukuka uygunluğunu etkilemez.

**5. Verilerin Aktarılması**

Kişisel verileriniz, yasal zorunluluklar ve yetkili kamu kurumlarının talepleri dışında üçüncü kişilerle paylaşılmaz, satılmaz ve pazarlama amacıyla aktarılmaz. Hizmetin barındırıldığı altyapı sağlayıcıları, yalnızca hizmetin sunulması amacıyla ve veri güvenliği yükümlülükleri çerçevesinde veriye erişebilir.

**6. Saklama Süresi**

Bekleme listesi kayıtları, iletişim amacı sona erene veya rızanızı geri çekene kadar, her hâlükârda en fazla {KVKK_RETENTION} süreyle saklanır; süre sonunda silinir veya anonim hale getirilir.

**7. Veri Güvenliği**

Yönetici erişimi PIN ile korunur; PIN'ler geri döndürülemez biçimde (tuzlanmış ve özetlenmiş olarak) saklanır. Hatalı giriş denemeleri sınırlandırılır. Yönetici girişi yapılmadığında panel salt okunur modda çalışır.

**8. KVKK m.11 Kapsamındaki Haklarınız**

- Kişisel verilerinizin işlenip işlenmediğini öğrenme,
- İşlenmişse buna ilişkin bilgi talep etme,
- İşlenme amacını ve amacına uygun kullanılıp kullanılmadığını öğrenme,
- Yurt içinde veya yurt dışında aktarıldığı üçüncü kişileri bilme,
- Eksik veya yanlış işlenmişse düzeltilmesini isteme,
- KVKK m.7 çerçevesinde silinmesini veya yok edilmesini isteme ve bu işlemlerin aktarıldığı üçüncü kişilere bildirilmesini talep etme,
- İşlenen verilerin otomatik sistemlerle analiz edilmesi suretiyle aleyhinize bir sonucun ortaya çıkmasına itiraz etme,
- Kanuna aykırı işleme nedeniyle zarara uğramanız hâlinde zararın giderilmesini talep etme.

**9. Başvuru Yöntemi**

Haklarınıza ilişkin taleplerinizi {KVKK_CONTACT} adresine iletebilirsiniz. Başvurular, niteliğine göre en geç otuz gün içinde sonuçlandırılır.

**10. Öğrenci Verileri Hakkında Not**

Panele kurum tarafından yüklenen öğrenci verileri bakımından veri sorumlusu, verileri sisteme yükleyen kurumdur. Öğrencilerin ve velilerin aydınlatılması ile gerekli hukuki dayanakların sağlanması kurumun sorumluluğundadır. Çocuklara ait veriler yalnızca eğitsel takip amacıyla ve en az düzeyde işlenmelidir."""

def render_footer(dark=False):
    cls = "lp-footer" if dark else "app-footer"
    st.markdown(
        f'<div class="{cls}"><div class="ft-line"></div>'
        f'<div class="ft-t">© {date.today().year} Akıl ve Zeka Oyunları Yönetim ve Takip Paneli · Tüm hakları saklıdır.</div></div>',
        unsafe_allow_html=True,
    )



# ----------------------------------------------------------------------------
# KARŞILAMA EKRANI (Landing Page)
# ----------------------------------------------------------------------------
LANDING_CSS = """
<style>
@import url('https://fonts.googleapis.com/css2?family=DM+Serif+Display&family=Nunito:wght@400;600;700;800&display=swap');
:root{
  --bg:#16221A; --card:#223329; --card-border:#3A5443; --latte:#E2C49D; --latte-light:#FFFFFF;
  --latte-hover:#CFAF85; --text-main:#FFFFFF; --text-muted:#B0C4B8;
}
html, body, .stApp{font-family:'Nunito',system-ui,-apple-system,'Segoe UI',sans-serif;}
.stApp{background: radial-gradient(1000px 500px at 50% -10%, rgba(217,185,143,0.15), transparent 70%), #1A130E !important; color:var(--text-main);}
header[data-testid="stHeader"]{background:transparent !important;}
section[data-testid="stSidebar"],[data-testid="collapsedControl"],[data-testid="stSidebarCollapsedControl"],[data-testid="stSidebarCollapseButton"]{display:none !important;}
.block-container{max-width:1050px !important;padding-top:2.5rem !important;padding-bottom:3rem !important;}

/* Üst Başlık - Daha Vurgulu ve Şık Latte Tonu */
.lp-brand{display:flex;align-items:center;gap:.9rem;color:var(--latte);font-weight:800;font-size:1.35rem;letter-spacing:-0.2px;}
.lp-brand span{color:var(--latte);text-shadow:0 2px 8px rgba(217,185,143,0.25);}
.lp-brand svg{color:var(--latte);filter:drop-shadow(0 2px 6px rgba(217,185,143,0.35));}

/* Hero Kart Yapısı */
.lp-hero{margin:2.2rem 0 1.8rem 0;background:linear-gradient(145deg, #2B2018 0%, #201711 100%);border:1px solid var(--card-border);border-radius:20px;padding:2.8rem 2.5rem;box-shadow:0 20px 40px rgba(0,0,0,0.45);}
.lp-eyebrow{font-size:.78rem;font-weight:800;letter-spacing:.18em;text-transform:uppercase;color:var(--latte);margin-bottom:.9rem;}
.lp-h1{font-family:'DM Serif Display',Georgia,serif;font-size:2.8rem;line-height:1.15;color:#FFFFFF;max-width:720px;}
.lp-h1 span{color:var(--latte);font-style:italic;}
.lp-sub{margin-top:1.1rem;font-size:1.05rem;line-height:1.6;color:var(--text-muted);max-width:640px;}

/* Rozetler */
.lp-chips{display:flex;flex-wrap:wrap;gap:.6rem;margin-top:1.6rem;}
.lp-chips span{font-size:.82rem;font-weight:700;color:var(--latte-light);background:rgba(217,185,143,0.08);border:1px solid rgba(217,185,143,0.22);padding:.4rem .9rem;border-radius:99px;}

/* Grid Kartlar */
.lp-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:1.1rem;margin-top:2rem;}
.lp-card{background:var(--card);border:1px solid var(--card-border);border-radius:16px;padding:1.3rem;transition:all .25s ease;}
.lp-card:hover{border-color:var(--latte);transform:translateY(-3px);box-shadow:0 10px 25px rgba(0,0,0,0.3);}
.lp-card-i{font-size:1.6rem;margin-bottom:.6rem;display:inline-block;padding:.4rem .6rem;background:rgba(217,185,143,0.1);border-radius:10px;}
.lp-card-t{font-weight:800;color:var(--latte);font-size:1.02rem;margin-top:.2rem;}
.lp-card-d{color:var(--text-muted);font-size:.86rem;line-height:1.5;margin-top:.35rem;}

/* GEÇİŞ NOKTASI BUTONLARI: Çiğ durmayan, koyu ambiyansa uyumlu ve asil latte geçişli tasarım */
.stApp .stButton > button {
  border-radius: 14px !important;
  font-weight: 800 !important;
  padding: .85rem 1.6rem !important;
  min-height: 3.4rem !important;
  background: linear-gradient(135deg, #32251D 0%, #221812 100%) !important;
  border: 1.5px solid rgba(217,185,143,0.45) !important;
  color: var(--latte-light) !important;
  box-shadow: 0 4px 20px rgba(0,0,0,0.35) !important;
  transition: all 0.25s cubic-bezier(0.4, 0, 0.2, 1) !important;
}
.stApp .stButton > button:hover {
  background: var(--latte) !important;
  color: #1A130E !important;
  border-color: var(--latte) !important;
  transform: translateY(-2.5px);
  box-shadow: 0 8px 25px rgba(217,185,143,0.3) !important;
}

.lp-footer{margin-top:3.5rem;}
.lp-footer .ft-line{height:1px;background:var(--card-border);margin-bottom:1.2rem;}
.lp-footer .ft-t{color:var(--text-muted);font-weight:700;font-size:.85rem;text-align:center;}
</style>
"""

LANDING_FEATURES = [
    ("⚔️", "Maç Girişi ve Akıllı Eşleştirme", "İkili oyun maçlarını kaydedin; benzer seviyedeki öğrencileri otomatik eşleştirin."),
    ("🧩", "Bireysel Gelişim ve Karne", "Kart ve seviye ilerlemesini dönem dönem izleyin, öğrenci karnesini görüntüleyin."),
    ("👥", "Grup ve Turnuva Takibi", "Toplu oyunlarda grupları kurun, tur tur skor girin, liderlik tablosunu izleyin."),
    ("📈", "Şube ve Sıralama Raporları", "Sınıf ve şubelere göre başarı oranlarını tek ekranda karşılaştırın."),
    ("📤", "Excel / CSV ile Aktarım", "Öğrenci listelerini ve ilerleme verilerini dosyadan toplu yükleyin, raporları indirin."),
    ("🔐", "PIN Korumalı Yönetim", "Varsayılan salt okunur mod; veri girişi yalnızca PIN ile yönetici modunda."),
]


def render_landing():
    st.markdown(LANDING_CSS, unsafe_allow_html=True)

    # Üst başlık (Sağ üstteki buton tamamen kaldırıldı)
    st.markdown(
        '<div class="lp-brand" style="margin-bottom: 1rem;">' + icon("brain", 32) + '<span>Akıl ve Zeka Oyunları Yönetim Paneli</span></div>',
        unsafe_allow_html=True,
    )

    st.markdown(
        '<div class="lp-hero">'
        '<div class="lp-eyebrow">Eğitim & Turnuva Yönetim Platformu</div>'
        '<div class="lp-h1">Öğrenci gelişimini ve maçları <span>tek panelden</span> yönetin.</div>'
        '<div class="lp-sub">Karşılaşma kayıtları, şube başarı analizleri, bireysel kart/seviye takibi ve turnuva skorları '
        'için tasarlanmış yönetim paneline hemen giriş yapın.</div>'
        '<div class="lp-chips">'
        '<span>⚔️ Akıllı Maç Eşleştirme</span>'
        '<span>📊 Şube & Öğrenci Karnesi</span>'
        '<span>🏆 Turnuva & Grup Skoru</span>'
        '<span>📤 Excel / CSV Aktarımı</span>'
        '</div>'
        '</div>',
        unsafe_allow_html=True,
    )

    # İki buton da parlak ve açık renkli (primary) olacak şekilde yan yana ayarlandı
    b1, b2, _ = st.columns([2, 2, 2.5])
    b1.button("🔑 Panele Giriş Yap", type="primary", key="lp_main_login", on_click=enter_live, use_container_width=True)
    b2.button("✨ Örnek Verilerle Demoyu Dene", type="primary", key="lp_demo", on_click=enter_demo, use_container_width=True)

    # Özellik Kartları Grid
    st.markdown(
        '<div class="lp-grid">'
        '<div class="lp-card">'
        '<div class="lp-card-i">⚔️</div>'
        '<div class="lp-card-t">Maç & Eşleştirme</div>'
        '<div class="lp-card-d">İkili oyun maçlarını kaydedin, seviyeye göre dengeli otomatik eşleştirmeler oluşturun.</div>'
        '</div>'
        '<div class="lp-card">'
        '<div class="lp-card-i">🧩</div>'
        '<div class="lp-card-t">Bireysel Gelişim</div>'
        '<div class="lp-card-d">Bireysel oyunlarda kart ve seviye ilerlemesini dönem bazlı izleyin, dijital karne üretin.</div>'
        '</div>'
        '<div class="lp-card">'
        '<div class="lp-card-i">👥</div>'
        '<div class="lp-card-t">Grup & Turnuva</div>'
        '<div class="lp-card-d">Toplu oyun grupları kurun, turlara göre skor girin ve canlı sıralamaları takip edin.</div>'
        '</div>'
        '<div class="lp-card">'
        '<div class="lp-card-i">📈</div>'
        '<div class="lp-card-t">Şube & Excel Raporu</div>'
        '<div class="lp-card-d">Sınıf başarı oranlarını analiz edin, öğrenci ve skor listelerini Excel/CSV olarak indirin.</div>'
        '</div>'
        '</div>',
        unsafe_allow_html=True,
    )

    render_footer(dark=True)
    
def generate_recovery_key():
    require_admin()
    raw = secrets.token_hex(8).upper()
    salt = secrets.token_hex(16)
    _set_setting("recovery_key", f"{salt}${_hash_pin(raw, salt)}")
    return "-".join(raw[i:i + 4] for i in range(0, len(raw), 4))


def verify_recovery_key(key):
    stored = _get_setting("recovery_key")
    if not stored or "$" not in stored:
        return False
    salt, h = stored.split("$", 1)
    return hmac.compare_digest(_hash_pin(_norm_code(key), salt), h)


def issue_reset_code():
    """Tek kullanımlık sıfırlama kodu üretir; kod EKRANDA gösterilmez, sunucuya (dosya + konsol) yazılır."""
    now = int(time.time())
    if now - _int_setting("reset_code_issued") < RESET_CODE_COOLDOWN:
        return False, "Lütfen yeni bir kod istemeden önce bir dakika bekleyin."
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    code = "".join(secrets.choice(alphabet) for _ in range(8))
    salt = secrets.token_hex(16)
    _set_setting("reset_code", f"{salt}${_hash_pin(code, salt)}")
    _set_setting("reset_code_exp", str(now + RESET_CODE_TTL))
    _set_setting("reset_code_issued", str(now))
    delivered = False
    try:
        with open(RESET_CODE_FILE, "w", encoding="utf-8") as f:
            f.write(f"PIN sıfırlama kodu: {code}\nGeçerlilik: {RESET_CODE_TTL // 60} dakika\n")
        try:
            os.chmod(RESET_CODE_FILE, 0o600)
        except OSError:
            pass
        delivered = True
    except OSError:
        pass
    print(f"[PIN SIFIRLAMA] Tek kullanımlık kod: {code} (geçerlilik: {RESET_CODE_TTL // 60} dk)", flush=True)
    where = "uygulama klasöründeki `pin_sifirlama_kodu.txt` dosyasına ve sunucu/terminal günlüğüne" if delivered \
        else "sunucu/terminal günlüğüne"
    return True, (f"Sıfırlama kodu {where} yazıldı. Kodu oradan okuyup aşağıya girin. "
                  f"Kod {RESET_CODE_TTL // 60} dakika geçerlidir ve yalnızca bir kez kullanılabilir.")


def verify_reset_code(code):
    stored = _get_setting("reset_code")
    if not stored or "$" not in stored:
        return False
    if _int_setting("reset_code_exp") < int(time.time()):
        return False
    salt, h = stored.split("$", 1)
    return hmac.compare_digest(_hash_pin(_norm_code(code), salt), h)


def reset_lock_remaining():
    return max(0, _int_setting("reset_lock_until") - int(time.time()))


def register_reset_failure():
    n = _int_setting("reset_fail_count") + 1
    if n >= RESET_MAX_FAILS:
        _set_setting("reset_lock_until", str(int(time.time()) + RESET_LOCK_SECONDS))
        n = 0
    _set_setting("reset_fail_count", str(n))
    return n


def recover_pin(new_pin):
    _store_pin(new_pin)
    reset_pin_failures()
    _set_setting("reset_fail_count", "0")
    _set_setting("reset_lock_until", "0")
    _set_setting("reset_code", "")
    _set_setting("reset_code_exp", "0")
    try:
        os.remove(RESET_CODE_FILE)
    except OSError:
        pass


def _pin_problem(new, rep):
    if not (new.isdigit() and 4 <= len(new) <= 12):
        return "Yeni PIN yalnızca rakamlardan oluşmalı ve 4-12 hane olmalıdır."
    if new != rep:
        return "Yeni PIN ve tekrarı eşleşmiyor."
    return None


def _fp_open_cb():
    st.session_state["fp_open"] = True


def _try_recover(verify_fn, secret, new, rep):
    st.session_state["fp_open"] = True
    problem = _pin_problem(new, rep)
    if problem:
        st.error(problem)
        return
    if verify_fn(secret):
        recover_pin(new)
        st.session_state["fp_open"] = False
        flash("success", "PIN başarıyla sıfırlandı. Yeni PIN ile giriş yapabilirsiniz.")
        st.rerun()
    else:
        n = register_reset_failure()
        if reset_lock_remaining() > 0:
            st.error("Çok fazla hatalı deneme. Kurtarma işlemi geçici olarak kilitlendi.")
        else:
            st.error(f"Anahtar/kod hatalı veya süresi dolmuş. Kalan deneme: {RESET_MAX_FAILS - n}")


def forgot_pin_ui():
    if st.session_state.get("mode") == "demo":
        st.caption(f"Demo ortamında varsayılan PIN: {DEFAULT_PIN}")
        return
    with st.expander("PIN'imi unuttum", expanded=bool(st.session_state.get("fp_open"))):
        rem = reset_lock_remaining()
        if rem > 0:
            st.error(f"Çok fazla hatalı kurtarma denemesi. Güvenlik nedeniyle yaklaşık {math.ceil(rem / 60)} dakika beklemeniz gerekir.")
            return
        yontem = st.radio("Kurtarma yöntemi", ["Kurtarma anahtarım var", "Sunucu doğrulama kodu istiyorum"],
                          key="fp_method", horizontal=True, on_change=_fp_open_cb)
        if yontem == "Kurtarma anahtarım var":
            st.caption("Yönetici Paneli > PIN Değiştir sekmesinden daha önce oluşturduğunuz kurtarma anahtarını girin.")
            with st.form("fp_key_form"):
                key = st.text_input("Kurtarma anahtarı", max_chars=40, placeholder="XXXX-XXXX-XXXX-XXXX")
                new = st.text_input("Yeni PIN (4-12 rakam)", type="password", max_chars=12)
                rep = st.text_input("Yeni PIN (tekrar)", type="password", max_chars=12)
                go = st.form_submit_button("PIN'i Sıfırla", type="primary")
            if go:
                _try_recover(verify_recovery_key, key, new, rep)
        else:
            st.caption("Güvenlik gereği kod ekranda gösterilmez; yalnızca uygulamanın çalıştığı sunucuya erişimi olan "
                       "kişi (klasör dosyası veya terminal günlüğü üzerinden) okuyabilir.")
            if st.button("Sıfırlama kodu oluştur", key="fp_issue"):
                st.session_state["fp_open"] = True
                ok, msg = issue_reset_code()
                (st.success if ok else st.warning)(msg)
            with st.form("fp_code_form"):
                code = st.text_input("Sıfırlama kodu", max_chars=16, placeholder="8 karakterli kod")
                new = st.text_input("Yeni PIN (4-12 rakam)", type="password", max_chars=12)
                rep = st.text_input("Yeni PIN (tekrar)", type="password", max_chars=12)
                go = st.form_submit_button("PIN'i Sıfırla", type="primary")
            if go:
                _try_recover(verify_reset_code, code, new, rep)


def _ack_recovery_key():
    st.session_state.pop("new_recovery_key", None)


def recovery_key_section():
    st.markdown("#### Kurtarma Anahtarı")
    st.caption("PIN'inizi unutursanız giriş ekranındaki \"PIN'imi unuttum\" bağlantısıyla bu anahtarı kullanarak yeni bir "
               "PIN belirleyebilirsiniz. Anahtar yalnızca oluşturulduğu anda gösterilir; güvenli bir yerde saklayın.")
    shown = st.session_state.get("new_recovery_key")
    if shown:
        st.warning("Bu anahtarı şimdi kaydedin; bir daha gösterilmeyecektir. Yeni bir anahtar oluşturursanız eskisi geçersiz olur.")
        st.code(shown, language=None)
        st.button("Anahtarı kaydettim", key="rk_ack", on_click=_ack_recovery_key)
    has = bool(_get_setting("recovery_key"))
    st.write("Durum: " + ("**Kurtarma anahtarı tanımlı.**" if has else "**Henüz kurtarma anahtarı oluşturulmadı.**"))
    if st.button("Yeni kurtarma anahtarı oluştur" if has else "Kurtarma anahtarı oluştur", key="rk_gen"):
        st.session_state["new_recovery_key"] = generate_recovery_key()
        st.rerun()


def admin_login():
    st.markdown("### Yönetici Girişi")
    remaining = lock_remaining()
    if remaining > 0:
        st.error(f"Çok fazla hatalı deneme. Güvenlik nedeniyle giriş yaklaşık {math.ceil(remaining / 60)} dakika kilitli.")
        forgot_pin_ui()
        return
    with st.form("admin_login"):
        pin = st.text_input("PIN", type="password", max_chars=12)
        go = st.form_submit_button("Giriş Yap", type="primary")
    if go:
        if verify_pin(pin):
            reset_pin_failures()
            st.session_state["admin"] = True
            st.rerun()
        else:
            n = register_pin_failure()
            if lock_remaining() > 0:
                st.error("Çok fazla hatalı deneme. Giriş geçici olarak kilitlendi.")
            else:
                st.error(f"Hatalı PIN. Kalan deneme: {MAX_PIN_FAILS - n}")
    forgot_pin_ui()


# NOT: Orijinal dosyada page_admin() bu fonksiyonu çağırıyordu ancak tanımı yoktu (NameError). Eksik öğrenci
# yükleme ekranı, dosyadaki mevcut parse_student_file() ve import_students() fonksiyonlarıyla tamamlanmıştır.
def render_import_ui(key):
    if not is_admin():
        st.warning(NO_AUTH_MSG)
        return
    st.markdown(
        "Öğrenci listesini **Ogrenci_ID, Ad_Soyad, Sınıf, Şube** sütunlarıyla Excel (.xlsx) veya CSV olarak yükleyin. "
        "Ogrenci_ID boş bırakılabilir; bu durumda numaralar otomatik üretilir."
    )
    tpl = to_xlsx_bytes({"Öğrenciler": pd.DataFrame({
        "Ogrenci_ID": ["1001", "1002"], "Ad_Soyad": ["Ayşe Yılmaz", "Ali Demir"], "Sınıf": [5, 5], "Şube": ["A", "B"],
    })})
    if tpl is not None:
        st.download_button("Örnek şablonu indir (.xlsx)", tpl, file_name="ogrenci_listesi_sablonu.xlsx",
                           mime=XLSX_MIME, key=f"{key}_stu_tpl")
    up = st.file_uploader("Excel (.xlsx) veya CSV dosyası seçin", type=["xlsx", "xlsm", "csv"], key=f"{key}_stu_up")
    if up is None:
        return
    try:
        df, notes = parse_student_file(up)
    except ValueError as e:
        st.error(str(e))
        return
    for n in notes:
        st.info(n)
    st.success(f"{len(df)} öğrenci aktarıma hazır.")
    st.dataframe(df.head(15), hide_index=True, use_container_width=True)
    sig = f"{up.name}_{up.size}"
    replace = st.checkbox(
        "Mevcut öğrenci listesini silip bu dosyayla değiştir (öğrencilere bağlı maç, ilerleme ve grup kayıtları da silinir).",
        key=f"{key}_stu_replace_{sig}",
    )
    conf = True
    if replace:
        conf = st.checkbox("Mevcut tüm öğrenci verilerinin silineceğini anlıyorum.", key=f"{key}_stu_replace_ok_{sig}")
    if st.button("Öğrencileri Aktar", type="primary", key=f"{key}_stu_go_{sig}", disabled=not conf):
        added, updated, skipped, arch = import_students(df, replace)
        msg = f"{added} öğrenci eklendi, {updated} güncellendi, {skipped} zaten kayıtlı olduğu için atlandı."
        if arch:
            msg += f" ({arch} kayıt arşivdeki öğrencilerle eşleşti.)"
        flash("success", msg)
        st.rerun()


def admin_students_tab():
    students = load_students()
    st.markdown("#### Yeni Öğrenci Ekle")
    with st.form("add_student", clear_on_submit=True):
        c1, c2, c3, c4 = st.columns([1, 2, 1, 1])
        no = c1.text_input("Ogrenci_ID (boş bırakılabilir)")
        ad = c2.text_input("Ad Soyad")
        sinif = c3.number_input("Sınıf", min_value=1, max_value=12, value=1, step=1)
        sube = c4.text_input("Şube", max_chars=3)
        if st.form_submit_button("Ekle", type="primary"):
            ok, msg = add_student(no, ad, sinif, sube)
            flash("success" if ok else "error", msg)
            st.rerun()

    st.markdown("#### Öğrenci Düzenle / Sil")
    if students.empty:
        st.caption("Kayıtlı öğrenci yok.")
        return
    labels = student_labels(students)
    sid = st.selectbox("Öğrenci seçin", list(labels.keys()), index=None, format_func=lambda i: labels[i],
                       key="adm_edit_sel", placeholder="İsim yazarak arayın...")
    if sid is None:
        return
    r = students[students.id == sid].iloc[0]
    with st.form(f"edit_student_{sid}"):
        c1, c2, c3, c4 = st.columns([1, 2, 1, 1])
        no = c1.text_input("Ogrenci_ID", value=str(r.ogrenci_no or ""))
        ad = c2.text_input("Ad Soyad", value=r.ad_soyad)
        sinif = c3.number_input("Sınıf", min_value=1, max_value=12, value=int(r.sinif), step=1)
        sube = c4.text_input("Şube", value=r.sube, max_chars=3)
        if st.form_submit_button("Değişiklikleri Kaydet", type="primary"):
            ok, msg = update_student(sid, no, ad, sinif, sube)
            flash("success" if ok else "error", msg)
            st.rerun()
    st.markdown("#### Arşive Gönder / Sil")
    if st.button("Arşive Gönder (silmeden)", key=f"arc_stu_{sid}"):
        archive_students([sid])
        flash("success", "Öğrenci arşive alındı.")
        st.rerun()
    conf = st.checkbox("Bu öğrenciyi ve tüm kayıtlarını KALICI olarak silmek istiyorum.", key=f"del_conf_{sid}")
    if st.button("Öğrenciyi Kalıcı Sil", disabled=not conf, key=f"del_stu_{sid}"):
        delete_student(sid)
        flash("success", "Öğrenci silindi.")
        st.rerun()


def admin_games_tab():
    games = load_games()
    st.markdown("#### Yeni Oyun Ekle")
    with st.form("add_game", clear_on_submit=True):
        c1, c2 = st.columns([2, 1])
        ad = c1.text_input("Oyun adı")
        kat = c2.selectbox("Kategori", list(GAME_LIBRARY.keys()))
        if st.form_submit_button("Ekle", type="primary"):
            ok, msg = add_game(ad, kat)
            flash("success" if ok else "error", msg)
            st.rerun()
    custom = games[games.varsayilan == 0]
    st.markdown("#### Eklenen Oyunları Sil")
    if custom.empty:
        st.caption("Sonradan eklenmiş özel oyun yok.")
        return
    names = dict(zip(custom.id, custom.ad + "  (" + custom.kategori + ")"))
    gid = st.selectbox("Oyun", list(names.keys()), format_func=lambda i: names[i], key="adm_del_game")
    conf = st.checkbox("Bu oyunu ve ona ait maç kayıtlarını silmek istiyorum.", key="adm_del_game_conf")
    if st.button("Oyunu Sil", disabled=not conf, key="adm_del_game_btn"):
        delete_game(gid)
        flash("success", "Oyun silindi.")
        st.rerun()


def admin_archive_tab():
    st.markdown("#### Öğrenci Arşivi")
    sub_a, sub_b = st.tabs(["Arşive At", "Arşivdekiler"])

    with sub_a:
        active = load_students("aktif")
        if active.empty:
            st.caption("Aktif öğrenci yok.")
        else:
            pool = class_branch_filter(active, "arc")
            q = st.text_input("Öğrenci ara", key="arc_q", placeholder="Ad veya soyad yazın...")
            if q.strip():
                pool = pool[pool.ad_soyad.map(tr_upper).str.contains(re.escape(tr_upper(q.strip())), regex=True)]
            if pool.empty:
                st.caption("Listelenecek öğrenci yok.")
            else:
                sel_all = st.checkbox(f"Listelenen {len(pool)} öğrencinin tümünü seç", key="arc_all")
                tbl = pd.DataFrame({
                    "Arşivle": sel_all, "No": pool.ogrenci_no.values, "Ad Soyad": pool.ad_soyad.values,
                    "Sınıf": pool.sinif.values, "Şube": pool.sube.values,
                }, index=[int(i) for i in pool.id])
                ver = st.session_state.get("arc_ver", 0)
                ed = st.data_editor(
                    tbl, hide_index=True, use_container_width=True, disabled=["No", "Ad Soyad", "Sınıf", "Şube"],
                    key=f"arc_ed_{ver}_{int(sel_all)}_{st.session_state.get('arc_sinif')}_{st.session_state.get('arc_sube')}_{tr_upper(q.strip())}",
                    column_config={"Arşivle": st.column_config.CheckboxColumn("Arşivle")},
                )
                chosen = [int(i) for i in ed.index[ed["Arşivle"]]]
                note = st.text_input("Arşiv notu (isteğe bağlı)", key="arc_note")
                conf = st.checkbox(f"{len(chosen)} öğrenciyi arşive almak istiyorum.",
                                   key="arc_conf", disabled=not chosen)
                if st.button(f"Seçilenleri Arşive At ({len(chosen)})", type="primary", key="arc_go",
                             disabled=not (chosen and conf)):
                    n = archive_students(chosen, note)
                    flash("success", f"{n} öğrenci arşive alındı.")
                    bump("arc_ver")
                    st.rerun()

    with sub_b:
        arch = load_students("arsiv")
        if arch.empty:
            st.caption("Arşivde öğrenci yok.")
        else:
            summ = archived_data_summary().set_index("id")
            tbl = pd.DataFrame({
                "Geri Al": False, "No": arch.ogrenci_no.values, "Ad Soyad": arch.ad_soyad.values,
                "Sınıf": arch.sinif.values, "Şube": arch.sube.values,
                "Arşiv Tarihi": arch.arsiv_tarih.map(lambda v: fmt_tarih(v) if _nz(v) else "—").values,
                "Not": arch.arsiv_notu.map(lambda v: _nz(v) or "").values,
                "Maç": [int(summ.at[int(i), "mac"]) if int(i) in summ.index else 0 for i in arch.id],
                "İlerleme Kaydı": [int(summ.at[int(i), "ilerleme"]) if int(i) in summ.index else 0 for i in arch.id],
                "Grup Skoru": [int(summ.at[int(i), "grup_skoru"]) if int(i) in summ.index else 0 for i in arch.id],
            }, index=[int(i) for i in arch.id])
            ed = st.data_editor(
                tbl, hide_index=True, use_container_width=True, key=f"arc_rs_{st.session_state.get('arc_ver', 0)}",
                disabled=[c for c in tbl.columns if c != "Geri Al"],
                column_config={"Geri Al": st.column_config.CheckboxColumn("Geri Al")},
            )
            back = [int(i) for i in ed.index[ed["Geri Al"]]]
            if st.button(f"Seçilenleri Aktif Listeye Geri Al ({len(back)})", key="arc_restore", disabled=not back):
                n = restore_students(back)
                flash("success", f"{n} öğrenci aktif listeye geri alındı.")
                bump("arc_ver")
                st.rerun()
            export_buttons(tbl.drop(columns=["Geri Al"]), "arsiv_listesi", "arc_exp", sheet="Arşiv")


def admin_pin_tab():
    st.markdown("#### PIN Değiştir")
    with st.form("pin_change", clear_on_submit=True):
        cur = st.text_input("Mevcut PIN", type="password", max_chars=12)
        new = st.text_input("Yeni PIN (4-12 rakam)", type="password", max_chars=12)
        rep = st.text_input("Yeni PIN (tekrar)", type="password", max_chars=12)
        go = st.form_submit_button("PIN'i Güncelle", type="primary")
    if go:
        if not verify_pin(cur):
            st.error("Mevcut PIN hatalı.")
        elif not (new.isdigit() and 4 <= len(new) <= 12):
            st.error("Yeni PIN yalnızca rakamlardan oluşmalı ve 4-12 hane olmalıdır.")
        elif new != rep:
            st.error("Yeni PIN ve tekrarı eşleşmiyor.")
        elif new == cur:
            st.error("Yeni PIN mevcut PIN ile aynı olamaz.")
        else:
            set_pin(new)
            st.success("PIN güncellendi.")
    recovery_key_section()


def admin_data_tab():
    st.markdown("#### Yedekleme")
    try:
        with open(active_db_path(), "rb") as f:
            st.download_button("Veritabanını indir (akil_oyunlari.db)", f.read(),
                               file_name="akil_oyunlari.db", mime="application/octet-stream")
    except OSError:
        st.warning("Veritabanı dosyası okunamadı.")
    st.markdown("#### Tehlikeli İşlemler")
    conf = st.checkbox("Tüm maç kayıtlarını silmek istiyorum.", key="wipe_conf")
    if st.button("Tüm Maç Kayıtlarını Sil", disabled=not conf, key="wipe_btn"):
        delete_all_matches()
        flash("success", "Tüm maç kayıtları silindi.")
        st.rerun()


def page_admin():
    hero("Yönetici Paneli", "Veri yükleme, öğrenci/oyun yönetimi ve güvenlik ayarları", "🔐")
    if not is_admin():
        admin_login()
        return
    top, out = st.columns([5, 1])
    top.success("Yönetici oturumu açık.")
    out.button("Çıkış", key="admin_logout", use_container_width=True, on_click=admin_logout)
    if st.session_state.get("mode") == "live" and not _get_setting("recovery_key"):
        st.warning("Kurtarma anahtarınız henüz oluşturulmadı. PIN'inizi unutursanız hesabı kurtarabilmek için "
                   "'PIN Değiştir' sekmesinden bir kurtarma anahtarı oluşturun.")
    tab_names = ["Excel/CSV Yükle", "Öğrenciler", "Arşiv", "Oyunlar", "PIN Değiştir", "Veri & Yedek"]
    live = st.session_state.get("mode") == "live"
    if live:
        tab_names.append("Bekleme Listesi")
    tabs = st.tabs(tab_names)
    t1, t2, t3, t4, t5, t6 = tabs[:6]
    with t1:
        render_import_ui("adm")
    with t2:
        admin_students_tab()
    with t3:
        admin_archive_tab()
    with t4:
        admin_games_tab()
    with t5:
        admin_pin_tab()
    with t6:
        admin_data_tab()
    if live:
        with tabs[6]:
            admin_waitlist_tab()


PAGES = {
    PG_HOME: page_dashboard,
    PG_BRANCH: page_branch,
    PG_MATCH: page_match,
    PG_BOARD: page_leaderboard,
    PG_INDIV: page_individual,
    PG_GROUP: page_groups,
    PG_LIB: page_library,
    PG_ADMIN: page_admin,
}


def main():
    # --- GÜVENLİ GİRİŞ / PIN KONTROL SİSTEMİ ---
    if "authenticated" not in st.session_state:
        st.session_state.authenticated = False

    if st.session_state.get("mode") == "live" and not st.session_state.authenticated:
        st.markdown(LANDING_CSS, unsafe_allow_html=True)
        st.markdown(
            '<div class="lp-hero" style="max-width: 450px; margin: 4rem auto; text-align: center;">'
            '<div class="lp-eyebrow">🔒 Güvenli Yönetici Girişi</div>'
            '<div class="lp-h1" style="font-size: 1.8rem; margin-bottom: 1rem;">Yetkili PIN Kodu</div>'
            '<div class="lp-sub" style="margin-bottom: 1.5rem; font-size: 0.95rem;">Bu alan sadece size özeldir. Lütfen yönetici şifrenizi girin.</div>'
            '</div>',
            unsafe_allow_html=True,
        )
        
        col1, col2, col3 = st.columns([1, 1.5, 1])
        with col2:
            pin_input = st.text_input("Yönetici PIN / Şifre", type="password", key="admin_pin_box")
            if st.button("🔓 Giriş Yap", type="primary", use_container_width=True):
                # İstediğiniz şifreyi buraya yazabilirsiniz (Örn: neslihan)
                if pin_input == "neslihan" or pin_input == "1453": 
                    st.session_state.authenticated = True
                    st.rerun()
                else:
                    st.error("Hatalı şifre! Lütfen tekrar deneyin.")
            
            if st.button("← Ana Sayfaya Dön", use_container_width=True):
                st.session_state.mode = "landing"
                st.rerun()
        return
    # ---------------------------------------------
    st.set_page_config(
        page_title="Akıl ve Zeka Oyunları Paneli", page_icon="🧠", layout="wide", initial_sidebar_state="auto"
    )
    ensure_theme_config()
    init_db()
    inject_css()

    mode = st.session_state.get("mode")
    if mode not in ("demo", "live"):
        render_landing()
        return

    
    if mode == "demo":
        seed_demo_data()

    with st.sidebar:
        st.markdown(
            '<div class="brand"><div class="brand-logo">'
            + icon("brain", 24) + '</div><div>'
            '<div class="brand-t">Akıl ve Zeka<br>Oyunları</div><div class="brand-s">Yönetim & Takip</div></div></div>',
            unsafe_allow_html=True,
        )
        st.markdown('<div class="side-label">Menü</div>', unsafe_allow_html=True)
        page = st.radio("Menü", list(PAGES.keys()), label_visibility="collapsed", key="nav",
                        on_change=reset_match_tab)
        if is_admin():
            st.markdown(
                '<div class="side-note admin-on"><span class="dot"></span><b>Yönetici modu: AÇIK</b>'
                "<small>Silme, düzenleme, Excel yükleme ve veri girişleri açık.</small></div>",
                unsafe_allow_html=True,
            )
            st.button("Yönetici Çıkışı", key="side_logout", on_click=admin_logout, use_container_width=True)
        else:
            st.markdown(
                '<div class="side-note admin-off"><span class="dot"></span><b>Salt Okunur Mod</b>'
                "<small>Verileri görüntüleyebilir ve inceleyebilirsiniz. Veri girişi ve düzenleme için Yönetici Paneli'ne girin.</small></div>",
                unsafe_allow_html=True,
            )
        if mode == "demo":
            st.button("Demoyu Sıfırla", key="side_demo_reset", on_click=reset_demo, use_container_width=True)
            st.button("← Demoyu Bitir", key="side_home", on_click=back_to_landing, use_container_width=True)
        else:
            st.button("← Karşılama Ekranı", key="side_home", on_click=back_to_landing, use_container_width=True)

    if mode == "demo":
        demo_banner()
    show_flash()
    PAGES[page]()
    render_footer()


if __name__ == "__main__":
    main()
