


import random
import base64
import json
import os
import uuid
import time
import threading
import asyncio
import logging
import glob
import datetime
from pathlib import Path
import string
import ssl
import websockets
from apscheduler.schedulers.background import BackgroundScheduler

# Load .env file from current and parent directory
try:
    from dotenv import load_dotenv
    # Load backend's own .env first
    local_env_path = Path(__file__).resolve().parent / '.env'
    if local_env_path.exists():
        load_dotenv(local_env_path)
        
    # Then load frontend's .env
    env_path = Path(__file__).resolve().parent.parent / '.env'
    if env_path.exists():
        load_dotenv(env_path)
except Exception:
    pass
from urllib.parse import urlparse, parse_qs, quote, urlencode

import jwt
import requests
import urllib.request
import urllib.error
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from encryption import encrypt, decrypt, hash_val, decrypt_row, decrypt_rows
from flask import Flask, request, jsonify, Response, redirect
from flask_compress import Compress
import psycopg2
import requests
from psycopg2 import Error as Psycopg2Error, IntegrityError as Psycopg2IntegrityError
from psycopg2.extras import RealDictCursor
import websockets

try:
    from supabase import create_client, Client
except ImportError:
    create_client = None

SUPABASE_URL = os.environ.get("NEXT_PUBLIC_SUPABASE_URL")
SUPABASE_KEY = os.environ.get("NEXT_PUBLIC_SUPABASE_PUBLISHABLE_KEY")
supabase_client = None
if create_client and SUPABASE_URL and SUPABASE_KEY:
    try:
        supabase_client = create_client(SUPABASE_URL, SUPABASE_KEY)
    except Exception as e:
        print("Failed to initialize supabase client:", e)
logging.basicConfig(level=logging.DEBUG)
# Suppress opening handshake traceback warnings for HEAD health checks
logging.getLogger('websockets.server').setLevel(logging.CRITICAL)
logging.getLogger('websockets.protocol').setLevel(logging.CRITICAL)
logging.getLogger('websockets').setLevel(logging.CRITICAL)

try:
    from google.oauth2 import service_account as ga_service_account
    from google.auth.transport import requests as ga_requests
    GOOGLE_AUTH_AVAILABLE = True
except Exception:
    GOOGLE_AUTH_AVAILABLE = False

app = Flask(__name__)
Compress(app)




app.config['JWT_SECRET'] = os.environ.get('JWT_SECRET')
app.config['JWT_ALGO'] = 'HS256'
app.config['JWT_EXP_SECONDS'] = 60 * 60 * 24 * 7
app.config['FCM_SERVICE_ACCOUNT'] = os.environ.get('FCM_SERVICE_ACCOUNT')
app.config['FCM_PROJECT_ID'] = os.environ.get('FCM_PROJECT_ID')
FCM_V1_URL_TEMPLATE = 'https://fcm.googleapis.com/v1/projects/{project_id}/messages:send'

# File transfer mode configuration
FILE_TRANSFER_MODE = os.environ.get('FILE_TRANSFER_MODE', 'server').lower()  # 'server' or 'webrtc'

# App version reported to clients (used for update detection).
# Keep in sync with package.json /version on the frontend.
APP_VERSION = os.environ.get('APP_VERSION', '1.0.0')

# ---------------------------------------------------------------------------
# Supabase Storage config
# ---------------------------------------------------------------------------

@app.route("/google-drive/token", methods=["OPTIONS"])
@app.route("/google-drive/refresh", methods=["OPTIONS"])
def cors_options():
    return '', 204

_fcm_sa_credentials = None
_fcm_sa_token = None
_fcm_sa_token_expiry = 0

DB_CONFIG = {
    "host": os.environ.get("DB_HOST"),
    "user": os.environ.get("DB_USER"),
    "password": os.environ.get("DB_PASSWORD"),
    "database": os.environ.get("DB_NAME"),
    "port": int(os.environ.get("DB_PORT")) if os.environ.get("DB_PORT") else 5432,
    "sslmode": os.environ.get("DB_SSLMODE"),
    "sslrootcert":os.environ.get("CA_cirtificate") ,
    "connect_timeout": 10,
}
_column_cache = {}

_db_conn = None

def map_exception_to_error_msg(e):
    err_str = str(e)
    if "connection" in err_str.lower() or "timeout" in err_str.lower() or "could not connect" in err_str.lower():
        return "Database connection error: The database server is currently unreachable. Please check connection configurations."
    if "permission denied" in err_str.lower() or "access denied" in err_str.lower():
        return "Access denied: The server does not have permission to execute this operation."
    if "transaction is aborted" in err_str.lower() or "transaction block" in err_str.lower():
        return "Database transaction aborted: A query failure occurred. Please reload and try again."
    return f"Internal Server Error: {err_str}"


def get_db():
    global _db_conn
    if _db_conn is None or _db_conn.closed:
        connect_kwargs = {
            "host": DB_CONFIG["host"], "user": DB_CONFIG["user"],
            "password": DB_CONFIG["password"], "database": DB_CONFIG["database"],
            "port": DB_CONFIG["port"], "sslmode": DB_CONFIG.get("sslmode", "disable"),
            "connect_timeout": DB_CONFIG.get("connect_timeout", 10),
        }
        if "sslrootcert" in DB_CONFIG:
            connect_kwargs["sslrootcert"] = DB_CONFIG["sslrootcert"]
        _db_conn = psycopg2.connect(**connect_kwargs)
        _db_conn.autocommit = False
    return _db_conn

ALLOWED_EXTENSIONS = {
    'png', 'jpg', 'jpeg', 'gif', 'mp4', 'mov', 'webm', 'mkv', 'avi', 'flv',
    'pdf', 'doc', 'docx', 'xls', 'xlsx', 'ppt', 'pptx', 'txt', 'csv',
    'zip', 'rar', '7z', 'apk', 'svg', 'mp3', 'wav', 'ogg', 'm4a', 'avif'
}



def generate_sw_no():
    for _ in range(100):
        sw = f"{random.randint(0, 9999):04d}"
        if not execute_query("SELECT 1 FROM users WHERE sw_no_hash = %s LIMIT 1", (hash_val(sw),), fetch=True):
            return sw
    return None

# Get the string from .env, or default to localhost if not found
origins_str = os.environ.get("ALLOWED_ORIGINS", "http://localhost:3000")
# Split by comma, remove whitespace, and convert to a set
ALLOWED_ORIGINS = {origin.strip() for origin in origins_str.split(",")}


@app.after_request
def add_cors_headers(response):
    if request.path.startswith('/google-drive/') or request.path.startswith('/google-login'):
        response.headers['Access-Control-Allow-Origin'] = '*'
        response.headers['Access-Control-Allow-Methods'] = 'GET, POST, OPTIONS'
        response.headers['Access-Control-Allow-Headers'] = 'Content-Type, Authorization'
    else:
        origin = request.headers.get("Origin")
        if origin in ALLOWED_ORIGINS:
            response.headers["Access-Control-Allow-Origin"] = origin
        response.headers["Access-Control-Allow-Headers"] = "Content-Type, Authorization"
        response.headers["Access-Control-Allow-Methods"] = "GET, POST, PUT, DELETE, OPTIONS"
        response.headers["Access-Control-Allow-Credentials"] = "true"
    return response

@app.route('/', defaults={'path': ''}, methods=['OPTIONS', 'GET', 'HEAD'])
@app.route('/<path:path>', methods=['OPTIONS'])
def handle_options(path):
    if request.method in ['GET', 'HEAD'] and path == '':
        return jsonify({"status": "ok"}), 200
    return "", 204

_authed_route_cache = {}
_rate_limit_store = {}

connected_clients = {}
connected_lock = threading.Lock()
ws_loop = None

SSE_CLIENTS = {}
SSE_CLIENT_COUNTER = 0
SSE_LOCK = threading.Lock()

MESSAGE_TRACKER = {}
MESSAGE_TRACKER_LOCK = threading.Lock()
MESSAGE_SSE_CLIENTS = {}
MESSAGE_SSE_COUNTER = 0
MESSAGE_SSE_LOCK = threading.Lock()

CALL_REQUESTS = {}
CALL_SIGNALS = {}
call_lock = threading.Lock()

def execute_query(query, params=None, fetch=False, commit=True, get_lastrowid=False):
    global _db_conn
    cur = None
    for attempt in range(2):
        try:
            conn = get_db()
            cur = conn.cursor(cursor_factory=RealDictCursor)
            cur.execute(query, params or ())
            if fetch:
                result = cur.fetchall()
                if commit:
                    conn.commit()
                return result
            if get_lastrowid:
                conn.commit()
                return cur.fetchone().get("id") if cur.description else None
            if commit:
                conn.commit()
            return
        except Psycopg2Error as e:
            app.logger.error(f"DB error: {e}")
            _db_conn = None
            if attempt == 1:
                raise
        finally:
            if cur: cur.close()

def get_user_by_email(email):
    rows = execute_query("SELECT * FROM users WHERE email_hash = %s LIMIT 1", (hash_val(email),), fetch=True)
    return decrypt_row(rows[0], ["username", "email", "sw_no"]) if rows else None

def get_user_by_id(uid):
    rows = execute_query("SELECT * FROM users WHERE id = %s LIMIT 1", (uid,), fetch=True)
    return decrypt_row(rows[0], ["username", "email", "sw_no"]) if rows else None

def get_auth_user_id():
    auth = request.headers.get('Authorization') or ''
    if not auth.startswith('Bearer '):
        return None
    token = auth.split(' ', 1)[1].strip()
    try:
        if isinstance(token, bytes):
            token = token.decode('utf-8')
        if (token.startswith("b'") and token.endswith("'")) or (token.startswith('b"') and token.endswith('"')):
            token = token[2:-1]
        if (token.startswith('"') and token.endswith('"')) or (token.startswith("'") and token.endswith("'")):
            token = token[1:-1]
        payload = jwt.decode(token, app.config['JWT_SECRET'], algorithms=[app.config.get('JWT_ALGO', 'HS256')])
        uid = payload.get('user_id') or payload.get('id') or payload.get('sub')
        return int(uid) if uid else None
    except Exception:
        return None

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

STORAGE_HOST_URL = os.environ.get("STORAGE_HOST_URL", "http://13.212.57.105:5006")
UPLOAD_FOLDER = os.path.join(os.path.dirname(os.path.abspath(__name__)), 'uploads')
os.makedirs(UPLOAD_FOLDER, exist_ok=True)

from flask import send_from_directory

@app.route('/uploads/<path:filename>')
def serve_upload(filename):
    return send_from_directory(UPLOAD_FOLDER, filename)

def save_file_to_supabase(file_obj, filename, mime_type, prefix="profiles"):
    if not supabase_client:
        # Fallback to local
        try:
            file_obj.seek(0)
            fname = secure_filename(f"{uuid.uuid4().hex}_{filename}")
            file_path = os.path.join(UPLOAD_FOLDER, fname)
            file_obj.save(file_path)
            relative_url = f"/uploads/{fname}"
            app.logger.info(f"File uploaded to local storage: {relative_url}")
            return {
                'type': 'local',
                'url': relative_url,
                'filename': fname,
                'mime_type': mime_type,
            }
        except Exception as e:
            app.logger.error(f"Failed to save local file: {e}")
            return None

    try:
        file_obj.seek(0)
        fname = secure_filename(f"{uuid.uuid4().hex}_{filename}")
        
        # Read the file contents
        file_bytes = file_obj.read()
        
        bucket_name = "uploads"
        
        # Upload the file
        res = supabase_client.storage.from_(bucket_name).upload(
            fname,
            file_bytes,
            {"content-type": mime_type}
        )
        
        # Construct the public URL
        public_url = supabase_client.storage.from_(bucket_name).get_public_url(fname)
        
        app.logger.info(f"File uploaded to Supabase: {public_url}")
        
        return {
            'type': 'supabase',
            'url': public_url,
            'filename': fname,
            'mime_type': mime_type,
        }
    except Exception as e:
        app.logger.error(f"Supabase upload failed: {e}")
        return None

def column_exists(table_name, column_name):
    key = f"{table_name}.{column_name}"
    if key in _column_cache:
        return _column_cache[key]
    conn = None; cur = None
    try:
        conn = get_db(); cur = conn.cursor()
        cur.execute("SELECT 1 FROM information_schema.columns WHERE table_name=%s AND column_name=%s", (table_name, column_name))
        result = cur.fetchone() is not None
        _column_cache[key] = result
        return result
    except Exception:
        _column_cache[key] = False
        return False
    finally:
        if cur: cur.close()

def add_column_if_missing(table_name, column_name, column_def):
    key = f"{table_name}.{column_name}"
    _column_cache.pop(key, None)
    try:
        if not column_exists(table_name, column_name):
            app.logger.info(f"Adding column {column_name} to {table_name}")
            execute_query(f"ALTER TABLE {table_name} ADD COLUMN {column_name} {column_def}", commit=True)
            _column_cache[key] = True
            return True
    except Exception as e:
        app.logger.exception(f"Failed to add column: {e}")
    return False

def check_rate_limit(user_id, max_per_second=10):
    key = str(user_id); now = time.time()
    if key not in _rate_limit_store:
        _rate_limit_store[key] = []
    _rate_limit_store[key] = [t for t in _rate_limit_store[key] if now - t < 1]
    if len(_rate_limit_store[key]) >= max_per_second:
        return False
    _rate_limit_store[key].append(now)
    return True




# ---------------------------------------------------------------------------
# FCM
# ---------------------------------------------------------------------------
def _load_service_account_credentials():
    sa = app.config.get('FCM_SERVICE_ACCOUNT')
    if not sa: return None
    try:
        if sa.strip().startswith('{'): return json.loads(sa)
        with open(sa, 'r', encoding='utf-8') as fh: return json.load(fh)
    except Exception:
        app.logger.exception('Failed to load service account info')
        return None

def _auto_config_service_account():
    if app.config.get('FCM_SERVICE_ACCOUNT'): return
    candidates = []
    try:
        candidates.extend(glob.glob(os.path.join(os.getcwd(), '*.json')))
        dl = Path.home() / 'Downloads'
        if dl.exists(): candidates.extend(glob.glob(str(dl / '*.json')))
        for p in candidates:
            try:
                with open(p, 'r', encoding='utf-8') as fh: j = json.load(fh)
                if isinstance(j, dict) and j.get('type') == 'service_account':
                    app.logger.info(f'Auto-configuring FCM from {p}')
                    app.config['FCM_SERVICE_ACCOUNT'] = str(p)
                    if not app.config.get('FCM_PROJECT_ID') and j.get('project_id'):
                        app.config['FCM_PROJECT_ID'] = j['project_id']
                    return
            except Exception: continue
    except Exception: pass
_auto_config_service_account()

def _get_fcm_v1_access_token():
    global _fcm_sa_credentials, _fcm_sa_token, _fcm_sa_token_expiry
    try:
        if not GOOGLE_AUTH_AVAILABLE: return None
        if _fcm_sa_credentials is None:
            info = _load_service_account_credentials()
            if not info: return None
            _fcm_sa_credentials = ga_service_account.Credentials.from_service_account_info(info, scopes=["https://www.googleapis.com/auth/firebase.messaging"])
        now = int(time.time())
        if _fcm_sa_token and _fcm_sa_token_expiry - 60 > now: return _fcm_sa_token
        req = ga_requests.Request(); _fcm_sa_credentials.refresh(req)
        _fcm_sa_token = _fcm_sa_credentials.token
        _fcm_sa_token_expiry = int(_fcm_sa_credentials.expiry.timestamp()) if _fcm_sa_credentials.expiry else now + 300
        return _fcm_sa_token
    except Exception:
        app.logger.exception('Failed to obtain FCM token')
        return None

def get_google_auth_request():
    try:
        if not GOOGLE_AUTH_AVAILABLE: return None
        info = _load_service_account_credentials()
        if not info: return None
        creds = ga_service_account.Credentials.from_service_account_info(info, scopes=["https://www.googleapis.com/auth/firebase.messaging"])
        req = ga_requests.Request(); creds.refresh(req)
        return creds.token
    except Exception:
        app.logger.exception('get_google_auth_request failed')
        return None

def send_fcm_request(token, title, body, data=None):  # NOSONAR
    try:
        sa = _load_service_account_credentials()
        if not sa or not GOOGLE_AUTH_AVAILABLE: return
        access_token = _get_fcm_v1_access_token()
        if not access_token: return
        project_id = app.config.get('FCM_PROJECT_ID') or sa.get('project_id')
        if not project_id: return
        url = FCM_V1_URL_TEMPLATE.format(project_id=project_id)
        if isinstance(data, dict):
            sn = data.get('sender_name') or data.get('sender_username') or data.get('sender') or data.get('senderName')
            if sn: title = str(sn)
        data_map = {k: str(v) for k, v in (data or {}).items()}
        if title is not None: data_map.setdefault('title', str(title))
        if body is not None: data_map.setdefault('body', str(body))
        body_obj = {'message': {'token': token, 'data': data_map, 'android': {'priority': 'HIGH'}}}
        req = urllib.request.Request(url, data=json.dumps(body_obj).encode('utf-8'), method='POST')
        req.add_header('Content-Type', 'application/json')
        req.add_header('Authorization', f'Bearer {access_token}')
        try:
            with urllib.request.urlopen(req, timeout=10) as resp:
                app.logger.debug(f'FCM response: {resp.read().decode("utf-8")}')
        except urllib.error.HTTPError as he:
            try: err = he.read().decode('utf-8')
            except Exception: err = str(he)
            app.logger.error(f'FCM HTTPError: {he.code} {err}')
            try:
                j = json.loads(err) if err else {}
                details = j.get('error', {}).get('details', []) if isinstance(j, dict) else []
                for d in details:
                    if isinstance(d, dict) and d.get('@type','').endswith('FcmError') and d.get('errorCode') in ('UNREGISTERED',):
                        execute_query('DELETE FROM push_tokens WHERE token=%s', (token,), commit=True); break  # NOSONAR
            except Exception: pass
    except Exception:
        app.logger.exception('FCM send error')

def send_fcm_message(user_id, title, body, data_payload=None):  # NOSONAR
    try:
        rows = execute_query("SELECT token FROM push_tokens WHERE user_id=%s", (user_id,), fetch=True)
        if not rows: return False
        token = rows[0].get('token')
        if not token: return False
        access_token = get_google_auth_request()
        if not access_token: return False
        project_id = app.config.get('FCM_PROJECT_ID') or 'vijaychat-70ca1'
        url = f'https://fcm.googleapis.com/v1/projects/{project_id}/messages:send'
        data_iter = {}
        if isinstance(data_payload, dict): data_iter = dict(data_payload)
        else:
            try: data_iter = json.loads(json.dumps(data_payload)) if data_payload is not None else {}
            except Exception: data_iter = {}
        if not isinstance(data_iter, dict): data_iter = {}
        sender_name = data_iter.get('sender_name') or data_iter.get('sender_username') or data_iter.get('sender') or data_iter.get('senderName')
        if not sender_name:
            sid = data_iter.get('sender_id') or data_iter.get('senderId') or data_iter.get('sender_id_str')
            if sid:
                try:
                    u = get_user_by_id(int(sid))
                    if u: sender_name = u.get('username')
                except Exception: pass
        notif_title = sender_name or title
        notif_body = body
        data_block = {k: str(v) for k, v in data_iter.items()}
        data_block['title'] = str(notif_title)
        data_block['body'] = str(notif_body)
        if sender_name: data_block['sender_name'] = str(sender_name)
        payload = {'message': {'token': token, 'notification': {'title': str(notif_title), 'body': str(notif_body)}, 'data': data_block, 'android': {'priority': 'HIGH'}}}
        headers = {'Authorization': f'Bearer {access_token}', 'Content-Type': 'application/json'}
        resp = requests.post(url, headers=headers, json=payload, timeout=10)
        if resp.status_code == 200: return True
        text = resp.text
        try:
            j = resp.json()
            for d in (j.get('error',{}).get('details',[]) or []):
                if isinstance(d,dict) and d.get('@type','').endswith('FcmError') and d.get('errorCode') in ('UNREGISTERED',):
                    execute_query('DELETE FROM push_tokens WHERE token=%s', (token,), commit=True); break
        except Exception:
            if resp.status_code == 404 and 'UNREGISTERED' in text.upper():
                execute_query('DELETE FROM push_tokens WHERE token=%s', (token,), commit=True)
        return False
    except Exception:
        app.logger.exception('send_fcm_message failed'); return False

def send_fcm_to_user(user_id, payload):
    try:
        rows = execute_query("SELECT token FROM push_tokens WHERE user_id=%s", (user_id,), fetch=True)
        if not rows: return
        title = payload.get('sender_username') or 'New Message'
        body = (payload.get('content') or '')[:120] or 'New message'
        for r in rows:
            if r.get('token'): send_fcm_request(r['token'], title, body, payload)
    except Exception: app.logger.exception('send_fcm_to_user failed')

def _send_fcm_v1_notification(token, title, body, data=None):
    try:
        if not all([token, title, body]): return False
        if not GOOGLE_AUTH_AVAILABLE or not _load_service_account_credentials(): return False
        send_fcm_request(token, title, body, data or {})
        return True
    except Exception: return False

def broadcast_fcm_message(title, body, data_payload=None, exclude_user_id=None):
    def _task():
        try:
            rows = execute_query("SELECT DISTINCT user_id FROM push_tokens", fetch=True)
            if not rows: return
            for r in rows:
                uid = r.get('user_id')
                if not uid or (exclude_user_id and str(uid) == str(exclude_user_id)): continue
                send_fcm_message(uid, title, body, data_payload)
        except Exception:
            app.logger.exception("broadcast_fcm_message task failed")
    threading.Thread(target=_task, daemon=True).start()

# ---------------------------------------------------------------------------
# WEBSOCKET
# ---------------------------------------------------------------------------
from http import HTTPStatus
from websockets.http import Headers

async def ws_http_handler(*args):
    try:
        # Support websockets < 14 (path, headers) and >= 14 (connection, request)
        if len(args) == 2 and hasattr(args[1], 'headers'):
            headers = args[1].headers
        elif len(args) == 2:
            headers = args[1]
        else:
            return None
            
        connection = headers.get("connection", "").lower() if hasattr(headers, "get") else ""
        upgrade = headers.get("upgrade", "").lower() if hasattr(headers, "get") else ""
        
        if "upgrade" not in connection and "upgrade" not in upgrade:
            return HTTPStatus.OK, [("Content-Length", "2"), ("Content-Type", "text/plain")], b"OK"
    except Exception as e:
        pass
    return None

async def ws_handler(*args):  # NOSONAR
    websocket = args[0]
    path = args[1] if len(args) > 1 else getattr(getattr(websocket, "request", None), "path", "/")
    user_id = None
    try:
        parsed = urlparse(path); qs = parse_qs(parsed.query)
        tokens = qs.get('token') or qs.get('jwt') or []
        if not tokens: await websocket.close(code=4001, reason='token required'); return
        token = tokens[0]
        try:
            payload = jwt.decode(token, app.config['JWT_SECRET'], algorithms=[app.config['JWT_ALGO']])
            user_id = str(payload.get('user_id'))
            if not user_id: await websocket.close(code=4002, reason='invalid token'); return
        except jwt.PyJWTError: await websocket.close(code=4003, reason='invalid token'); return
        with connected_lock: connected_clients.setdefault(user_id, set()).add(websocket)
        app.logger.info(f'WS connected user:{user_id}')
        async for raw in websocket:
            try:
                data = json.loads(raw); msg_type = data.get("t")
                if msg_type in ("delivered","delivered_batch"):
                    cids = data.get("cids",[data.get("cid")]); ldid=data.get("ldid"); conv=data.get("conv"); via=data.get("via","ws"); src=data.get("src","server")
                    if ldid and conv:
                        parts=conv.split("_")
                        if len(parts)==2:
                            sid,rid=int(parts[0]),int(parts[1])
                            receiver=sid if rid==int(user_id) else rid
                            execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE receiver_id=%s AND sender_id=%s AND id<=%s AND version<2",(receiver,int(user_id),ldid),commit=True)
                            publish_to_user(str(receiver),{"t":"delivered","conv":conv,"ldid":ldid,"v":2,"via":via,"src":src})
                    for cid in cids:
                        if not cid: continue
                        r=execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE client_id=%s AND version<2 RETURNING sender_id",(cid,),commit=True)
                        if r: publish_to_user(str(r[0]["sender_id"]),{"t":"delivered","cid":cid,"v":2,"via":via,"src":src})
                elif msg_type in ("seen","seen_range"):
                    conv=data.get("conv"); lsid=data.get("lsid"); from_id=data.get("from",lsid); via=data.get("via","ws"); src=data.get("src","server")
                    if conv and lsid:
                        parts=conv.split("_")
                        if len(parts)==2:
                            sid,rid=int(parts[0]),int(parts[1]); other=sid if rid==int(user_id) else rid; uid_int=int(user_id)
                            execute_query("UPDATE messages SET status='seen',version=3,status_updated_at=NOW() WHERE sender_id=%s AND receiver_id=%s AND id>=%s AND id<=%s AND version<3",(other,uid_int,from_id,lsid),commit=True)
                            publish_to_user(str(other),{"t":"seen","conv":conv,"lsid":lsid,"via":via,"src":src})
                elif msg_type=="status":
                    conv=data.get("conv"); ldid=data.get("ldid",0); lsid=data.get("lsid",0); via=data.get("via","ws"); src=data.get("src","server")
                    if conv:
                        parts=conv.split("_")
                        if len(parts)==2:
                            sid,rid=int(parts[0]),int(parts[1])
                            if ldid>0: execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE receiver_id=%s AND sender_id=%s AND id<=%s AND version<2",(rid,sid,ldid),commit=True)
                            if lsid>0 and lsid<=ldid: execute_query("UPDATE messages SET status='seen',version=3,status_updated_at=NOW() WHERE receiver_id=%s AND sender_id=%s AND id<=%s AND version<3",(rid,sid,lsid),commit=True)
                            publish_to_user(str(sid),{"t":"status","conv":conv,"ldid":ldid,"lsid":lsid,"v":3,"via":via,"src":src})
                # Send message via WebSocket (fallback when WebRTC unavailable)
                elif msg_type == "message":
                    try:
                        ws_sender_id = int(user_id)
                        ws_receiver_id = data.get("receiver_id")
                        ws_room_id = data.get("room_id")
                        if ws_receiver_id is not None: ws_receiver_id = int(ws_receiver_id)
                        if ws_room_id is not None: ws_room_id = int(ws_room_id)
                        ws_content = data.get("content", "")
                        ws_client_id = data.get("client_id")
                        ws_reply_to_id = int(data["reply_to_id"]) if data.get("reply_to_id") and str(data["reply_to_id"]).isdigit() else None
                        
                        if ws_receiver_id is None and ws_room_id is None:
                            await websocket.send(json.dumps({"t":"error","msg":"receiver_id or room_id required"}))
                            continue
                        
                        if ws_receiver_id is not None and ws_receiver_id != 0:
                            if execute_query("SELECT 1 FROM blocked_users WHERE (blocker_id=%s AND blocked_id=%s) OR (blocker_id=%s AND blocked_id=%s)",(ws_sender_id,ws_receiver_id,ws_receiver_id,ws_sender_id),fetch=True):
                                await websocket.send(json.dumps({"t":"error","msg":"blocked"}))
                                continue
                        enc_content = encrypt(ws_content)
                        ws_result=execute_query("INSERT INTO messages (client_id,sender_id,receiver_id,room_id,content,reply_to_id,files,status,version,server_timestamp,status_updated_at) VALUES (%s,%s,%s,%s,%s,'[]','sent',1,NOW(),NOW()) RETURNING id,client_id",(ws_client_id,ws_sender_id,ws_receiver_id,ws_room_id,enc_content,ws_reply_to_id),fetch=True,commit=True)
                        ws_message_id=ws_result[0].get("id") if ws_result else None
                        ws_mc_id=ws_result[0].get("client_id") if ws_result else None
                        
                        if ws_message_id:
                            ws_payload={"id":ws_message_id,"sender_id":ws_sender_id,"receiver_id":ws_receiver_id,"room_id":ws_room_id,"content":ws_content,"files":[],"client_id":ws_client_id}
                            ws_vtoken=jwt.encode({"message_id":ws_message_id,"client_id":ws_mc_id,"sender_id":ws_sender_id,"receiver_id":ws_receiver_id,"room_id":ws_room_id,"timestamp":time.time(),"status":"sent"},app.config['JWT_SECRET'],algorithm='HS256')
                            
                            try:
                                if ws_room_id is not None:
                                    ws_payload["sender_username"] = ""
                                    sender_row = execute_query("SELECT username FROM users WHERE id = %s", (ws_sender_id,), fetch=True)
                                    if sender_row:
                                        sender_row = decrypt_rows(sender_row, ["username"])
                                        ws_payload["su"] = sender_row[0]['username']
                                        ws_payload["sender_name"] = sender_row[0]['username']
                                    
                                    members = execute_query("SELECT user_id FROM chat_room_members WHERE room_id=%s", (ws_room_id,), fetch=True)
                                    for m in members:
                                        if str(m['user_id']) != str(ws_sender_id):
                                            publish_to_user(str(m['user_id']), ws_payload)
                                    execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE id=%s AND version<2",(ws_message_id,),commit=True)
                                    publish_to_user(str(ws_sender_id),{"t":"delivered","conv":f"room_{ws_room_id}","id":ws_message_id,"cid":ws_mc_id or str(ws_message_id),"v":2})
                                
                                elif ws_receiver_id == 0:
                                    ws_payload["sender_username"] = "Global Chat" # Quick patch
                                    sender_row = execute_query("SELECT username FROM users WHERE id = %s", (ws_sender_id,), fetch=True)
                                    if sender_row:
                                        sender_row = decrypt_rows(sender_row, ["username"])
                                        ws_payload["su"] = sender_row[0]['username']
                                        ws_payload["sender_username"] = sender_row[0]['username']
                                    msg = json.dumps(ws_payload)
                                    async def _send_all_global():
                                        to_remove=[]
                                        with connected_lock:
                                            all_conns = [ws for conns in connected_clients.values() for ws in conns]
                                        for ws in all_conns:
                                            try: await ws.send(msg)
                                            except Exception: to_remove.append(ws)
                                        if to_remove:
                                            with connected_lock:
                                                for uid, conns in list(connected_clients.items()):
                                                    for r in to_remove:
                                                        if r in conns: conns.remove(r)
                                                    if not conns: del connected_clients[uid]
                                    asyncio.create_task(_send_all_global())
                                else:
                                    publish_to_user(str(ws_receiver_id),ws_payload)
                                    execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE id=%s AND version<2",(ws_message_id,),commit=True)
                                    publish_to_user(str(ws_sender_id),{"t":"delivered","conv":f"{min(ws_sender_id,ws_receiver_id)}_{max(ws_sender_id,ws_receiver_id)}","id":ws_message_id,"cid":ws_mc_id or str(ws_message_id),"v":2})
                            except Exception: pass
                            
                            try: 
                                if ws_receiver_id is not None and ws_receiver_id != 0:
                                    execute_query("INSERT INTO unread_counts (receiver_id,sender_id,count) VALUES (%s,%s,1) ON CONFLICT (receiver_id,sender_id) DO UPDATE SET count=unread_counts.count+1",(ws_receiver_id,ws_sender_id),commit=True)
                            except Exception: pass
                            
                            try:
                                sender_row = execute_query("SELECT username FROM users WHERE id = %s", (ws_sender_id,), fetch=True)
                                sender_row = decrypt_rows(sender_row, ["username"])
                                sender_name = sender_row[0]['username'] if sender_row else "Someone"
                                if ws_room_id is not None:
                                    room_row = execute_query("SELECT name FROM chat_rooms WHERE id=%s", (ws_room_id,), fetch=True)
                                    room_name = room_row[0]['name'] if room_row else 'Room'
                                    preview = (ws_content or '').strip()[:120] if ws_content and ws_content.strip() else 'sent an attachment'
                                    room_members = execute_query("SELECT user_id FROM chat_room_members WHERE room_id=%s", (ws_room_id,), fetch=True)
                                    for m in room_members or []:
                                        if str(m['user_id']) != str(ws_sender_id):
                                            send_fcm_message(
                                                int(m['user_id']),
                                                room_name,
                                                f"@{sender_name}: {preview}",
                                                {"type": "room_message", "room_id": str(ws_room_id), "sender_id": str(ws_sender_id), "room_name": room_name}
                                            )
                                elif ws_receiver_id is not None and ws_receiver_id != 0:
                                    send_fcm_message(
                                        int(ws_receiver_id),
                                        "New Message",
                                        f"@{sender_name} sent you a message.",
                                        {"type": "chat", "sender_id": str(ws_sender_id)}
                                    )
                            except Exception:
                                pass
                                
                            await websocket.send(json.dumps({"t":"confirm","id":ws_message_id,"client_id":ws_client_id,"verification_token":ws_vtoken}))
                    except Exception as e:
                        app.logger.exception('WS message send error')
                        try: await websocket.send(json.dumps({"t":"error","msg":str(e)}))
                        except: pass

            except Exception: pass
    except websockets.exceptions.ConnectionClosed: pass
    except Exception: app.logger.exception('WS handler error')
    finally:
        try:
            with connected_lock:
                conns=connected_clients.get(user_id)
                if conns and websocket in conns:
                    conns.remove(websocket)
                    if not conns: del connected_clients[user_id]
        except Exception: pass



def publish_to_user(user_id, payload):  # NOSONAR
    try:
        with connected_lock: conns=list(connected_clients.get(str(user_id),[]))
        if not conns: return
        msg=json.dumps(payload)
        async def _send_all():
            to_remove=[]
            sent=0
            for ws in conns:
                try: await ws.send(msg); sent+=1
                except Exception: to_remove.append(ws)
            if to_remove:
                with connected_lock:
                    cur=connected_clients.get(str(user_id),set())
                    for r in to_remove:
                        if r in cur: cur.remove(r)
                    if not cur: connected_clients.pop(str(user_id),None)
        try:
            if ws_loop and getattr(ws_loop,'is_running',lambda:False)():
                future=asyncio.run_coroutine_threadsafe(_send_all(),ws_loop)
                future.add_done_callback(lambda f: app.logger.exception('WS pub error') if f.exception() else None)
            else:
                loop=asyncio.new_event_loop(); loop.run_until_complete(_send_all()); loop.close()
        except Exception: app.logger.exception('Failed to schedule WS publish')
    except Exception: app.logger.exception('Failed to publish WS message')

def sse_broadcast(user_id, _event_type, data):
    with SSE_LOCK:
        for client in SSE_CLIENTS.get(user_id,[]):
            if "queue" in client: client["queue"].append(data)

def _broadcast_to_sse(user_id, event_type, data):
    with MESSAGE_SSE_LOCK:
        for client in MESSAGE_SSE_CLIENTS.get(str(user_id),[]):
            try: client["queue"].append({"event":event_type,"data":data})
            except Exception: pass

# ---------------------------------------------------------------------------
# MIGRATIONS / STARTUP
# ---------------------------------------------------------------------------

def ensure_core_tables():
    app.logger.info("Ensuring core tables exist...")
    queries = [
        '''CREATE TABLE IF NOT EXISTS users (
            id SERIAL PRIMARY KEY,
            username text,
            email text NOT NULL,
            email_hash VARCHAR(64),
            sw_no text,
            sw_no_hash VARCHAR(64),
            created_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP,
            profile_picture_url character varying(255),
            bio text,
            google_id character varying(255),
            google_refresh_token text,
            google_access_token text,
            google_token_expiry bigint DEFAULT 0
        )''',
        '''CREATE TABLE IF NOT EXISTS messages (
            id SERIAL PRIMARY KEY,
            sender_id integer NOT NULL,
            receiver_id integer NOT NULL,
            content text,
            reply_to_id integer,
            files jsonb DEFAULT '[]'::jsonb,
            deleted_by_sender boolean DEFAULT false,
            deleted_by_receiver boolean DEFAULT false,
            seen boolean DEFAULT false,
            created_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP,
            client_id character varying(100),
            version integer DEFAULT 1,
            server_timestamp timestamp without time zone DEFAULT CURRENT_TIMESTAMP,
            status_updated_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP,
            conversation_id character varying(100),
            client_timestamp timestamp without time zone,
            status character varying(20) DEFAULT 'sent'::character varying
        )''',
        '''CREATE TABLE IF NOT EXISTS friend_requests (
            id SERIAL PRIMARY KEY,
            sender_id integer NOT NULL,
            receiver_id integer NOT NULL,
            status character varying(20) DEFAULT 'pending'::character varying,
            created_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP
        )''',
        '''CREATE TABLE IF NOT EXISTS blocked_users (
            blocker_id integer NOT NULL,
            blocked_id integer NOT NULL,
            created_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP
        )''',
        '''CREATE TABLE IF NOT EXISTS profiles (
            id SERIAL PRIMARY KEY,
            user_id integer NOT NULL,
            bio text,
            location character varying(255),
            profile_picture_url character varying(500),
            updated_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP
        )''',

        '''CREATE TABLE IF NOT EXISTS user_sessions (
            id SERIAL PRIMARY KEY,
            user_id integer NOT NULL,
            session_id character varying(100) NOT NULL,
            last_seen timestamp without time zone DEFAULT CURRENT_TIMESTAMP,
            is_online boolean DEFAULT true
        )''',
        '''CREATE TABLE IF NOT EXISTS trades (
            id SERIAL PRIMARY KEY,
            user_id integer NOT NULL,
            type character varying(10) NOT NULL,
            symbol character varying(50) NOT NULL,
            price numeric NOT NULL,
            qty numeric NOT NULL,
            created_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP
        )''',
        '''CREATE TABLE IF NOT EXISTS withdrawals (
            id SERIAL PRIMARY KEY,
            user_id integer NOT NULL,
            amount numeric NOT NULL,
            method character varying(20) NOT NULL,
            details text NOT NULL,
            status character varying(20) DEFAULT 'pending'::character varying,
            notes text,
            created_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP,
            updated_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP
        )''',
        '''CREATE TABLE IF NOT EXISTS message_delivery (
            client_msg_id character varying(128) NOT NULL,
            server_msg_id character varying(128),
            sender_id integer NOT NULL,
            receiver_id integer NOT NULL,
            content text,
            files jsonb DEFAULT '[]'::jsonb,
            reply_to_id integer,
            client_timestamp bigint,
            server_timestamp bigint NOT NULL,
            status character varying(20) NOT NULL DEFAULT 'SENT'::character varying,
            created_at timestamp without time zone DEFAULT CURRENT_TIMESTAMP
        )''',
        '''CREATE TABLE IF NOT EXISTS trader_comments (
            id SERIAL PRIMARY KEY,
            trader_id INTEGER NOT NULL,
            commenter_id INTEGER NOT NULL,
            content TEXT NOT NULL,
            trade_date_str VARCHAR(255),
            parent_id INTEGER REFERENCES trader_comments(id) ON DELETE CASCADE,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )''',
        '''ALTER TABLE trader_comments ADD COLUMN IF NOT EXISTS parent_id INTEGER REFERENCES trader_comments(id) ON DELETE CASCADE;''',
        '''CREATE TABLE IF NOT EXISTS news_comments (
            id SERIAL PRIMARY KEY,
            news_url VARCHAR(500) NOT NULL,
            user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            content TEXT NOT NULL,
            created_at TIMESTAMP WITHOUT TIME ZONE DEFAULT CURRENT_TIMESTAMP
        )''',
        '''CREATE TABLE IF NOT EXISTS news_likes (
            id SERIAL PRIMARY KEY,
            news_url VARCHAR(500) NOT NULL,
            user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            created_at TIMESTAMP WITHOUT TIME ZONE DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(news_url, user_id)
        )''',
        '''CREATE TABLE IF NOT EXISTS followers (
            id SERIAL PRIMARY KEY,
            follower_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            following_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(follower_id, following_id)
        )''',
        '''CREATE TABLE IF NOT EXISTS saved_profiles (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            saved_user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(user_id, saved_user_id)
        )''',
        '''CREATE TABLE IF NOT EXISTS trade_notifications (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            trader_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            content TEXT NOT NULL,
            is_read BOOLEAN DEFAULT false,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )''',
        '''CREATE TABLE IF NOT EXISTS app_downloads (
            id SERIAL PRIMARY KEY,
            platform VARCHAR(50),
            architecture VARCHAR(50),
            timestamp TIMESTAMP WITHOUT TIME ZONE DEFAULT CURRENT_TIMESTAMP
        )'''
    ]
    for q in queries:
        try:
            execute_query(q, commit=True)
        except Exception as e:
            app.logger.error(f"Failed to create table: {e}")
    # Migrate existing tables — add hash columns if missing
    for col in ["email_hash VARCHAR(64)", "sw_no_hash VARCHAR(64)"]:
        try:
            execute_query(f"ALTER TABLE users ADD COLUMN IF NOT EXISTS {col}", commit=True)
        except Exception as e:
            app.logger.error(f"Migration failed: {e}")


def ensure_push_tokens_table():
    try:
        execute_query("""CREATE TABLE IF NOT EXISTS push_tokens (
            user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            token VARCHAR(500) NOT NULL, platform VARCHAR(50),
            last_updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, token));""", commit=True)
    except Exception: app.logger.exception('Failed to ensure push_tokens table')

def ensure_unread_table():
    try:
        execute_query("""CREATE TABLE IF NOT EXISTS unread_counts (
            receiver_id INTEGER NOT NULL, sender_id INTEGER NOT NULL,
            count INTEGER DEFAULT 0, PRIMARY KEY (receiver_id, sender_id));""", commit=True)
    except Exception: app.logger.exception('Failed to ensure unread_counts table')

def ensure_feed_tables():
    try:
        execute_query("""CREATE TABLE IF NOT EXISTS feed_posts (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            content TEXT,
            trade_symbol VARCHAR(50),
            trade_type VARCHAR(20),
            trade_qty NUMERIC,
            trade_price NUMERIC,
            created_at TIMESTAMP WITHOUT TIME ZONE DEFAULT CURRENT_TIMESTAMP
        );""", commit=True)
        execute_query("""CREATE TABLE IF NOT EXISTS feed_likes (
            user_id INTEGER REFERENCES users(id) ON DELETE CASCADE,
            post_id INTEGER REFERENCES feed_posts(id) ON DELETE CASCADE,
            created_at TIMESTAMP WITHOUT TIME ZONE DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, post_id)
        );""", commit=True)
        execute_query("""CREATE TABLE IF NOT EXISTS feed_comments (
            id SERIAL PRIMARY KEY,
            post_id INTEGER REFERENCES feed_posts(id) ON DELETE CASCADE,
            user_id INTEGER REFERENCES users(id) ON DELETE CASCADE,
            content TEXT NOT NULL,
            created_at TIMESTAMP WITHOUT TIME ZONE DEFAULT CURRENT_TIMESTAMP
        );""", commit=True)
    except Exception: app.logger.exception('Failed to ensure feed tables')

def ensure_chat_rooms():
    try:
        execute_query("""CREATE TABLE IF NOT EXISTS chat_rooms (
            id SERIAL PRIMARY KEY,
            name VARCHAR(255) NOT NULL,
            created_by INTEGER REFERENCES users(id) ON DELETE SET NULL,
            is_public BOOLEAN DEFAULT true,
            icon_url VARCHAR(500),
            description TEXT,
            created_at TIMESTAMP WITHOUT TIME ZONE DEFAULT CURRENT_TIMESTAMP
        );""", commit=True)
        try: add_column_if_missing("chat_rooms", "icon_url", "VARCHAR(500)")
        except Exception: pass
        try: add_column_if_missing("chat_rooms", "description", "TEXT")
        except Exception: pass
        
        execute_query("""CREATE TABLE IF NOT EXISTS chat_room_members (
            room_id INTEGER REFERENCES chat_rooms(id) ON DELETE CASCADE,
            user_id INTEGER REFERENCES users(id) ON DELETE CASCADE,
            joined_at TIMESTAMP WITHOUT TIME ZONE DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (room_id, user_id)
        );""", commit=True)
        
        execute_query("ALTER TABLE messages ADD COLUMN IF NOT EXISTS room_id INTEGER REFERENCES chat_rooms(id) ON DELETE CASCADE;", commit=True)
        execute_query("ALTER TABLE messages ALTER COLUMN receiver_id DROP NOT NULL;", commit=True)
    except Exception: app.logger.exception('Failed to ensure chat_rooms tables/columns')

# ---------------------------------------------------------------------------
# AUTH & USERS
# ---------------------------------------------------------------------------
@app.route("/login", methods=["POST"])
def login():
    try:
        data=request.json or {}; email=data.get("email"); password=data.get("password")
        if not email or not password: return jsonify({"error":"Email and password required"}),400
        user=get_user_by_email(email)
        if not user: return jsonify({"error":"User not found"}),404  # NOSONAR
        if not user.get("password"): return jsonify({"error":"No password set"}),400
        if not check_password_hash(user["password"],password): return jsonify({"error":"Password is incorrect"}),401
        user.pop("password",None)
        execute_query("UPDATE users SET last_login = CURRENT_TIMESTAMP, last_seen = CURRENT_TIMESTAMP WHERE id = %s", (user.get("id"),), commit=True)
        token=jwt.encode({"user_id":user.get("id")},app.config['JWT_SECRET'],algorithm=app.config['JWT_ALGO'])
        return jsonify({"message":"Login successful","user":user,"token":token}),200
    except Exception as e: return jsonify({"error":"Login failed","details":map_exception_to_error_msg(e)}),500

@app.route("/google-login", methods=["POST"])
def google_login():
    """Accept Google ID token, verify it, create/find user, return JWT."""
    data = request.get_json(force=True) or {}
    id_token = data.get("id_token")
    temp_token = data.get("temp_token")
    if not id_token:
        return jsonify({"error": "id_token required"}), 400

    try:
        # Verify token with Google's tokeninfo endpoint
        resp = requests.get(
            f"https://oauth2.googleapis.com/tokeninfo?id_token={id_token}",
            timeout=10,
        )
        if resp.status_code != 200:
            return jsonify({"error": "Invalid Google token"}), 401

        info = resp.json()
        email = info.get("email")
        name = info.get("name") or info.get("email", "").split("@")[0]
        google_id = info.get("sub")
        picture = info.get("picture", "")

        if not email or not google_id:
            return jsonify({"error": "Google token missing email or sub"}), 400

        # Handle Verification of Temporary Account
        temp_user_id = None
        if temp_token:
            try:
                payload = jwt.decode(temp_token, app.config['JWT_SECRET'], algorithms=[app.config['JWT_ALGO']])
                temp_user_id = payload.get("user_id")
            except Exception:
                pass

        if temp_user_id:
            # Check if this Google account is already used by someone else
            existing_google = execute_query("SELECT id FROM users WHERE google_id = %s LIMIT 1", (google_id,), fetch=True)
            if existing_google and str(existing_google[0]["id"]) != str(temp_user_id):
                return jsonify({"error": "This Google account is already linked to another user profile!"}), 400
                
            # Update the temporary user's row with the new verified Google data
            # This automatically "moves" all their data since the ID stays exactly the same
            enc_email = encrypt(email)
            execute_query(
                "UPDATE users SET google_id = %s, email = %s, email_hash = %s, profile_picture_url = %s WHERE id = %s",
                (google_id, enc_email, hash_val(email), picture or None, temp_user_id), commit=True
            )
            
            # Fetch the updated user to return
            updated = execute_query("SELECT * FROM users WHERE id = %s LIMIT 1", (temp_user_id,), fetch=True)
            if updated:
                user_row = dict(decrypt_rows(updated, ["username", "email", "sw_no"])[0])
                token = jwt.encode({"user_id": user_row.get("id")}, app.config["JWT_SECRET"], algorithm=app.config["JWT_ALGO"])
                return jsonify({"message": "Account successfully verified!", "user": user_row, "token": token}), 200

        overwrite = data.get("overwrite", False)
        adopt = data.get("adopt", False)

        # Standard Google Login Flow
        # Look up user by google_id first (exact match)
        existing = execute_query(
            "SELECT * FROM users WHERE google_id = %s LIMIT 1",
            (google_id,), fetch=True,
        )
        
        if not existing:
            # Check if there is an unverified temporary account with this email
            existing = execute_query(
                "SELECT * FROM users WHERE email_hash = %s LIMIT 1",
                (hash_val(email),), fetch=True,
            )
            if existing and not existing[0].get("google_id"):
                if adopt:
                    # User clicked "This is me!", so we allow it to fall through and verify the account
                    pass 
                elif not overwrite:
                    return jsonify({
                        "error": "unverified_account_exists",
                        "message": f"An unverified temporary account was found for {email}.",
                        "email": email
                    }), 409
                else:
                    # Archive the fake account safely by mangling its email
                    fake_id = existing[0]["id"]
                    fake_email = f"fake_{fake_id}_{email}"
                    execute_query(
                        "UPDATE users SET email = %s, email_hash = %s WHERE id = %s", 
                        (encrypt(fake_email), hash_val(fake_email), fake_id), 
                        commit=True
                    )
                    existing = None # Proceed to create a new one
                    
        if existing:
            existing = decrypt_rows(existing, ["username", "email", "sw_no"])
            user_row = dict(existing[0])
            if not user_row.get("google_id"):
                execute_query("UPDATE users SET google_id = %s WHERE id = %s", (google_id, user_row["id"]), commit=True)
                user_row["google_id"] = google_id
            
            if user_row.get("email") != email:
                execute_query("UPDATE users SET email = %s, email_hash = %s WHERE id = %s", (encrypt(email), hash_val(email), user_row["id"]), commit=True)
                user_row["email"] = email

            if picture and user_row.get("profile_picture_url") != picture:
                execute_query("UPDATE users SET profile_picture_url = %s WHERE id = %s", (picture, user_row["id"]), commit=True)
                user_row["profile_picture_url"] = picture
            elif not picture and user_row.get("profile_picture_url"):
                execute_query("UPDATE users SET profile_picture_url = NULL WHERE id = %s", (user_row["id"],), commit=True)
                user_row["profile_picture_url"] = None
        else:
            sw_no = generate_sw_no()
            enc_name = encrypt(name)
            enc_email = encrypt(email)
            enc_sw = encrypt(sw_no)
            execute_query(
                "INSERT INTO users (username, email, email_hash, google_id, sw_no, sw_no_hash, profile_picture_url, created_at) VALUES (%s, %s, %s, %s, %s, %s, %s, %s)",
                (enc_name, enc_email, hash_val(email), google_id, enc_sw, hash_val(sw_no), picture or None, datetime.datetime.now(datetime.timezone.utc)),
                commit=True,
            )
            created = execute_query(
                "SELECT * FROM users WHERE email_hash = %s LIMIT 1",
                (hash_val(email),), fetch=True,
            )
            created = decrypt_rows(created, ["username", "email", "sw_no"])
            if not created:
                return jsonify({"error": "User creation failed"}), 500
            user_row = dict(created[0])
            
            execute_query("INSERT INTO wallets (user_id, balance) VALUES (%s, 1000.0)", (user_row["id"],), commit=True)
            try:
                broadcast_fcm_message("New User Joined!", f"@{name} just joined the app!", {"type": "new_user"}, exclude_user_id=user_row["id"])
            except Exception: pass

        # Update last login and seen
        execute_query("UPDATE users SET last_login = CURRENT_TIMESTAMP, last_seen = CURRENT_TIMESTAMP WHERE id = %s", (user_row.get("id"),), commit=True)

        # Generate JWT matching the /login response format
        token = jwt.encode(
            {"user_id": user_row.get("id")},
            app.config["JWT_SECRET"],
            algorithm=app.config["JWT_ALGO"],
        )
        return jsonify({"message": "Login successful", "user": user_row, "token": token}), 200

    except requests.RequestException as e:
        return jsonify({"error": "Failed to verify Google token", "details": map_exception_to_error_msg(e)}), 502
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/temporary-login", methods=["POST"])
def temporary_login():
    """Allows a user to login temporarily using just an email. 
    They have 5 days to verify the account using Google Login before it is locked."""
    data = request.get_json(force=True) or {}
    email = data.get("email")
    if not email:
        return jsonify({"error": "Email is required for temporary login."}), 400
    
    email = email.lower().strip()
    
    try:
        existing = execute_query(
            "SELECT id, username, email, google_id, sw_no, profile_picture_url, created_at FROM users WHERE email_hash = %s LIMIT 1",
            (hash_val(email),), fetch=True,
        )
        existing = decrypt_rows(existing, ["username", "email", "sw_no"])
        
        if existing:
            user_row = dict(existing[0])
            
            # 1. If already verified with Google, block temporary login!
            if user_row.get("google_id"):
                return jsonify({"error": "This account is already verified. Please use the 'Continue with Google' button."}), 403
                
            # 2. Check if 5 days have passed since creation
            created_at = user_row.get("created_at")
            if created_at:
                if created_at.tzinfo is None:
                    created_at = created_at.replace(tzinfo=datetime.timezone.utc)
                now = datetime.datetime.now(datetime.timezone.utc)
                if (now - created_at).days >= 5:
                    return jsonify({"error": "Your temporary period has expired! Please verify your account using the 'Continue with Google' button."}), 403
            
            # Temporary login successful
            token = jwt.encode(
                {"user_id": user_row.get("id")},
                app.config["JWT_SECRET"],
                algorithm=app.config["JWT_ALGO"],
            )
            return jsonify({"message": "Temporary login successful.", "user": user_row, "token": token}), 200
            
        else:
            # Check if creation is allowed by frontend
            if data.get("allow_creation") is False:
                return jsonify({"error": "Daily limit reached. You can only create 3 temporary accounts per day, but you can still login to existing ones."}), 403

            # Create a new temporary user
            sw_no = generate_sw_no()
            name = data.get("name")
            if not name or not str(name).strip():
                name = email.split("@")[0]
            name = str(name).strip()
            enc_name = encrypt(name)
            enc_email = encrypt(email)
            enc_sw = encrypt(sw_no)
            
            execute_query(
                "INSERT INTO users (username, email, email_hash, google_id, sw_no, sw_no_hash, profile_picture_url, created_at) VALUES (%s, %s, %s, %s, %s, %s, %s, %s)",
                (enc_name, enc_email, hash_val(email), None, enc_sw, hash_val(sw_no), None, datetime.datetime.now(datetime.timezone.utc)),
                commit=True,
            )
            created = execute_query(
                "SELECT id, username, email, google_id, sw_no, profile_picture_url, created_at FROM users WHERE email_hash = %s LIMIT 1",
                (hash_val(email),), fetch=True,
            )
            created = decrypt_rows(created, ["username", "email", "sw_no"])
            if not created:
                return jsonify({"error": "Failed to create temporary user."}), 500
                
            user_row = dict(created[0])
            execute_query("INSERT INTO wallets (user_id, balance) VALUES (%s, 1000.0)", (user_row["id"],), commit=True)
            try:
                broadcast_fcm_message("New User Joined!", f"@{name} just joined the app!", {"type": "new_user"}, exclude_user_id=user_row["id"])
            except Exception: pass
            
            token = jwt.encode(
                {"user_id": user_row.get("id")},
                app.config["JWT_SECRET"],
                algorithm=app.config["JWT_ALGO"],
            )
            return jsonify({"message": "Temporary account created successfully.", "user": user_row, "token": token}), 200
            
    except Exception as e:
        app.logger.error(f"Temporary login error: {e}")
        return jsonify({"error": map_exception_to_error_msg(e)}), 500


@app.route("/auth/google", methods=["GET"])
def auth_google():
    """Redirect to Google OAuth consent screen for sign-in."""
    origin = request.args.get("origin", "http://localhost:5173")
    client_id = os.environ.get("client_id")

    if not client_id:
        return jsonify({"error": "GOOGLE_CLIENT_ID not configured"}), 500

    scheme = request.headers.get("X-Forwarded-Proto", request.scheme)
    host = request.host
    redirect_uri = f"{scheme}://{host}/auth/google/callback"

    state = base64.urlsafe_b64encode(json.dumps({"origin": origin}).encode()).decode()

    auth_url = (
        "https://accounts.google.com/o/oauth2/v2/auth?"
        f"client_id={client_id}"
        f"&redirect_uri={quote(redirect_uri)}"
        "&response_type=code"
        "&access_type=offline"
        f"&state={state}"
        "&scope=openid%20email%20profile"
        "&prompt=consent"
    )
    return redirect(auth_url, 302)

@app.route("/auth/google/callback", methods=["GET"])
def auth_google_callback():
    """Handle Google OAuth callback, exchange code, create/find user, redirect to frontend."""
    code = request.args.get("code")
    state_raw = request.args.get("state")
    error = request.args.get("error")

    if error:
        return f"<script>if(window.opener){{window.opener.postMessage({{type:'google_login',error:'{error}'}},'*')}};window.close()</script>", 400

    if not code:
        return jsonify({"error": "Authorization code required"}), 400

    try:
        state = json.loads(base64.urlsafe_b64decode(state_raw.encode()).decode()) if state_raw else {}
    except Exception:
        state = {}
    origin = state.get("origin", "http://localhost:5173")

    client_id = os.environ.get("client_id")
    client_secret = os.environ.get("client_secret")
    if not client_id or not client_secret:
        return jsonify({"error": "Google OAuth not configured"}), 500

    scheme = request.headers.get("X-Forwarded-Proto", request.scheme)
    host = request.host
    redirect_uri = f"{scheme}://{host}/auth/google/callback"

    try:
        # Exchange authorization code for tokens
        token_url = "https://oauth2.googleapis.com/token"
        params = urlencode({
            "code": code,
            "client_id": client_id,
            "client_secret": client_secret,
            "redirect_uri": redirect_uri,
            "grant_type": "authorization_code"
        })
        req = urllib.request.Request(token_url, data=params.encode(), method="POST")
        req.add_header("Content-Type", "application/x-www-form-urlencoded")
        with urllib.request.urlopen(req) as resp:
            tokens = json.loads(resp.read())

        id_token = tokens.get("id_token")
        if not id_token:
            return jsonify({"error": "No ID token received"}), 400

        # Verify the ID token with Google's tokeninfo endpoint
        verify_resp = requests.get(
            f"https://oauth2.googleapis.com/tokeninfo?id_token={id_token}",
            timeout=10,
        )
        if verify_resp.status_code != 200:
            return jsonify({"error": "Token verification failed"}), 401

        info = verify_resp.json()
        email = info.get("email")
        name = info.get("name") or (email or "").split("@")[0]
        google_id = info.get("sub")
        picture = info.get("picture", "")

        if not email or not google_id:
            return jsonify({"error": "Missing email or sub"}), 400

        # Find or create user — google_id first, then email_hash fallback
        existing = execute_query(
            "SELECT id, username, email, google_id, sw_no, profile_picture_url FROM users WHERE google_id = %s LIMIT 1",
            (google_id,), fetch=True,
        )
        if not existing:
            existing = execute_query(
                "SELECT id, username, email, google_id, sw_no, profile_picture_url FROM users WHERE email_hash = %s LIMIT 1",
                (hash_val(email),), fetch=True,
            )
        existing = decrypt_rows(existing, ["username", "email", "sw_no"])
        if existing:
            user_row = dict(existing[0])
            if not user_row.get("google_id"):
                execute_query("UPDATE users SET google_id = %s WHERE id = %s", (google_id, user_row["id"]), commit=True)
                user_row["google_id"] = google_id
            
            if user_row.get("email") != email:
                execute_query("UPDATE users SET email = %s, email_hash = %s WHERE id = %s", (encrypt(email), hash_val(email), user_row["id"]), commit=True)
                user_row["email"] = email

            if picture and user_row.get("profile_picture_url") != picture:
                execute_query("UPDATE users SET profile_picture_url = %s WHERE id = %s", (picture, user_row["id"]), commit=True)
                user_row["profile_picture_url"] = picture
            elif not picture and user_row.get("profile_picture_url"):
                execute_query("UPDATE users SET profile_picture_url = NULL WHERE id = %s", (user_row["id"],), commit=True)
                user_row["profile_picture_url"] = None
        else:
            sw_no = generate_sw_no()
            enc_name = encrypt(name)
            enc_email = encrypt(email)
            enc_sw = encrypt(sw_no)
            execute_query(
                "INSERT INTO users (username, email, email_hash, google_id, sw_no, sw_no_hash, profile_picture_url, created_at) VALUES (%s, %s, %s, %s, %s, %s, %s, %s)",
                (enc_name, enc_email, hash_val(email), google_id, enc_sw, hash_val(sw_no), picture or None, datetime.datetime.now(datetime.timezone.utc)),
                commit=True,
            )
            created = execute_query(
                "SELECT id, username, email, google_id, sw_no, profile_picture_url FROM users WHERE email_hash = %s LIMIT 1",
                (hash_val(email),), fetch=True,
            )
            created = decrypt_rows(created, ["username", "email", "sw_no"])
            if not created:
                return jsonify({"error": "User creation failed"}), 500
            user_row = dict(created[0])
            try:
                broadcast_fcm_message("New User Joined!", f"@{name} just joined the app!", {"type": "new_user"}, exclude_user_id=user_row["id"])
            except Exception: pass

        # Generate JWT
        token = jwt.encode(
            {"user_id": user_row.get("id")},
            app.config["JWT_SECRET"],
            algorithm=app.config["JWT_ALGO"],
        )

        # Extract Drive tokens from the OAuth response
        gd_access_token = tokens.get("access_token", "")
        gd_refresh_token = tokens.get("refresh_token", "")
        gd_expires_in = tokens.get("expires_in", 3600)

        user_json_str = json.dumps(user_row)
        html = f"""<!doctype html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Signing in...</title>
    <style>
      body {{ font-family: Arial, sans-serif; display: flex; justify-content: center; align-items: center; height: 100vh; margin: 0; background: #f5f5f5; }}
      .container {{ text-align: center; padding: 40px; background: white; border-radius: 8px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); }}
      .spinner {{ width: 40px; height: 40px; border: 4px solid #f3f3f3; border-top: 4px solid #4285f4; border-radius: 50%; animation: spin 1s linear infinite; margin: 0 auto 20px; }}
      @keyframes spin {{ 0% {{ transform: rotate(0deg); }} 100% {{ transform: rotate(360deg); }} }}
    </style>
  </head>
  <body>
    <div class="container">
      <div class="spinner"></div>
      <p id="message">Signed in! You can close this window.</p>
    </div>
    <script>
      if (window.opener) {{
        window.opener.postMessage({{
          type: 'google_login',
          token: '{token}',
          user: {user_json_str},
          gd_token: '{gd_access_token}',
          gd_refresh_token: '{gd_refresh_token}',
          gd_expiry: '{gd_expires_in}'
        }}, '*');
      }}
      setTimeout(function() {{ window.close(); }}, 1000);
    </script>
  </body>
</html>"""
        return html, 200

    except Exception as e:
        app.logger.exception("Google auth callback failed")
        return f"<script>if(window.opener){{window.opener.postMessage({{type:'google_login',error:'{str(e)}'}},'*')}};window.close()</script>", 500


@app.route("/auth/google/store-tokens", methods=["POST"])
def auth_google_store_tokens():
    """Store Google Drive tokens on the server for a user."""
    data = request.get_json(force=True) or {}
    refresh_token = data.get("refresh_token")
    access_token = data.get("access_token")
    expires_in = data.get("expires_in", 3600)

    uid = get_auth_user_id()
    if not uid:
        return jsonify({"error": "Authentication required"}), 401
    if not refresh_token:
        return jsonify({"error": "refresh_token required"}), 400

    try:
        expiry = int(time.time()) + int(expires_in)
        execute_query(
            "UPDATE users SET google_refresh_token = %s, google_access_token = %s, google_token_expiry = %s WHERE id = %s",
            (encrypt(refresh_token), encrypt(access_token or ""), expiry, uid), commit=True,
        )
        return jsonify({"message": "Tokens stored"}), 200
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/auth/google/access-token", methods=["GET"])
def auth_google_access_token():
    """Return a valid Google Drive access token for the authenticated user, refreshing if needed."""
    uid = get_auth_user_id()
    if not uid:
        return jsonify({"error": "Authentication required"}), 401

    try:
        user = get_user_by_id(uid)
        if not user:
            return jsonify({"error": "User not found in database. Please login again."}), 404

        enc_refresh_token = user.get("google_refresh_token")
        if not enc_refresh_token:
            return jsonify({"error": "No Google Drive refresh token. Sign in with Google again."}), 400

        refresh_token = decrypt(enc_refresh_token)
        stored_access_token = decrypt(user.get("google_access_token") or "")
        stored_expiry = user.get("google_token_expiry") or 0

        # If access token is still valid (> 5 min buffer), return it
        if stored_access_token and int(stored_expiry) > int(time.time()) + 300:
            return jsonify({"access_token": stored_access_token, "expires_in": int(stored_expiry) - int(time.time())}), 200

        # Refresh the access token
        client_id = os.environ.get("VITE_GOOGLE_CLIENT_ID")
        client_secret = os.environ.get("VITE_GOOGLE_CLIENT_SECRET")
        if not client_id or not client_secret:
            return jsonify({"error": "Server OAuth not configured"}), 500

        token_url = "https://oauth2.googleapis.com/token"
        params = urlencode({
            "client_id": client_id,
            "client_secret": client_secret,
            "refresh_token": refresh_token,
            "grant_type": "refresh_token",
        })
        req = urllib.request.Request(token_url, data=params.encode(), method="POST")
        req.add_header("Content-Type", "application/x-www-form-urlencoded")
        with urllib.request.urlopen(req) as resp:
            tokens = json.loads(resp.read())

        new_access_token = tokens.get("access_token")
        new_expires_in = tokens.get("expires_in", 3600)
        new_expiry = int(time.time()) + int(new_expires_in)

        if new_access_token:
            execute_query(
                "UPDATE users SET google_access_token = %s, google_token_expiry = %s WHERE id = %s",
                (encrypt(new_access_token), new_expiry, uid), commit=True,
            )

        return jsonify({"access_token": new_access_token, "expires_in": new_expires_in}), 200

    except urllib.error.HTTPError as e:
        if e.code == 400:
            # Refresh token invalid — clear stored tokens
            try:
                execute_query(
                    "UPDATE users SET google_refresh_token = NULL, google_access_token = NULL, google_token_expiry = 0 WHERE id = %s",
                    (uid,), commit=True,
                )
            except Exception:
                pass
            return jsonify({"error": "Google session expired. Sign in with Google again."}), 401
        return jsonify({"error": f"Token refresh failed: {e.code}"}), 502
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/google-drive/token", methods=["POST"])
def google_drive_exchange_token():
    """Exchange OAuth code for access and refresh tokens"""
    data=request.get_json(force=True) or {}
    code=data.get("code")
    client_id=data.get("client_id")
    client_secret=data.get("client_secret")
    redirect_uri=data.get("redirect_uri")
    
    if not code or not client_id or not client_secret or not redirect_uri:
        return jsonify({"error":"code, client_id, client_secret, and redirect_uri required"}),400
    
    try:
        import urllib.parse
        import urllib.request
        
        # Exchange code for tokens
        token_url = "https://oauth2.googleapis.com/token"
        params = urllib.parse.urlencode({
            "code": code,
            "client_id": client_id,
            "client_secret": client_secret,
            "redirect_uri": redirect_uri,
            "grant_type": "authorization_code"
        })
        
        req = urllib.request.Request(token_url, data=params.encode(), method="POST")
        req.add_header("Content-Type", "application/x-www-form-urlencoded")
        
        with urllib.request.urlopen(req) as response:
            tokens = json.loads(response.read())
            
        access_token = tokens.get("access_token")
        refresh_token = tokens.get("refresh_token")
        expires_in = tokens.get("expires_in")
        
        if not access_token:
            return jsonify({"error":"Failed to get access token"}),400
            
        return jsonify({
            "access_token": access_token,
            "refresh_token": refresh_token,
            "expires_in": expires_in
        }),200
        
    except Exception as e:
        app.logger.error(f"Google Drive token exchange failed: {e}")
        return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/google-drive/refresh", methods=["POST"])
def google_drive_refresh_token():
    """Refresh access token using refresh token"""
    data=request.get_json(force=True) or {}
    refresh_token=data.get("refresh_token")
    client_id=data.get("client_id")
    client_secret=data.get("client_secret")
    
    if not refresh_token or not client_id or not client_secret:
        return jsonify({"error":"refresh_token, client_id, and client_secret required"}),400
    
    try:
        import urllib.parse
        import urllib.request
        
        token_url = "https://oauth2.googleapis.com/token"
        params = urllib.parse.urlencode({
            "client_id": client_id,
            "client_secret": client_secret,
            "refresh_token": refresh_token,
            "grant_type": "refresh_token"
        })
        
        req = urllib.request.Request(token_url, data=params.encode(), method="POST")
        req.add_header("Content-Type", "application/x-www-form-urlencoded")
        
        with urllib.request.urlopen(req) as response:
            tokens = json.loads(response.read())
            
        access_token = tokens.get("access_token")
        expires_in = tokens.get("expires_in")
        
        if not access_token:
            return jsonify({"error":"Failed to refresh access token"}),400
            
        return jsonify({
            "access_token": access_token,
            "expires_in": expires_in
        }),200
        
    except Exception as e:
        app.logger.error(f"Google Drive token refresh failed: {e}")
        return jsonify({"error":map_exception_to_error_msg(e)}),500

# In-memory cache for drive proxy (key=file_id, value=(timestamp, Response))


@app.route("/register", methods=["POST"])
def register():
    data=request.get_json(force=True) or {}; email=data.get("email"); username=data.get("username"); sw_no=data.get("sw_no"); password=data.get("password")
    if not all([email,username,sw_no,password]): return jsonify({"error":"All fields required"}),400
    try:
        existing = execute_query("SELECT id FROM users WHERE email_hash=%s LIMIT 1",(hash_val(email),),fetch=True)
        if not existing: return jsonify({"error":"Google login required first"}),400
        uid = existing[0]["id"]
        hashed=generate_password_hash(password)
        execute_query("UPDATE users SET username=%s,email=%s,email_hash=%s,sw_no=%s,sw_no_hash=%s,password=%s WHERE id=%s",
                      (encrypt(username), encrypt(email), hash_val(email), encrypt(sw_no), hash_val(sw_no), hashed, uid),commit=True)
        profile=execute_query("SELECT id,username,sw_no,email FROM users WHERE id=%s",(uid,),fetch=True)
        profile = decrypt_rows(profile, ["username", "email", "sw_no"])
        return jsonify({"message":"Registered successfully","user":profile[0]}),201
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/traders", methods=["GET"])
def get_traders():
    try:
        users = execute_query("""
            SELECT u.id, u.username, u.profile_picture_url, u.bio, u.is_private, COALESCE(w.balance, 0) as wallet_balance, (u.google_id IS NOT NULL) as is_verified
            FROM users u
            LEFT JOIN wallets w ON u.id = w.user_id
            WHERE EXISTS (SELECT 1 FROM trades WHERE user_id = u.id)
        """, fetch=True)
        
        user_ids = [u["id"] for u in users]
        if user_ids:
            placeholders = ','.join(['%s'] * len(user_ids))
            trades = execute_query(f"""
                SELECT user_id, type, symbol, price, qty
                FROM trades
                WHERE user_id IN ({placeholders})
                ORDER BY created_at ASC
            """, tuple(user_ids), fetch=True)
            
            user_pnls = {uid: 0.0 for uid in user_ids}
            user_invested = {uid: 0.0 for uid in user_ids}
            user_holdings = {uid: {} for uid in user_ids}
            
            for t in trades:
                uid = t["user_id"]
                sym = t["symbol"]
                qty = float(t["qty"])
                price = float(t["price"])
                t_type = t["type"].lower()
                
                if sym not in user_holdings[uid]:
                    user_holdings[uid][sym] = {"qty": 0.0, "total_cost": 0.0}
                
                h = user_holdings[uid][sym]
                if t_type == "buy":
                    h["qty"] += qty
                    cost = qty * price
                    h["total_cost"] += cost
                    user_invested[uid] += cost
                elif t_type == "sell":
                    avg_cost = (h["total_cost"] / h["qty"]) if h["qty"] > 0 else 0
                    trade_profit = (price - avg_cost) * qty
                    user_pnls[uid] += trade_profit
                    h["qty"] -= qty
                    h["total_cost"] -= (avg_cost * qty)
                    if h["qty"] < 1e-8:
                        h["qty"] = 0.0
                        h["total_cost"] = 0.0
            
            for u in users:
                u["realized_pnl"] = user_pnls[u["id"]]
                u["total_invested"] = user_invested[u["id"]]
        else:
            for u in users:
                u["realized_pnl"] = 0.0
                u["total_invested"] = 0.0

        users.sort(key=lambda x: x["realized_pnl"], reverse=True)
        users = decrypt_rows(users, ["username"])
        return jsonify(users), 200
    except Exception as e:
        app.logger.exception("Failed to fetch traders directory")
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/wallet", methods=["GET"])
def get_wallet():
    try:
        user_id = request.args.get("user_id")
        if not user_id:
            return jsonify({"error": "user_id required"}), 400
        try:
            uid = int(user_id)
        except (ValueError, TypeError):
            return jsonify({"error": "user_id must be an integer"}), 400
            
        auth_uid = get_auth_user_id()
        if auth_uid is None or auth_uid != uid:
            return jsonify({"error": "Authentication mismatch or token invalid"}), 401
            
        user_check = execute_query("SELECT 1 FROM users WHERE id=%s", (uid,), fetch=True)
        if not user_check:
            return jsonify({"error": "User not found in database. Please login again."}), 404

        wallet = execute_query("SELECT * FROM wallets WHERE user_id=%s", (uid,), fetch=True)
        if not wallet:
            milestones = execute_query("SELECT COALESCE(SUM(reward_amount),0) AS total FROM instagram_milestone_rewards WHERE user_id=%s", (uid,), fetch=True)
            milestone_earned = float(milestones[0]["total"]) if milestones else 0
            total_earned = milestone_earned
            execute_query("INSERT INTO wallets (user_id, balance, total_earned) VALUES (%s,%s,%s) ON CONFLICT (user_id) DO NOTHING", (uid, total_earned, total_earned), commit=True)
            wallet = execute_query("SELECT * FROM wallets WHERE user_id=%s", (uid,), fetch=True)

        w = wallet[0]
        return jsonify({
            "user_id": w["user_id"],
            "balance": float(w["balance"]),
            "total_earned": float(w["total_earned"]),
            "updated_at": str(w["updated_at"])
        })
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/wallet/sync", methods=["POST"])
def sync_wallet():
    try:
        data = request.get_json() or {}
        user_id = data.get("user_id")
        if not user_id:
            return jsonify({"error": "user_id required"}), 400
        try:
            uid = int(user_id)
        except (ValueError, TypeError):
            return jsonify({"error": "user_id must be an integer"}), 400
            
        auth_uid = get_auth_user_id()
        if auth_uid is None or auth_uid != uid:
            return jsonify({"error": "Authentication mismatch or token invalid"}), 401
            
        user_check = execute_query("SELECT 1 FROM users WHERE id=%s", (uid,), fetch=True)
        if not user_check:
            return jsonify({"error": "User not found in database. Please login again."}), 404

        milestones = execute_query("SELECT COALESCE(SUM(reward_amount),0) AS total FROM instagram_milestone_rewards WHERE user_id=%s", (uid,), fetch=True)
        milestone_earned = float(milestones[0]["total"]) if milestones else 0
        total_earned = milestone_earned

        execute_query("""
            INSERT INTO wallets (user_id, balance, total_earned, updated_at)
            VALUES (%s,%s,%s,CURRENT_TIMESTAMP)
            ON CONFLICT (user_id) DO UPDATE SET
                balance=EXCLUDED.total_earned,
                total_earned=EXCLUDED.total_earned,
                updated_at=CURRENT_TIMESTAMP
        """, (uid, total_earned, total_earned), commit=True)

        return jsonify({"user_id": uid, "balance": total_earned, "total_earned": total_earned})
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/users", methods=["GET"])
def get_users():
    try:
        rows=execute_query("SELECT id,username,email,created_at,profile_picture_url,profile_pictures,is_private, (google_id IS NOT NULL) as is_verified FROM users",fetch=True)
        decrypted = decrypt_rows(rows, ["username", "email"])
        filtered = []
        for r in decrypted:
            if not r.get("email", "").startswith("fake_"):
                r.pop("email", None) # Remove email for privacy before returning
                filtered.append(r)
        return jsonify(filtered),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/users/<int:uid>", methods=["GET"])
def get_user(uid):
    try:
        user=get_user_by_id(uid)
        if not user: return jsonify({"error":"User not found in database. Please login again."}),404
        user.pop("password",None); return jsonify(user),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/users/<int:uid>", methods=["PUT"])
def update_user(uid):
    data=request.get_json(force=True) or {}; username=data.get("username"); sw_no=data.get("sw_no"); password=data.get("password")
    if not all([username,sw_no]): return jsonify({"error":"username, sw_no required"}),400
    try:
        enc_user = encrypt(username)
        enc_sw = encrypt(sw_no)
        if password:
            execute_query("UPDATE users SET username=%s,sw_no=%s,sw_no_hash=%s,password=%s WHERE id=%s",(enc_user,enc_sw,hash_val(sw_no),generate_password_hash(password),uid),commit=True)
        else:
            execute_query("UPDATE users SET username=%s,sw_no=%s,sw_no_hash=%s WHERE id=%s",(enc_user,enc_sw,hash_val(sw_no),uid),commit=True)
        return jsonify({"message":"User updated successfully"}),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/profile/<int:user_id>", methods=["GET"])
def get_user_profile(user_id):
    try:
        user=execute_query("SELECT id,username,email,sw_no,created_at,profile_picture_url,profile_pictures,bio, (google_id IS NOT NULL) as is_verified FROM users WHERE id=%s LIMIT 1",(user_id,),fetch=True)
        if not user: return jsonify({"error":"User not found in database. Please login again."}),404
        
        follows_row = execute_query("SELECT COUNT(*) as count FROM instagram_follows WHERE user_id = %s", (user_id,), fetch=True)
        v_count = follows_row[0]['count'] if follows_row else 0
        
        profile_data = decrypt_row(user[0], ["username", "email", "sw_no"])
        if profile_data.get("email", "").startswith("fake_"):
            return jsonify({"error":"User not found"}),404
            
        profile_data.pop("email", None)
        profile_data["instagram_follows_count"] = v_count
        return jsonify(profile_data), 200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500


@app.route("/profile/<int:user_id>", methods=["PUT"])
def update_user_profile(user_id):
    try:
        user_check = execute_query("SELECT profile_pictures FROM users WHERE id=%s", (user_id,), fetch=True)
        if not user_check:
            return jsonify({"error": "User not found in database. Please login again."}), 404

        current_pictures = user_check[0].get("profile_pictures") or []

        data=request.form; bio=data.get("bio"); pp_url=None

        existing_pictures_str = data.get("existing_pictures")
        if existing_pictures_str:
            import json
            try:
                current_pictures = json.loads(existing_pictures_str)
            except Exception:
                pass

        uploaded_urls = []
        for f in request.files.getlist("profile_pictures"):
            if f and allowed_file(f.filename):
                sb_result = save_file_to_supabase(f, f.filename, f.mimetype)
                if sb_result: uploaded_urls.append(sb_result['url'])
        
        if "profile_picture" in request.files and len(request.files.getlist("profile_pictures")) == 0:
            f=request.files["profile_picture"]
            if f and allowed_file(f.filename):
                sb_result = save_file_to_supabase(f, f.filename, f.mimetype)
                if sb_result: 
                    current_pictures.insert(0, sb_result['url'])
        
        current_pictures.extend(uploaded_urls)
        current_pictures = current_pictures[:10]

        fields=[]; params=[]
        if bio is not None: fields.append("bio=%s"); params.append(bio)
        
        import json
        fields.append("profile_pictures=%s"); params.append(json.dumps(current_pictures))
        if len(current_pictures) > 0:
            fields.append("profile_picture_url=%s"); params.append(current_pictures[0])
        else:
            fields.append("profile_picture_url=NULL")

        if not fields: return jsonify({"message":"No fields to update"}),200
        execute_query(f"UPDATE users SET {', '.join(fields)} WHERE id=%s",tuple(params+[user_id]),commit=True)
        return jsonify({"message":"User profile updated successfully", "profile_pictures": current_pictures}),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/delete_user/<int:user_id>", methods=["DELETE","OPTIONS"])
def delete_user(user_id):
    if request.method=="OPTIONS": return jsonify({"message":"OK"}),200
    uid = get_auth_user_id()
    if uid is None: return jsonify({"error":"Authentication required"}),401
    if uid != user_id: return jsonify({"error":"Not authorized to delete this user"}),403
    try:
        for q in [
            "DELETE FROM friend_requests WHERE sender_id=%s OR receiver_id=%s",
            "DELETE FROM messages WHERE sender_id=%s OR receiver_id=%s",
            "DELETE FROM blocked_users WHERE blocker_id=%s OR blocked_id=%s",

            "DELETE FROM user_sessions WHERE user_id=%s",
            "DELETE FROM push_tokens WHERE user_id=%s",
            "DELETE FROM users WHERE id=%s",
        ]: execute_query(q,(user_id,),commit=True)
        return jsonify({"message":"User deleted successfully"}),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

# ---------------------------------------------------------------------------
# FRIEND REQUESTS
# ---------------------------------------------------------------------------
@app.route("/friend-request", methods=["POST"])
def send_friend_request():
    try:
        data=request.get_json(silent=True) or {}; sid=data.get("sender_id"); sw=data.get("sw_no")
        if not sid or not sw: return jsonify({"error":"sender_id and sw_no required"}),400
        try:
            sid = int(sid)
        except (ValueError, TypeError):
            return jsonify({"error":"sender_id must be an integer"}),400
        uid = get_auth_user_id()
        if uid is None or uid != sid:
            return jsonify({"error":"Authentication mismatch"}),401
        recv=execute_query("SELECT id,username FROM users WHERE sw_no_hash=%s LIMIT 1",(hash_val(sw),),fetch=True)
        recv = decrypt_rows(recv, ["username"])
        if not recv: return jsonify({"error":"User not found with this SW number"}),404
        rid=recv[0]["id"]
        if rid==sid: return jsonify({"error":"Cannot send to yourself"}),400
        if execute_query("SELECT 1 FROM blocked_users WHERE (blocker_id=%s AND blocked_id=%s) OR (blocker_id=%s AND blocked_id=%s) LIMIT 1",(sid,rid,rid,sid),fetch=True):
            return jsonify({"error":"User is blocked"}),403
        if execute_query("SELECT 1 FROM friend_requests WHERE ((sender_id=%s AND receiver_id=%s) OR (sender_id=%s AND receiver_id=%s)) AND status='accepted' LIMIT 1",(sid,rid,rid,sid),fetch=True):
            return jsonify({"error":"Already friends"}),400
        ex=execute_query("SELECT id,status FROM friend_requests WHERE (sender_id=%s AND receiver_id=%s) OR (sender_id=%s AND receiver_id=%s) ORDER BY id DESC LIMIT 1",(sid,rid,rid,sid),fetch=True)
        if ex and ex[0]["status"]=="pending": return jsonify({"error":"Pending request exists"}),400
        # After successfully inserting the friend request, notify the receiver via FCM
        try:
            sender_row = execute_query("SELECT username FROM users WHERE id = %s", (sid,), fetch=True)
            sender_row = decrypt_rows(sender_row, ["username"])
            sender_name = sender_row[0]['username'] if sender_row else "Someone"

            send_fcm_message(
                int(rid),
                "Friend Request",
                f"@{sender_name} sent you a friend request.",
                {"type": "friend_request", "sender_id": str(sid)},
            )
        except Exception as notif_err:
            app.logger.exception("Failed to send friend request notification")
        res=execute_query("INSERT INTO friend_requests (sender_id,receiver_id,status,created_at) VALUES (%s,%s,'pending',%s) RETURNING id",(sid,rid,datetime.datetime.now(datetime.timezone.utc)),commit=True,fetch=True)
        if not res: return jsonify({"error":"Insert failed"}),500
        created=execute_query("SELECT * FROM friend_requests WHERE id=%s LIMIT 1",(res[0]["id"],),fetch=True)  # NOSONAR
        return jsonify(created[0]),201
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/friend-requests/<int:user_id>", methods=["GET"])
def get_friend_requests(user_id):
    try:
        uid = get_auth_user_id()
        if uid is None:
            return jsonify({"error":"Not authorized"}),403
        user_check = execute_query("SELECT 1 FROM users WHERE id=%s", (user_id,), fetch=True)
        if not user_check:
            return jsonify({"error": "User not found in database. Please login again."}), 404
        inc=execute_query("SELECT f.id,f.status,s.id as sender_id,s.username as sender_name,s.sw_no as sender_sw, s.email as sender_email, (s.google_id IS NOT NULL) as is_verified FROM friend_requests f JOIN users s ON s.id=f.sender_id WHERE f.receiver_id=%s AND f.status='pending' ORDER BY f.id DESC",(user_id,),fetch=True)
        out=execute_query("SELECT f.id,f.status,r.id as receiver_id,r.username as receiver_name,r.sw_no as receiver_sw, r.email as receiver_email, (r.google_id IS NOT NULL) as is_verified FROM friend_requests f JOIN users r ON r.id=f.receiver_id WHERE f.sender_id=%s AND f.status='pending' ORDER BY f.id DESC",(user_id,),fetch=True)
        
        inc_decrypted = decrypt_rows(inc, ["sender_name", "sender_sw", "sender_email"])
        out_decrypted = decrypt_rows(out, ["receiver_name", "receiver_sw", "receiver_email"])
        
        filtered_inc = []
        for r in inc_decrypted:
            if not r.get("sender_email", "").startswith("fake_"):
                r.pop("sender_email", None)
                filtered_inc.append(r)
                
        filtered_out = []
        for r in out_decrypted:
            if not r.get("receiver_email", "").startswith("fake_"):
                r.pop("receiver_email", None)
                filtered_out.append(r)
                
        return jsonify({
            "incoming": filtered_inc,
            "outgoing": filtered_out
        }),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/friend-requests/<int:req_id>/accept", methods=["POST"])
def accept_friend_request(req_id):
    try:
        uid = get_auth_user_id()
        if uid is None:
            return jsonify({"error":"Authentication required"}),401
        u=execute_query("SELECT * FROM friend_requests WHERE id=%s LIMIT 1",(req_id,),fetch=True)
        if not u: return jsonify({"error":"Request not found"}),404
        if u[0]["receiver_id"] != uid:
            return jsonify({"error":"Not authorized to accept this request"}),403
        execute_query("UPDATE friend_requests SET status='accepted' WHERE id=%s AND status='pending'",(req_id,),commit=True)
        updated=execute_query("SELECT * FROM friend_requests WHERE id=%s LIMIT 1",(req_id,),fetch=True)
        return jsonify(updated[0]),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/friend-requests/<int:req_id>/reject", methods=["POST"])
def reject_friend_request(req_id):
    try:
        uid = get_auth_user_id()
        if uid is None:
            return jsonify({"error":"Authentication required"}),401
        u=execute_query("SELECT * FROM friend_requests WHERE id=%s LIMIT 1",(req_id,),fetch=True)
        if not u: return jsonify({"error":"Request not found"}),404
        if u[0]["receiver_id"] != uid:
            return jsonify({"error":"Not authorized to reject this request"}),403
        execute_query("UPDATE friend_requests SET status='rejected' WHERE id=%s AND status='pending'",(req_id,),commit=True)
        updated=execute_query("SELECT * FROM friend_requests WHERE id=%s LIMIT 1",(req_id,),fetch=True)
        return jsonify(updated[0]),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/friends/<int:user_id>", methods=["GET"])
def get_friends(user_id):
    try:
        uid = get_auth_user_id()
        if uid is None:
            return jsonify({"error":"Not authorized"}),403
        user_check = execute_query("SELECT 1 FROM users WHERE id=%s", (user_id,), fetch=True)
        if not user_check:
            return jsonify({"error": "User not found in database. Please login again."}), 404
        f=execute_query("SELECT u.id,u.username,u.email,u.sw_no,u.created_at,u.profile_picture_url,u.profile_pictures, (u.google_id IS NOT NULL) as is_verified FROM users u JOIN friend_requests f ON((f.sender_id=u.id AND f.receiver_id=%s) OR (f.receiver_id=u.id AND f.sender_id=%s)) WHERE f.status='accepted' OR (f.status='pending' AND f.receiver_id=%s)",(user_id,user_id,user_id),fetch=True)
        decrypted = decrypt_rows(f, ["username", "email", "sw_no"])
        filtered = []
        for r in decrypted:
            if not r.get("email", "").startswith("fake_"):
                filtered.append(r)
        return jsonify(filtered),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/remove_friend", methods=["POST","OPTIONS"])
def remove_friend():
    if request.method=="OPTIONS": return jsonify({"message":"OK"}),200
    try:
        data=request.json or {}; uid=data.get("user_id"); fid=data.get("friend_id")
        if not uid or not fid: return jsonify({"error":"user_id and friend_id required"}),400
        try:
            uid = int(uid)
            fid = int(fid)
        except (ValueError, TypeError):
            return jsonify({"error":"user_id and friend_id must be integers"}),400
        auth_uid = get_auth_user_id()
        if auth_uid is None or auth_uid != uid:
            return jsonify({"error":"Not authorized to remove friend"}),403
        execute_query("DELETE FROM friend_requests WHERE (sender_id=%s AND receiver_id=%s) OR (sender_id=%s AND receiver_id=%s)",(uid,fid,fid,uid),commit=True)
        return jsonify({"message":"Friend removed successfully"}),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

# ---------------------------------------------------------------------------
# BLOCK / UNBLOCK
# ---------------------------------------------------------------------------
@app.route("/block_user", methods=["POST","OPTIONS"])
def block_user():
    if request.method=="OPTIONS": return jsonify({"message":"OK"}),200
    try:
        data=request.json or {}; b1=data.get("blocker_id"); b2=data.get("blocked_id")
        if not b1 or not b2: return jsonify({"error":"blocker_id and blocked_id required"}),400  # NOSONAR
        try: execute_query("INSERT INTO blocked_users (blocker_id,blocked_id) VALUES (%s,%s)",(b1,b2),commit=True)
        except Psycopg2IntegrityError: pass
        return jsonify({"message":"User blocked successfully"}),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/is_blocked", methods=["GET"])
def is_blocked():
    b1=request.args.get("blocker_id"); b2=request.args.get("blocked_id")
    if not b1 or not b2: return jsonify({"error":"blocker_id and blocked_id required"}),400
    try:
        r=execute_query("SELECT EXISTS(SELECT 1 FROM blocked_users WHERE blocker_id=%s AND blocked_id=%s) AS is_blocked",(b1,b2),fetch=True)
        return jsonify({"is_blocked":bool(r and r[0].get("is_blocked"))}),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route("/unblock_user", methods=["POST","OPTIONS"])
def unblock_user():
    if request.method=="OPTIONS": return jsonify({"message":"OK"}),200
    try:
        data=request.json or {}; b1=data.get("blocker_id"); b2=data.get("blocked_id")
        if not b1 or not b2: return jsonify({"error":"blocker_id and blocked_id required"}),400
        execute_query("DELETE FROM blocked_users WHERE blocker_id=%s AND blocked_id=%s",(b1,b2),commit=True)
        return jsonify({"message":"User unblocked successfully"}),200
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

# ---------------------------------------------------------------------------
# CHAT ROOMS
# ---------------------------------------------------------------------------
@app.route("/rooms", methods=["GET"])
def get_rooms():
    try:
        uid = get_auth_user_id()
        rooms = execute_query("""
            SELECT r.id, r.name, r.created_by, r.is_public, r.icon_url, r.description, r.created_at, u.username as creator_username, (u.google_id IS NOT NULL) as is_verified
            FROM chat_rooms r
            LEFT JOIN users u ON r.created_by = u.id
            WHERE r.is_public=true 
            ORDER BY r.created_at DESC
        """, fetch=True)
        rooms = decrypt_rows(rooms, ["creator_username"])
        if uid:
            # Check memberships
            memberships = execute_query("SELECT room_id, role FROM chat_room_members WHERE user_id=%s", (uid,), fetch=True)
            member_room_roles = {m["room_id"]: m["role"] for m in memberships}
            for r in rooms:
                r["is_member"] = r["id"] in member_room_roles
                r["my_role"] = member_room_roles.get(r["id"])
        return jsonify(rooms), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms", methods=["POST"])
def create_room():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        
        if request.content_type and "multipart/form-data" in request.content_type:
            data = request.form
            is_public = str(data.get("is_public", "true")).lower() == "true"
        else:
            data = request.get_json(silent=True) or {}
            is_public = data.get("is_public", True)
            
        name = data.get("name")
        if not name: return jsonify({"error": "Name required"}), 400
        
        existing_room = execute_query("SELECT id FROM chat_rooms WHERE LOWER(name) = LOWER(%s)", (name,), fetch=True)
        if existing_room:
            return jsonify({"error": "Channel name already exists"}), 409
        
        icon_url = None
        icon_file = request.files.get("icon")
        if icon_file and allowed_file(icon_file.filename):
            sb_result = save_file_to_supabase(icon_file, icon_file.filename, icon_file.mimetype)
            if sb_result: icon_url = sb_result['url']
        
        description = data.get("description")
        r = execute_query("INSERT INTO chat_rooms (name, created_by, is_public, icon_url, description) VALUES (%s, %s, %s, %s, %s) RETURNING id, name, created_by, is_public, icon_url, description, created_at", (name, uid, is_public, icon_url, description), commit=True, fetch=True)
        room = r[0]
        execute_query("INSERT INTO chat_room_members (room_id, user_id, role) VALUES (%s, %s, 'owner')", (room["id"], uid), commit=True)
        if is_public:
            try:
                creator_row = execute_query("SELECT username FROM users WHERE id=%s", (uid,), fetch=True)
                creator_row = decrypt_rows(creator_row, ["username"])
                creator_name = creator_row[0]['username'] if creator_row else "Someone"
                broadcast_fcm_message("New Room Created!", f"@{creator_name} just created a new room: {name}", {"type": "new_room", "room_id": str(room["id"])}, exclude_user_id=uid)
            except Exception: pass
        room["is_member"] = True
        return jsonify(room), 201
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>", methods=["PUT"])
def edit_room(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        
        requester = execute_query("SELECT role FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not requester or requester[0]["role"] not in ["admin", "owner"]:
            return jsonify({"error": "Forbidden: Requires Admin or Owner role"}), 403
        
        if request.content_type and "multipart/form-data" in request.content_type:
            data = request.form
        else:
            data = request.get_json(silent=True) or {}
            
        update_fields = []
        update_values = []
        
        if "name" in data:
            name = data["name"].strip()
            if not name: return jsonify({"error": "Name cannot be empty"}), 400
            
            existing = execute_query("SELECT id FROM chat_rooms WHERE LOWER(name) = LOWER(%s) AND id != %s", (name, room_id), fetch=True)
            if existing: return jsonify({"error": "Channel name already exists"}), 409
            
            update_fields.append("name=%s")
            update_values.append(name)
            
        if "is_public" in data:
            is_public = str(data.get("is_public", "true")).lower() == "true"
            update_fields.append("is_public=%s")
            update_values.append(is_public)
            
        if "description" in data:
            update_fields.append("description=%s")
            update_values.append(data.get("description"))
            
        icon_file = request.files.get("icon")
        if icon_file and allowed_file(icon_file.filename):
            sb_result = save_file_to_supabase(icon_file, icon_file.filename, icon_file.mimetype)
            if sb_result:
                update_fields.append("icon_url=%s")
                update_values.append(sb_result['url'])
                
        if not update_fields:
            return jsonify({"error": "No fields to update"}), 400
            
        update_values.append(room_id)
        query = "UPDATE chat_rooms SET " + ", ".join(update_fields) + " WHERE id=%s RETURNING *"
        updated = execute_query(query, tuple(update_values), commit=True, fetch=True)
        
        return jsonify(updated[0]), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>/join", methods=["POST"])
def join_room(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        room = execute_query("SELECT 1 FROM chat_rooms WHERE id=%s", (room_id,), fetch=True)
        if not room: return jsonify({"error": "Room not found"}), 404
        
        banned = execute_query("SELECT 1 FROM chat_room_bans WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if banned: return jsonify({"error": "You are banned from this room"}), 403
        
        member = execute_query("SELECT 1 FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not member:
            execute_query("INSERT INTO chat_room_members (room_id, user_id) VALUES (%s, %s)", (room_id, uid), commit=True)
        return jsonify({"message": "Joined successfully"}), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>/leave", methods=["POST"])
def leave_room(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        execute_query("DELETE FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), commit=True)
        return jsonify({"message": "Left successfully"}), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>/messages", methods=["GET"])
def get_room_messages(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        room_info = execute_query("SELECT is_public FROM chat_rooms WHERE id=%s", (room_id,), fetch=True)
        if not room_info: return jsonify({"error": "Room not found"}), 404
        is_public = room_info[0].get("is_public", True)
        
        member = execute_query("SELECT 1 FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not member and not is_public: return jsonify({"error": "Not a member"}), 403
        
        msgs = execute_query("""
            SELECT m.id, m.client_id AS cid, m.sender_id AS sid, u.username as su, (u.google_id IS NOT NULL) as is_verified,
                   m.room_id, cr.name as ru, m.content, m.reply_to_id AS rpid,
                   m.files, m.status, m.version AS v, m.server_timestamp AS sts,
                   m.status_updated_at AS uts, m.created_at AS ct
            FROM messages m 
            JOIN users u ON m.sender_id = u.id 
            JOIN chat_rooms cr ON m.room_id = cr.id
            WHERE m.room_id = %s 
            ORDER BY m.created_at DESC
            LIMIT 50
        """, (room_id,), fetch=True)
        msgs = decrypt_rows(msgs, ["su", "ru", "content"])
        for r in msgs:
            if isinstance(r.get("ct"), datetime.datetime): r["ct"] = r["ct"].isoformat()
            if isinstance(r.get("sts"), datetime.datetime): r["sts"] = r["sts"].isoformat()
            if isinstance(r.get("uts"), datetime.datetime): r["uts"] = r["uts"].isoformat()
            fv = r.get("files")
            if fv is None: r["files"] = []
            elif isinstance(fv, str):
                try:
                    parsed = json.loads(fv)
                    r["files"] = parsed if isinstance(parsed, list) else []
                except Exception: r["files"] = []
            else: r["files"] = fv
        return jsonify(msgs), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>/members", methods=["GET"])
def get_room_members(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        room_info = execute_query("SELECT is_public FROM chat_rooms WHERE id=%s", (room_id,), fetch=True)
        if not room_info: return jsonify({"error": "Room not found"}), 404
        is_public = room_info[0].get("is_public", True)
        
        member = execute_query("SELECT 1 FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not member and not is_public: return jsonify({"error": "Not a member"}), 403
        
        members = execute_query("""
            SELECT u.id, u.username, crm.role, crm.joined_at, (u.google_id IS NOT NULL) as is_verified
            FROM chat_room_members crm
            JOIN users u ON crm.user_id = u.id
            WHERE crm.room_id = %s
            ORDER BY crm.joined_at ASC
        """, (room_id,), fetch=True)
        members = decrypt_rows(members, ["username"])
        for m in members:
            if isinstance(m.get("joined_at"), datetime.datetime):
                m["joined_at"] = m["joined_at"].isoformat()
        return jsonify(members), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>/kick", methods=["POST"])
def kick_member(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        data = request.get_json(silent=True) or {}
        target_id = data.get("user_id")
        if not target_id: return jsonify({"error": "Target user_id required"}), 400
        
        requester = execute_query("SELECT role FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not requester or requester[0]["role"] not in ["admin", "owner"]:
            return jsonify({"error": "Forbidden: Requires Admin or Owner role"}), 403
            
        target = execute_query("SELECT role FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, target_id), fetch=True)
        if not target: return jsonify({"error": "Target not in room"}), 404
        if target[0]["role"] == "owner": return jsonify({"error": "Cannot kick the owner"}), 403
        
        execute_query("DELETE FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, target_id), commit=True)
        return jsonify({"message": "User kicked successfully"}), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>/ban", methods=["POST"])
def ban_member(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        data = request.get_json(silent=True) or {}
        target_id = data.get("user_id")
        reason = data.get("reason", "")
        if not target_id: return jsonify({"error": "Target user_id required"}), 400
        
        requester = execute_query("SELECT role FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not requester or requester[0]["role"] not in ["admin", "owner"]:
            return jsonify({"error": "Forbidden: Requires Admin or Owner role"}), 403
            
        target = execute_query("SELECT role FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, target_id), fetch=True)
        if target and target[0]["role"] == "owner": return jsonify({"error": "Cannot ban the owner"}), 403
        
        execute_query("DELETE FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, target_id), commit=True)
        execute_query("INSERT INTO chat_room_bans (room_id, user_id, banned_by, reason) VALUES (%s, %s, %s, %s) ON CONFLICT (room_id, user_id) DO UPDATE SET banned_by=EXCLUDED.banned_by, reason=EXCLUDED.reason", (room_id, target_id, uid, reason), commit=True)
        return jsonify({"message": "User banned successfully"}), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>/promote", methods=["POST"])
def promote_member(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        data = request.get_json(silent=True) or {}
        target_id = data.get("user_id")
        if not target_id: return jsonify({"error": "Target user_id required"}), 400
        
        requester = execute_query("SELECT role FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not requester or requester[0]["role"] != "owner":
            return jsonify({"error": "Forbidden: Requires Owner role"}), 403
            
        execute_query("UPDATE chat_room_members SET role='admin' WHERE room_id=%s AND user_id=%s", (room_id, target_id), commit=True)
        return jsonify({"message": "User promoted to admin"}), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>/demote", methods=["POST"])
def demote_member(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        data = request.get_json(silent=True) or {}
        target_id = data.get("user_id")
        if not target_id: return jsonify({"error": "Target user_id required"}), 400
        
        requester = execute_query("SELECT role FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not requester or requester[0]["role"] != "owner":
            return jsonify({"error": "Forbidden: Requires Owner role"}), 403
            
        execute_query("UPDATE chat_room_members SET role='member' WHERE room_id=%s AND user_id=%s AND role != 'owner'", (room_id, target_id), commit=True)
        return jsonify({"message": "User demoted to member"}), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/rooms/<int:room_id>", methods=["DELETE"])
def delete_room(room_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 403
        
        requester = execute_query("SELECT role FROM chat_room_members WHERE room_id=%s AND user_id=%s", (room_id, uid), fetch=True)
        if not requester or requester[0]["role"] != "owner":
            return jsonify({"error": "Forbidden: Requires Owner role"}), 403
            
        execute_query("DELETE FROM chat_rooms WHERE id=%s", (room_id,), commit=True)
        return jsonify({"message": "Room deleted successfully"}), 200
    except Exception as e: return jsonify({"error": map_exception_to_error_msg(e)}), 500


# ---------------------------------------------------------------------------
# FCM / PUSH TOKENS
# ---------------------------------------------------------------------------
@app.route('/register_fcm', methods=['POST'])
def register_fcm():
    try:
        data=request.get_json(silent=True)
        if not data: return jsonify({'error':'Invalid JSON'}),400
        uid=data.get('user_id'); tok=data.get('token'); plat=data.get('platform')
        if not uid or not tok: return jsonify({'error':'user_id and token required'}),400  # NOSONAR
        try: execute_query('INSERT INTO push_tokens (user_id,token,platform,created_at) VALUES (%s,%s,%s,NOW())',(uid,tok,plat),commit=True)
        except Exception:
            try: execute_query('UPDATE push_tokens SET user_id=%s,platform=%s WHERE token=%s',(uid,plat,tok),commit=True)
            except Exception as e:
                app.logger.exception('FCM token registration update failed')
                return jsonify({'error': map_exception_to_error_msg(e)}), 500
        return jsonify({'message':'registered'}),201
    except Exception as e:
        app.logger.exception('register_fcm failed')
        return jsonify({'error': map_exception_to_error_msg(e)}), 500

@app.route('/register_token', methods=['POST'])
def register_token():
    try:
        data=request.get_json(silent=True) or request.form or {}
        uid=data.get('user_id') or data.get('userId') or data.get('uid'); tok=data.get('token') or data.get('fcm_token'); plat=data.get('platform')
        if not uid or not tok: return jsonify({'error':'user_id and token required'}),400
        try: execute_query('INSERT INTO push_tokens (user_id,token,platform,created_at) VALUES (%s,%s,%s,NOW())',(int(uid),tok,plat),commit=True)
        except Exception:
            try: execute_query('UPDATE push_tokens SET user_id=%s,platform=%s,created_at=NOW() WHERE token=%s',(int(uid),plat,tok),commit=True)
            except Exception as e:
                app.logger.exception('register_token update failed')
                return jsonify({'error': map_exception_to_error_msg(e)}), 500
        return jsonify({'message':'registered'}),201
    except Exception as e:
        app.logger.exception('register_token failed')
        return jsonify({'error': map_exception_to_error_msg(e)}), 500

@app.route("/register_push_token", methods=["POST"])
def register_push_token():
    data=request.get_json() or {}; uid=data.get("user_id"); tok=data.get("token")
    if not uid or not tok: return jsonify({"success":False,"error":"Missing fields"}),400
    try:
        execute_query("INSERT INTO push_tokens (user_id,token) VALUES (%s,%s) ON CONFLICT (user_id,token) DO UPDATE SET token=EXCLUDED.token",(uid,tok),commit=True)
        return jsonify({"success":True}),200
    except Exception as e:
        app.logger.exception('register_push_token failed')
        return jsonify({"success":False,"error": map_exception_to_error_msg(e)}), 500

@app.route('/update_fcm_token', methods=['POST'])
def update_fcm_token():
    try:
        data=request.get_json(silent=True) or request.form or {}
        uid=data.get('user_id') or data.get('uid'); tok=data.get('token') or data.get('fcm_token'); plat=data.get('platform')
        if not uid or not tok: return jsonify({'error':'user_id and token required'}),400
        try: execute_query("INSERT INTO push_tokens (user_id,token,platform) VALUES (%s,%s,%s) ON CONFLICT (user_id,token) DO UPDATE SET platform=EXCLUDED.platform",(int(uid),tok,plat),commit=True)
        except Exception as e:
            app.logger.exception('update_fcm_token write failed')
            return jsonify({'error': map_exception_to_error_msg(e)}), 500
        return jsonify({'message':'token updated'}),200
    except Exception as e:
        app.logger.exception('update_fcm_token failed')
        return jsonify({'error': map_exception_to_error_msg(e)}), 500

@app.route('/api/v1/fcm_token', methods=['POST'])
def api_fcm_token():
    try:
        data=request.get_json(silent=True) or {}
        uid=data.get('user_id') or data.get('userId'); tok=data.get('token') or data.get('fcm_token'); plat=data.get('platform')
        if not uid or not tok: return jsonify({'error':'user_id and token required'}),400
        execute_query("INSERT INTO push_tokens (user_id,token,platform) VALUES (%s,%s,%s) ON CONFLICT (user_id,token) DO UPDATE SET platform=EXCLUDED.platform",(int(uid),tok,plat),commit=True)
        return jsonify({'message':'ok'}),200
    except Exception as e:
        app.logger.exception('api_fcm_token failed')
        return jsonify({'error': map_exception_to_error_msg(e)}), 500

@app.route('/test_fcm', methods=['POST'])
def test_fcm():
    try:
        data=request.get_json(silent=True)
        if not data: return jsonify({'error':'Invalid JSON'}),400
        tok=data.get("token"); title=data.get("title"); body=data.get("body")
        if not all([tok,title,body]): return jsonify({'error':'token, title, body required'}),400
        if not GOOGLE_AUTH_AVAILABLE or not app.config.get('FCM_SERVICE_ACCOUNT'): return jsonify({'error':'FCM not configured'}),503
        ok=_send_fcm_v1_notification(tok,title,body,data.get("data",{}))
        return (jsonify({"message":"FCM test sent"}),200) if ok else (jsonify({'error':'send failed'}),500)
    except Exception as e: return jsonify({"error":map_exception_to_error_msg(e)}),500

@app.route('/api/v1/internal/send_push', methods=['POST'])
def internal_send_push():
    try:
        data = request.get_json(silent=True)
        if not data: return jsonify({'error': 'Invalid JSON'}), 400
        
        user_id = data.get("user_id")
        title = data.get("title")
        body = data.get("body")
        payload = data.get("data", {})
        
        if not all([user_id, title, body]): 
            return jsonify({'error': 'user_id, title, body required'}), 400
            
        send_fcm_message(int(user_id), title, body, payload)
        return jsonify({"message": "Push triggered"}), 200
    except Exception as e:
        app.logger.exception('internal_send_push failed')
        return jsonify({"error": str(e)}), 500

# ---------------------------------------------------------------------------
# CALL / WEBRTC SIGNALING (IN-MEMORY)
# ---------------------------------------------------------------------------
@app.route("/home", methods=["GET"])
def home(): return jsonify({"status":"server running"})

@app.route("/test", methods=["GET"])
def test(): return "OK"

@app.route("/gleam/webhook", methods=["POST"])
def gleam_webhook():
    # Optionally verify a secret token from headers (not implemented)
    payload = request.get_json(force=True) or {}
    
    # 1) Try to extract user_id (for paid Gleam plans using custom fields)
    user_id = payload.get("custom_fields", {}).get("user_id")
    
    # 2) Fallback: Extract email from Gleam's user/entrant payload (for free Gleam plans)
    email = None
    if "user" in payload and isinstance(payload["user"], dict):
        email = payload["user"].get("email")
    elif "entrant" in payload and isinstance(payload["entrant"], dict):
        email = payload["entrant"].get("email")
        
    if not user_id and not email:
        return jsonify({"error": "Neither user_id nor email was found in the payload"}), 400

    user_id_int = None
    if user_id:
        try:
            user_id_int = int(user_id)
        except (ValueError, TypeError):
            pass

    try:
        # If user_id_int was resolved, update directly. Otherwise, look up by email_hash
        if not user_id_int and email:
            email_clean = email.strip().lower()
            email_h = hash_val(email_clean)
            user_rows = execute_query("SELECT id FROM users WHERE email_hash = %s LIMIT 1", (email_h,), fetch=True)
            if user_rows:
                user_id_int = user_rows[0]["id"]
            else:
                return jsonify({"error": f"No user found matching email hash for {email_clean}"}), 404
        elif not user_id_int:
            return jsonify({"error": "Invalid user_id provided"}), 400

        execute_query(
            "UPDATE users SET follow_unlocked = TRUE WHERE id = %s",
            (user_id_int,), commit=True
        )
        # Send a push notification to the user (FCM) if they have a registered token
        try:
            send_fcm_message(
                user_id_int,
                "Feature Unlocked",
                "Your follow‑to‑unlock feature is now available.",
                {"type": "unlock", "feature": "follow"}
            )
        except Exception as notif_err:
            app.logger.exception("Failed to send unlock notification")
        return jsonify({"status": "unlocked"}), 200
    except Exception as e:
        app.logger.exception("Gleam webhook failed")
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/sse/health", methods=["GET"])
def sse_health():
    with SSE_LOCK: total=sum(len(c) for c in SSE_CLIENTS.values())
    return jsonify({"active":total,"users":len(SSE_CLIENTS)})

@app.route("/health", methods=["GET"])
def health_check():
    try: conn=get_db(); db="healthy"
    except Exception: db="unhealthy"
    return jsonify({"status":"healthy","database":db,"ws_connections":len(connected_clients),"active":True,"version":APP_VERSION})

@app.route("/api/v1/version", methods=["GET", "OPTIONS"])
def app_version():
    return jsonify({"version": APP_VERSION, "service": "myvibes-backend"})






# ---------------------------------------------------------------------------
# TRADING API PROXIES (DexScreener, Frankfurter)
# ---------------------------------------------------------------------------
@app.route("/trading/dex/trending/<chain>", methods=["GET"])
def trading_dex_trending(chain):
    try:
        resp = requests.get(f"https://api.dexscreener.com/latest/dex/trending/{chain}", timeout=15)
        if resp.status_code != 200:
            return jsonify({"error": f"Failed fetching trending data (HTTP {resp.status_code})"}), resp.status_code
        try:
            return jsonify(resp.json()), 200
        except ValueError:
            return jsonify({"error": "Failed to decode response from DexScreener"}), 502
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/trading/dex/search", methods=["GET"])
def trading_dex_search():
    try:
        q = request.args.get("q", "")
        if not q:
            return jsonify({"error": "query param 'q' required"}), 400
        resp = requests.get(f"https://api.dexscreener.com/latest/dex/search?q={q}", timeout=15)
        if resp.status_code != 200:
            return jsonify({"error": f"Failed fetching search results (HTTP {resp.status_code})"}), resp.status_code
        try:
            return jsonify(resp.json()), 200
        except ValueError:
            return jsonify({"error": "Failed to decode response from DexScreener"}), 502
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/trading/forex", methods=["GET"])
def trading_forex():
    try:
        base = request.args.get("from", "USD")
        date = request.args.get("date", "latest")
        url = f"https://api.frankfurter.app/{date}?from={base}"
        resp = requests.get(url, timeout=15)
        if resp.status_code != 200:
            return jsonify({"error": f"Failed fetching forex data (HTTP {resp.status_code})"}), resp.status_code
        try:
            return jsonify(resp.json()), 200
        except ValueError:
            return jsonify({"error": "Failed to decode response from Frankfurter"}), 502
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500



# ---------------------------------------------------------------------------
# STARTUP: ensure all tables exist
# ---------------------------------------------------------------------------
def run_migrations():
    try:
        # Automatically execute the full schema on startup
        try:
            import os
            schema_path = os.path.join(os.path.dirname(__file__), 'aiven_schema.sql')
            if os.path.exists(schema_path):
                with open(schema_path, 'r', encoding='utf-8') as f:
                    schema_sql = f.read()
                execute_query(schema_sql, commit=True)
                app.logger.info("Executed aiven_schema.sql to ensure all tables exist.")
        except Exception as e:
            app.logger.exception(f"Failed to execute schema SQL: {e}")

        ensure_core_tables()
        ensure_push_tokens_table()
        ensure_unread_table()
        ensure_chat_rooms()
        ensure_feed_tables()

        # Ensure messages table has delete tracking columns (older deployments may lack them)
        try:
            add_column_if_missing("messages", "deleted_by_sender", "BOOLEAN DEFAULT FALSE")
        except Exception:
            app.logger.exception("Failed to add deleted_by_sender column (may not exist yet)")
        try:
            add_column_if_missing("messages", "deleted_by_receiver", "BOOLEAN DEFAULT FALSE")
        except Exception:
            app.logger.exception("Failed to add deleted_by_receiver column (may not exist yet)")
        try:
            add_column_if_missing("users", "welcome_reminder_sent", "BOOLEAN DEFAULT FALSE")
        except Exception:
            app.logger.exception("Failed to add welcome_reminder_sent column")
    except Exception as e:
        app.logger.error(f"Migration failed during startup: {e}")

# Run migrations in a background thread to prevent blocking main Flask port binding on boot
threading.Thread(target=run_migrations, daemon=True).start()


# ---------------------------------------------------------------------------
# TRADING ENDPOINTS
# ---------------------------------------------------------------------------

@app.route("/trading/portfolio/<int:user_id>", methods=["GET"])
def get_user_portfolio(user_id):
    try:
        wallet = execute_query("SELECT balance FROM wallets WHERE user_id=%s", (user_id,), fetch=True)
        if not wallet:
            execute_query("INSERT INTO wallets (user_id, balance) VALUES (%s, 1000.0)", (user_id,), commit=True)
            balance = 1000.0
        else:
            balance = float(wallet[0]["balance"])
        
        # Calculate holdings dynamically from trades
        trades = execute_query("SELECT symbol, type, qty, price FROM trades WHERE user_id=%s", (user_id,), fetch=True)
        holdings_dict = {}
        for t in trades:
            sym = t["symbol"]
            qty = float(t["qty"])
            price = float(t["price"])
            if sym not in holdings_dict:
                holdings_dict[sym] = {"qty": 0.0, "total_cost": 0.0}
            if t["type"] == "buy":
                holdings_dict[sym]["qty"] += qty
                holdings_dict[sym]["total_cost"] += qty * price
            elif t["type"] == "sell":
                # Average cost subtraction
                prev_qty = holdings_dict[sym]["qty"]
                holdings_dict[sym]["qty"] -= qty
                if holdings_dict[sym]["qty"] > 0.000001 and prev_qty > 0:
                    avg = holdings_dict[sym]["total_cost"] / prev_qty
                    holdings_dict[sym]["total_cost"] -= qty * avg
                else:
                    holdings_dict[sym]["total_cost"] = 0.0

        active_holdings = {k: v for k, v in holdings_dict.items() if v["qty"] > 0.000001}
        
        # Fetch live prices from Binance (Spot + Futures)
        prices_dict = {}
        if active_holdings:
            try:
                import requests
                # Spot Prices
                res_spot = requests.get("https://api.binance.com/api/v3/ticker/price", timeout=3)
                if res_spot.status_code == 200:
                    for item in res_spot.json():
                        prices_dict[item["symbol"]] = float(item["price"])
                
                # Futures Prices (Overwrite spot if exists or add new)
                res_futures = requests.get("https://fapi.binance.com/fapi/v1/ticker/price", timeout=3)
                if res_futures.status_code == 200:
                    for item in res_futures.json():
                        prices_dict[item["symbol"]] = float(item["price"])
            except Exception as e:
                app.logger.warning(f"Could not fetch Binance prices for portfolio: {e}")

        holdings = []
        in_market_value = 0.0

        for sym, data in active_holdings.items():
            qty = data["qty"]
            avg_cost = data["total_cost"] / qty if qty > 0 else 0
            current_price = prices_dict.get(sym, avg_cost) # Fallback to avg_cost if API fails
            value = qty * current_price
            pnl = value - data["total_cost"]
            
            in_market_value += value
            holdings.append({
                "symbol": sym,
                "quantity": qty,
                "avg_cost": avg_cost,
                "current_price": current_price,
                "value": value,
                "pnl": pnl
            })
            
        total_value = balance + in_market_value

        return jsonify({
            "balance": balance, 
            "total_value": total_value, 
            "holdings": holdings,
            "savings_balance": 0.0,
            "savings_apy": 0.05
        }), 200
    except Exception as e:
        app.logger.exception("Failed to fetch portfolio")
        return jsonify({"error": str(e)}), 500

@app.route("/trading/portfolio/<int:user_id>/comments", methods=["GET"])
def get_trader_comments(user_id):
    try:
        comments = execute_query("""
            SELECT c.id, c.content, c.trade_date_str, c.parent_id, c.created_at, 
                   u.id as commenter_id, u.username, p.profile_picture_url
            FROM trader_comments c
            JOIN users u ON c.commenter_id = u.id
            LEFT JOIN profiles p ON u.id = p.user_id
            WHERE c.trader_id = %s
            ORDER BY c.created_at ASC
        """, (user_id,), fetch=True)
        
        comments = decrypt_rows(comments, ["username"])
        
        for c in comments:
            c["created_at"] = c["created_at"].isoformat()
            
        return jsonify(comments), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/trading/portfolio/<int:user_id>/comments", methods=["POST", "OPTIONS"])
def add_trader_comment(user_id):
    if request.method == "OPTIONS": return jsonify({"message":"OK"}), 200
    try:
        data = request.get_json(force=True)
        commenter_id = data.get("commenter_id")
        content = data.get("content")
        trade_date_str = data.get("trade_date_str")
        parent_id = data.get("parent_id")
        
        if not commenter_id or not content:
            return jsonify({"error": "Missing required fields"}), 400
            
        execute_query("""
            INSERT INTO trader_comments (trader_id, commenter_id, content, trade_date_str, parent_id)
            VALUES (%s, %s, %s, %s, %s)
        """, (user_id, commenter_id, content, trade_date_str, parent_id), commit=True)
        
        return jsonify({"message": "Comment added successfully"}), 201
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/trading/earnings/<int:user_id>", methods=["GET"])
def get_user_earnings(user_id):
    try:
        wallet = execute_query("SELECT total_earned FROM wallets WHERE user_id=%s", (user_id,), fetch=True)
        earned = float(wallet[0]["total_earned"]) if wallet else 0.0
        return jsonify({"earnings": earned}), 200
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/trading/portfolio/<int:user_id>/history", methods=["GET"])
def get_user_trade_history(user_id):
    try:
        trades = execute_query("SELECT id, type, symbol, price, qty, created_at as timestamp FROM trades WHERE user_id=%s ORDER BY created_at DESC", (user_id,), fetch=True)
        for t in trades:
            t["price"] = float(t["price"])
            t["qty"] = float(t["qty"])
            t["timestamp"] = t["timestamp"].isoformat()
        return jsonify(trades), 200
    except Exception as e:
        return jsonify({"error": map_exception_to_error_msg(e)}), 500

@app.route("/trading/klines", methods=["GET"])
def proxy_binance_klines():
    symbol = request.args.get("symbol")
    interval = request.args.get("interval", "1h")
    limit = request.args.get("limit", "200")
    if not symbol:
        return jsonify({"error": "Missing symbol parameter"}), 400
    try:
        import requests
        url = f"https://api.binance.com/api/v3/klines?symbol={symbol}&interval={interval}&limit={limit}"
        r = requests.get(url, timeout=10)
        data = r.json()
        if r.status_code == 200 and isinstance(data, list):
            return jsonify(data), 200
            
        f_url = f"https://fapi.binance.com/fapi/v1/klines?symbol={symbol}&interval={interval}&limit={limit}"
        fr = requests.get(f_url, timeout=10)
        fdata = fr.json()
        if fr.status_code == 200 and isinstance(fdata, list):
            return jsonify(fdata), 200
            
        return jsonify(data), r.status_code
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/trading/portfolio/<int:user_id>/history_chart", methods=["GET"])
def get_user_trade_history_chart(user_id):
    try:
        import time
        import requests
        from datetime import datetime, timezone

        STARTING_EQUITY = 1000.0
        
        trades = execute_query("SELECT type, symbol, price, qty, created_at FROM trades WHERE user_id=%s ORDER BY created_at ASC", (user_id,), fetch=True)
        
        chart_data = []
        
        if not trades:
            wallet = execute_query("SELECT balance FROM wallets WHERE user_id=%s", (user_id,), fetch=True)
            balance = float(wallet[0]["balance"]) if wallet else 1000.0
            now = int(time.time())
            return jsonify([
                {"time": now - 86400, "value": balance},
                {"time": now, "value": balance}
            ]), 200
            
        first_trade_ts = int(trades[0]["created_at"].replace(tzinfo=timezone.utc).timestamp())
        chart_data.append({"time": first_trade_ts - 3600, "value": STARTING_EQUITY})
        
        holdings = {}
        running_equity = STARTING_EQUITY
        
        for t in trades:
            sym = t["symbol"]
            qty = float(t["qty"])
            price = float(t["price"])
            ts = int(t["created_at"].replace(tzinfo=timezone.utc).timestamp())
            
            if sym not in holdings:
                holdings[sym] = {"qty": 0.0, "total_cost": 0.0}
            
            h = holdings[sym]
            
            if t["type"] == "buy":
                h["qty"] += qty
                h["total_cost"] += (qty * price)
            elif t["type"] == "sell":
                if h["qty"] > 0:
                    avg_cost = h["total_cost"] / h["qty"]
                else:
                    avg_cost = 0
                
                trade_profit = (price - avg_cost) * qty
                
                h["qty"] -= qty
                h["total_cost"] -= (avg_cost * qty)
                if h["qty"] < 1e-8:
                    h["qty"] = 0.0
                    h["total_cost"] = 0.0
                    
                running_equity += trade_profit
                chart_data.append({"time": ts, "value": running_equity})
                
        unrealized_pnl = 0.0
        open_symbols = [sym for sym, h in holdings.items() if h["qty"] > 0]
        if open_symbols:
            try:
                res = requests.get("https://api.binance.com/api/v3/ticker/price", timeout=3)
                if res.status_code == 200:
                    prices = {item["symbol"]: float(item["price"]) for item in res.json()}
                    for sym in open_symbols:
                        h = holdings[sym]
                        current_price = prices.get(sym, 0.0)
                        current_value = h["qty"] * current_price
                        unrealized_pnl += (current_value - h["total_cost"])
            except Exception as e:
                pass
                
        live_portfolio_value = running_equity + unrealized_pnl
        now = int(time.time())
        chart_data.append({"time": now, "value": live_portfolio_value})
        
        return jsonify(chart_data), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/trading/portfolio/<int:user_id>/analytics", methods=["GET"])
def get_user_trade_analytics(user_id):
    try:
        import requests
        wallet = execute_query("SELECT balance FROM wallets WHERE user_id=%s", (user_id,), fetch=True)
        usdt_balance = float(wallet[0]["balance"]) if wallet else 0.0
        
        trades = execute_query("SELECT type, symbol, price, qty, created_at FROM trades WHERE user_id=%s ORDER BY created_at ASC", (user_id,), fetch=True)
        
        total_trades = len(trades)
        
        holdings = {}
        realized_pnl = 0.0
        winning_trades = 0
        losing_trades = 0
        best_trade = None
        worst_trade = None
        
        for t in trades:
            sym = t["symbol"]
            qty = float(t["qty"])
            price = float(t["price"])
            
            if sym not in holdings:
                holdings[sym] = {"qty": 0.0, "total_cost": 0.0}
            
            h = holdings[sym]
            
            if t["type"] == "buy":
                h["qty"] += qty
                h["total_cost"] += (qty * price)
            elif t["type"] == "sell":
                if h["qty"] > 0:
                    avg_cost = h["total_cost"] / h["qty"]
                else:
                    avg_cost = 0
                
                trade_profit = (price - avg_cost) * qty
                realized_pnl += trade_profit
                
                if trade_profit > 0:
                    winning_trades += 1
                elif trade_profit < 0:
                    losing_trades += 1
                
                if best_trade is None or trade_profit > best_trade["pnl"]:
                    best_trade = {"symbol": sym, "pnl": trade_profit, "return_pct": (trade_profit / (avg_cost * qty) * 100) if avg_cost > 0 else 0.0}
                if worst_trade is None or trade_profit < worst_trade["pnl"]:
                    worst_trade = {"symbol": sym, "pnl": trade_profit, "return_pct": (trade_profit / (avg_cost * qty) * 100) if avg_cost > 0 else 0.0}
                
                h["qty"] -= qty
                h["total_cost"] -= (avg_cost * qty)
                
                if h["qty"] < 1e-8:
                    h["qty"] = 0.0
                    h["total_cost"] = 0.0
        
        unrealized_pnl = 0.0
        asset_allocation = [{"name": "USDT", "value": usdt_balance}]
        
        open_symbols = [sym for sym, h in holdings.items() if h["qty"] > 0]
        if open_symbols:
            try:
                res = requests.get("https://api.binance.com/api/v3/ticker/price", timeout=3)
                if res.status_code == 200:
                    prices = {item["symbol"]: float(item["price"]) for item in res.json()}
                    for sym in open_symbols:
                        h = holdings[sym]
                        current_price = prices.get(sym, 0.0)
                        current_value = h["qty"] * current_price
                        unrealized_pnl += (current_value - h["total_cost"])
                        asset_allocation.append({"name": sym.replace("USDT", ""), "value": current_value})
            except Exception as e:
                pass
                
        total_closed_trades = winning_trades + losing_trades
        win_rate = (winning_trades / total_closed_trades * 100) if total_closed_trades > 0 else 0.0
        
        return jsonify({
            "total_trades": total_trades,
            "win_rate": win_rate,
            "realized_pnl": realized_pnl,
            "unrealized_pnl": unrealized_pnl,
            "asset_allocation": asset_allocation,
            "best_trade": best_trade,
            "worst_trade": worst_trade
        }), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/trading/order/<action>", methods=["POST"])
def place_trade_order(action):
    try:
        if action not in ["buy", "sell"]:
            return jsonify({"error": "Invalid action"}), 400
        data = request.json
        user_id = data.get("user_id")
        symbol = data.get("symbol")
        qty = float(data.get("qty", 0))
        price = float(data.get("price", 0))
        
        if not user_id or not symbol or qty <= 0 or price <= 0:
            return jsonify({"error": "Invalid order parameters"}), 400
            
        execute_query("INSERT INTO trades (user_id, type, symbol, price, qty) VALUES (%s, %s, %s, %s, %s)", 
                      (user_id, action, symbol, price, qty), commit=True)
        
        # Simple wallet update logic (mock logic for paper trading)
        cost = price * qty
        if action == "buy":
            execute_query("UPDATE wallets SET balance = balance - %s WHERE user_id = %s", (cost, user_id), commit=True)
        else:
            execute_query("UPDATE wallets SET balance = balance + %s WHERE user_id = %s", (cost, user_id), commit=True)
            
        # Notify followers
        trader = execute_query("SELECT username FROM users WHERE id=%s", (user_id,), fetch=True)
        if trader:
            trader = decrypt_rows(trader, ["username"])
            trader_name = trader[0].get("username")
            followers = execute_query("SELECT follower_id FROM followers WHERE following_id=%s AND status='approved'", (user_id,), fetch=True)
            if followers:
                sym_clean = symbol.replace("USDT", "")
                notif_content = f"@{trader_name} just {action} {qty} {sym_clean} for ${price:,.2f}"
                for f in followers:
                    execute_query(
                        "INSERT INTO trade_notifications (user_id, trader_id, content) VALUES (%s, %s, %s)",
                        (f["follower_id"], user_id, notif_content), commit=True
                    )
            
        return jsonify({"message": f"{action.upper()} order successful"}), 200
    except Exception as e:
        app.logger.exception("Trade order failed")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/news/comments", methods=["GET"])
def get_news_comments():
    try:
        news_url = request.args.get("news_url")
        if not news_url:
            return jsonify({"error": "news_url required"}), 400
        
        comments = execute_query(
            "SELECT c.id, c.news_url, c.user_id, c.content, c.created_at, u.username, u.profile_picture_url, (u.google_id IS NOT NULL) as is_verified "
            "FROM news_comments c "
            "JOIN users u ON c.user_id = u.id "
            "WHERE c.news_url = %s "
            "ORDER BY c.created_at DESC",
            (news_url,), fetch=True
        )
        comments = decrypt_rows(comments, ["username"])
        for c in comments:
            if isinstance(c.get("created_at"), datetime.datetime):
                c["created_at"] = c["created_at"].isoformat()
        return jsonify({"comments": comments}), 200
    except Exception as e:
        app.logger.exception("get_news_comments error")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/news/comments", methods=["POST"])
def post_news_comment():
    try:
        uid = get_auth_user_id()
        if not uid:
            return jsonify({"error": "Unauthorized"}), 401
        
        data = request.json or {}
        news_url = data.get("news_url")
        content = data.get("content")
        
        if not news_url or not content:
            return jsonify({"error": "news_url and content required"}), 400
        
        execute_query(
            "INSERT INTO news_comments (news_url, user_id, content) VALUES (%s, %s, %s)",
            (news_url, uid, content), commit=True
        )
        return jsonify({"message": "Comment added successfully"}), 200
    except Exception as e:
        app.logger.exception("post_news_comment error")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/news/likes/batch", methods=["POST"])
def post_news_likes_batch():
    try:
        uid = get_auth_user_id()
        data = request.json or {}
        urls = data.get("news_urls", [])
        if not isinstance(urls, list):
            return jsonify({"error": "news_urls must be a list"}), 400
        
        if not urls:
            return jsonify({"likes": {}}), 200

        # format list of urls for IN clause
        placeholders = ', '.join(['%s'] * len(urls))
        
        # Get total likes
        query_total = f"SELECT news_url, COUNT(*) as c FROM news_likes WHERE news_url IN ({placeholders}) GROUP BY news_url"
        total_rows = execute_query(query_total, tuple(urls), fetch=True)
        
        # Get user likes
        user_rows = []
        if uid:
            params = list(urls)
            params.append(uid)
            query_user = f"SELECT news_url FROM news_likes WHERE news_url IN ({placeholders}) AND user_id = %s"
            user_rows = execute_query(query_user, tuple(params), fetch=True)
            
        user_liked_set = set([r["news_url"] for r in user_rows]) if user_rows else set()
        
        result = {}
        for url in urls:
            result[url] = {"like_count": 0, "liked_by_me": (url in user_liked_set)}
            
        if total_rows:
            for r in total_rows:
                result[r["news_url"]]["like_count"] = r["c"]
                
        return jsonify({"likes": result}), 200
    except Exception as e:
        app.logger.exception("post_news_likes_batch error")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/news/like", methods=["POST"])
def post_news_like():
    try:
        uid = get_auth_user_id()
        if not uid:
            return jsonify({"error": "Unauthorized"}), 401
            
        data = request.json or {}
        news_url = data.get("news_url")
        if not news_url:
            return jsonify({"error": "news_url required"}), 400
            
        # Check if already liked
        existing = execute_query("SELECT id FROM news_likes WHERE news_url = %s AND user_id = %s", (news_url, uid), fetch=True)
        if existing:
            execute_query("DELETE FROM news_likes WHERE news_url = %s AND user_id = %s", (news_url, uid), commit=True)
            return jsonify({"message": "Unliked", "liked": False}), 200
        else:
            execute_query("INSERT INTO news_likes (news_url, user_id) VALUES (%s, %s)", (news_url, uid), commit=True)
            return jsonify({"message": "Liked", "liked": True}), 200
    except Exception as e:
        app.logger.exception("post_news_like error")
        return jsonify({"error": str(e)}), 500

# ---------------------------------------------------------------------------
# FOLLOWERS & NOTIFICATIONS
# ---------------------------------------------------------------------------

@app.route("/api/v1/follow", methods=["POST"])
def follow_user():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        data = request.json or {}
        following_id = data.get("following_id")
        if not following_id: return jsonify({"error": "following_id required"}), 400
        
        target = execute_query("SELECT is_private FROM users WHERE id=%s", (following_id,), fetch=True)
        if not target: return jsonify({"error": "User not found"}), 404
        
        status = 'pending' if target[0].get('is_private') else 'approved'
        
        execute_query("INSERT INTO followers (follower_id, following_id, status) VALUES (%s, %s, %s) ON CONFLICT (follower_id, following_id) DO UPDATE SET status = EXCLUDED.status", 
                      (uid, following_id, status), commit=True)
        return jsonify({"message": "Followed successfully", "status": status}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/follow/<int:following_id>", methods=["DELETE"])
def unfollow_user(following_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        execute_query("DELETE FROM followers WHERE follower_id=%s AND following_id=%s", (uid, following_id), commit=True)
        return jsonify({"message": "Unfollowed successfully"}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/follow/status/<int:following_id>", methods=["GET"])
def follow_status(following_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        res = execute_query("SELECT status FROM followers WHERE follower_id=%s AND following_id=%s", (uid, following_id), fetch=True)
        status = res[0]['status'] if res else 'not_following'
        return jsonify({"is_following": bool(res), "status": status}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/following", methods=["GET"])
def get_following():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        res = execute_query("SELECT following_id FROM followers WHERE follower_id=%s", (uid,), fetch=True)
        return jsonify([r['following_id'] for r in res]), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/follow/requests", methods=["GET"])
def get_follow_requests():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        res = execute_query("""
            SELECT f.id, f.follower_id, u.username, u.profile_picture_url, f.created_at, (u.google_id IS NOT NULL) as is_verified 
            FROM followers f 
            JOIN users u ON f.follower_id = u.id 
            WHERE f.following_id=%s AND f.status='pending' 
            ORDER BY f.created_at DESC
        """, (uid,), fetch=True)
        return jsonify(res), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/follow/requests/<int:request_id>/approve", methods=["POST"])
def approve_follow_request(request_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        res = execute_query("UPDATE followers SET status='approved' WHERE id=%s AND following_id=%s RETURNING id", (request_id, uid), fetch=True, commit=True)
        if not res: return jsonify({"error": "Request not found"}), 404
        return jsonify({"message": "Request approved"}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/follow/requests/<int:request_id>/deny", methods=["POST"])
def deny_follow_request(request_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        res = execute_query("DELETE FROM followers WHERE id=%s AND following_id=%s RETURNING id", (request_id, uid), fetch=True, commit=True)
        if not res: return jsonify({"error": "Request not found"}), 404
        return jsonify({"message": "Request denied"}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

# ---------------------------------------------------------------------------
# SAVED PROFILES
# ---------------------------------------------------------------------------

@app.route("/api/v1/saved_profiles", methods=["GET"])
def get_saved_profiles():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        res = execute_query("SELECT saved_user_id FROM saved_profiles WHERE user_id=%s", (uid,), fetch=True)
        return jsonify([r['saved_user_id'] for r in res]), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/saved_profiles", methods=["POST"])
def save_profile():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        data = request.json or {}
        saved_user_id = data.get("saved_user_id")
        if not saved_user_id: return jsonify({"error": "saved_user_id required"}), 400
        execute_query("INSERT INTO saved_profiles (user_id, saved_user_id) VALUES (%s, %s) ON CONFLICT (user_id, saved_user_id) DO NOTHING", (uid, saved_user_id), commit=True)
        return jsonify({"message": "Profile saved"}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/saved_profiles/<int:saved_user_id>", methods=["DELETE"])
def unsave_profile(saved_user_id):
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        execute_query("DELETE FROM saved_profiles WHERE user_id=%s AND saved_user_id=%s", (uid, saved_user_id), commit=True)
        return jsonify({"message": "Profile unsaved"}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/account/privacy", methods=["POST"])
def toggle_privacy():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        data = request.json or {}
        is_private = bool(data.get("is_private"))
        execute_query("UPDATE users SET is_private=%s WHERE id=%s", (is_private, uid), commit=True)
        return jsonify({"message": "Privacy updated", "is_private": is_private}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/notifications", methods=["GET"])
def get_notifications():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        notifs = execute_query("SELECT id, content, is_read, created_at, trader_id FROM trade_notifications WHERE user_id=%s ORDER BY created_at DESC LIMIT 50", (uid,), fetch=True)
        for n in notifs:
            if isinstance(n.get("created_at"), datetime.datetime):
                n["created_at"] = n["created_at"].isoformat()
        
        # Also get unread count
        unread_res = execute_query("SELECT COUNT(*) as count FROM trade_notifications WHERE user_id=%s AND is_read=false", (uid,), fetch=True)
        unread_count = unread_res[0]["count"] if unread_res else 0
        
        return jsonify({"notifications": notifs, "unread_count": unread_count}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/notifications/read", methods=["POST"])
def mark_notifications_read():
    try:
        uid = get_auth_user_id()
        if not uid: return jsonify({"error": "Unauthorized"}), 401
        execute_query("UPDATE trade_notifications SET is_read=true WHERE user_id=%s AND is_read=false", (uid,), commit=True)
        return jsonify({"message": "Marked read"}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

# ---------------------------------------------------------------------------
# PRICE ALERTS & POLLING
# ---------------------------------------------------------------------------
@app.route("/trading/alerts/<int:user_id>", methods=["GET"])
def get_user_alerts(user_id):
    try:
        alerts = execute_query("SELECT * FROM price_alerts WHERE user_id=%s ORDER BY created_at DESC", (user_id,), fetch=True)
        for a in alerts:
            a["target_price"] = float(a["target_price"])
            if isinstance(a.get("created_at"), datetime.datetime):
                a["created_at"] = a["created_at"].isoformat()
        return jsonify(alerts), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/trading/alerts", methods=["POST"])
def create_alert():
    try:
        uid = get_auth_user_id()
        if not uid:
            return jsonify({"error": "Unauthorized"}), 401
        data = request.json
        symbol = data.get("symbol")
        target = float(data.get("target_price", 0))
        cond = data.get("condition")
        if not symbol or target <= 0 or cond not in ["above", "below"]:
            return jsonify({"error": "Invalid alert parameters"}), 400
        
        execute_query(
            "INSERT INTO price_alerts (user_id, symbol, target_price, condition, is_active) VALUES (%s, %s, %s, %s, TRUE)",
            (uid, symbol, target, cond), commit=True
        )
        return jsonify({"message": "Alert created successfully"}), 201
    except Exception as e:
        app.logger.exception("create_alert failed")
        return jsonify({"error": str(e)}), 500

@app.route("/trading/alerts/<int:alert_id>", methods=["DELETE"])
def delete_alert(alert_id):
    try:
        uid = get_auth_user_id()
        if not uid:
            return jsonify({"error": "Unauthorized"}), 401
        
        execute_query("DELETE FROM price_alerts WHERE id=%s AND user_id=%s", (alert_id, uid), commit=True)
        return jsonify({"message": "Alert deleted"}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500


def poll_competitions():
    while True:
        try:
            # Find active duels that have expired (end_date < NOW())
            expired_duels = execute_query("SELECT * FROM competitions WHERE type = 'duel' AND status = 'active' AND end_date < NOW()", (), fetch=True)
            for d in expired_duels:
                duel_id = d['id']
                wager = float(d['wager_amount'])
                pot = wager * 2
                
                participants = execute_query("SELECT user_id, current_balance FROM competition_participants WHERE competition_id = %s ORDER BY current_balance DESC", (duel_id,), fetch=True)
                
                if len(participants) == 2:
                    winner_id = participants[0]['user_id']
                    # Settle
                    execute_query("UPDATE wallets SET balance = balance + %s WHERE user_id = %s", (pot, winner_id), commit=True)
                    execute_query("UPDATE competitions SET status = 'completed' WHERE id = %s", (duel_id,), commit=True)
                    
                    # Notify winner
                    try:
                        broadcast_fcm_message("Duel Won! 🏆", f"You won the 1v1 duel and earned ${pot}!", {"type": "duel_win"}, include_user_id=winner_id)
                    except: pass
                    
        except Exception as e:
            app.logger.exception("poll_competitions error")
        time.sleep(60) # Check every 60 seconds

def poll_price_alerts():
    import requests
    import time
    while True:
        try:
            time.sleep(30)
            alerts = execute_query("SELECT * FROM price_alerts WHERE is_active=TRUE", fetch=True)
            if not alerts:
                continue
                
            symbols = set([a["symbol"] for a in alerts])
            prices = {}
            # Get Spot prices
            try:
                res = requests.get("https://api.binance.com/api/v3/ticker/price", timeout=5)
                if res.status_code == 200:
                    for item in res.json():
                        if item["symbol"] in symbols:
                            prices[item["symbol"]] = float(item["price"])
            except Exception:
                pass
            
            for a in alerts:
                sym = a["symbol"]
                target = float(a["target_price"])
                cond = a["condition"]
                current_price = prices.get(sym)
                
                if current_price is None:
                    continue
                    
                triggered = False
                if cond == "above" and current_price >= target:
                    triggered = True
                elif cond == "below" and current_price <= target:
                    triggered = True
                    
                if triggered:
                    # Update DB
                    execute_query("UPDATE price_alerts SET is_active=FALSE WHERE id=%s", (a["id"],), commit=True)
                    # Send Notification
                    try:
                        title = f"Price Alert: {sym}"
                        body = f"{sym} has gone {cond} your target of ${target:,.2f} (Current: ${current_price:,.2f})"
                        send_fcm_message(a["user_id"], title, body, {"type": "price_alert", "symbol": sym})
                    except Exception as push_err:
                        app.logger.exception("Failed to send price alert push")
        except Exception as e:
            app.logger.error(f"Error in poll_price_alerts: {e}")

def poll_marketing_campaigns():
    import time, datetime
    while True:
        try:
            time.sleep(1800) # Check every 30 minutes
            
            # 1. Festival Notifications (Check if current time is between 12:00 and 12:30)
            now = datetime.datetime.now()
            today_str = now.strftime("%m-%d")
            festivals = {
                "01-01": ("Happy New Year!", "Start your year with green portfolios! 🎆"),
                "10-31": ("Happy Halloween!", "No tricks, just profitable treats! 🎃"),
                "12-25": ("Merry Christmas!", "Wishing you joy and prosperous trading this Christmas! 🎄"),
                "10-18": ("Happy Diwali!", "Wishing you wealth and light this Diwali! 🪔")
            }
            if today_str in festivals and now.hour == 12 and now.minute < 30:
                title, body = festivals[today_str]
                broadcast_fcm_message(title, body, {"type": "festival"})

            # 2. Inactivity Reminder (Balance 1000, 0 trades, created > 3 days ago, reminder not sent)
            # This logic is robust to Render server sleep because we rely on a DB column flag rather than a narrow time window.
            inactive_query = """
                SELECT u.id
                FROM users u
                JOIN wallets w ON u.id = w.user_id
                WHERE w.balance = 1000.0
                  AND u.welcome_reminder_sent = FALSE
                  AND NOT EXISTS (SELECT 1 FROM trades t WHERE t.user_id = u.id)
                  AND u.created_at <= NOW() - INTERVAL '3 days'
            """
            rows = execute_query(inactive_query, fetch=True)
            if rows:
                for r in rows:
                    uid = r['id']
                    # Mark it as sent immediately so we don't accidentally send it twice if the thread crashes
                    execute_query("UPDATE users SET welcome_reminder_sent = TRUE WHERE id = %s", (uid,), commit=True)
                    send_fcm_message(
                        uid, 
                        "We miss you! 👋", 
                        "Your $1000 virtual balance is waiting. Come back and make your first trade!", 
                        {"type": "reminder"}
                    )
                    
        except Exception as e:
            app.logger.error(f"Error in poll_marketing_campaigns: {e}")

# ---------------------------------------------------------------------------
# SOCIAL FEED
# ---------------------------------------------------------------------------
@app.route("/api/v1/feed", methods=["GET"])
def get_feed():
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        posts = execute_query("""
            SELECT p.id, p.content, p.trade_symbol, p.trade_type, p.trade_qty, p.trade_price, p.created_at,
                   u.username, u.profile_picture_url,
                   (u.google_id IS NOT NULL) as is_verified,
                   (SELECT COUNT(*) FROM feed_likes WHERE post_id = p.id) as likes_count,
                   (SELECT COUNT(*) FROM feed_comments WHERE post_id = p.id) as comments_count,
                   EXISTS(SELECT 1 FROM feed_likes WHERE post_id = p.id AND user_id = %s) as is_liked
            FROM feed_posts p
            JOIN users u ON p.user_id = u.id
            ORDER BY p.created_at DESC
            LIMIT 50
        """, (auth_uid,), fetch=True)
        
        posts = decrypt_rows(posts, ["username"])
        
        # Convert created_at to string and format results
        for p in posts:
            if p.get('created_at'):
                p['created_at'] = p['created_at'].isoformat() + "Z"
            # Ensure boolean for is_liked and is_verified
            p['is_liked'] = bool(p['is_liked'])
            p['is_verified'] = bool(p['is_verified'])
            
        return jsonify(posts), 200
    except Exception as e:
        app.logger.exception("Failed to get feed")
        return jsonify({"error": "Failed to get feed"}), 500

@app.route("/api/v1/feed", methods=["POST"])
def create_feed_post():
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        data = request.json or {}
        content = data.get("content")
        trade_symbol = data.get("trade_symbol")
        trade_type = data.get("trade_type")
        trade_qty = data.get("trade_qty")
        trade_price = data.get("trade_price")
        
        if not content and not trade_symbol:
            return jsonify({"error": "Content or trade data is required"}), 400
            
        post_id = execute_query("""
            INSERT INTO feed_posts (user_id, content, trade_symbol, trade_type, trade_qty, trade_price)
            VALUES (%s, %s, %s, %s, %s, %s)
            RETURNING id
        """, (auth_uid, content, trade_symbol, trade_type, trade_qty, trade_price), fetch=True, commit=True)
        
        return jsonify({"message": "Post created successfully", "id": post_id[0]["id"] if post_id else None}), 201
    except Exception as e:
        app.logger.exception("Failed to create post")
        return jsonify({"error": "Failed to create post"}), 500

@app.route("/api/v1/feed/<int:post_id>/like", methods=["POST"])
def toggle_like(post_id):
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        # Check if already liked
        liked = execute_query("SELECT 1 FROM feed_likes WHERE user_id = %s AND post_id = %s", (auth_uid, post_id), fetch=True)
        if liked:
            execute_query("DELETE FROM feed_likes WHERE user_id = %s AND post_id = %s", (auth_uid, post_id), commit=True)
            action = "unliked"
        else:
            execute_query("INSERT INTO feed_likes (user_id, post_id) VALUES (%s, %s)", (auth_uid, post_id), commit=True)
            action = "liked"
        return jsonify({"message": f"Post {action} successfully"}), 200
    except Exception as e:
        app.logger.exception("Failed to toggle like")
        return jsonify({"error": "Failed to toggle like"}), 500

@app.route("/api/v1/feed/<int:post_id>/comments", methods=["GET"])
def get_comments(post_id):
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        comments = execute_query("""
            SELECT c.id, c.content, c.created_at, u.username, u.profile_picture_url,
                   (u.google_id IS NOT NULL) as is_verified
            FROM feed_comments c
            JOIN users u ON c.user_id = u.id
            WHERE c.post_id = %s
            ORDER BY c.created_at ASC
        """, (post_id,), fetch=True)
        
        comments = decrypt_rows(comments, ["username"])
        
        for c in comments:
            if c.get('created_at'):
                c['created_at'] = c['created_at'].isoformat() + "Z"
            c['is_verified'] = bool(c['is_verified'])
            
        return jsonify(comments), 200
    except Exception as e:
        app.logger.exception("Failed to get comments")
        return jsonify({"error": "Failed to get comments"}), 500

@app.route("/api/v1/feed/<int:post_id>/comments", methods=["POST"])
def create_comment(post_id):
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        data = request.json or {}
        content = data.get("content")
        
        if not content:
            return jsonify({"error": "Content is required"}), 400
            
        execute_query("""
            INSERT INTO feed_comments (post_id, user_id, content)
            VALUES (%s, %s, %s)
        """, (post_id, auth_uid, content), commit=True)
        
        return jsonify({"message": "Comment created successfully"}), 201
    except Exception as e:
        app.logger.exception("Failed to create comment")
        return jsonify({"error": "Failed to create comment"}), 500

# ---------------------------------------------------------------------------
# APP DOWNLOAD TRACKING
# ---------------------------------------------------------------------------
@app.route("/api/track-download", methods=["POST", "OPTIONS"])
def track_download():
    if request.method == "OPTIONS":
        return jsonify({}), 200
        
    try:
        data = request.json or {}
        platform = data.get("platform", "unknown")
        architecture = data.get("architecture", "unknown")
        
        execute_query(
            "INSERT INTO app_downloads (platform, architecture) VALUES (%s, %s)",
            (platform, architecture),
            commit=True
        )
        return jsonify({"success": True}), 201
    except Exception as e:
        app.logger.exception("Failed to track download")
        return jsonify({"error": "Failed to track download"}), 500

# Start the polling thread
threading.Thread(target=poll_competitions, daemon=True).start()
threading.Thread(target=poll_price_alerts, daemon=True).start()
threading.Thread(target=poll_marketing_campaigns, daemon=True).start()



# ---------------------------------------------------------------------------
# COMPETITIONS
# ---------------------------------------------------------------------------
@app.route("/api/v1/competitions", methods=["GET", "OPTIONS"])
def get_competitions():
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        rows = execute_query("SELECT * FROM competitions ORDER BY start_date DESC", (), fetch=True)
        return jsonify({"competitions": rows}), 200
    except Exception as e:
        app.logger.exception("Failed to fetch competitions")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/competitions/join", methods=["POST", "OPTIONS"])
def join_competition():
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        data = request.json or {}
        comp_id = data.get("competition_id")
        
        comp = execute_query("SELECT starting_balance FROM competitions WHERE id = %s AND is_active = TRUE", (comp_id,), fetch=True)
        if not comp: return jsonify({"error": "Competition not found or inactive"}), 404
        
        starting_balance = comp[0]["starting_balance"]
        
        execute_query(
            "INSERT INTO competition_participants (competition_id, user_id, current_balance) VALUES (%s, %s, %s) ON CONFLICT DO NOTHING",
            (comp_id, auth_uid, starting_balance), commit=True
        )
        return jsonify({"message": "Joined competition successfully"}), 200
    except Exception as e:
        app.logger.exception("Failed to join competition")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/competitions/<int:comp_id>/leaderboard", methods=["GET", "OPTIONS"])
def get_competition_leaderboard(comp_id):
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        rows = execute_query("""
            SELECT cp.user_id, u.username, cp.current_balance
            FROM competition_participants cp
            JOIN users u ON cp.user_id = u.id
            WHERE cp.competition_id = %s
            ORDER BY cp.current_balance DESC
        """, (comp_id,), fetch=True)
        rows = decrypt_rows(rows, ["username"])
        return jsonify({"leaderboard": rows}), 200
    except Exception as e:
        app.logger.exception("Failed to fetch leaderboard")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/competitions/duels/<int:duel_id>/portfolios", methods=["GET", "OPTIONS"])
def get_duel_portfolios(duel_id):
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        # Get participants
        participants = execute_query("""
            SELECT cp.user_id, u.username, cp.current_balance 
            FROM competition_participants cp 
            JOIN users u ON cp.user_id = u.id 
            WHERE cp.competition_id = %s
        """, (duel_id,), fetch=True)
        participants = decrypt_rows(participants, ["username"])
        
        # Get all open trades
        trades = execute_query("SELECT user_id, symbol, buy_price, quantity FROM competition_trades WHERE competition_id = %s AND status = 'OPEN'", (duel_id,), fetch=True)
        
        from collections import defaultdict
        trades_by_user = defaultdict(list)
        for t in trades:
            trades_by_user[t['user_id']].append({
                "symbol": t['symbol'],
                "buy_price": float(t['buy_price']),
                "quantity": float(t['quantity'])
            })
            
        portfolios = []
        for p in participants:
            portfolios.append({
                "user_id": p['user_id'],
                "username": p['username'],
                "balance": float(p['current_balance']),
                "open_trades": trades_by_user.get(p['user_id'], [])
            })
            
        return jsonify({"portfolios": portfolios}), 200
    except Exception as e:
        app.logger.exception("Failed to fetch portfolios")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/competitions/<int:comp_id>/trade", methods=["POST", "OPTIONS"])
def execute_competition_trade(comp_id):
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        data = request.json or {}
        symbol = data.get("symbol", "").upper()
        if symbol and symbol != "USDT" and not symbol.endswith("USDT"):
            symbol = f"{symbol}USDT"
        
        price = float(data.get("price", 0))
        quantity = float(data.get("quantity", 0))
        trade_type = data.get("type") # "BUY" or "SELL"
        
        if not symbol or price <= 0 or quantity <= 0 or trade_type not in ["BUY", "SELL"]:
            return jsonify({"error": "Invalid trade parameters"}), 400
            
        participant = execute_query("SELECT current_balance FROM competition_participants WHERE competition_id = %s AND user_id = %s", (comp_id, auth_uid), fetch=True)
        if not participant: return jsonify({"error": "Not joined in competition"}), 400
        
        current_balance = float(participant[0]["current_balance"])
        total_cost = price * quantity
        
        if trade_type == "BUY":
            if current_balance < total_cost:
                return jsonify({"error": "Insufficient virtual balance"}), 400
            
            # Execute Buy
            execute_query("UPDATE competition_participants SET current_balance = current_balance - %s WHERE competition_id = %s AND user_id = %s", (total_cost, comp_id, auth_uid), commit=True)
            execute_query("INSERT INTO competition_trades (competition_id, user_id, symbol, buy_price, quantity, status) VALUES (%s, %s, %s, %s, %s, 'OPEN')", (comp_id, auth_uid, symbol, price, quantity), commit=True)
        
        else: # SELL
            # Support partial sells and multiple lots to match frontend holdings aggregation
            open_trades = execute_query("SELECT id, buy_price, quantity FROM competition_trades WHERE competition_id = %s AND user_id = %s AND symbol = %s AND status = 'OPEN' ORDER BY id ASC", (comp_id, auth_uid, symbol), fetch=True)
            if not open_trades:
                return jsonify({"error": "No open trade for this symbol"}), 400
                
            total_owned = sum(float(t["quantity"]) for t in open_trades)
            if quantity > total_owned + 0.000001:
                return jsonify({"error": "Cannot sell more than owned"}), 400
                
            revenue = price * quantity
            
            # Update balance
            execute_query("UPDATE competition_participants SET current_balance = current_balance + %s WHERE competition_id = %s AND user_id = %s", (revenue, comp_id, auth_uid), commit=True)
            
            remaining_to_sell = quantity
            for t in open_trades:
                if remaining_to_sell <= 0:
                    break
                t_qty = float(t["quantity"])
                if remaining_to_sell >= t_qty:
                    # Close this lot completely
                    execute_query("UPDATE competition_trades SET sell_price = %s, status = 'CLOSED' WHERE id = %s", (price, t["id"]), commit=True)
                    remaining_to_sell -= t_qty
                else:
                    # Partial close: split the lot
                    new_open_qty = t_qty - remaining_to_sell
                    execute_query("UPDATE competition_trades SET quantity = %s WHERE id = %s", (new_open_qty, t["id"]), commit=True)
                    execute_query("INSERT INTO competition_trades (competition_id, user_id, symbol, buy_price, sell_price, quantity, status) VALUES (%s, %s, %s, %s, %s, %s, 'CLOSED')", (comp_id, auth_uid, symbol, t["buy_price"], price, remaining_to_sell), commit=True)
                    remaining_to_sell = 0

        return jsonify({"message": f"Trade {trade_type} executed successfully"}), 200
        
    except Exception as e:
        app.logger.exception("Failed to execute trade")
        return jsonify({"error": str(e)}), 500


# ---------------------------------------------------------------------------
# 1v1 DUELS
# ---------------------------------------------------------------------------
@app.route("/api/v1/competitions/duels", methods=["GET", "OPTIONS"])
def get_duels():
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        # Fetch duels (LIMIT 50 for performance)
        duels_rows = execute_query("SELECT * FROM competitions WHERE type = 'duel' ORDER BY start_date DESC LIMIT 50", (), fetch=True)
        
        if not duels_rows:
            return jsonify({"duels": []}), 200
            
        duel_ids = tuple(d['id'] for d in duels_rows)
        
        # Fetch all participants in ONE query
        participants_rows = execute_query("""
            SELECT cp.competition_id, u.username, cp.current_balance 
            FROM competition_participants cp 
            JOIN users u ON cp.user_id = u.id 
            WHERE cp.competition_id IN %s
        """, (duel_ids,), fetch=True)
        
        participants_rows = decrypt_rows(participants_rows, ["username"])
        
        # Group participants by duel_id
        from collections import defaultdict
        p_map = defaultdict(list)
        for p in participants_rows:
            p_map[p['competition_id']].append(dict(p))
            
        duels = []
        for duel in duels_rows:
            d = dict(duel)
            d['participants'] = p_map.get(d['id'], [])
            duels.append(d)
        
        return jsonify({"duels": duels}), 200
    except Exception as e:
        app.logger.exception("Failed to fetch duels")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/competitions/duels/create", methods=["POST", "OPTIONS"])

@app.route("/api/v1/competitions/duels/<int:duel_id>", methods=["GET", "OPTIONS"])
def get_single_duel(duel_id):
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        duel = execute_query("SELECT * FROM competitions WHERE id = %s AND type = 'duel'", (duel_id,), fetch=True)
        if not duel: return jsonify({"error": "Duel not found"}), 404
        d = dict(duel[0])
        
        participants = execute_query("""
            SELECT u.username, cp.current_balance 
            FROM competition_participants cp 
            JOIN users u ON cp.user_id = u.id 
            WHERE cp.competition_id = %s
        """, (duel_id,), fetch=True)
        participants = decrypt_rows(participants, ["username"])
        d['participants'] = [dict(p) for p in participants]
        
        return jsonify({"duel": d}), 200
    except Exception as e:
        app.logger.exception("Failed to fetch single duel")
        return jsonify({"error": str(e)}), 500

def create_duel():
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        data = request.json or {}
        wager_amount = float(data.get("wager_amount", 200))
        starting_balance = float(data.get("starting_balance", 3000))
        
        # Check wallet balance
        wallet = execute_query("SELECT balance FROM wallets WHERE user_id = %s", (auth_uid,), fetch=True)
        if not wallet or float(wallet[0]["balance"]) < wager_amount:
            return jsonify({"error": f"Insufficient wallet balance. You need ${wager_amount} to wager."}), 400
        
        # Deduct wager
        execute_query("UPDATE wallets SET balance = balance - %s WHERE user_id = %s", (wager_amount, auth_uid), commit=True)
        
        # Create Duel
        duel_id_rows = execute_query("""
            INSERT INTO competitions (name, description, type, wager_amount, max_participants, starting_balance, created_by, status)
            VALUES ('1v1 Duel', 'Head-to-head paper trading battle', 'duel', %s, 2, %s, %s, 'waiting')
            RETURNING id;
        """, (wager_amount, starting_balance, auth_uid), fetch=True, commit=True)
        
        duel_id = duel_id_rows[0]['id']
        
        # Add creator to participants
        execute_query(
            "INSERT INTO competition_participants (competition_id, user_id, current_balance) VALUES (%s, %s, %s)",
            (duel_id, auth_uid, starting_balance), commit=True
        )
        
        return jsonify({"message": "Duel created successfully", "duel_id": duel_id}), 200
    except Exception as e:
        app.logger.exception("Failed to create duel")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/competitions/duels/join", methods=["POST", "OPTIONS"])
def join_duel():
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        data = request.json or {}
        duel_id = data.get("duel_id")
        
        duel = execute_query("SELECT * FROM competitions WHERE id = %s AND type = 'duel'", (duel_id,), fetch=True)
        if not duel: return jsonify({"error": "Duel not found"}), 404
        d = duel[0]
        
        if d['status'] != 'waiting':
            return jsonify({"error": "Duel is no longer waiting for challengers"}), 400
            
        # Check if already joined
        existing = execute_query("SELECT 1 FROM competition_participants WHERE competition_id = %s AND user_id = %s", (duel_id, auth_uid), fetch=True)
        if existing: return jsonify({"error": "You are already in this duel"}), 400
        
        wager_amount = float(d['wager_amount'])
        
        # Check wallet balance
        wallet = execute_query("SELECT balance FROM wallets WHERE user_id = %s", (auth_uid,), fetch=True)
        if not wallet or float(wallet[0]["balance"]) < wager_amount:
            return jsonify({"error": f"Insufficient wallet balance. You need ${wager_amount} to wager."}), 400
            
        # Deduct wager
        execute_query("UPDATE wallets SET balance = balance - %s WHERE user_id = %s", (wager_amount, auth_uid), commit=True)
        
        # Add to participants
        execute_query(
            "INSERT INTO competition_participants (competition_id, user_id, current_balance) VALUES (%s, %s, %s)",
            (duel_id, auth_uid, d['starting_balance']), commit=True
        )
        
        # Check participant count to activate
        participants = execute_query("SELECT COUNT(*) as count FROM competition_participants WHERE competition_id = %s", (duel_id,), fetch=True)
        if participants and participants[0]['count'] >= 2:
            execute_query("UPDATE competitions SET status = 'active', start_date = NOW(), end_date = NOW() + INTERVAL '3 days' WHERE id = %s", (duel_id,), commit=True)
            
        return jsonify({"message": "Joined duel successfully"}), 200
    except Exception as e:
        app.logger.exception("Failed to join duel")
        return jsonify({"error": str(e)}), 500

@app.route("/api/v1/competitions/duels/cancel", methods=["POST", "OPTIONS"])
def cancel_duel():
    if request.method == "OPTIONS":
        return jsonify({}), 200
    try:
        auth_uid = get_auth_user_id()
        if not auth_uid: return jsonify({"error": "Unauthorized"}), 401
        
        data = request.json or {}
        duel_id = data.get("duel_id")
        
        duel = execute_query("SELECT * FROM competitions WHERE id = %s AND type = 'duel'", (duel_id,), fetch=True)
        if not duel: return jsonify({"error": "Duel not found"}), 404
        d = duel[0]
        
        if str(d.get('created_by')) != str(auth_uid):
            return jsonify({"error": "Only the creator can cancel this duel"}), 403
            
        if d['status'] != 'waiting':
            return jsonify({"error": "Only waiting duels can be cancelled"}), 400
            
        # Refund wager
        execute_query("UPDATE wallets SET balance = balance + %s WHERE user_id = %s", (d['wager_amount'], auth_uid), commit=True)
        
        # Delete dependencies and room
        execute_query("DELETE FROM competition_participants WHERE competition_id = %s", (duel_id,), commit=True)
        execute_query("DELETE FROM competitions WHERE id = %s", (duel_id,), commit=True)
        
        return jsonify({"message": "Duel cancelled and wager refunded"}), 200
    except Exception as e:
        app.logger.exception("Failed to cancel duel")
        return jsonify({"error": str(e)}), 500

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000, debug=True)
