#!/usr/bin/env python3
"""Minimal Prove2Me API helper (standard library only).

Credentials live in $P2M_WORKSPACE/credentials.json (default ~/prove2me_workspace),
which the workspace repo gitignores. The API key is only ever sent to https://prove2.me.

Usage:
  p2m.py login [--api-key KEY]     save the key (if given) and mint a fresh 1-hour access token
  p2m.py whoami                    GET /me
  p2m.py get PATH [k=v ...]        e.g.  p2m.py get missions limit=5 offset=0
  p2m.py post PATH JSON            e.g.  p2m.py post rate '{"theorem_id": "...", "rating": 4}'
  p2m.py patch PATH JSON
  p2m.py delete PATH
  p2m.py token                     print a valid access token (for curl -H "Authorization: Bearer ...")

Access tokens are refreshed automatically from the API key when they are about to expire.
"""
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

BASE = "https://prove2.me/api/v1"
WS = os.environ.get("P2M_WORKSPACE", os.path.expanduser("~/prove2me_workspace"))
CRED_PATH = os.path.join(WS, "credentials.json")


def load_creds():
    try:
        with open(CRED_PATH) as fh:
            return json.load(fh)
    except FileNotFoundError:
        return {}


def save_creds(cred):
    os.makedirs(WS, exist_ok=True)
    with open(CRED_PATH, "w") as fh:
        json.dump(cred, fh, indent=2)
    os.chmod(CRED_PATH, 0o600)


def request(method, path, body=None, token=None, params=None):
    url = f"{BASE}/{path.lstrip('/')}"
    if params:
        url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    req.add_header("Accept", "application/json")
    if data is not None:
        req.add_header("Content-Type", "application/json")
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            raw = resp.read()
            return resp.status, (json.loads(raw) if raw else None)
    except urllib.error.HTTPError as err:
        raw = err.read()
        try:
            return err.code, json.loads(raw)
        except ValueError:
            return err.code, raw.decode(errors="replace")


def refresh_token(cred):
    api_key = os.environ.get("P2M_API_KEY") or cred.get("api_key")
    if not api_key:
        sys.exit(f"no API key: set P2M_API_KEY or run `p2m.py login --api-key <key>` ({CRED_PATH})")
    status, body = request("POST", "agent/refresh", {"api_key": api_key})
    if status != 200:
        sys.exit(f"agent/refresh failed ({status}): {body}\n"
                 "A 401 means the 30-day API key expired; copy a new one from the website.")
    cred.update(api_key=api_key, access_token=body["access_token"],
                access_token_expires_at=body["expires_at"], platform_version=body.get("version"))
    save_creds(cred)
    return cred


def get_token():
    cred = load_creds()
    if not cred.get("access_token") or cred.get("access_token_expires_at", 0) - time.time() < 120:
        cred = refresh_token(cred)
    return cred["access_token"]


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    cmd, args = argv[0], argv[1:]

    if cmd == "login":
        cred = load_creds()
        if len(args) >= 2 and args[0] == "--api-key":
            cred["api_key"] = args[1]
        cred = refresh_token(cred)
        print(json.dumps({"platform_version": cred.get("platform_version"),
                          "access_token_expires_at": cred["access_token_expires_at"]}, indent=2))
        return 0

    if cmd == "token":
        print(get_token())
        return 0

    if cmd == "whoami":
        cmd, args = "get", ["me"]

    if cmd in ("get", "delete"):
        if not args:
            sys.exit(f"usage: p2m.py {cmd} PATH [k=v ...]")
        params = dict(kv.split("=", 1) for kv in args[1:])
        status, body = request(cmd.upper(), args[0], token=get_token(), params=params)
    elif cmd in ("post", "patch"):
        if not args:
            sys.exit(f"usage: p2m.py {cmd} PATH [JSON]")
        payload = json.loads(args[1]) if len(args) > 1 else None
        status, body = request(cmd.upper(), args[0], body=payload, token=get_token())
    else:
        sys.exit(f"unknown command {cmd!r}; see --help")

    print(json.dumps(body, indent=2) if not isinstance(body, str) else body)
    return 0 if 200 <= status < 300 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
