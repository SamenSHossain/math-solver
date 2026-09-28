#!/usr/bin/env python3
"""Minimal Prove2Me API client and CLI.

Reads the API key from credentials.json at the workspace root (key "api_key")
or from the PROVE2ME_API_KEY environment variable, exchanges it for a 1-hour
access token, and caches the token back into credentials.json.

Usage:
  python tools/p2m.py me
  python tools/p2m.py get "/missions?limit=5"
  python tools/p2m.py post /rate '{"theorem_id": "...", "rating": 5}'
  python tools/p2m.py patch /submissions/<id> '{"explanation": "..."}'
  python tools/p2m.py theorem <theorem_id> [--mirror]
  python tools/p2m.py verify <theorem_id> Solutions/Sol_x.lean [--disprove]
                             [--explanation-file FILE] [--wait]
  python tools/p2m.py poll <submission_id> [--wait]

Security: the key and token are only ever sent to https://prove2.me.
"""
import argparse
import json
import os
import sys
import time
from pathlib import Path

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

BASE = "https://prove2.me/api/v1"
SKILL_VERSION = "0.11.4"  # metadata.version of skill.md this client follows
ROOT = Path(__file__).resolve().parent.parent
CRED = ROOT / "credentials.json"


def _session():
    s = requests.Session()
    retry = Retry(
        total=6, connect=6, read=2, backoff_factor=1.0,
        status_forcelist=(502, 503, 504),
        allowed_methods=frozenset(["GET", "HEAD", "OPTIONS", "DELETE"]),
    )
    s.mount("https://", HTTPAdapter(max_retries=retry))
    return s


class Client:
    def __init__(self):
        self.s = _session()
        self.creds = json.loads(CRED.read_text()) if CRED.exists() else {}
        key = os.environ.get("PROVE2ME_API_KEY") or self.creds.get("api_key")
        if not key:
            sys.exit("No API key: set PROVE2ME_API_KEY or put \"api_key\" in credentials.json")
        self.creds["api_key"] = key

    def _save(self):
        # atomic write: concurrent refreshes never leave a half-written file
        tmp = CRED.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(self.creds, indent=2) + "\n")
        os.chmod(tmp, 0o600)
        os.replace(tmp, CRED)

    def token(self):
        if self.creds.get("access_token") and self.creds.get("expires_at", 0) - time.time() > 120:
            return self.creds["access_token"]
        r = self.s.post(f"{BASE}/agent/refresh", json={"api_key": self.creds["api_key"]}, timeout=60)
        if r.status_code == 401:
            sys.exit("API key expired or invalid: copy a new one from prove2.me (account menu -> API key)")
        r.raise_for_status()
        d = r.json()
        self.creds.update(access_token=d["access_token"], expires_at=d["expires_at"])
        self._save()
        if d.get("version") != SKILL_VERSION:
            print(f"warning: platform version {d.get('version')} != skill version {SKILL_VERSION}; "
                  f"re-read https://prove2.me/skill.md", file=sys.stderr)
        return d["access_token"]

    def req(self, method, path, **kw):
        kw.setdefault("timeout", 120)
        headers = kw.pop("headers", {})
        headers["Authorization"] = f"Bearer {self.token()}"
        r = self.s.request(method, BASE + path, headers=headers, **kw)
        try:
            body = r.json()
        except ValueError:
            body = r.text
        if not r.ok:
            raise RuntimeError(f"{method} {path} -> {r.status_code}: {body}")
        return body

    def get(self, path):
        return self.req("GET", path)

    def post(self, path, body=None):
        return self.req("POST", path, json=body)

    def patch(self, path, body=None):
        return self.req("PATCH", path, json=body)

    def verify(self, theorem_id, file, explanation=None, disprove=False):
        data = {"theorem_id": theorem_id}
        if disprove:
            data["proof_type"] = "disprove"
        if explanation:
            data["explanation"] = explanation
        with open(file, "rb") as f:
            return self.req("POST", "/verify", data=data, files={"file": (os.path.basename(file), f)})

    def poll(self, submission_id, wait=False, interval=10, limit=3600):
        t0 = time.time()
        while True:
            d = self.get(f"/verify?submission_id={submission_id}")
            if not wait or d.get("status") != "PENDING" or time.time() - t0 > limit:
                return d
            time.sleep(interval)


def slug(name):
    return name.replace(".", "_")


def mirror_theorem(c, theorem_id):
    """Save a platform theorem as Theorems/Thm_<slug>.lean (preamble + statement, ends in `by sorry`)."""
    t = c.get(f"/theorems/{theorem_id}")
    path = ROOT / "Theorems" / f"Thm_{slug(t['theorem_name'])}.lean"
    path.write_text((t.get("preamble") or "").rstrip() + "\n\n" + t["formal_statement"].rstrip() + "\n")
    return t, path


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("me")
    g = sub.add_parser("get"); g.add_argument("path")
    po = sub.add_parser("post"); po.add_argument("path"); po.add_argument("body", nargs="?")
    pa = sub.add_parser("patch"); pa.add_argument("path"); pa.add_argument("body", nargs="?")
    th = sub.add_parser("theorem"); th.add_argument("theorem_id"); th.add_argument("--mirror", action="store_true")
    v = sub.add_parser("verify"); v.add_argument("theorem_id"); v.add_argument("file")
    v.add_argument("--disprove", action="store_true"); v.add_argument("--explanation-file")
    v.add_argument("--wait", action="store_true")
    pl = sub.add_parser("poll"); pl.add_argument("submission_id"); pl.add_argument("--wait", action="store_true")
    a = p.parse_args(argv)

    c = Client()
    if a.cmd == "me":
        out = c.get("/me")
    elif a.cmd == "get":
        out = c.get(a.path)
    elif a.cmd in ("post", "patch"):
        body = json.loads(a.body) if a.body else None
        out = (c.post if a.cmd == "post" else c.patch)(a.path, body)
    elif a.cmd == "theorem":
        if a.mirror:
            out, path = mirror_theorem(c, a.theorem_id)
            print(f"wrote {path.relative_to(ROOT)}", file=sys.stderr)
        else:
            out = c.get(f"/theorems/{a.theorem_id}")
    elif a.cmd == "verify":
        expl = Path(a.explanation_file).read_text() if a.explanation_file else None
        out = c.verify(a.theorem_id, a.file, explanation=expl, disprove=a.disprove)
        if a.wait and out.get("submission_id"):
            out = c.poll(out["submission_id"], wait=True)
    elif a.cmd == "poll":
        out = c.poll(a.submission_id, wait=a.wait)
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
