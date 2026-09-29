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
  python tools/p2m.py scout <mission_id> [--mirror] [--out DIR]

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


def _safe(c, path):
    try:
        return c.get(path)
    except Exception as e:  # keep scouting even if one endpoint fails
        return {"_error": str(e)}


def scout_mission(c, mission_id, mirror=False, out=None):
    """One-shot reconnaissance of a mission: detail, milestones (+history), frontier,
    decompositions of the root, discussion, and submissions of every open leaf.
    Optionally mirrors every frontier theorem into Theorems/ and writes a JSON dump."""
    missions = _safe(c, "/missions?limit=100&offset=0")
    mission = None
    if isinstance(missions, dict):
        total = missions.get("total", 0)
        found = [m for m in missions.get("missions", []) if m.get("id") == mission_id]
        offset = 100
        while not found and offset < total:
            page = _safe(c, f"/missions?limit=100&offset={offset}")
            found = [m for m in page.get("missions", []) if m.get("id") == mission_id]
            offset += 100
        mission = found[0] if found else None
    report = {"mission": mission}
    root = (mission or {}).get("main_theorem", {}).get("theorem_id")
    report["milestones"] = _safe(c, f"/missions/{mission_id}/milestones?limit=100")
    for m in (report["milestones"] or {}).get("milestones", []) or []:
        m["history"] = _safe(c, f"/milestones/{m['id']}/history?limit=20")
        if m.get("theorem"):
            m["theorem_detail"] = _safe(c, f"/theorems/{m['theorem']['id']}")
    report["comments"] = _safe(c, f"/missions/{mission_id}/comments?limit=100")
    if root:
        report["root"] = _safe(c, f"/theorems/{root}")
        report["open_leaves"] = _safe(c, f"/theorems/{root}/open-leaves?limit=100")
        report["decompositions"] = _safe(c, f"/theorems/{root}/decompositions")
        report["graph"] = _safe(c, f"/theorems/{root}/graph")
        leaves = (report["open_leaves"] or {}).get("open_leaves", []) or []
        report["leaves"] = []
        for leaf in leaves:
            tid = leaf["theorem_id"]
            d = _safe(c, f"/theorems/{tid}")
            d["submissions"] = _safe(c, f"/theorems/{tid}/submissions")
            d["mentions"] = _safe(c, f"/theorems/{tid}/mentions")
            d["decompositions"] = _safe(c, f"/theorems/{tid}/decompositions")
            report["leaves"].append(d)
            if mirror and "theorem_name" in d:
                path = ROOT / "Theorems" / f"Thm_{slug(d['theorem_name'])}.lean"
                path.write_text((d.get("preamble") or "").rstrip() + "\n\n" + d["formal_statement"].rstrip() + "\n")
                print(f"mirrored {path.relative_to(ROOT)}", file=sys.stderr)
    if out:
        Path(out).write_text(json.dumps(report, indent=2, ensure_ascii=False))
        print(f"wrote {out}", file=sys.stderr)
    return report


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
    sc = sub.add_parser("scout"); sc.add_argument("mission_id"); sc.add_argument("--mirror", action="store_true")
    sc.add_argument("--out")
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
    elif a.cmd == "scout":
        out = scout_mission(c, a.mission_id, mirror=a.mirror, out=a.out)
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
