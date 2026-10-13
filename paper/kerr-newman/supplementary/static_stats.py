#!/usr/bin/env python3
"""Static statistics for the Kerr-Newman Lean formalization (read-only on the sources)."""
import os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_NOHAIR = _os.path.normpath(_os.path.join(_HERE, '..', '..', '..', 'prove2me', 'nohair'))
import json, os, re, sys, glob, time

R = _NOHAIR
OUT = _os.path.join(_HERE, "static_stats.json")


def strip_comments(src):
    # remove nested block comments /- ... -/ (incl. doc comments) and line comments --
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == "\n":
                out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(src[i]); i += 1
    return "".join(out)


DECL_PREFIX = r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|irreducible|unsafe|partial)\s+)*"
RE_THM = re.compile(DECL_PREFIX + r"(?:theorem|lemma)\s", re.M)
RE_DEF = re.compile(DECL_PREFIX + r"(?:def|abbrev)\s", re.M)
RE_STRUCT = re.compile(DECL_PREFIX + r"(?:structure|inductive|class)\s", re.M)
TACTICS = {
    "linear_combination": re.compile(r"\blinear_combination\b"),
    "field_simp": re.compile(r"\bfield_simp\b"),
    "ring": re.compile(r"(?<![\w.])ring(?![\w'])"),
    "ring_nf": re.compile(r"\bring_nf\b"),
    "fin_cases": re.compile(r"\bfin_cases\b"),
    "simp_only": re.compile(r"\bsimp only\b"),
    "nlinarith": re.compile(r"\bnlinarith\b"),
    "positivity": re.compile(r"\bpositivity\b"),
}


def file_stats(path):
    raw = open(path, "rb").read()
    src = raw.decode("utf-8")
    code = strip_comments(src)
    d = {
        "file": os.path.relpath(path, R),
        "lines": src.count("\n") + (0 if src.endswith("\n") else 1),
        "bytes": len(raw),
        "theorems": len(RE_THM.findall(code)),
        "defs": len(RE_DEF.findall(code)),
        "structures": len(RE_STRUCT.findall(code)),
    }
    for k, rx in TACTICS.items():
        d[k] = len(rx.findall(code))
    d["sorry"] = len(re.findall(r"\bsorry\b", code))
    return d


def classify(f):
    b = os.path.basename(f)
    if b.startswith("Thm_"):
        return "stub"
    if b.startswith("Def_NoHair_KerrNewmanEinstein_"):
        return "einstein_def"
    if b.startswith("Sol_NoHair_KNE_thm_"):
        return "einstein_thm_sol"
    if b == "Sol_NoHair_kerrNewman_einstein.lean":
        return "einstein_final"
    if b.startswith("Sol_NoHair_kerrNewman_"):
        return "maxwell_part"
    return "other"


def main():
    files = sorted(glob.glob(R + "/*.lean")) + sorted(glob.glob(R + "/einstein/*.lean"))
    rows = [dict(file_stats(f), cls=classify(f)) for f in files]
    keys = ["lines", "bytes", "theorems", "defs", "structures"] + list(TACTICS) + ["sorry"]

    def tot(cls_set):
        sel = [r for r in rows if r["cls"] in cls_set]
        t = {k: sum(r[k] for r in sel) for k in keys}
        t["files"] = len(sel)
        return t

    totals = {
        "einstein_def_blocks": tot({"einstein_def"}),
        "einstein_thm_solutions": tot({"einstein_thm_sol"}),
        "einstein_final": tot({"einstein_final"}),
        "einstein_all": tot({"einstein_def", "einstein_thm_sol", "einstein_final"}),
        "maxwell_parts_incl_glue": tot({"maxwell_part"}),
        "stubs": tot({"stub"}),
        "grand_total_excl_stubs": tot({"einstein_def", "einstein_thm_sol", "einstein_final", "maxwell_part"}),
    }
    json.dump({"rows": rows, "totals": totals}, open(OUT, "w"), indent=1)
    hdr = ["file", "cls"] + keys
    print("\t".join(hdr))
    for r in rows:
        print("\t".join(str(r[k]) for k in hdr))
    for k, t in totals.items():
        print(k, json.dumps(t))


if __name__ == "__main__":
    main()
