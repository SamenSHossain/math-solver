#!/usr/bin/env python3
"""Statistics of the linear_combination certificates and the closed-form polynomials
in the Einstein definition blocks (read-only on the sources)."""
import os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_NOHAIR = _os.path.normpath(_os.path.join(_HERE, '..', '..', '..', 'prove2me', 'nohair'))
import json, os, re, glob, statistics, time
import sympy as sp
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

E = _os.path.join(_NOHAIR, "einstein")
OUT = _os.path.join(_HERE, "cert_stats.json")
VARS = "a m e R K1 K2 K3 W".split()
P, *G = ring(",".join(VARS), QQ)
GD = dict(zip(VARS, G))
SYMS = sp.symbols(VARS)
SD = dict(zip(VARS, SYMS))
ATOMS = ["R", "K1", "K2", "K3", "W"]


def lean_to_py(s):
    s = re.sub(r"\(\s*(-?[0-9]+(?:\s*/\s*[0-9]+)?)\s*:\s*[ℕℝ]\s*\)", r"(\1)", s)
    s = s.replace("^", "**")
    return s


def match_paren(s, i):
    assert s[i] == "("
    d = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            d += 1
        elif s[j] == ")":
            d -= 1
            if d == 0:
                return j
    raise ValueError("unbalanced")


def split_top(s):
    """split a flat sum at top-level + / - into signed terms"""
    terms, d, cur, sign = [], 0, [], 1
    i = 0
    s = s.strip()
    while i < len(s):
        c = s[i]
        if c == "(":
            d += 1
        elif c == ")":
            d -= 1
        if d == 0 and c in "+-" and i > 0 and s[i - 1] == " " and i + 1 < len(s) and s[i + 1] == " ":
            terms.append((sign, "".join(cur).strip()))
            cur, sign = [], (1 if c == "+" else -1)
            i += 1
            continue
        cur.append(c)
        i += 1
    terms.append((sign, "".join(cur).strip()))
    return [(sg, t) for sg, t in terms if t]


def to_poly(expr_lean):
    """Return (PolyElement or None, sympy rational expr or None)."""
    py = lean_to_py(expr_lean)
    if "/" in py:
        ex = sp.sympify(py, locals=SD)
        num, den = sp.fraction(sp.together(ex))
        return None, (sp.Poly(sp.expand(num), *SYMS), sp.Poly(sp.expand(den), *SYMS))
    tot = P(0)
    for sg, t in split_top(py):
        v = eval(t, {"__builtins__": {}}, GD)
        tot += sg * v
    return tot, None


def poly_info(p):
    if p == 0:
        return dict(monomials=0, total_degree=0, atom_degree=0, max_W=0, max_R=0, max_coeff=0)
    ex = list(p.keys())
    idx = [VARS.index(v) for v in ATOMS]
    return dict(
        monomials=len(ex),
        total_degree=max(sum(m) for m in ex),
        atom_degree=max(sum(m[i] for i in idx) for m in ex),
        max_W=max(m[VARS.index("W")] for m in ex),
        max_R=max(m[VARS.index("R")] for m in ex),
        max_coeff=int(max(abs(c) for c in p.values())),
    )


def sympoly_info(q):
    if q.is_zero:
        return dict(monomials=0, total_degree=0)
    return dict(monomials=len(q.terms()), total_degree=q.total_degree())


RE_LC = re.compile(r"linear_combination\s*")


def certificates(path):
    src = open(path, encoding="utf-8").read()
    res = []
    for mt in RE_LC.finditer(src):
        i = mt.end()
        line_end = src.find("\n", i)
        stmt = src[i:line_end]
        norm = None
        mo = re.match(r"\(norm := ", stmt)
        if mo:
            j = match_paren(stmt, 0)
            norm = stmt[: j + 1]
            stmt = stmt[j + 1 :].lstrip()
        # expected: (C1) * hrel + (C2) * hW
        if not stmt.startswith("("):
            res.append(dict(kind="other", text=stmt[:120]))
            continue
        j = match_paren(stmt, 0)
        c1 = stmt[1:j]
        rest = stmt[j + 1 :]
        mo = re.match(r"\s*\*\s*hrel\s*\+\s*", rest)
        if not mo:
            res.append(dict(kind="other", text=stmt[:120]))
            continue
        rest = rest[mo.end() :]
        k = match_paren(rest, 0)
        c2 = rest[1:k]
        tail = rest[k + 1 :].strip()
        if tail != "* hW":
            res.append(dict(kind="other", text=stmt[:120]))
            continue
        # name of enclosing theorem
        th = re.findall(r"^theorem\s+(\S+)", src[: mt.start()], re.M)
        res.append(dict(kind="groebner", theorem=th[-1] if th else None, norm=norm, c1=c1, c2=c2,
                        chars=len(c1) + len(c2), line=src[: mt.start()].count("\n") + 1))
    return res


def main():
    t0 = time.time()
    files = sorted(glob.glob(E + "/Def_NoHair_KerrNewmanEinstein_*.lean")) + [E + "/Sol_NoHair_kerrNewman_einstein.lean"]
    allc, others = [], []
    for f in files:
        blk = os.path.basename(f).replace("Def_NoHair_KerrNewmanEinstein_", "").replace(".lean", "")
        for c in certificates(f):
            c["block"] = blk
            if c["kind"] != "groebner":
                others.append(dict(block=blk, text=c["text"]))
                continue
            for key in ("c1", "c2"):
                p, rat = to_poly(c[key])
                if p is not None:
                    c[key + "_info"] = poly_info(p)
                    c[key + "_rational"] = False
                else:
                    num, den = rat
                    c[key + "_info"] = dict(numerator=sympoly_info(num), denominator=sympoly_info(den))
                    c[key + "_rational"] = True
            allc.append(c)
    # summary
    poly = [c for c in allc if not (c["c1_rational"] or c["c2_rational"])]
    rat = [c for c in allc if (c["c1_rational"] or c["c2_rational"])]
    nontriv = [c for c in poly if c["c1_info"]["monomials"] + c["c2_info"]["monomials"] > 0]
    mons = [c["c1_info"]["monomials"] + c["c2_info"]["monomials"] for c in poly]
    chars = [c["chars"] for c in allc]
    big = max(poly, key=lambda c: c["c1_info"]["monomials"] + c["c2_info"]["monomials"])
    bigc = max(allc, key=lambda c: c["chars"])
    per_block = {}
    for c in allc:
        b = per_block.setdefault(c["block"], dict(certs=0, zero=0, rational=0, chars=0, monomials=0, max_monomials=0, max_total_degree=0))
        b["certs"] += 1
        b["chars"] += c["chars"]
        if c["c1_rational"] or c["c2_rational"]:
            b["rational"] += 1
            continue
        mm = c["c1_info"]["monomials"] + c["c2_info"]["monomials"]
        if mm == 0:
            b["zero"] += 1
        b["monomials"] += mm
        b["max_monomials"] = max(b["max_monomials"], mm)
        b["max_total_degree"] = max(b["max_total_degree"], c["c1_info"]["total_degree"], c["c2_info"]["total_degree"])
    summary = dict(
        n_certificates=len(allc),
        n_polynomial=len(poly),
        n_rational_cofactor=len(rat),
        n_zero_cofactors=len(poly) - len(nontriv),
        n_nonzero_polynomial=len(nontriv),
        chars_total=sum(chars), chars_mean=statistics.mean(chars), chars_median=statistics.median(chars), chars_max=max(chars),
        chars_max_where=f'{bigc["block"]}:{bigc["theorem"]}',
        monomials_total=sum(mons),
        monomials_mean_nonzero=statistics.mean([m for m in mons if m]),
        monomials_median_nonzero=statistics.median([m for m in mons if m]),
        monomials_max=max(mons),
        monomials_max_where=f'{big["block"]}:{big["theorem"]}',
        monomials_max_detail=dict(hrel=big["c1_info"], hW=big["c2_info"], chars=big["chars"]),
        max_total_degree=max(max(c["c1_info"]["total_degree"], c["c2_info"]["total_degree"]) for c in poly),
        max_atom_degree=max(max(c["c1_info"]["atom_degree"], c["c2_info"]["atom_degree"]) for c in poly),
        max_W_exponent=max(max(c["c1_info"]["max_W"], c["c2_info"]["max_W"]) for c in poly),
        max_abs_coefficient=max(max(c["c1_info"]["max_coeff"], c["c2_info"]["max_coeff"]) for c in poly),
        other_linear_combination=others,
        per_block=per_block,
        elapsed_s=round(time.time() - t0, 1),
    )
    # closed forms from Base
    base = open(E + "/Def_NoHair_KerrNewmanEinstein_Base.lean", encoding="utf-8").read()
    closed = {}
    for mo in re.finditer(r"^noncomputable def (\w+) \(([^)]*)\) : ℝ :=\n((?:  .*\n)+)", base, re.M):
        name, body = mo.group(1), mo.group(3)
        body = " ".join(l.strip() for l in body.splitlines())
        try:
            p, rat = to_poly(body)
        except Exception as ex:  # not a polynomial (e.g. uses other defs)
            closed[name] = dict(error=str(ex)[:80], chars=len(body))
            continue
        if p is not None:
            closed[name] = dict(poly_info(p), chars=len(body))
        else:
            closed[name] = dict(rational=True, chars=len(body))
    # vector-valued atom partials dRt, dKt, dWt, dfA, dHA
    for mo in re.finditer(r"^noncomputable def (dRt|dKt|dWt|dfA|dHA) \(([^)]*)\) : [^\n]*:=\n((?:  .*\n)+)", base, re.M):
        name, body = mo.group(1), mo.group(3)
        body = " ".join(l.strip() for l in body.splitlines())
        entries = [x for x in re.split(r"!\[|\]|,", body) if x.strip() and x.strip() != "0"]
        infos = []
        for x in entries:
            p, _ = to_poly(x.strip())
            infos.append(poly_info(p))
        closed[name] = dict(entries_nonzero=len(entries), monomials_total=sum(i["monomials"] for i in infos),
                            monomials_max=max(i["monomials"] for i in infos), total_degree=max(i["total_degree"] for i in infos))
    groups = {}
    for pref in ("G", "DD", "Ric", "Fc", "Fu", "FFA"):
        sel = {k: v for k, v in closed.items() if re.fullmatch(pref + (r"\d+" if pref != "FFA" else ""), k) and "monomials" in v}
        if sel:
            groups[pref] = dict(count=len(sel), monomials_total=sum(v["monomials"] for v in sel.values()),
                                monomials_max=max(v["monomials"] for v in sel.values()),
                                monomials_max_name=max(sel, key=lambda k: sel[k]["monomials"]),
                                max_total_degree=max(v["total_degree"] for v in sel.values()),
                                max_W=max(v["max_W"] for v in sel.values()), chars_total=sum(v["chars"] for v in sel.values()))
    scal = {k: v for k, v in closed.items() if "monomials" in v}
    biggest = max(scal, key=lambda k: scal[k]["monomials"])
    out = dict(summary=summary, closed_forms=closed, closed_form_groups=groups,
               largest_closed_form=dict(name=biggest, **scal[biggest]),
               certificates=[{k: v for k, v in c.items() if k not in ("c1", "c2")} for c in allc])
    json.dump(out, open(OUT, "w"), indent=1, default=str)
    print(json.dumps(summary, indent=1, default=str))
    print(json.dumps(groups, indent=1))
    print("largest closed form", biggest, scal[biggest])
    print("errors", {k: v for k, v in closed.items() if "error" in v})


if __name__ == "__main__":
    main()
