"""Generator: closed forms + cofactors for the Kerr-Newman Einstein proof (atom variables).
Lean variable names: R K1 K2 K3 a m e.  Relation hrel : K1^2 + K2^2 + K3^2 = 1."""
import sympy as sp, pickle, sys
from ks_atoms import r, k1, k2, k3, a, m, e, S, Q, REL, D, Dr, dk1, dk2, dk3, red

NAMES = {r: 'R', k1: 'K1', k2: 'K2', k3: 'K3', a: 'a', m: 'm', e: 'e'}
VARS = [r, k1, k2, k3, a, m, e]
SSTR = '(R ^ 2 + a ^ 2 * K3 ^ 2)'
QSTR = '(R ^ 2 + a ^ 2)'

def poly_str(p):
    """Print an expanded polynomial in VARS with integer/rational coefficients."""
    p = sp.Poly(sp.expand(p), *VARS)
    if p.is_zero:
        return '0'
    out = []
    for mon, c in p.terms():
        c = sp.Rational(c)
        vs = []
        for v, ex in zip(VARS, mon):
            if ex == 1: vs.append(NAMES[v])
            elif ex > 1: vs.append(f'{NAMES[v]} ^ ({ex} : ℕ)')
        neg = c < 0
        ca = -c if neg else c
        if ca.q != 1:
            cstr = f'({ca.p} / {ca.q})'
        else:
            cstr = str(ca.p)
        if vs:
            body = '*'.join(vs) if ca == 1 else cstr + ' * ' + ' * '.join(vs)
            if ca == 1: body = ' * '.join(vs)
        else:
            body = cstr
        out.append(('- ' if neg else '+ ') + body)
    s = ' '.join(out)
    if s.startswith('+ '): s = s[2:]
    elif s.startswith('- '): s = '-' + s[2:]
    return s

def den_str(dn):
    """Factored denominator into canonical Lean string; dn is a sympy expr (product of powers)."""
    dn = sp.factor(dn)
    c, factors = sp.factor_list(dn)
    parts = []
    if c != 1:
        assert c > 0 and c.q == 1, dn
        parts.append(str(c))
    for f, ex in factors:
        f = sp.expand(f)
        if f == r: s = 'R'
        elif sp.expand(f - S) == 0: s = SSTR
        elif sp.expand(f - Q) == 0: s = QSTR
        elif f == a: s = 'a'
        elif f == k3: s = 'K3'
        else: raise ValueError(f'unexpected denominator factor {f}')
        parts.append(s if ex == 1 else f'{s} ^ ({ex} : ℕ)')
    return ' * '.join(parts) if parts else '1'

def frac_str(expr):
    expr = sp.cancel(sp.together(expr))
    if expr == 0: return '0'
    num, dn = sp.fraction(expr)
    # move sign/constant of the factored denominator into numerator
    c, _ = sp.factor_list(dn)
    if c < 0:
        num, dn = -num, -dn
    ds = den_str(dn)
    ns = poly_str(num)
    return f'({ns})' if ds == '1' else f'({ns}) / ({ds})'

def cofactor(lhs, rhs):
    """c with lhs - rhs = c * REL; returns Lean string 'c'."""
    d = sp.cancel(sp.together(lhs - rhs))
    if d == 0: return None
    num, dn = sp.fraction(d)
    q, rem = sp.div(sp.expand(num), sp.expand(REL), k1)
    assert sp.expand(rem) == 0, 'not in ideal'
    c, _ = sp.factor_list(dn)
    if c < 0: q, dn = -q, -dn
    ds = den_str(dn)
    qs = poly_str(q)
    return f'({qs})' if ds == '1' else f'({qs}) / ({ds})'

if __name__ == '__main__':
    pass

# ---------------------------------------------------------------- tables
import itertools
ATOM_ARGS = 'a m e R K1 K2 K3'
def tab1(name, args, vals, doc):
    s = f'/-- {doc} -/\nnoncomputable def {name} ({args} : ℝ) : Fin 4 → ℝ :=\n  ![' + ',\n    '.join(frac_str(v) for v in vals) + ']\n'
    return s
def tab2(name, args, vals, doc):
    rows = ['![' + ', '.join(frac_str(v) for v in row) + ']' for row in vals]
    return f'/-- {doc} -/\nnoncomputable def {name} ({args} : ℝ) : Fin 4 → Fin 4 → ℝ :=\n  ![' + ',\n    '.join(rows) + ']\n'
def tab3(name, args, vals, doc):
    blocks = []
    for M in vals:
        rows = ['![' + ', '.join(frac_str(v) for v in row) + ']' for row in M]
        blocks.append('![' + ',\n      '.join(rows) + ']')
    return f'/-- {doc} -/\nnoncomputable def {name} ({args} : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=\n  ![' + ',\n    '.join(blocks) + ']\n'

def closed_forms():
    from ks_atoms import k1 as K1_, k2 as K2_, k3 as K3_
    d = pickle.load(open('ks_atoms.pkl', 'rb'))
    dR = [sp.cancel(sp.together(Dr[j])) for j in range(4)]
    dK = [[0]*4, [sp.cancel(sp.together(dk1(j))) for j in range(4)], [sp.cancel(sp.together(dk2(j))) for j in range(4)], [sp.cancel(sp.together(dk3(j))) for j in range(4)]]
    f = (2*m*r - e**2) / S
    df = [red(D(j, f)) for j in range(4)]
    H = e*r/S
    dH = [red(D(j, H)) for j in range(4)]
    return d, dR, dK, f, df, H, dH
