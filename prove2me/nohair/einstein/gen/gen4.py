"""Generator v4: atoms R K1 K2 K3 W (W = 1/(R^2 + a^2 K3^2)); all closed forms are polynomials.
Relations: hrel : K1^2 + K2^2 + K3^2 = 1, hW : W * (R^2 + a^2 * K3^2) = 1."""
import sympy as sp, pickle, sys, time
from ks_atoms import r, k1, k2, k3, a, m, e, S, Q, REL, D, Dr, dk1, dk2, dk3, red

W = sp.Symbol('W')
WREL = sp.expand(W*(r**2 + a**2*k3**2) - 1)
RELX = sp.expand(REL)
GENS = [W, k1, r, k2, k3, a, m, e]
VARS = [r, k1, k2, k3, W, a, m, e]
ATOMS = [r, k1, k2, k3, W]
NAME = {r: 'R', k1: 'K1', k2: 'K2', k3: 'K3', W: 'W', a: 'a', m: 'm', e: 'e'}
HCP = {r: 'hR', k1: 'hK1', k2: 'hK2', k3: 'hK3', W: 'hWc'}
ARGS = 'a m e R K1 K2 K3 W'
FARGS = 'a e R K1 K2 K3 W'
ATZ = '(ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)'
ATW = '(ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w)'
HYPS = '(hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1)'

def towpoly(expr):
    expr = sp.cancel(sp.together(expr))
    num, den = sp.fraction(expr)
    c, fl = sp.factor_list(den)
    k = 0
    for f, ex in fl:
        if sp.expand(f - S) == 0: k = ex
        else: raise ValueError(f'bad denominator {f}')
    return sp.expand(num * W**k / c)

# ---------------------------------------------------------------- printing
def mono_str(c, mon):
    vs = []
    for v, ex in zip(VARS, mon):
        if ex == 1: vs.append(NAME[v])
        elif ex > 1: vs.append(f'{NAME[v]} ^ ({ex} : ℕ)')
    c = sp.Rational(c)
    neg = c < 0; ca = -c if neg else c
    cs = str(ca.p) if ca.q == 1 else f'({ca.p} / {ca.q})'
    body = ' * '.join(([cs] if (ca != 1 or not vs) else []) + vs)
    return neg, body
def poly_str(p):
    P = sp.Poly(sp.expand(p), *VARS)
    if P.is_zero: return '0'
    out = []
    for mon, c in P.terms():
        neg, body = mono_str(c, mon)
        out.append(('- ' if neg else '+ ') + body)
    s = ' '.join(out)
    return s[2:] if s.startswith('+ ') else '-' + s[2:]

def rat_str(expr):
    """rational expression -> Lean string N / D with D factored canonical (for glue cofactors)."""
    expr = sp.cancel(sp.together(expr))
    if expr == 0: return '0'
    num, den = sp.fraction(expr)
    c, fl = sp.factor_list(den)
    if c < 0: num, den, c = -num, -den, -c
    parts = [] if c == 1 else [str(c)]
    for f, ex in fl:
        f = sp.expand(f)
        if f == r: s = 'R'
        elif sp.expand(f - S) == 0: s = '(R ^ 2 + a ^ 2 * K3 ^ 2)'
        elif sp.expand(f - Q) == 0: s = '(R ^ 2 + a ^ 2)'
        else: raise ValueError(f'den factor {f}')
        parts.append(s if ex == 1 else f'{s} ^ ({ex} : ℕ)')
    ds = ' * '.join(parts)
    return f'({poly_str(num)})' + (f' / ({ds})' if ds else '')

def cofactors(diff):
    """diff (rational) = c1 * REL + c2 * WREL ; returns Lean strings."""
    diff = sp.cancel(sp.together(diff))
    if diff == 0: return '0', '0'
    num, den = sp.fraction(diff)
    (q1, q2), rem = sp.reduced(sp.expand(num), [RELX, WREL], *GENS, order='lex')
    assert sp.expand(rem) == 0, 'not in ideal'
    return rat_str(q1 / den), rat_str(q2 / den)

def lc(lhs, rhs, norm=None):
    c1, c2 = cofactors(lhs - rhs)
    n = '' if norm is None else f'(norm := {norm}) '
    return f'linear_combination {n}({c1}) * hrel + ({c2}) * hW'

# ---------------------------------------------------------------- expression trees (for HasCP terms)
class N:
    def __init__(self, op, *args): self.op, self.args = op, args
    def has_atom(self):
        if self.op == 'atom': return True
        if self.op == 'const': return False
        return any(x.has_atom() for x in self.args if isinstance(x, N))
    def s(self):
        o, A = self.op, self.args
        if o == 'atom': return NAME[A[0]]
        if o == 'const': return A[0]
        if o == 'pow': return f'({A[0].s()} ^ ({A[1]} : ℕ))'
        return f'({A[0].s()} {dict(add="+", mul="*")[o]} {A[1].s()})'
    def hcp(self):
        o, A = self.op, self.args
        if not self.has_atom(): return f'(HasCP.cst {self.s()} z)'
        if o == 'atom': return HCP[A[0]]
        if o == 'pow': return f'(HasCP.pow {A[0].hcp()} {A[1]})'
        return f'(HasCP.{o} {A[0].hcp()} {A[1].hcp()})'

def cst_node(c):
    c = sp.Rational(c)
    if c.q != 1: return N('const', f'({c.p} / {c.q} : ℝ)')
    return N('const', f'({c.p} : ℝ)')
def poly_node(p):
    P = sp.Poly(sp.expand(p), *VARS)
    if P.is_zero: return cst_node(0)
    terms = []
    for mon, c in P.terms():
        t = None
        c = sp.Rational(c)
        if c != 1 or all(ex == 0 for ex in mon): t = cst_node(c)
        for v, ex in zip(VARS, mon):
            if ex == 0: continue
            vn = N('atom', v) if v in ATOMS else N('const', NAME[v])
            if ex > 1: vn = N('pow', vn, ex)
            t = vn if t is None else N('mul', t, vn)
        terms.append(t)
    # balanced sum
    while len(terms) > 1:
        nt = []
        for i in range(0, len(terms), 2):
            nt.append(terms[i] if i + 1 == len(terms) else N('add', terms[i], terms[i+1]))
        terms = nt
    return terms[0]

# ---------------------------------------------------------------- data
d = pickle.load(open('ks_atoms.pkl', 'rb'))
eta = [[-1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]
Kv = [sp.Integer(1), k1, k2, k3]
Ks = [sp.Integer(-1), k1, k2, k3]
dR = [towpoly(red(Dr[j])) for j in range(4)]
dK = [[sp.Integer(0)]*4] + [[towpoly(red(fn(j))) for j in range(4)] for fn in (dk1, dk2, dk3)]
dWp = [sp.expand(-W**2*(2*r*dR[j] + 2*a**2*k3*dK[3][j])) for j in range(4)]
DAT = {r: dR, k1: dK[1], k2: dK[2], k3: dK[3], W: dWp}
def Dp(c, p):
    if c == 0: return sp.Integer(0)
    return sp.expand(sum(sp.diff(p, at)*DAT[at][c] for at in ATOMS))
fP = sp.expand((2*m*r - e**2)*W)
dF = [towpoly(red(D(j, (2*m*r - e**2)/S))) for j in range(4)]
HP = sp.expand(e*r*W)
dH = [towpoly(red(D(j, e*r/S))) for j in range(4)]
def nterms_(p): return len(sp.Add.make_args(sp.expand(p)))
def best(p):
    p = sp.expand(p)
    if p == 0: return p
    cands = [p] + [sp.expand(sp.rem(p, RELX, v)) for v in (k2, k3)]
    return min(cands, key=nterms_)
G = [[[best(towpoly(d['Gam'][i][j][k])) for k in range(4)] for j in range(4)] for i in range(4)]
DD = [[[sp.Integer(0) if rho == 0 else best(towpoly(d['dGam'][rho][nu][sg][rho])) for sg in range(4)] for nu in range(4)] for rho in range(4)]
Ric = [[towpoly(d['Ric'][s][n]) for n in range(4)] for s in range(4)]
def ginv(i, l): return eta[i][l] - fP*Ks[i]*Ks[l]
def gmet(i, l): return eta[i][l] + fP*Kv[i]*Kv[l]
FA = [[towpoly(d['F'][mu][nu]) for nu in range(4)] for mu in range(4)]
Fup = [[towpoly(red(sum(ginv(al, mu)*ginv(be, nu)*FA[mu][nu] for mu in range(4) for nu in range(4)).subs(W, 1/S))) for be in range(4)] for al in range(4)]
FF = towpoly(red(sum(FA[al][be]*Fup[al][be] for al in range(4) for be in range(4)).subs(W, 1/S)))

def pdef(name, args, p, doc=None):
    return (f'/-- {doc} -/\n' if doc else '') + f'noncomputable def {name} ({args} : ℝ) : ℝ :=\n  {poly_str(p)}\n'
def ptab1(name, args, vals, doc):
    return f'/-- {doc} -/\nnoncomputable def {name} ({args} : ℝ) : Fin 4 → ℝ :=\n  ![' + ',\n    '.join(poly_str(v) for v in vals) + ']\n'
def ptab2(name, args, vals, doc):
    return f'/-- {doc} -/\nnoncomputable def {name} ({args} : ℝ) : Fin 4 → Fin 4 → ℝ :=\n  ![' + ',\n    '.join('![' + ', '.join(poly_str(v) for v in row) + ']' for row in vals) + ']\n'

if __name__ == '__main__':
    t0 = time.time()
    D_ = []
    D_.append(ptab1('dRt', 'a R K1 K2 K3 W', dR, 'Coordinate partials `∂_j r` in atom form.'))
    D_.append(ptab2('dKt', 'a R K1 K2 K3 W', dK, 'Coordinate partials `∂_j k_l` (`dKt l j`) in atom form.'))
    D_.append(ptab1('dWt', 'a R K1 K2 K3 W', dWp, 'Coordinate partials of `W = 1/(r² + a² k₃²)`.'))
    D_.append(ptab1('dfA', ARGS, dF, 'Coordinate partials of the profile `f = (2 m r - e²) W`.'))
    D_.append(ptab1('dHA', FARGS, dH, 'Coordinate partials of `H = e r W`.'))
    for i in range(4):
        for j in range(4):
            for k in range(j, 4):
                D_.append(f'noncomputable def G{i}{j}{k} ({ARGS} : ℝ) : ℝ :=\n  {poly_node(G[i][j][k]).s()}\n')
    gn = lambda i, j, k: f'G{i}{min(j,k)}{max(j,k)} {ARGS}'
    rows = ['![' + ', '.join('![' + ', '.join(gn(i, j, k) for k in range(4)) + ']' for j in range(4)) + ']' for i in range(4)]
    D_.append('/-- Closed-form Christoffel symbols `Γ^i_{jk}`. -/\nnoncomputable def Gam (' + ARGS + ' : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=\n  ![' + ',\n    '.join(rows) + ']\n')
    for rho in range(1, 4):
        for nu in range(4):
            for sg in range(nu, 4):
                D_.append(pdef(f'DD{rho}{nu}{sg}', ARGS, DD[rho][nu][sg]))
    dn = lambda rho, nu, sg: f'DD{rho}{min(nu,sg)}{max(nu,sg)} {ARGS}' if rho > 0 else '0'
    rows = ['![' + ', '.join('![' + ', '.join(dn(rho, nu, sg) for sg in range(4)) + ']' for nu in range(4)) + ']' for rho in range(4)]
    D_.append('/-- Closed-form `∂_ρ Γ^ρ_{νσ}` (no sum; `0` for `ρ = 0`). -/\nnoncomputable def dDivT (' + ARGS + ' : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=\n  ![' + ',\n    '.join(rows) + ']\n')
    for s in range(4):
        for n in range(s, 4):
            D_.append(pdef(f'Ric{s}{n}', ARGS, Ric[s][n]))
    rows = ['![' + ', '.join(f'Ric{min(s,n)}{max(s,n)} {ARGS}' for n in range(4)) + ']' for s in range(4)]
    D_.append('/-- Closed-form Ricci tensor. -/\nnoncomputable def RicA (' + ARGS + ' : ℝ) : Fin 4 → Fin 4 → ℝ :=\n  ![' + ',\n    '.join(rows) + ']\n')
    def fn_(mu, nu, pre, args):
        if mu == nu: return '0'
        return f'{pre}{mu}{nu} {args}' if mu < nu else f'(-{pre}{nu}{mu} {args})'
    for mu in range(4):
        for nu in range(mu+1, 4):
            D_.append(pdef(f'Fc{mu}{nu}', FARGS, FA[mu][nu]))
            D_.append(pdef(f'Fu{mu}{nu}', ARGS, Fup[mu][nu]))
    rows = ['![' + ', '.join(fn_(mu, nu, 'Fc', FARGS) for nu in range(4)) + ']' for mu in range(4)]
    D_.append('/-- Closed-form field strength `F_{μν}`. -/\nnoncomputable def FA (' + FARGS + ' : ℝ) : Fin 4 → Fin 4 → ℝ :=\n  ![' + ',\n    '.join(rows) + ']\n')
    rows = ['![' + ', '.join(fn_(mu, nu, 'Fu', ARGS) for nu in range(4)) + ']' for mu in range(4)]
    D_.append('/-- Closed-form raised field strength `F^{μν}`. -/\nnoncomputable def FupA (' + ARGS + ' : ℝ) : Fin 4 → Fin 4 → ℝ :=\n  ![' + ',\n    '.join(rows) + ']\n')
    D_.append(pdef('FFA', ARGS, FF, 'Closed-form invariant `F_{αβ} F^{αβ}`.'))
    open('g4_defs.lean', 'w').write('\n'.join(D_))
    print('defs', time.time() - t0, file=sys.stderr)

    # ------------------------------------------------ atom glue lemmas (rational -> polynomial), field_simp
    L = []
    x = r*k1 - a*k2; y = a*k1 + r*k2; zz = r*k3
    def vB(k): return [1 if i == k else 0 for i in range(4)]
    def drf_expr(v): return r*(r**2*(x*v[1] + y*v[2]) + (r**2 + a**2)*zz*v[3]) / (r**4 + a**2*zz**2)
    FS_NORM = '(field_simp; ring)'
    PREP = '''  have hx1 := ks_x1 a z hz
  have hx2 := ks_x2 a z hz
  have hx3 := ks_x3 a z hz
  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  have hRne : ksRadius a z ≠ 0 := hz.ne'
  have hQ : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
'''
    SETS = '''  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
'''
    cases = [f'  · simp [coordBasis, dRt] <;> {lc(drf_expr(vB(k)), dR[k], FS_NORM)}' for k in range(4)]
    L.append(f'''theorem hasCP_R (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => ksRadius a w) z (dRt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)) := by
  refine ⟨ksRadius_differentiableAt a z hz, fun k =>
    (hasDerivAt_ksRadius_line a z (coordBasis k) hz).congr_deriv ?_⟩
{PREP}  simp only [hx1, hx2, hx3]
{SETS}  fin_cases k
''' + '\n'.join(cases) + '\n')
    def dkf_expr(l, v):
        dr = drf_expr(v)
        if l == 1: return ((dr*x + r*v[1] + a*v[2])*(r**2 + a**2) - (r*x + a*y)*(2*r*dr)) / (r**2 + a**2)**2
        if l == 2: return ((dr*y + r*v[2] - a*v[1])*(r**2 + a**2) - (r*y - a*x)*(2*r*dr)) / (r**2 + a**2)**2
        return (v[3]*r - zz*dr) / r**2
    for l in (1, 2, 3):
        cases = [f'  · simp [coordBasis, dKt] <;> {lc(dkf_expr(l, vB(k)), dK[l][k], FS_NORM)}' for k in range(4)]
        L.append(f'''theorem hasCP_K{l} (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => ksNull a w {l}) z (dKt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) {l}) := by
  refine HasCP.of_fderiv (ksNull_differentiableAt a z hz {l}) (fun k => ?_)
  rw [fderiv_k{l} a z hz]
{PREP}  simp only [dk{l}f, drf, hx1, hx2, hx3]
{SETS}  fin_cases k
''' + '\n'.join(cases) + '\n')
    # W: derivative of 1/(R^2 + a^2 K3^2) via HasCP.div of cst 1
    Rs, K3s = sp.symbols('Rs K3s')
    wbody = 1/(Rs**2 + a**2*K3s**2)
    cases = []
    for k in range(4):
        lhs = (sp.diff(wbody, Rs)*dR[k] + sp.diff(wbody, K3s)*dK[3][k]).subs({Rs: r, K3s: k3})
        cases.append(f'  · simp [dRt, dKt, dWt] <;> {lc(lhs, dWp[k], FS_NORM)}')
    L.append(f'''theorem hasCP_W (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => Wf a w) z (dWt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)) := by
  have hR := hasCP_R a z hz
  have hK3 := hasCP_K3 a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have h := HasCP.div (HasCP.cst 1 z) ((hR.pow 2).add ((HasCP.cst (a ^ 2) z).mul (hK3.pow 2))) hne
  refine h.congr_d (fun k => ?_)
{PREP}{SETS}  fin_cases k
''' + '\n'.join(cases) + '\n')
    # profile and H : bodies in R and z3
    Zs = sp.Symbol('Zs')
    def body_cases(body, closed, dname):
        cs = []
        for k in range(4):
            lhs = (sp.diff(body, Rs)*dR[k] + sp.diff(body, Zs)*(1 if k == 3 else 0)).subs({Rs: r, Zs: zz})
            cs.append(f'  · simp [coordBasis, dRt, {dname}] <;> {lc(lhs, closed[k], FS_NORM)}')
        return '\n'.join(cs)
    L.append(f'''theorem hasCP_profile (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => ksProfile m a e w) z (dfA a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)) := by
  have hR := hasCP_R a z hz
  have h3 := hasCP_coord z 3
  have hden : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := (ks_den_pos a z hz).ne'
  have h : HasCP (fun w => ksProfile m a e w) z _ :=
    ((hR.pow 2).mul (((HasCP.cst (2 * m) z).mul hR).sub (HasCP.cst (e ^ 2) z))).div
      ((hR.pow 4).add ((HasCP.cst (a ^ 2) z).mul (h3.pow 2))) hden
  refine h.congr_d (fun k => ?_)
{PREP}  simp only [hx3]
{SETS}  fin_cases k
''' + body_cases(Rs**2*(2*m*Rs - e**2)/(Rs**4 + a**2*Zs**2), dF, 'dfA') + '\n')
    L.append(f'''theorem hasCP_H (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => e * ksRadius a w ^ 3 / (ksRadius a w ^ 4 + a ^ 2 * w 3 ^ 2)) z
      (dHA a e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)) := by
  have hR := hasCP_R a z hz
  have h3 := hasCP_coord z 3
  have hden : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := (ks_den_pos a z hz).ne'
  have h : HasCP (fun w => e * ksRadius a w ^ 3 / (ksRadius a w ^ 4 + a ^ 2 * w 3 ^ 2)) z _ :=
    ((HasCP.cst e z).mul (hR.pow 3)).div ((hR.pow 4).add ((HasCP.cst (a ^ 2) z).mul (h3.pow 2))) hden
  refine h.congr_d (fun k => ?_)
{PREP}  simp only [hx3]
{SETS}  fin_cases k
''' + body_cases(e*Rs**3/(Rs**4 + a**2*Zs**2), dH, 'dHA') + '\n')
    open('g4_atoms.lean', 'w').write('\n'.join(L))
    print('atoms', time.time() - t0, file=sys.stderr)

    # ------------------------------------------------ polynomial algebra lemmas
    L = []
    UNF = 'Matrix.cons_val, Fin.sum_univ_four'
    def dgS(l, kk, j): return dF[j]*Kv[l]*Kv[kk] + fP*dK[l][j]*Kv[kk] + fP*Kv[l]*dK[kk][j]
    for i in range(4):
        for j in range(4):
            for kk in range(j, 4):
                lhs = sum(sp.Rational(1, 2)*ginv(i, l)*(dgS(l, kk, j) + dgS(l, j, kk) - dgS(j, kk, l)) for l in range(4))
                L.append(f'''theorem chrS_Gam_{i}{j}{kk} ({ARGS} : ℝ) {HYPS} :
    chrS {ARGS} {i} {j} {kk} = Gam {ARGS} {i} {j} {kk} := by
  simp only [chrS, ginvA, dgA, Kv, Ks, fA, dfA, dKt, etaT, Gam, G{i}{j}{kk}, {UNF}]
  {lc(lhs, G[i][j][kk])}
''')
    print('chr', time.time() - t0, file=sys.stderr)
    PRE_D = '''  have hR := hasCP_R a z hz
  have hK1 := hasCP_K1 a z hz
  have hK2 := hasCP_K2 a z hz
  have hK3 := hasCP_K3 a z hz
  have hWc := hasCP_W a z hz
'''
    SETZ = '''  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
'''
    for rho in range(4):
        for nu in range(4):
            for sg in range(nu, 4):
                if rho == 0 and nu != 0: continue
                node = poly_node(G[rho][nu][sg])
                term = node.hcp()
                if rho >= 1:
                    L.append(f'''theorem dG{rho}{nu}{sg} (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (fun w => G{rho}{nu}{sg} a m e {ATW}) z ∧
    coordPartial (fun w => G{rho}{nu}{sg} a m e {ATW}) {rho} z = DD{rho}{nu}{sg} a m e {ATZ} := by
{PRE_D}  have h : HasCP (fun w => G{rho}{nu}{sg} a m e {ATW}) z _ :=
    {term}
  refine ⟨h.diff, ?_⟩
  rw [h.eq]
  simp only [dRt, dKt, dWt, DD{rho}{nu}{sg}, Matrix.cons_val, Nat.cast_ofNat, Nat.reduceSub, pow_one]
{SETZ}  {lc(Dp(rho, G[rho][nu][sg]), DD[rho][nu][sg])}
''')
                else:
                    L.append(f'''theorem dG{rho}{nu}{sg} (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (fun w => G{rho}{nu}{sg} a m e {ATW}) z := by
{PRE_D}  exact ({term}).diff
''')
    print('dG', time.time() - t0, file=sys.stderr)
    for sg in range(4):
        names = sorted(set(f'G{rho}{min(rho,sg)}{max(rho,sg)}' for rho in range(4)))
        L.append(f'''theorem trGam_{sg} ({ARGS} : ℝ) {HYPS} :
    ∑ ρ, Gam {ARGS} ρ ρ {sg} = 0 := by
  simp only [Gam, {", ".join(names)}, {UNF}]
  {lc(sum(G[rho][rho][sg] for rho in range(4)), 0)}
''')
    allG = ', '.join(f'G{i}{j}{k}' for i in range(4) for j in range(4) for k in range(j, 4))
    allDD = ', '.join(f'DD{rr}{j}{k}' for rr in range(1, 4) for j in range(4) for k in range(j, 4))
    for s in range(4):
        for n in range(s, 4):
            lhs = sum(DD[rho][n][s] for rho in range(4)) - sum(G[rho][n][l]*G[l][rho][s] for rho in range(4) for l in range(4))
            L.append(f'''theorem ricS_{s}{n} ({ARGS} : ℝ) {HYPS} :
    RicS {ARGS} {s} {n} = RicA {ARGS} {s} {n} := by
  simp only [RicS, RicA, Gam, dDivT, Ric{min(s,n)}{max(s,n)}, {UNF}]
  simp only [{allG}, {allDD}]
  {lc(lhs, Ric[s][n])}
''')
    print('ric', time.time() - t0, file=sys.stderr)
    allRic = ', '.join(f'Ric{s}{n}' for s in range(4) for n in range(s, 4))
    L.append(f'''theorem scal_zero ({ARGS} : ℝ) {HYPS} :
    ∑ σ, ∑ ν, ginvA {ARGS} σ ν * RicA {ARGS} σ ν = 0 := by
  simp only [ginvA, RicA, Ks, fA, etaT, {allRic}, {UNF}]
  {lc(sum(ginv(s, n)*Ric[s][n] for s in range(4) for n in range(4)), 0)}
''')
    allFc = ', '.join(f'Fc{x_}{y_}' for x_ in range(4) for y_ in range(x_+1, 4))
    allFu = ', '.join(f'Fu{x_}{y_}' for x_ in range(4) for y_ in range(x_+1, 4))
    for mu in range(4):
        for nu in range(4):
            lhs = dH[mu]*Kv[nu] + HP*dK[nu][mu] - (dH[nu]*Kv[mu] + HP*dK[mu][nu])
            L.append(f'''theorem fS_{mu}{nu} ({FARGS} : ℝ) {HYPS} :
    FS {FARGS} {mu} {nu} = FA {FARGS} {mu} {nu} := by
  simp only [FS, FA, HA, dHA, dKt, Kv{"" if mu == nu else f", Fc{min(mu,nu)}{max(mu,nu)}"}, Matrix.cons_val]
  {lc(lhs, FA[mu][nu])}
''')
    for al in range(4):
        for be in range(4):
            lhs = sum(ginv(al, mu)*ginv(be, nu)*FA[mu][nu] for mu in range(4) for nu in range(4))
            L.append(f'''theorem fU_{al}{be} ({ARGS} : ℝ) {HYPS} :
    ∑ μ, ∑ ν, ginvA {ARGS} {al} μ * ginvA {ARGS} {be} ν * FA {FARGS} μ ν = FupA {ARGS} {al} {be} := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, {allFc}{"" if al == be else f", Fu{min(al,be)}{max(al,be)}"}, {UNF}]
  {lc(lhs, Fup[al][be])}
''')
    L.append(f'''theorem fF ({ARGS} : ℝ) {HYPS} :
    ∑ α, ∑ β, FA {FARGS} α β * FupA {ARGS} α β = FFA {ARGS} := by
  simp only [FA, FupA, FFA, {allFc}, {allFu}, {UNF}]
  {lc(sum(FA[al][be]*Fup[al][be] for al in range(4) for be in range(4)), FF)}
''')
    for mu in range(4):
        for nu in range(4):
            lhs = 2*(sum(FA[mu][al]*ginv(al, be)*FA[nu][be] for al in range(4) for be in range(4)) - sp.Rational(1, 4)*gmet(mu, nu)*FF)
            L.append(f'''theorem tS_{mu}{nu} ({ARGS} : ℝ) {HYPS} :
    TS {ARGS} {mu} {nu} = RicA {ARGS} {mu} {nu} := by
  simp only [TS, gA, ginvA, FA, RicA, Kv, Ks, fA, FFA, etaT, {allFc}, Ric{min(mu,nu)}{max(mu,nu)}, {UNF}]
  {lc(lhs, Ric[mu][nu])}
''')
    open('g4_lemmas.lean', 'w').write('\n'.join(L))
    print('maxwell', time.time() - t0, file=sys.stderr)
