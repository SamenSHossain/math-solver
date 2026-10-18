"""Intermediate platform theorems (statements + proofs) for the Kerr–Newman Einstein equation."""
import json
N='/tmp/claude-0/-home-user-math-solver/ee9f98fb-9768-5748-b1b3-ebbf1e9b4bc0/scratchpad/nh_ein'
W='/root/prove2me_workspace'
A='a m e R K1 K2 K3 W'
H='(hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1)'
ATW='(ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w)'
ATY='(ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y)'
ATZ='(ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)'
PRE='import Mathlib\nimport Definitions.Def_NoHair_KerrNewmanEinstein_Base\n\nopen scoped BigOperators\nopen NoHair'
T={}
T['thm_christoffel']=dict(stmt=f'''theorem thm_christoffel (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i j k : Fin 4) :
    christoffel (kerrNewmanMetric m a e) z i j k = Gam a m e {ATZ} i j k''',
  imports=['Christoffel'], proof='  NoHair.KNE.chr_closed m a e z hz i j k',
  title='Kerr–Newman Christoffel symbols in closed form',
  nl='For all real $m,a,e$ and every point $z$ of coordinate space with Kerr–Schild radius $r(z)>0$, the Christoffel symbols $\\Gamma^i_{jk}$ of the Kerr–Newman metric (`christoffel (kerrNewmanMetric m a e) z i j k`) equal the explicit polynomial `Gam` in the atoms $r$, $k_1,k_2,k_3$ (components of the Kerr–Schild null covector) and $W=1/(r^2+a^2k_3^2)$, as defined in the block `NoHair_KerrNewmanEinstein_Base`.')
def divstmt(rho):
    parts=[]
    if rho==1:
        parts.append(f'(∀ σ, DifferentiableAt ℝ (fun w => Gam a m e {ATW} 0 0 σ) y)')
    parts.append(f'(∀ σ, DifferentiableAt ℝ (fun w => Gam a m e {ATW} {rho} {rho} σ) y)')
    parts.append(f'(∀ ν σ, coordPartial (fun w => Gam a m e {ATW} {rho} ν σ) {rho} y = dDivT a m e {ATY} {rho} ν σ)')
    return ' ∧\n    '.join(parts)
NAMES={1:'one',2:'two',3:'three'}
for rho in (1,2,3):
    imps={1:['Div1','Div2'],2:['Div3'],3:['Div4']}[rho]
    pr=[]
    lines=['  refine ⟨' + ('?_, ' if rho==1 else '') + '?_, ?_⟩']
    if rho==1:
        lines.append('  · intro σ\n    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]')
        for s in range(4): lines.append(f'    · exact NoHair.KNE.dG00{s} m a e y hy')
    lines.append('  · intro σ\n    fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]')
    for s in range(4): lines.append(f'    · exact (NoHair.KNE.dG{rho}{min(rho,s)}{max(rho,s)} m a e y hy).1')
    lines.append('  · intro ν σ\n    fin_cases ν <;> fin_cases σ <;> simp only [Gam, dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]')
    for n in range(4):
        for s in range(4): lines.append(f'    · exact (NoHair.KNE.dG{rho}{min(n,s)}{max(n,s)} m a e y hy).2')
    T[f'thm_div_{NAMES[rho]}']=dict(stmt=f'''theorem thm_div_{NAMES[rho]} (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    {divstmt(rho)}''', imports=imps, proof='by\n'+'\n'.join(lines),
      title=f'Kerr–Newman closed-form Christoffel symbols: divergence in direction {rho}',
      nl=(f'For all real $m,a,e$ and every point $y$ with $r(y)>0$, the closed-form Christoffel symbols `Gam` (block `NoHair_KerrNewmanEinstein_Base`) composed with the atoms $w\\mapsto(r(w),k_1(w),k_2(w),k_3(w),W(w))$ satisfy: '
          + ('the functions $\\Gamma^0_{0\\sigma}$ and ' if rho==1 else 'the functions ')
          + f'$\\Gamma^{{{rho}}}_{{{rho}\\sigma}}$ are differentiable at $y$, and the coordinate partial $\\partial_{rho}\\Gamma^{rho}_{{\\nu\\sigma}}(y)$ equals the closed form `dDivT` for all $\\nu,\\sigma$.'))
RGROUPS={'a':['00','01','02','03'],'b':['11','12'],'c':['13','22','23','33']}
RBLK={'a':['Ricci1','Ricci2'],'b':['Ricci3','Ricci4'],'c':['Ricci5','Ricci6']}
for g,comps in RGROUPS.items():
    st=' ∧\n    '.join(f'RicS {A} {c[0]} {c[1]} = RicA {A} {c[0]} {c[1]}' for c in comps)
    pf='  ⟨' + ', '.join(f'NoHair.KNE.ricS_{c} {A} hrel hW' for c in comps) + '⟩'
    T[f'thm_ricci_{g}']=dict(stmt=f'''theorem thm_ricci_{g} ({A} : ℝ) {H} :
    {st}''', imports=RBLK[g], proof=pf,
      title=f'Kerr–Newman Ricci tensor in closed form: components {", ".join("("+c[0]+","+c[1]+")" for c in comps)}',
      nl=f'Polynomial identities in the atoms: if $k_1^2+k_2^2+k_3^2=1$ and $W(r^2+a^2k_3^2)=1$, then the Ricci tensor `RicS` assembled from the closed-form Christoffel symbols and their divergences (block `NoHair_KerrNewmanEinstein_Base`) equals the closed form `RicA` for the components {", ".join("$("+c[0]+","+c[1]+")$" for c in comps)}.')
T['thm_maxwell']=dict(stmt=f'''theorem thm_maxwell ({A} : ℝ) {H} :
    (∀ μ ν, FS a e R K1 K2 K3 W μ ν = FA a e R K1 K2 K3 W μ ν) ∧
    (∀ α β, ∑ μ, ∑ ν, ginvA {A} α μ * ginvA {A} β ν * FA a e R K1 K2 K3 W μ ν = FupA {A} α β) ∧
    (∑ α, ∑ β, FA a e R K1 K2 K3 W α β * FupA {A} α β = FFA {A}) ∧
    (∀ μ ν, TS {A} μ ν = RicA {A} μ ν)''', imports=['MaxwellF','MaxwellT'],
  proof=f'  ⟨NoHair.KNE.fS a e R K1 K2 K3 W hrel hW, NoHair.KNE.fU {A} hrel hW, NoHair.KNE.fF {A} hrel hW, NoHair.KNE.tS {A} hrel hW⟩',
  title='Kerr–Newman Maxwell source in closed form',
  nl='Polynomial identities in the atoms: if $k_1^2+k_2^2+k_3^2=1$ and $W(r^2+a^2k_3^2)=1$, then (i) the field strength `FS` of $A=H k$ (with $H=erW$) equals the closed form `FA`, (ii) raising both indices with $g^{-1}=\\eta-f\\,k^\\sharp k^{\\sharp T}$ gives `FupA`, (iii) the invariant $F_{\\alpha\\beta}F^{\\alpha\\beta}$ equals `FFA`, and (iv) the Maxwell source tensor `TS` equals the closed-form Ricci tensor `RicA` (all in block `NoHair_KerrNewmanEinstein_Base`).')
meta={}
for name,t in T.items():
    fs=f'namespace NoHair.KNE\n\n{t["stmt"]} := by\n  sorry\n\nend NoHair.KNE'
    mirror=PRE+'\n\n'+fs+'\n'
    open(f'{W}/Theorems/Thm_NoHair_KNE_{name}.lean','w').write(mirror)
    imps=''.join(f'import Definitions.Def_NoHair_KerrNewmanEinstein_{b}\n' for b in t['imports'])
    stmt_sol=t['stmt'].replace(f'theorem {name}', 'theorem solution', 1)
    proof=t['proof']
    body = f' :=\n{proof}' if not proof.startswith('by') else f' := {proof}'
    sol=f'import Mathlib\nimport Definitions.Def_NoHair_KerrNewmanEinstein_Base\n{imps}\nset_option autoImplicit false\n\nopen scoped BigOperators\nopen NoHair NoHair.KNE\n\n{stmt_sol}{body}\n'
    open(f'{W}/Solutions/Sol_NoHair_KNE_{name}.lean','w').write(sol)
    meta[name]=dict(formal_statement=fs, preamble=PRE, title=t['title'], nl=t['nl'], imports=t['imports'])
json.dump(meta, open(f'{N}/thm_meta.json','w'), indent=1, ensure_ascii=False)
print(list(T))
