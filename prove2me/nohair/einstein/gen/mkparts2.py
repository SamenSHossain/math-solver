import re, json
N='/tmp/claude-0/-home-user-math-solver/ee9f98fb-9768-5748-b1b3-ebbf1e9b4bc0/scratchpad/nh_ein'
W='/root/prove2me_workspace/Definitions'
rd=lambda f: open(f'{N}/{f}').read()
lem=rd('g4_lemmas.lean')
blocks=[b if b.startswith('theorem') else 'theorem '+b for b in lem.split('\ntheorem ')]
def fam(pat): return [b.rstrip()+'\n' for b in blocks if re.match(pat,b)]
disp=rd('glue4_disp.lean')
dblocks=[b if b.startswith('theorem') else 'theorem '+b for b in disp.split('\ntheorem ')]
def dfam(name): return [b.rstrip()+'\n' for b in dblocks if re.match(r'theorem '+name+r'\s',b)]
final=rd('glue4_final.lean').split('end NoHair.KNE')[0] + '''
/-- The Einstein equation for the Kerr–Newman metric in Kerr–Schild coordinates (wherever `r > 0`). -/
theorem kerrNewman_einstein_holds (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν := by
  intro μ ν
  rw [einstein_eq m a e y hy, maxwell_eq m a e y hy]
'''
infra=rd('infra_copied.lean').replace('private lemma','theorem').replace('private noncomputable def','noncomputable def').replace('private theorem','theorem')
mulinv=rd('mulinv.lean').replace('private lemma','theorem')
dG=fam(r'theorem dG')
ric=fam(r'theorem ricS_')
pick=lambda names: [b for b in ric if any(b.startswith(f'theorem ricS_{n} ') for n in names)]
dgsel=lambda names: [b for b in dG if any(b.startswith(f'theorem dG{n} ') for n in names)]
d_all=[re.match(r'theorem dG(\d+)',b).group(1) for b in dG]
d1=[n for n in d_all if n.startswith('00')] + [n for n in d_all if n.startswith('1')][:4]
d2=[n for n in d_all if n.startswith('1')][4:]
d3=[n for n in d_all if n.startswith('2')]
d4=[n for n in d_all if n.startswith('3')]
NS='namespace NoHair.KNE\n\n'
END='\nend NoHair.KNE\n'
parts = [
 ('Base', [None], 'Atoms r, k1, k2, k3, W = 1/(r^2 + a^2 k3^2) of the Kerr–Schild geometry; a small calculus of coordinate partials (`HasCP`); the closed-form polynomial expressions (Christoffel symbols, their divergences, Ricci tensor, field strength) used in later parts.',
   infra + '\n' + mulinv + rd('core_new.lean') + rd('glue4_W.lean') + '\n' + rd('g4_defs.lean') + rd('glue4_defs.lean') + END),
 ('Atoms', ['Base'], 'Coordinate partials of the atoms, of the Kerr–Schild profile and of the potential factor; the metric, its inverse and its Christoffel symbols as formulas in the atoms.',
   NS + rd('g4_atoms.lean') + rd('glue4_metric.lean') + END),
 ('Christoffel', ['Atoms'], 'The Christoffel symbols of the Kerr–Newman metric equal the closed forms `Gam` on `r > 0`; symmetry facts.',
   NS + '\n'.join(fam(r'theorem chrS_Gam_')) + '\n' + '\n'.join(dfam('chrS_Gam') + dfam('chr_closed') + dfam('Gam_symm') + dfam('dDivT_symm') + dfam('RicA_symm') + dfam('RicS_symm')) + END),
] + [
 (f'Div{i+1}', ['Atoms'], f'Differentiability and coordinate divergence of the closed-form Christoffel symbols, group {i+1} of 4.', NS + '\n'.join(dgsel(g)) + END)
 for i, g in enumerate([d1, d2, d3, d4])
] + [
 (f'Ricci{i+1}', ['Base'], f'Closed-form Ricci tensor components {", ".join("("+n[0]+","+n[1]+")" for n in g)}: pure polynomial identities modulo k1^2+k2^2+k3^2 = 1 and W (r^2 + a^2 k3^2) = 1.', NS + '\n'.join(pick(g)) + END)
 for i, g in enumerate([['00','01','02'], ['03','11'], ['12','13'], ['22','23','33']])
] + [
 ('Maxwell', ['Base'], 'The Maxwell side in closed form: field strength, raised field strength, the invariant F_{ab}F^{ab}, and the source tensor (pure polynomial identities).',
   NS + '\n'.join(fam(r'theorem fS_') + fam(r'theorem fU_') + fam(r'theorem fF') + fam(r'theorem tS_')) + '\n' + '\n'.join(dfam('fS') + dfam('fU') + dfam('tS')) + END),
 ('Assembly', ['Christoffel', 'Div1', 'Div2', 'Div3', 'Div4', 'Ricci1', 'Ricci2', 'Ricci3', 'Ricci4', 'Maxwell'],
   'Assembly: the trace of the Christoffel symbols vanishes, the Ricci tensor and scalar curvature at a point with r > 0, and the Einstein equation G_{μν} = 2 (F_{μα} F_ν^α - ¼ g_{μν} F²).',
   NS + '\n'.join(dfam('cp_div') + dfam('diff_tr')) + '\n' + '\n'.join(fam(r'theorem trGam_') + fam(r'theorem scal_zero')) + '\n' + '\n'.join(dfam('trGam') + dfam('ricS')) + final + END),
]
NP=len(parts)
meta=[]
for i,(key,deps,desc,body) in enumerate(parts,1):
    name=f'NoHair_KerrNewmanEinstein_{key}'
    imps=''.join(f'import Definitions.Def_NoHair_KerrNewmanEinstein_{d}\n' for d in deps if d) or 'import Definitions.Def_NoHair_kerrNewman\n'
    src=f'''/-
Kerr–Newman satisfies the Einstein equation (Kerr–Schild coordinates): {key} ({i} of {NP}).
{desc}
The development is split into parts only so that each piece compiles within the platform limits.
-/
import Mathlib
{imps}
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

open scoped BigOperators
open NoHair

''' + body
    open(f'{W}/Def_{name}.lean','w').write(src)
    meta.append({'key':key,'name':name,'deps':deps,'desc':desc,'i':i})
    print(i, key, 'deps', deps, len(src.splitlines()), 'thms', src.count('\ntheorem '))
json.dump(meta, open(f'{N}/parts_meta.json','w'), indent=1)
