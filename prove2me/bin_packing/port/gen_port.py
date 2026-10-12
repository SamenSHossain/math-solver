import json, re, sys, os
UP='/home/user/openai/math/lean'
DEFS='/root/prove2me_workspace/Definitions'
P='OAI.Computability.BinPacking.'
HB_FROM=6
HERE=os.path.dirname(os.path.abspath(__file__))
order=[m for m in json.load(open(os.path.join(HERE,'order.json'))) if m!=P+'Model']
def short(m): return m[len(P):]
def path(m): return UP+'/'+m.replace('.','/')+'.lean'
def body(m, edits):
    src=open(path(m)).read()
    b='\n'.join(l for l in src.splitlines() if not l.startswith('import '))
    for old,new in edits:
        assert old in b,(m,old)
        b=b.replace(old,new)
    return f'-- ===== Adapted from lean/OAI/Computability/BinPacking/{short(m).replace(".","/")}.lean =====\n'+b.strip()+'\n'
SHIM='''-- Compatibility shims: core lemmas present in the newer Lean version used upstream but not in
-- Lean 4.33.1, restated from `if_pos`, `if_neg`, `dif_pos` and `dif_neg`.
namespace OAI

theorem ite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

theorem ite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

theorem dite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : c) : dite c t e = t h := dif_pos h

theorem dite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : ¬c) : dite c t e = e h := dif_neg h

end OAI
'''
def header(k,N,mods_in,notes):
    files=', '.join(short(m).replace('.','/')+'.lean' for m in mods_in)
    return f'''/-
Structural additive gap for bin packing (port of OpenAI's formalization), part {k} of {N}.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: {files}
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper{"; compatibility shims restating four core lemmas absent from Lean 4.33.1 are added" if k==1 else ""}{notes}.
-/
'''
if __name__=='__main__':
    cmd=sys.argv[1]
    extra=json.load(open(os.path.join(HERE,'patches.json'))) if os.path.exists(os.path.join(HERE,'patches.json')) else {}
    if cmd=='all':
        out='import Mathlib\nimport Definitions.Def_BinPackingGap\n\nset_option autoImplicit false\n\n'+SHIM+'\n'
        lines=[out.count('\n')]
        for m in order:
            out+=body(m, extra.get(short(m),{}).get('edits',[]))+'\n'
        open(sys.argv[2],'w').write(out); print('wrote', out.count('\n'),'lines')
        # line map
        json.dump(lineinfo(order,extra) if False else None, open(os.path.join(HERE,'dummy.json'),'w'))
    elif cmd=='write':
        groups=json.load(open(sys.argv[2])); N=len(groups)
        for k,g in enumerate(groups,1):
            pn=[f"in {short(m).replace('.','/')}.lean, {extra[short(m)]['note']}" for m in g if short(m) in extra]
            notes=('; compatibility edits for the platform Lean/Mathlib versions: '+'; '.join(pn)) if pn else ''
            prev='Definitions.Def_BinPackingGap' if k==1 else f'Definitions.Def_OAI_BinPackingGap_Part{str(k-1).zfill(2)}'
            hb = k >= HB_FROM
            if hb: notes += '; `set_option maxHeartbeats 1000000` is set for this part (the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally)'
            txt=header(k,N,g,notes)+f'import Mathlib\nimport {prev}\n\nset_option autoImplicit false\n'+('set_option maxHeartbeats 1000000\n' if hb else '')+'\n'
            if k==1: txt+=SHIM+'\n'
            txt+='\n'.join(body(m, extra.get(short(m),{}).get('edits',[])) for m in g)
            open(f'{DEFS}/Def_OAI_BinPackingGap_Part{str(k).zfill(2)}.lean','w').write(txt)
        print('wrote',N,'parts')
