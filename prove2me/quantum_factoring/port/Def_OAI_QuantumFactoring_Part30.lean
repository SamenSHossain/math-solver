/-
Exact quantum factoring development (port of OpenAI's formalization), part 30 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: NetworkEmissionWords.lean, NetworkEmissionRewire.lean, AIGNetworkEmission.lean, AIGNetworkProcedure.lean, NativeAIGShift.lean, NativeAIGIf.lean, NativeAIGMul.lean, NativeAIGIfProcedure.lean, NativeAIGVectorBounds.lean, NativeAIGMulBounded.lean, NativeAIGMulProcedure.lean, NativeAIGMulWrapper.lean, NativeAIGNot.lean, NativeAIGCarry.lean, NativeAIGSub.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part29

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionWords.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma pairPack_spec {n m l : ℕ} (a b : Pack) (f : BooleanNetwork n m) (g : BooleanNetwork n l)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (pairPack a b).val.value=erase (f.pair g):=by
  rw [pairPack_value,ha,hb,erase_pair]
  rw [ha,hb];rfl
lemma compPack_spec {n m l : ℕ} (a b : Pack) (f : BooleanNetwork n m) (g : BooleanNetwork m l)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (compPack a b).val.value=erase (f.comp g):=by
  rw [compPack_value,ha,hb,erase_comp]
  rw [ha,hb];simp [erase]
def borPack (a b : Pack) : Pack:=bnotPack (bandPack (bnotPack a) (bnotPack b))
def bxorPack (a b : Pack) : Pack:=borPack (bandPack a (bnotPack b)) (bandPack (bnotPack a) b)
def muxPack (c a b : Pack) : Pack:=borPack (bandPack c a) (bandPack (bnotPack c) b)
lemma borPack_value {n : ℕ} (a b : Pack) (f g : BooleanNetwork n 1)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (borPack a b).val.value=erase (f.bor g):=
  bnotPack_value _ _ (bandPack_value _ _ _ _ (bnotPack_value _ _ ha) (bnotPack_value _ _ hb))
lemma bxorPack_value {n : ℕ} (a b : Pack) (f g : BooleanNetwork n 1)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (bxorPack a b).val.value=erase (f.bxor g):=
  borPack_value _ _ _ _ (bandPack_value _ _ _ _ ha (bnotPack_value _ _ hb))
    (bandPack_value _ _ _ _ (bnotPack_value _ _ ha) hb)
lemma muxPack_value {n : ℕ} (c a b : Pack) (f g h : BooleanNetwork n 1)
    (hc : c.val.value=erase f) (ha : a.val.value=erase g) (hb : b.val.value=erase h) :
    (muxPack c a b).val.value=erase (BooleanNetwork.mux f g h):=
  borPack_value _ _ _ _ (bandPack_value _ _ _ _ hc ha)
    (bandPack_value _ _ _ _ (bnotPack_value _ _ hc) hb)

def wordConstPack (n w c : ℕ) : Pack:=vectorPack n ((List.range w).map (fun i=>constantPack n (c.testBit i)))
lemma wordConstPack_value (n w c : ℕ) : (wordConstPack n w c).val.value=
    erase (BitArithmetic.wordConstant (n:=n) (BitVec.ofNat w c)):=by
  unfold wordConstPack BitArithmetic.wordConstant
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  dsimp only [Function.comp_apply]
  simpa [←BitVec.getLsbD_eq_getElem,BitVec.getLsbD_ofNat,i.isLt] using constantPack_value n (c.testBit i.val)

def wordMuxPack (w : ℕ) (c a b : Pack) : Pack:=
  compPack (pairPack (pairPack c a) b) (vectorPack (1+w+w) ((List.range w).map (fun i=>
    muxPack (bitPack (1+w+w) 0) (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i)))))
lemma wordMuxPack_value {n w : ℕ} (c a b : Pack) (f : BooleanNetwork n 1) (g h : BooleanNetwork n w)
    (hc : c.val.value=erase f) (ha : a.val.value=erase g) (hb : b.val.value=erase h) :
    (wordMuxPack w c a b).val.value=erase (BitArithmetic.wordMux f g h):=by
  unfold wordMuxPack BitArithmetic.wordMux
  apply compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (pairPack_spec _ _ _ _ hc ha) hb)
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  exact muxPack_value _ _ _ _ _ _ (bitPack_value ⟨0,by omega⟩)
    (bitPack_value ⟨1+i.val,by omega⟩) (bitPack_value ⟨1+w+i.val,by omega⟩)
namespace Emission
noncomputable def borPackP : Procedure (prodCode packCode packCode) packCode (fun x=>borPack x.1 x.2):=
  bnotPackP.comp (bandPackP.comp (bnotPackP.parallel bnotPackP))
noncomputable def bxorPackP : Procedure (prodCode packCode packCode) packCode (fun x=>bxorPack x.1 x.2):=by
  let a:=first packCode packCode
  let b:=second packCode packCode
  exact borPackP.comp ((bandPackP.comp (a.pair (bnotPackP.comp b))).pair
    (bandPackP.comp ((bnotPackP.comp a).pair b)))
noncomputable def muxPackP : Procedure (prodCode packCode (prodCode packCode packCode)) packCode
    (fun x=>muxPack x.1 x.2.1 x.2.2):=by
  let c:=first packCode (prodCode packCode packCode)
  let a:=(first packCode packCode).comp (second packCode (prodCode packCode packCode))
  let b:=(second packCode packCode).comp (second packCode (prodCode packCode packCode))
  exact borPackP.comp ((bandPackP.comp (c.pair a)).pair (bandPackP.comp ((bnotPackP.comp c).pair b)))
noncomputable def wordConstPackP : Procedure (prodCode unaryCode (prodCode unaryCode Nat.bits)) packCode
    (fun x=>wordConstPack x.1 x.2.1 x.2.2):=by
  let idx:=first unaryCode (prodCode unaryCode Nat.bits)
  let e:=second unaryCode (prodCode unaryCode Nat.bits)
  let n:=(first unaryCode Nat.bits).comp e
  let c:=(second unaryCode Nat.bits).comp e
  let step:=constantPackP.comp (n.pair (testBit.comp (c.pair idx)))
  let n₀:=first unaryCode (prodCode unaryCode Nat.bits)
  let rest:=second unaryCode (prodCode unaryCode Nat.bits)
  let c₀:=(second unaryCode Nat.bits).comp rest
  let w₀:=(first unaryCode Nat.bits).comp rest
  let parts:=(tabulate (f:=fun (x:ℕ×ℕ) i=>constantPack x.1 (x.2.testBit i)) emptyPack step).comp (w₀.pair (n₀.pair c₀))
  exact vectorPackP.comp (n₀.pair parts)
noncomputable def muxVectorPackP : Procedure unaryCode packCode
    (fun w=>vectorPack (1+w+w) ((List.range w).map (fun i=>muxPack (bitPack (1+w+w) 0)
      (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i))))):=by
  let i:=unaryToBits.comp (first unaryCode unaryCode)
  let w:=second unaryCode unaryCode
  let width:=unarySuccessor.comp (unaryAdd.comp (w.pair w))
  let c:=bitPackP.comp (width.pair (Procedure.constant _ Nat.bits 0))
  let a:=bitPackP.comp (width.pair (successor.comp i))
  let b:=bitPackP.comp (width.pair (successor.comp (binaryAdd.comp ((unaryToBits.comp w).pair i))))
  let step:=muxPackP.comp (c.pair (a.pair b))
  let parts:=(tabulate (f:=fun w i=>muxPack (bitPack (1+w+w) 0) (bitPack (1+w+w) (1+i))
    (bitPack (1+w+w) (1+w+i))) emptyPack (step.congrFun (by intro x;simp only [Function.comp_apply,id_eq,Nat.succ_eq_add_one]; simp only [Nat.add_assoc,Nat.add_comm]))).comp
    ((identity unaryCode).pair (identity unaryCode))
  let width₀:=unarySuccessor.comp (unaryAdd.comp ((identity unaryCode).pair (identity unaryCode)))
  exact (vectorPackP.comp (width₀.pair parts)).congrFun (by intro w;simp only [Function.comp_apply,id_eq,Nat.succ_eq_add_one]; simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
noncomputable def wordMuxPackP : Procedure (prodCode unaryCode (prodCode packCode (prodCode packCode packCode))) packCode
    (fun x=>wordMuxPack x.1 x.2.1 x.2.2.1 x.2.2.2):=by
  let rest:=second unaryCode (prodCode packCode (prodCode packCode packCode))
  let c:=(first packCode (prodCode packCode packCode)).comp rest
  let ab:=(second packCode (prodCode packCode packCode)).comp rest
  let a:=(first packCode packCode).comp ab
  let b:=(second packCode packCode).comp ab
  exact compPackP.comp ((pairPackP.comp ((pairPackP.comp (c.pair a)).pair b)).pair
    (muxVectorPackP.comp (first unaryCode (prodCode packCode (prodCode packCode packCode)))))
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionRewire.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def rewireBy (a : Data) (is : List ℕ) : Data:=
  ⟨a.inputs,a.nodes,is.map (fun i=>(a.outputs.drop i).headD 0)⟩
lemma rewireBy_valid (a : Data) (ha : a.Valid) (is : List ℕ) : (rewireBy a is).Valid:=by
  refine ⟨ha.1,?_⟩
  intro i hi
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
  exact headD_drop_bound ha.2 j
lemma rewireBy_mass (a : Data) (is : List ℕ) : (rewireBy a is).mass≤a.mass+is.length:=by
  simp only [rewireBy,Data.mass,Data.width,List.length_map];omega
lemma erase_rewireBy {n m l : ℕ} (a : BooleanNetwork n m) (f : Fin l→Fin m) :
    rewireBy (erase a) (List.ofFn (fun i=>(f i).val))=erase (a.rewire f):=by
  unfold rewireBy erase BooleanNetwork.rewire
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp [(f i).isLt]
def rewirePack (a : Pack) (is : List ℕ) : Pack:=
  ⟨⟨a.val.budget+is.length,rewireBy a.val.value is⟩,rewireBy_valid a.val.value a.property.1 is,
    (rewireBy_mass _ _).trans (Nat.add_le_add_right a.property.2 _)⟩
lemma rewirePack_value {n m l : ℕ} (a : Pack) (b : BooleanNetwork n m) (f : Fin l→Fin m)
    (h : a.val.value=erase b) :
    (rewirePack a (List.ofFn (fun i=>(f i).val))).val.value=erase (b.rewire f):=by
  change rewireBy a.val.value _=_
  rw [h,erase_rewireBy]
def identityPack (n : ℕ) : Pack:=selectPack n (List.range n) (by intro i hi;exact Nat.le_of_lt (List.mem_range.mp hi))
lemma identityPack_value (n : ℕ) : (identityPack n).val.value=erase (BooleanNetwork.select (id : Fin n→Fin n)):=by
  rw [erase_select]
  change select n (List.range n)=select n (List.ofFn (fun i:Fin n=>i.val))
  congr 1
  exact (ofFn_val_range n).symm

def assignPack (n i : ℕ) (v : Pack) : Pack:=
  rewirePack (pairPack (identityPack n) v) ((List.range n).map (fun j=>if j=i then n else j))
lemma assignPack_value {n : ℕ} (i : Fin n) (a : Pack) (v : BooleanNetwork n 1) (ha : a.val.value=erase v) :
    (assignPack n i.val a).val.value=erase (BooleanNetwork.assign i v):=by
  have hp : (pairPack (identityPack n) a).val.value=erase ((BooleanNetwork.select id).pair v):=by
    rw [pairPack_value,identityPack_value,ha,erase_pair]
    rw [identityPack_value,ha];rfl
  have hi : ((List.range n).map (fun j=>if j=i.val then n else j))=
      List.ofFn (fun j:Fin n=>(if j=i then Fin.natAdd n (0 : Fin 1) else j.castAdd 1).val):=by
    rw [←ofFn_val_range,List.map_ofFn]
    congr 1
    funext j
    by_cases h : j=i
    · subst j;simp
    · have hn : j.val≠i.val:=fun hh=>h (Fin.ext hh)
      simp [h,hn]
  rw [assignPack,hi,rewirePack_value _ _ _ hp]
  rfl
namespace Emission
noncomputable def rewireByP : Procedure (prodCode dataCode (listCode Nat.bits)) dataCode
    (fun x=>rewireBy x.1 x.2):=by
  let a:=first dataCode (listCode Nat.bits)
  let is:=second dataCode (listCode Nat.bits)
  let out:=dataOutputsP.comp a
  let get:=(listGet Nat.bits 0).comp ((second (listCode Nat.bits) Nat.bits).pair (first (listCode Nat.bits) Nat.bits))
  let outs:=(listMapWith (f:=fun (xs:List ℕ) i=>(xs.drop i).headD 0) 0 0 get).comp (out.pair is)
  exact (dataPackP.comp ((dataInputP.comp a).pair ((dataNodesP.comp a).pair outs))).congrFun (by intro x;rfl)
noncomputable def rewirePackP : Procedure (prodCode packCode (listCode Nat.bits)) packCode
    (fun x=>rewirePack x.1 x.2):=by
  let a:=first packCode (listCode Nat.bits)
  let is:=second packCode (listCode Nat.bits)
  let v:=rewireByP.comp ((packValueP.comp a).pair is)
  let b:=unaryAdd.comp ((packBudgetP.comp a).pair ((NativeAIG.Emission.listUnaryLength Nat.bits 0).comp is))
  exact (b.pair v).result (by intro x;rfl)
noncomputable def rangeP : Procedure unaryCode (listCode Nat.bits) List.range:=by
  let p:=unaryToBits.comp (first unaryCode emptyCode)
  exact ((tabulate (f:=fun (_:Unit) i=>i) 0 p).comp
    ((identity unaryCode).pair (Procedure.constant _ emptyCode ()))).congrFun (by intro n;exact List.map_id _)
noncomputable def identityPackP : Procedure unaryCode packCode identityPack:=by
  let v:=selectP.comp (unaryToBits.pair rangeP)
  let b:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  exact (b.pair v).result (by intro n;change _=prodCode unaryCode dataCode (n+(List.range n).length,select n (List.range n));rw [List.length_range];rfl)
noncomputable def assignPackP : Procedure (prodCode unaryCode (prodCode Nat.bits packCode)) packCode
    (fun x=>assignPack x.1 x.2.1 x.2.2):=by
  let n:=first unaryCode (prodCode Nat.bits packCode)
  let i:=(first Nat.bits packCode).comp (second unaryCode (prodCode Nat.bits packCode))
  let v:=(second Nat.bits packCode).comp (second unaryCode (prodCode Nat.bits packCode))
  let env:=(unaryToBits.comp n).pair i
  let e:=first (prodCode Nat.bits Nat.bits) Nat.bits
  let j:=second (prodCode Nat.bits Nat.bits) Nat.bits
  let test:=binaryEq.comp (j.pair ((second Nat.bits Nat.bits).comp e))
  let choose:= (conditional test ((first Nat.bits Nat.bits).comp e) j).congrFun
    (show ∀ x : (ℕ×ℕ)×ℕ, _ = (if x.2=x.1.2 then x.1.1 else x.2) from by
      intro x;simp)
  let out:=(listMapWith (f:=fun (e:ℕ×ℕ) j=>if j=e.2 then e.1 else j) 0 0 choose).comp
    (env.pair (rangeP.comp n))
  exact rewirePackP.comp ((pairPackP.comp ((identityPackP.comp n).pair v)).pair out)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AIGNetworkEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat BooleanNetwork
open NetworkEmission

def faninPack (n gs : ℕ) (f : NativeAIG.Ref) : Pack:=
  let v:=if f.1<gs then bitPack (n+gs) (n+f.1) else constantPack (n+gs) false
  if f.2 then bnotPack v else v
lemma faninPack_value {n : ℕ} (g : AIG (Fin n)) (f : AIG.Fanin) :
    (faninPack n g.decls.size (f.gate,f.invert)).val.value=erase (AIGCompiler.faninNet g f):=by
  unfold faninPack AIGCompiler.faninNet
  by_cases h : f.gate<g.decls.size
  · simp only [h,↓reduceIte,↓reduceDIte]
    have hv:=bitPack_value (AIGCompiler.graphWire g ⟨f.gate,h⟩)
    change (bitPack (n+g.decls.size) (n+f.gate)).val.value=_ at hv
    cases f.invert
    · exact hv
    · exact bnotPack_value _ _ hv
  · simp only [h,↓reduceIte,↓reduceDIte]
    cases f.invert
    · exact constantPack_value _ _
    · exact bnotPack_value _ _ (constantPack_value _ _)

def nodePack (n gs : ℕ) : NativeAIG.Decl→Pack
  | .zero=>constantPack (n+gs) false
  | .atom v=>bitPack (n+gs) v
  | .gate a b=>bandPack (faninPack n gs a) (faninPack n gs b)
lemma nodePack_value {n : ℕ} (g : AIG (Fin n)) (i : Fin g.decls.size) :
    (nodePack n g.decls.size (NativeAIG.eraseDecl g.decls[i.val])).val.value=
      erase (AIGCompiler.nodeNet g i):=by
  unfold AIGCompiler.nodeNet
  cases h : g.decls[i.val] with
  | false=>exact constantPack_value _ _
  | atom v=>exact bitPack_value (v.castAdd g.decls.size)
  | gate a b=>exact bandPack_value _ _ _ _ (faninPack_value g a) (faninPack_value g b)

def partialPack (n : ℕ) (ds : List NativeAIG.Decl) (k : ℕ) : Pack:=
  ((List.range k).map (fun i=>assignPack (n+ds.length) (n+i)
    (nodePack n ds.length ((ds.drop i).headD .zero)))).foldl compPack (identityPack (n+ds.length))
lemma partialPack_value {n : ℕ} {r : NativeAIG.Graph} {g : AIG (Fin n)}
    (hr : NativeAIG.Rel r g) (k : ℕ) (hk : k≤g.decls.size) :
    (partialPack n r.decls k).val.value=erase (AIGCompiler.partialGraph g k hk):=by
  have hl : r.decls.length=g.decls.size:=by rw [hr.1,List.length_map,Array.length_toList]
  induction k with
  | zero=>simpa only [partialPack,List.range_zero,List.map_nil,List.foldl_nil,hl,AIGCompiler.partialGraph]
      using identityPack_value (n+g.decls.size)
  | succ k ih=>
    have hips:=ih (by omega)
    have hd : (r.decls.drop k).headD .zero=NativeAIG.eraseDecl g.decls[k]:=by
      rw [List.headD_eq_head?_getD,List.head?_drop,hr.1,List.getElem?_map,Array.getElem?_toList,
        Array.getElem?_eq_getElem (by omega),Option.map_some,Option.getD_some]
    have hn:=assignPack_value (AIGCompiler.graphWire g ⟨k,by omega⟩) _ _ (nodePack_value g ⟨k,by omega⟩)
    simp only [AIGCompiler.graphWire,Fin.val_natAdd] at hn
    unfold partialPack
    rw [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (compPack (partialPack n r.decls k) (assignPack (n+r.decls.length) (n+k)
      (nodePack n r.decls.length ((r.decls.drop k).headD .zero)))).val.value=_
    rw [compPack_value]
    · rw [hips,hl,hd,hn]
      exact (erase_comp _ _).symm
    · rw [hips,hl,hd,hn]
      simp [erase]

def padPack (n gs : ℕ) : Pack:=vectorPack n ((List.range (n+gs)).map
  (fun i=>if i<n then bitPack n i else constantPack n false))
lemma padPack_value (n gs : ℕ) : (padPack n gs).val.value=erase (BooleanNetwork.padRight n gs):=by
  unfold padPack BooleanNetwork.padRight
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  dsimp only [Function.comp_apply]
  by_cases h : i.val<n
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact bitPack_value ⟨i.val,h⟩
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact constantPack_value _ _

def compilePack (n : ℕ) (ds : List NativeAIG.Decl) (refs : List NativeAIG.Ref) : Pack:=
  compPack (compPack (padPack n ds.length) (partialPack n ds ds.length))
    (vectorPack (n+ds.length) (refs.map (faninPack n ds.length)))
lemma compilePack_value {n m : ℕ} {r : NativeAIG.Graph} {g : AIG (Fin n)}
    (hr : NativeAIG.Rel r g) (refs : Fin m→AIG.Ref g) :
    (compilePack n r.decls (List.ofFn (fun i=>((refs i).gate,(refs i).invert)))).val.value=
      erase (AIGCompiler.compile g refs):=by
  have hl : r.decls.length=g.decls.size:=by rw [hr.1,List.length_map,Array.length_toList]
  have hp:=partialPack_value hr g.decls.size le_rfl
  have hs : (compPack (padPack n r.decls.length) (partialPack n r.decls r.decls.length)).val.value=
      erase ((BooleanNetwork.padRight n g.decls.size).comp (AIGCompiler.partialGraph g g.decls.size le_rfl)):=by
    rw [compPack_value]
    · rw [hl,padPack_value,hp,erase_comp]
    · rw [hl,padPack_value,hp];simp [erase]
  have hv : (vectorPack (n+r.decls.length) ((List.ofFn (fun i=>((refs i).gate,(refs i).invert))).map
      (faninPack n r.decls.length))).val.value=
      erase (BooleanNetwork.vector (fun i=>AIGCompiler.faninNet g (.mk (refs i).gate (refs i).invert))):=by
    rw [hl,List.map_ofFn]
    apply vectorPack_value
    intro i
    dsimp only [Function.comp_apply]
    simpa only [AIG.Fanin.gate_mk,AIG.Fanin.invert_mk] using
      faninPack_value g (.mk (refs i).gate (refs i).invert)
  unfold compilePack
  rw [compPack_value]
  · rw [hs,hv];exact (erase_comp _ _).symm
  · rw [hs,hv];simp [erase]
end ExactQuantumFactoring.AIGNetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AIGNetworkProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open BitStackProgram BitStackProgram.Procedure NetworkEmission
open NetworkEmission.Emission
namespace Emission
abbrev dimsCode:=prodCode unaryCode unaryCode
noncomputable def faninPackP : Procedure (prodCode dimsCode NativeAIG.refCode) packCode
    (fun x=>faninPack x.1.1 x.1.2 x.2):=by
  let e:=first dimsCode NativeAIG.refCode
  let n:=(first unaryCode unaryCode).comp e
  let gs:=(second unaryCode unaryCode).comp e
  let w:=unaryAdd.comp (n.pair gs)
  let ref:=second dimsCode NativeAIG.refCode
  let idx:=(first Nat.bits boolCode).comp ref
  let inv:=(second Nat.bits boolCode).comp ref
  let off:=binaryAdd.comp ((unaryToBits.comp n).pair idx)
  let v:=conditional (binaryLt.comp (idx.pair (unaryToBits.comp gs)))
    (bitPackP.comp (w.pair off)) (constantPackP.comp (w.pair (Procedure.constant _ boolCode false)))
  exact (conditional inv (bnotPackP.comp v) v).congrFun (by intro x;simp only [Function.comp_apply,id_eq,decide_eq_true_eq,faninPack])

def declTag : NativeAIG.Decl→ℕ | .zero=>0 | .atom _=>1 | .gate _ _=>2
def declAtom : NativeAIG.Decl→ℕ | .atom i=>i | _=>0
def declGate : NativeAIG.Decl→NativeAIG.Key | .gate a b=>(a,b) | _=>((0,false),(0,false))
noncomputable def declTagP : Procedure NativeAIG.declCode Nat.bits declTag:=
  ((casesSum (Procedure.constant emptyCode Nat.bits 0)
    (casesSum (Procedure.constant Nat.bits Nat.bits 1) (Procedure.constant NativeAIG.keyCode Nat.bits 2))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def declAtomP : Procedure NativeAIG.declCode Nat.bits declAtom:=
  ((casesSum (Procedure.constant emptyCode Nat.bits 0)
    (casesSum (identity Nat.bits) (Procedure.constant NativeAIG.keyCode Nat.bits 0))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def declGateP : Procedure NativeAIG.declCode NativeAIG.keyCode declGate:=
  ((casesSum (Procedure.constant emptyCode NativeAIG.keyCode ((0,false),(0,false)))
    (casesSum (Procedure.constant Nat.bits NativeAIG.keyCode ((0,false),(0,false))) (identity NativeAIG.keyCode))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def nodePackP : Procedure (prodCode dimsCode NativeAIG.declCode) packCode
    (fun x=>nodePack x.1.1 x.1.2 x.2):=by
  let e:=first dimsCode NativeAIG.declCode
  let w:=unaryAdd.comp e
  let d:=second dimsCode NativeAIG.declCode
  let tag:=declTagP.comp d
  let z:=constantPackP.comp (w.pair (Procedure.constant _ boolCode false))
  let a:=bitPackP.comp (w.pair (declAtomP.comp d))
  let l:=(first NativeAIG.refCode NativeAIG.refCode).comp (declGateP.comp d)
  let r:=(second NativeAIG.refCode NativeAIG.refCode).comp (declGateP.comp d)
  let g:=bandPackP.comp ((faninPackP.comp (e.pair l)).pair (faninPackP.comp (e.pair r)))
  exact (conditional (binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits 0))) z
    (conditional (binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits 1))) a g)).congrFun (by
      rintro ⟨e,d⟩;cases d <;> rfl)

abbrev graphInputCode:=prodCode unaryCode (listCode NativeAIG.declCode)
noncomputable def partialPackP : Procedure (prodCode graphInputCode unaryCode) packCode
    (fun x=>partialPack x.1.1 x.1.2 x.2):=by
  let e:=second unaryCode graphInputCode
  let n:=(first unaryCode (listCode NativeAIG.declCode)).comp e
  let ds:=(second unaryCode (listCode NativeAIG.declCode)).comp e
  let gs:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ds
  let w:=unaryAdd.comp (n.pair gs)
  let i:=first unaryCode graphInputCode
  let off:=binaryAdd.comp ((unaryToBits.comp n).pair (unaryToBits.comp i))
  let d:=(listGet NativeAIG.declCode .zero).comp ((unaryToBits.comp i).pair ds)
  let node:=nodePackP.comp ((n.pair gs).pair d)
  let step:=assignPackP.comp (w.pair (off.pair node))
  let input:=first graphInputCode unaryCode
  let num:=second graphInputCode unaryCode
  let parts:=(tabulate (f:=fun (x:ℕ×List NativeAIG.Decl) i=>assignPack (x.1+x.2.length) (x.1+i)
    (nodePack x.1 x.2.length ((x.2.drop i).headD .zero))) emptyPack step).comp (num.pair input)
  let nn:=(first unaryCode (listCode NativeAIG.declCode)).comp input
  let gg:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ((second unaryCode (listCode NativeAIG.declCode)).comp input)
  exact foldCompP.comp (parts.pair (identityPackP.comp (unaryAdd.comp (nn.pair gg))))
noncomputable def padPackP : Procedure dimsCode packCode (fun x=>padPack x.1 x.2):=by
  let e:=second unaryCode dimsCode
  let n:=(first unaryCode unaryCode).comp e
  let i:=unaryToBits.comp (first unaryCode dimsCode)
  let v:=conditional (binaryLt.comp (i.pair (unaryToBits.comp n)))
    (bitPackP.comp (n.pair i)) (constantPackP.comp (n.pair (Procedure.constant _ boolCode false)))
  let parts:=(tabulate (f:=fun (x:ℕ×ℕ) i=>if i<x.1 then bitPack x.1 i else constantPack x.1 false)
    emptyPack (v.congrFun (by intro x;simp only [Function.comp_apply,id_eq,decide_eq_true_eq]))).comp (unaryAdd.pair (identity dimsCode))
  exact vectorPackP.comp ((first unaryCode unaryCode).pair parts)
noncomputable def compilePackP : Procedure (prodCode graphInputCode (listCode NativeAIG.refCode)) packCode
    (fun x=>compilePack x.1.1 x.1.2 x.2):=by
  let e:=first graphInputCode (listCode NativeAIG.refCode)
  let n:=(first unaryCode (listCode NativeAIG.declCode)).comp e
  let ds:=(second unaryCode (listCode NativeAIG.declCode)).comp e
  let gs:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ds
  let dim:=n.pair gs
  let pad:=padPackP.comp dim
  let graph:=partialPackP.comp (e.pair gs)
  let refs:=second graphInputCode (listCode NativeAIG.refCode)
  let parts:=(listMapWith (f:=fun (x:ℕ×ℕ) f=>faninPack x.1 x.2 f) (0,false) emptyPack faninPackP).comp (dim.pair refs)
  let output:=vectorPackP.comp ((unaryAdd.comp dim).pair parts)
  exact compPackP.comp ((compPackP.comp (pad.pair graph)).pair output)
end Emission
end ExactQuantumFactoring.AIGNetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGShift.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def shiftBit (xs : List Ref) (d i : ℕ) : Ref:=
  if i<d then (0,false) else (xs.drop (i-d)).headD (0,false)
def shiftLoop : ℕ→List Ref→ℕ→ℕ→List Ref→List Ref
  | 0,_,_,_,out=>out
  | k+1,xs,d,i,out=>shiftLoop k xs d (i+1) (out++[shiftBit xs d i])
def shift (xs : List Ref) (d : ℕ) : List Ref:=
  (List.range xs.length).map (shiftBit xs d)
lemma shiftLoop_value (k : ℕ) (xs : List Ref) (d i : ℕ) (out : List Ref) :
    shiftLoop k xs d i out=out++(List.range' i k).map (shiftBit xs d) := by
  induction k generalizing i out with
  | zero=>simp [shiftLoop]
  | succ k ih=>simp [shiftLoop,ih,List.range'_succ,List.append_assoc]
lemma shiftLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (d curr : ℕ) (hc : curr ≤ w) (out : AIG.RefVec g curr) :
    VecRel (r,shiftLoop (w-curr) (eraseVec xs) d curr (eraseVec out))
      (blastShiftLeftConst.go g xs d curr hc out) := by
  rw [blastShiftLeftConst.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,shiftLoop]
    by_cases he : curr<d
    · rw [dite_eq_left he,shiftBit,ite_eq_left he]
      have hh:=shiftLoop_rel hr xs d (curr+1) (by omega) (out.push (g.mkConstCached false))
      simpa only [eraseVec_push,AIG.mkConstCached] using hh
    · rw [dite_eq_right he,shiftBit,ite_eq_right he,eraseVec_get xs (by omega)]
      simpa only [eraseVec_push] using
        shiftLoop_rel hr xs d (curr+1) (by omega) (out.push (xs.get (curr-d) (by omega)))
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,shiftLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma shift_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (d : ℕ) :
    VecRel (r,shift (eraseVec xs) d) (blastShiftLeftConst g ⟨xs,d⟩) := by
  simpa only [blastShiftLeftConst,shiftLoop_value,eraseVec_empty,List.nil_append,
    AIG.RefVec.emptyWithCapacity_eq,Nat.sub_zero,List.range_eq_range',shift,eraseVec_length] using
    shiftLoop_rel hr xs d 0 (Nat.zero_le _) (.emptyWithCapacity w)

lemma const_zero_go {n w : ℕ} (g : AIG (Fin n)) (curr : ℕ) (hc : curr ≤ w)
    (out : AIG.RefVec g curr) :
    eraseVec (blastConst.go g (0 : BitVec w) curr out hc)=
      eraseVec out++List.replicate (w-curr) (0,false) := by
  rw [blastConst.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi,const_zero_go,eraseVec_push]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    simp only [AIG.mkConstCached]
    rw [hd,List.replicate_succ]
    simp [List.append_assoc]
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    simp
termination_by w-curr
lemma const_zero {n w : ℕ} (g : AIG (Fin n)) :
    eraseVec (blastConst g (0 : BitVec w))=List.replicate w (0,false) := by
  simpa only [blastConst,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,List.nil_append,Nat.sub_zero]
    using const_zero_go g 0 (Nat.zero_le _) (.emptyWithCapacity w)

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def shiftBitP : Procedure (prodCode unaryCode (prodCode (listCode refCode) Nat.bits)) refCode
    (fun x=>shiftBit x.2.1 x.2.2 x.1) := by
  let i:=unaryToBits.comp (first unaryCode (prodCode (listCode refCode) Nat.bits))
  let env:=second unaryCode (prodCode (listCode refCode) Nat.bits)
  let xs:=(first (listCode refCode) Nat.bits).comp env
  let d:=(second (listCode refCode) Nat.bits).comp env
  let idx:=binarySub.comp (i.pair d)
  let get:=(listGet refCode (0,false)).comp (idx.pair xs)
  exact (conditional (binaryLt.comp (i.pair d)) (Procedure.constant _ refCode (0,false)) get).congrFun (by
    intro x;unfold shiftBit;split <;> simp_all)
noncomputable def shiftP : Procedure (prodCode (listCode refCode) Nat.bits) (listCode refCode)
    (fun x=>shift x.1 x.2) :=
  (tabulate (f:=fun (x : List Ref×ℕ) i=>shiftBit x.1 x.2 i) (0,false) shiftBitP).comp
    (((listUnaryLength refCode (0,false)).comp (first (listCode refCode) Nat.bits)).pair (identity _))
end Emission
end ExactQuantumFactoring.NativeAIG

end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGIf.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

def ifGate (r : Graph) (d a b : Ref) : Graph×Ref :=
  let s:=gate r d a
  let t:=gate s.1 (notRef d) b
  orGate t.1 s.2 t.2
lemma if_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.TernaryInput g) :
    EPRel (ifGate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkIfCached i) := by
  let si : AIG.BinaryInput g:=⟨i.discr,i.lhs⟩
  let s:=g.mkAndCached si
  have hs:=gate_rel h si
  change EPRel (gate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert)) s at hs
  let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) g si
  let ti : AIG.BinaryInput s.aig:=⟨(i.discr.cast hsub).not,i.rhs.cast hsub⟩
  let t:=s.aig.mkAndCached ti
  have ht : EPRel (gate (gate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert)).1
      (notRef (i.discr.gate,i.discr.invert)) (i.rhs.gate,i.rhs.invert)) t := by
    simpa only [si,s,ti,t,AIG.mkAndCached,AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,AIG.Ref.cast,notRef] using gate_rel hs.1 ti
  let hlor:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) s.aig ti
  have hh:=or_rel ht.1 (⟨s.ref.cast hlor,t.ref⟩ : AIG.BinaryInput t.aig)
  change EPRel (orGate _ (s.ref.gate,s.ref.invert) (t.ref.gate,t.ref.invert)) _ at hh
  rw [←hs.2,←ht.2] at hh
  exact hh
lemma ifGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (d a b : Ref)
    (hd : d.1≤B) (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+3) (ifGate r d a b).1 ∧ (ifGate r d a b).2.1≤B+3 := by
  have hs:=gate_bound h d a hd ha
  have ht:=gate_bound hs.1 (notRef d) b (hd.trans (by omega)) (hb.trans (by omega))
  exact orGate_bound ht.1 _ _ (hs.2.trans (by omega)) ht.2

def ifLoop : ℕ→Graph→Ref→List Ref→List Ref→ℕ→List Ref→Graph×List Ref
  | 0,r,_,_,_,_,out=>(r,out)
  | k+1,r,d,lhs,rhs,curr,out=>
    let s:=ifGate r d ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false))
    ifLoop k s.1 d lhs rhs (curr+1) (out++[s.2])
def ifVec (r : Graph) (d : Ref) (lhs rhs : List Ref) : Graph×List Ref :=
  ifLoop lhs.length r d lhs rhs 0 []
lemma ifLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (d : AIG.Ref g) (lhs rhs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w)
    (out : AIG.RefVec g curr) :
    VecRel (ifLoop (w-curr) r (d.gate,d.invert) (eraseVec lhs) (eraseVec rhs) curr (eraseVec out))
      (AIG.RefVec.ite.go g curr hc d lhs rhs out) := by
  rw [AIG.RefVec.ite.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,ifLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let i : AIG.TernaryInput g:=⟨d,lhs.get curr hi,rhs.get curr hi⟩
    let s:=g.mkIfCached i
    have hs:=if_rel hr i
    let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkIfCached) g i
    have hh:=ifLoop_rel hs.1 (d.cast hsub) (lhs.cast hsub) (rhs.cast hsub)
      (curr+1) (by omega) ((out.cast hsub).push s.ref)
    simp only [eraseVec_cast,eraseVec_push,AIG.Ref.cast] at hh
    rw [hs.2]
    exact hh
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,ifLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma ifVec_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.RefVec.IfInput g w) :
    VecRel (ifVec r (i.discr.gate,i.discr.invert) (eraseVec i.lhs) (eraseVec i.rhs))
      (AIG.RefVec.ite g i) := by
  cases i with
  | mk d lhs rhs=>
    simpa only [AIG.RefVec.ite,ifVec,eraseVec_length,Nat.sub_zero,
      AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty] using
      ifLoop_rel hr d lhs rhs 0 (Nat.zero_le _) (.emptyWithCapacity w)

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def ifP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>ifGate x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let d:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let a:=(first refCode refCode).comp bc
  let b:=(second refCode refCode).comp bc
  let s:=gateP.comp (r.pair (d.pair a))
  let t:=gateP.comp (((first graphCode refCode).comp s).pair ((notRefP.comp d).pair b))
  exact (orP.comp (((first graphCode refCode).comp t).pair
    (((second graphCode refCode).comp s).pair ((second graphCode refCode).comp t)))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGMul.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def isZero (r : Graph) (a : Ref) : Bool:=constant r a==some false
lemma isZero_eq {n : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (a : AIG.Ref g) :
    isZero r (a.gate,a.invert)=g.isConstant a false := by
  rw [isZero,constant_eq hr,AIG.isConstant,AIG.getConstant]
  cases g.decls[a.gate]'a.hgate <;> simp

def mulLoop : ℕ→Graph→List Ref→List Ref→ℕ→List Ref→Graph×List Ref
  | 0,r,_,_,_,acc=>(r,acc)
  | k+1,r,lhs,rhs,curr,acc=>
    if isZero r ((rhs.drop curr).headD (0,false)) then mulLoop k r lhs rhs (curr+1) acc else
      let added:=add r acc (shift lhs curr)
      let next:=ifVec added.1 ((rhs.drop curr).headD (0,false)) added.2 acc
      mulLoop k next.1 lhs rhs (curr+1) next.2
def mulBlast (r : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  if lhs.length=0 then (r,[]) else
    let first:=ifVec r (rhs.headD (0,false)) lhs (List.replicate lhs.length (0,false))
    mulLoop (lhs.length-1) first.1 lhs rhs 1 first.2
def mul (r : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  if countKnown r lhs<countKnown r rhs then mulBlast r lhs rhs else mulBlast r rhs lhs

lemma mulLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (acc : AIG.RefVec g w) :
    VecRel (mulLoop (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (eraseVec acc))
      (blastMul.go g lhs rhs curr acc) := by
  rw [blastMul.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,mulLoop,eraseVec_get rhs hi,isZero_eq hr]
    split
    · exact mulLoop_rel hr lhs rhs (curr+1) acc
    · let sh:=blastShiftLeftConst g ⟨lhs,curr⟩
      have hsh:=shift_rel hr lhs curr
      let h₁:=AIG.LawfulVecOperator.le_size (f:=blastShiftLeftConst) g (⟨lhs,curr⟩ : AIG.ShiftTarget g w)
      let ai : AIG.BinaryRefVec sh.aig w:=⟨acc.cast h₁,sh.vec⟩
      let ad:=blastAdd sh.aig ai
      have had:=add_rel hsh.1 ai
      change VecRel (add r (eraseVec acc) (eraseVec sh.vec)) ad at had
      rw [←hsh.2] at had
      let h₂:=AIG.LawfulVecOperator.le_size (f:=blastAdd) sh.aig ai
      let ii : AIG.RefVec.IfInput ad.aig w:=⟨((rhs.cast h₁).cast h₂).get curr hi,ad.vec,(acc.cast h₁).cast h₂⟩
      let it:=AIG.RefVec.ite ad.aig ii
      have hit:=ifVec_rel had.1 ii
      change VecRel (ifVec _ ((rhs.get curr hi).gate,(rhs.get curr hi).invert)
        (eraseVec ad.vec) (eraseVec acc)) it at hit
      rw [←had.2] at hit
      let h₃:=AIG.LawfulVecOperator.le_size (f:=AIG.RefVec.ite) ad.aig ii
      have hh:=mulLoop_rel hit.1 (((lhs.cast h₁).cast h₂).cast h₃)
        (((rhs.cast h₁).cast h₂).cast h₃) (curr+1) it.vec
      simp only [eraseVec_cast] at hh
      rw [←hit.2] at hh
      exact hh
  · rw [dite_eq_right hi,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi),mulLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma mulBlast_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (mulBlast r (eraseVec i.lhs) (eraseVec i.rhs)) (blastMul.blast g i) := by
  cases i with
  | mk lhs rhs=>
    unfold mulBlast blastMul.blast
    rw [eraseVec_length]
    by_cases hw : w=0
    · rw [ite_eq_left hw,dite_eq_left hw]
      subst w
      exact ⟨hr,rfl⟩
    · rw [ite_eq_right hw,dite_eq_right hw]
      have hw' : 0<w:=Nat.pos_of_ne_zero hw
      let ii : AIG.RefVec.IfInput g w:=⟨rhs.get 0 hw',lhs,blastConst g 0⟩
      let it:=AIG.RefVec.ite g ii
      have hit:=ifVec_rel hr ii
      change VecRel (ifVec r ((rhs.get 0 hw').gate,(rhs.get 0 hw').invert)
        (eraseVec lhs) (eraseVec (blastConst g (0 : BitVec w)))) it at hit
      rw [const_zero] at hit
      have hget:=eraseVec_get rhs hw'
      simp only [List.drop_zero] at hget
      rw [hget]
      let h₁:=AIG.LawfulVecOperator.le_size (f:=AIG.RefVec.ite) g ii
      have hh:=mulLoop_rel hit.1 (lhs.cast h₁) (rhs.cast h₁) 1 it.vec
      simp only [eraseVec_cast] at hh
      rw [←hit.2] at hh
      exact hh
lemma mul_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (mul r (eraseVec i.lhs) (eraseVec i.rhs)) (blastMul g i) := by
  cases i with
  | mk lhs rhs=>
    unfold mul blastMul
    rw [countKnown_eq hr,countKnown_eq hr]
    split
    · exact mulBlast_rel hr ⟨lhs,rhs⟩
    · exact mulBlast_rel hr ⟨rhs,lhs⟩
end ExactQuantumFactoring.NativeAIG

end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGIfProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma RefsBound.push_inc {B c : ℕ} {xs : List Ref} (hx : RefsBound B xs)
    (hc : 1 ≤ c) (a : Ref) (ha : a.1 ≤ B+c) : RefsBound (B+c) (xs++[a]) := by
  refine ⟨?_,?_⟩
  · simp only [List.length_append,List.length_singleton];have:=hx.1;omega
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hx.2 r hr).trans (by omega)
    · have he : r=a:=List.mem_singleton.mp hr
      simpa only [he] using ha

def ifStepData (s : AddData) : AddData :=
  let r:=ifGate s.graph s.cin ((s.lhs.drop s.curr).headD (0,false)) ((s.rhs.drop s.curr).headD (0,false))
  ⟨s.budget+3,r.1,s.lhs,s.rhs,s.curr+1,s.cin,s.output++[r.2]⟩
lemma ifStep_ok (s : AddState) : AddOK (ifStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=ifGate_bound hg s.val.cin _ _ hci (hl.get s.val.curr) (hr.get s.val.curr)
  unfold AddOK
  dsimp only [ifStepData]
  exact ⟨hh.1,hl.mono (by omega),hr.mono (by omega),by omega,by omega,
    ho.push_inc (by omega) _ hh.2⟩
def ifStep (s : AddState) : AddState:=⟨ifStepData s.val,ifStep_ok s⟩
lemma ifStep_budget (s : AddState) : (ifStep s).val.budget=s.val.budget+3 := rfl
lemma ifStep_iterate_budget (s : AddState) (k : ℕ) :
    ((ifStep^[k]) s).val.budget=s.val.budget+3*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,ifStep_budget];omega
lemma ifStep_iterate_loop (s : AddState) (k : ℕ) :
    (((ifStep^[k]) s).val.graph,((ifStep^[k]) s).val.output)=
      ifLoop k s.val.graph s.val.cin s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl

def initializeIfData (s : AddData) : AddData:=⟨s.budget,s.graph,s.lhs,s.rhs,0,s.cin,[]⟩
lemma initializeIf_ok (s : AddState) : AddOK (initializeIfData s.val) := by
  exact ⟨s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,s.property.2.2.2.2.1,
    ⟨Nat.zero_le _,by intro a ha;cases ha⟩⟩
def initializeIf (s : AddState) : AddState:=⟨initializeIfData s.val,initializeIf_ok s⟩
def ifVecState (s : AddState) : AddState:=(ifStep^[s.val.lhs.length]) (initializeIf s)
lemma ifVecState_value (s : AddState) :
    ((ifVecState s).val.graph,(ifVecState s).val.output)=ifVec s.val.graph s.val.cin s.val.lhs s.val.rhs :=
  ifStep_iterate_loop (initializeIf s) s.val.lhs.length
lemma ifVecState_budget (s : AddState) :
    (ifVecState s).val.budget=s.val.budget+3*s.val.lhs.length :=
  ifStep_iterate_budget (initializeIf s) s.val.lhs.length
namespace Emission
noncomputable def ifStepDataP : Procedure addDataCode addDataCode ifStepData := by
  let budget:=(first unaryCode addTail1).comp addViewP
  let newBudget:=unaryAdd.comp (budget.pair (Procedure.constant _ unaryCode 3))
  let lhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=ifP.comp (addGraphP.pair (addCinP.pair (lhsBit.pair rhsBit)))
  let g:=(first graphCode refCode).comp s
  let outBit:=(second graphCode refCode).comp s
  let out:=(listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp outBit))
  exact (packAddP.comp (newBudget.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (addCinP.pair out))))))).congrFun (by intro s;rfl)
noncomputable def ifStepP : Procedure addStateCode addStateCode ifStep :=
  (ifStepDataP.precompose Subtype.val).result (by intro s;rfl)
noncomputable def ifIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(ifStep^[x.1]) x.2) :=
  ifStepP.iterate (Polynomial.C 2700*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((ifStep^[i]) s)
    rw [ifStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hb' : s.val.budget+3*i+1 ≤ 3*(n+(addStateCode s).length+1):=by omega
    have hs:=Nat.pow_le_pow_left hb' 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def initializeIfDataP : Procedure addDataCode addDataCode initializeIfData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addLhsP.pair (addRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair (addCinP.pair
      (Procedure.constant _ (listCode refCode) [])))))))).congrFun (by intro x;rfl)
noncomputable def initializeIfP : Procedure addStateCode addStateCode initializeIf :=
  (initializeIfDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def ifVecStateP : Procedure addStateCode addStateCode ifVecState :=
  ifIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeIfP)
noncomputable def ifVecP : Procedure addStateCode (prodCode graphCode (listCode refCode))
    (fun s=>ifVec s.val.graph s.val.cin s.val.lhs s.val.rhs) :=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp ifVecStateP).congrFun ifVecState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGVectorBounds.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
lemma shift_length (xs : List Ref) (d : ℕ) : (shift xs d).length=xs.length := by
  simp [shift]
lemma shift_refs {B : ℕ} {xs : List Ref} (h : RefsBound B xs) (d : ℕ) :
    RefsBound B (shift xs d) := by
  refine ⟨by simpa only [shift_length] using h.1,?_⟩
  intro a ha
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  unfold shiftBit
  split
  · exact Nat.zero_le _
  · exact h.get _
lemma addStep_length (s : AddState) : (addStep s).val.output.length=s.val.output.length+1 := by
  simp only [addStep,addStepData,List.length_append,List.length_singleton]
lemma addStep_iterate_length (s : AddState) (k : ℕ) :
    ((addStep^[k]) s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,addStep_length];omega
lemma addBlastState_length (s : AddState) : (addBlastState s).val.output.length=s.val.lhs.length := by
  rw [addBlastState,addStep_iterate_length]
  simp only [initializeAdd,initializeAddData,List.length_nil,Nat.zero_add]
lemma addState_length (s : AddState) (h : s.val.lhs.length=s.val.rhs.length) :
    (addState s).val.output.length=s.val.lhs.length := by
  unfold addState
  split
  · exact addBlastState_length s
  · rw [addBlastState_length];exact h.symm
lemma addState_budget_eq (s : AddState) (h : s.val.lhs.length=s.val.rhs.length) :
    (addState s).val.budget=s.val.budget+13*s.val.lhs.length := by
  unfold addState
  split
  · exact addBlastState_budget s
  · rw [addBlastState_budget];change s.val.budget+13*s.val.rhs.length=_;rw [h]
lemma ifStep_length (s : AddState) : (ifStep s).val.output.length=s.val.output.length+1 := by
  simp only [ifStep,ifStepData,List.length_append,List.length_singleton]
lemma ifStep_iterate_length (s : AddState) (k : ℕ) :
    ((ifStep^[k]) s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,ifStep_length];omega
lemma ifVecState_length (s : AddState) : (ifVecState s).val.output.length=s.val.lhs.length := by
  rw [ifVecState,ifStep_iterate_length]
  simp only [initializeIf,initializeIfData,List.length_nil,Nat.zero_add]
lemma add_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs)
    (he : lhs.length=rhs.length) :
    Bounded (B+13*lhs.length) (add g lhs rhs).1 ∧
    RefsBound (B+13*lhs.length) (add g lhs rhs).2 ∧ (add g lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hs : s.val.lhs.length=s.val.rhs.length:=he
  have hb:=addState_budget_eq s hs
  have ho:=(addState s).property
  have hv:=addState_value s
  have hn:=addState_length s hs
  rw [←hv]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,hn⟩
lemma ifVec_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref} {c : Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) (hc : c.1 ≤ B) :
    Bounded (B+3*lhs.length) (ifVec g c lhs rhs).1 ∧
    RefsBound (B+3*lhs.length) (ifVec g c lhs rhs).2 ∧ (ifVec g c lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,c,[]⟩,
    hg,hl,hr,Nat.zero_le _,hc,Nat.zero_le _,by intro a ha;cases ha⟩
  have hb:=ifVecState_budget s
  have ho:=(ifVecState s).property
  have hv:=ifVecState_value s
  have hn:=ifVecState_length s
  rw [←hv]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,hn⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGMulBounded.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def MulOK (s : AddData) : Prop:=AddOK s ∧ s.lhs.length=s.rhs.length ∧ s.output.length=s.lhs.length
abbrev MulState:={s : AddData // MulOK s}
def mulStateCode (s : MulState) : List Bool:=addDataCode s.val

def mulStepData (s : AddData) : AddData:=
  let next:=if isZero s.graph ((s.rhs.drop s.curr).headD (0,false)) then (s.graph,s.output) else
    let added:=add s.graph s.output (shift s.lhs s.curr)
    ifVec added.1 ((s.rhs.drop s.curr).headD (0,false)) added.2 s.output
  ⟨s.budget+16*s.lhs.length+1,next.1,s.lhs,s.rhs,s.curr+1,s.cin,next.2⟩
lemma mulStep_ok (s : MulState) : MulOK (mulStepData s.val) := by
  obtain ⟨⟨hg,hl,hr,hc,hci,ho⟩,he,ha⟩:=s.property
  have hb : s.val.budget ≤ s.val.budget+16*s.val.lhs.length+1:=by omega
  unfold MulOK AddOK mulStepData
  split
  · exact ⟨⟨hg.mono hb,hl.mono hb,hr.mono hb,by dsimp only;omega,hci.trans hb,ho.mono hb⟩,he,ha⟩
  · have had:=add_bound hg ho (shift_refs hl s.val.curr) (by rw [shift_length];exact ha)
    have hn : s.val.budget+13*s.val.output.length+3*(add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).2.length ≤
        s.val.budget+16*s.val.lhs.length+1:=by rw [had.2.2,ha];omega
    have hh:=ifVec_bound had.1 had.2.1 (ho.mono (by omega)) ((hr.get s.val.curr).trans (by omega))
    exact ⟨⟨hh.1.mono hn,hl.mono hb,hr.mono hb,by dsimp only;omega,hci.trans hb,hh.2.1.mono hn⟩,
      he,hh.2.2.trans (had.2.2.trans ha)⟩
def mulStep (s : MulState) : MulState:=⟨mulStepData s.val,mulStep_ok s⟩
lemma mulStep_budget (s : MulState) : (mulStep s).val.budget=s.val.budget+16*s.val.lhs.length+1 := rfl
lemma mulStep_lhs (s : MulState) : (mulStep s).val.lhs=s.val.lhs := rfl
lemma mulStep_iterate_lhs (s : MulState) (k : ℕ) : ((mulStep^[k]) s).val.lhs=s.val.lhs := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih,mulStep_lhs]
lemma mulStep_iterate_budget (s : MulState) (k : ℕ) :
    ((mulStep^[k]) s).val.budget=s.val.budget+(16*s.val.lhs.length+1)*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,mulStep_budget,mulStep_lhs];ring
lemma mulStep_iterate_loop (s : MulState) (k : ℕ) :
    (((mulStep^[k]) s).val.graph,((mulStep^[k]) s).val.output)=
      mulLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih,mulLoop]
    unfold mulStep mulStepData
    split <;> rfl
lemma mulStateCode_bound (s : MulState) : (mulStateCode s).length ≤ 300*(s.val.budget+1)^2 :=
  addStateCode_bound ⟨s.val,s.property.1⟩
lemma mulBudget_le_code (s : MulState) : s.val.budget ≤ (mulStateCode s).length :=
  budget_le_code ⟨s.val,s.property.1⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGMulProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def mulAddInput (s : MulState) : AddState:=
  ⟨⟨s.val.budget,s.val.graph,s.val.output,shift s.val.lhs s.val.curr,0,(0,false),[]⟩,
   s.property.1.1,s.property.1.2.2.2.2.2,shift_refs s.property.1.2.1 _,Nat.zero_le _,Nat.zero_le _,
   Nat.zero_le _,by intro a ha;cases ha⟩
def mulAdded (s : MulState) : AddState:=addState (mulAddInput s)
lemma mulAdded_value (s : MulState) : ((mulAdded s).val.graph,(mulAdded s).val.output)=
    add s.val.graph s.val.output (shift s.val.lhs s.val.curr) :=addState_value _
lemma mulAdded_budget (s : MulState) : (mulAdded s).val.budget=s.val.budget+13*s.val.lhs.length := by
  have hh:=addState_budget_eq (mulAddInput s) (by
    change s.val.output.length=(shift s.val.lhs s.val.curr).length
    rw [shift_length];exact s.property.2.2)
  simpa only [mulAdded,mulAddInput,s.property.2.2] using hh
lemma mulAdded_length (s : MulState) : (mulAdded s).val.output.length=s.val.lhs.length := by
  have hh:=addState_length (mulAddInput s) (by
    change s.val.output.length=(shift s.val.lhs s.val.curr).length
    rw [shift_length];exact s.property.2.2)
  exact hh.trans s.property.2.2

def mulIfInput (s : MulState) : AddState:=
  ⟨⟨(mulAdded s).val.budget,(mulAdded s).val.graph,(mulAdded s).val.output,s.val.output,0,
      (s.val.rhs.drop s.val.curr).headD (0,false),[]⟩,
    (mulAdded s).property.1,(mulAdded s).property.2.2.2.2.2,
    s.property.1.2.2.2.2.2.mono (by rw [mulAdded_budget];omega),Nat.zero_le _,
    (s.property.1.2.2.1.get _).trans (by rw [mulAdded_budget];omega),Nat.zero_le _,by intro a ha;cases ha⟩
lemma mulIfInput_value (s : MulState) :
    ifVec (mulIfInput s).val.graph (mulIfInput s).val.cin (mulIfInput s).val.lhs (mulIfInput s).val.rhs=
      ifVec (add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).1
        ((s.val.rhs.drop s.val.curr).headD (0,false))
        (add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).2 s.val.output := by
  have hh:=mulAdded_value s
  have h1:=congrArg Prod.fst hh
  have h2:=congrArg Prod.snd hh
  dsimp only [Prod.fst] at h1
  dsimp only [Prod.snd] at h2
  dsimp only [mulIfInput]
  rw [h1,h2]

namespace Emission
noncomputable def mulBudgetP : Procedure mulStateCode unaryCode (fun s=>s.val.budget):=
  ((first unaryCode addTail1).comp addViewP).precompose (fun s:MulState=>s.val)
noncomputable def mulGraphP : Procedure mulStateCode graphCode (fun s=>s.val.graph):=
  addGraphP.precompose (fun s:MulState=>s.val)
noncomputable def mulLhsP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.lhs):=
  addLhsP.precompose (fun s:MulState=>s.val)
noncomputable def mulRhsP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.rhs):=
  addRhsP.precompose (fun s:MulState=>s.val)
noncomputable def mulOutputP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.output):=
  addOutputP.precompose (fun s:MulState=>s.val)
noncomputable def mulCurrP : Procedure mulStateCode Nat.bits (fun s=>s.val.curr):=
  addCurrP.precompose (fun s:MulState=>s.val)
noncomputable def mulCinP : Procedure mulStateCode refCode (fun s=>s.val.cin):=
  addCinP.precompose (fun s:MulState=>s.val)
noncomputable def mulAddInputP : Procedure mulStateCode addStateCode mulAddInput := by
  let sh:=shiftP.comp (mulLhsP.pair mulCurrP)
  exact (packAddP.comp (mulBudgetP.pair (mulGraphP.pair (mulOutputP.pair (sh.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
    (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def mulAddedP : Procedure mulStateCode addStateCode mulAdded :=addStateP.comp mulAddInputP
noncomputable def mulIfInputP : Procedure mulStateCode addStateCode mulIfInput := by
  let ad:=mulAddedP
  let budget:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp ad
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp ad
  let added:=(addOutputP.precompose (fun s:AddState=>s.val)).comp ad
  let c:=(listGet refCode (0,false)).comp (mulCurrP.pair mulRhsP)
  exact (packAddP.comp (budget.pair (g.pair (added.pair (mulOutputP.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def isZeroP : Procedure (prodCode graphCode refCode) boolCode (fun x=>isZero x.1 x.2):=by
  let inv := (second Nat.bits boolCode).comp (second graphCode refCode)
  exact (boolAnd.comp (knownP.pair (boolNot.comp inv))).congrFun (by
    rintro ⟨g,⟨i,b⟩⟩
    dsimp only [Function.comp_apply, Prod.fst, Prod.snd]
    unfold known isZero constant
    cases g.decls[i]?.getD Decl.zero <;> cases b <;> rfl)
noncomputable def mulNextP : Procedure mulStateCode (prodCode graphCode (listCode refCode))
    (fun s=>if isZero s.val.graph ((s.val.rhs.drop s.val.curr).headD (0,false)) then (s.val.graph,s.val.output)
      else let added:=add s.val.graph s.val.output (shift s.val.lhs s.val.curr)
        ifVec added.1 ((s.val.rhs.drop s.val.curr).headD (0,false)) added.2 s.val.output) := by
  let c:=(listGet refCode (0,false)).comp (mulCurrP.pair mulRhsP)
  let test:=isZeroP.comp (mulGraphP.pair c)
  let no:=(ifVecP.comp mulIfInputP).congrFun mulIfInput_value
  exact conditional test (mulGraphP.pair mulOutputP) no
noncomputable def mulStepP : Procedure mulStateCode mulStateCode mulStep := by
  let len:=(listUnaryLength refCode (0,false)).comp mulLhsP
  let cost:=unaryMul.comp ((Procedure.constant _ unaryCode 16).pair len)
  let b:=unarySuccessor.comp (unaryAdd.comp (mulBudgetP.pair cost))
  let g:=(first graphCode (listCode refCode)).comp mulNextP
  let out:=(second graphCode (listCode refCode)).comp mulNextP
  exact (packAddP.comp (b.pair (g.pair (mulLhsP.pair (mulRhsP.pair
    ((successor.comp mulCurrP).pair (mulCinP.pair out))))))).result (by intro s;rfl)
noncomputable def mulIterationP : Procedure (prodCode unaryCode mulStateCode) mulStateCode
    (fun x=>(mulStep^[x.1]) x.2) :=
  mulStepP.iterate (Polynomial.C 97200*(Polynomial.X+1)^4) (by
    intro n s i hi
    have hh:=mulStateCode_bound ((mulStep^[i]) s)
    rw [mulStep_iterate_budget] at hh
    have hb:=mulBudget_le_code s
    have hl:=s.property.1.2.1.1
    let M:=n+(mulStateCode s).length+1
    have hM : 1 ≤ M:=by dsimp [M];omega
    have hB : s.val.budget+1 ≤ M:=by dsimp [M];omega
    have hw : 16*s.val.lhs.length+1 ≤ 17*M:=by omega
    have hii : i ≤ M:=by dsimp [M];omega
    have hm:=Nat.mul_le_mul hw hii
    have hx : s.val.budget+(16*s.val.lhs.length+1)*i+1 ≤ 18*M^2:=by nlinarith
    have hp:=Nat.pow_le_pow_left hx 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    calc
      (mulStateCode ((mulStep^[i]) s)).length ≤ 300*(s.val.budget+(16*s.val.lhs.length+1)*i+1)^2:=hh
      _ ≤ 300*(18*M^2)^2:=Nat.mul_le_mul_left _ hp
      _ = 97200*(n+(mulStateCode s).length+1)^4:=by dsimp [M];ring)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGMulWrapper.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

abbrev BinaryState:={s : AddState // s.val.lhs.length=s.val.rhs.length}
def binaryStateCode (s : BinaryState) : List Bool:=addStateCode s.val
lemma RefsBound.zeros {B w : ℕ} (h : w≤B) : RefsBound B (List.replicate w (0,false)) := by
  refine ⟨by simpa,?_⟩
  intro a ha
  have he:=List.eq_of_mem_replicate ha
  simpa only [he] using Nat.zero_le B

def mulFirstInput (s : BinaryState) : AddState:=
  ⟨⟨s.val.val.budget,s.val.val.graph,s.val.val.lhs,List.replicate s.val.val.lhs.length (0,false),
    0,s.val.val.rhs.headD (0,false),[]⟩,
  s.val.property.1,s.val.property.2.1,RefsBound.zeros s.val.property.2.1.1,Nat.zero_le _,
  by simpa using s.val.property.2.2.1.get 0,Nat.zero_le _,by intro a ha;cases ha⟩
def mulFirst (s : BinaryState) : AddState:=ifVecState (mulFirstInput s)
lemma mulFirst_budget (s : BinaryState) : (mulFirst s).val.budget=s.val.val.budget+3*s.val.val.lhs.length:=
  ifVecState_budget _
lemma mulFirst_length (s : BinaryState) : (mulFirst s).val.output.length=s.val.val.lhs.length:=
  ifVecState_length _
lemma mulFirst_value (s : BinaryState) : ((mulFirst s).val.graph,(mulFirst s).val.output)=
    ifVec s.val.val.graph (s.val.val.rhs.headD (0,false)) s.val.val.lhs
      (List.replicate s.val.val.lhs.length (0,false)):=ifVecState_value _
def initializeMul (s : BinaryState) : MulState:=
  ⟨⟨(mulFirst s).val.budget+1,(mulFirst s).val.graph,s.val.val.lhs,s.val.val.rhs,1,(0,false),
      (mulFirst s).val.output⟩,
  ⟨(mulFirst s).property.1.mono (by dsimp only;omega),
    s.val.property.2.1.mono (by dsimp only;rw [mulFirst_budget];omega),
    s.val.property.2.2.1.mono (by dsimp only;rw [mulFirst_budget];omega),by dsimp only;omega,Nat.zero_le _,
    (mulFirst s).property.2.2.2.2.2.mono (by dsimp only;omega)⟩,s.property,mulFirst_length s⟩
def mulBlastState (s : BinaryState) : MulState:=(mulStep^[s.val.val.lhs.length-1]) (initializeMul s)
lemma mulBlastState_value (s : BinaryState) :
    ((mulBlastState s).val.graph,(mulBlastState s).val.output)=
      mulBlast s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  rw [mulBlastState,mulStep_iterate_loop]
  have hh:=mulFirst_value s
  have h1:=congrArg Prod.fst hh
  have h2:=congrArg Prod.snd hh
  dsimp only [Prod.fst] at h1
  dsimp only [Prod.snd] at h2
  dsimp only [initializeMul]
  rw [h1,h2,mulBlast]
  split
  · rename_i hz
    have hl:=List.length_eq_zero_iff.mp hz
    simp only [hl,List.length_nil,Nat.zero_sub,List.replicate_zero,ifVec,ifLoop,mulLoop]
  · rfl

def swapBinary (s : BinaryState) : BinaryState:=⟨swapAdd s.val,s.property.symm⟩
def mulState (s : BinaryState) : MulState:=
  if countKnown s.val.val.graph s.val.val.lhs<countKnown s.val.val.graph s.val.val.rhs then
    mulBlastState s else mulBlastState (swapBinary s)
lemma mulState_value (s : BinaryState) : ((mulState s).val.graph,(mulState s).val.output)=
    mul s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  unfold mulState mul
  split <;> exact mulBlastState_value _
lemma mulBlastState_budget (s : BinaryState) : (mulBlastState s).val.budget=
    s.val.val.budget+3*s.val.val.lhs.length+1+(16*s.val.val.lhs.length+1)*(s.val.val.lhs.length-1) := by
  rw [mulBlastState,mulStep_iterate_budget]
  dsimp only [initializeMul]
  rw [mulFirst_budget]
lemma mulState_budget (s : BinaryState) : (mulState s).val.budget=
    s.val.val.budget+3*s.val.val.lhs.length+1+(16*s.val.val.lhs.length+1)*(s.val.val.lhs.length-1) := by
  unfold mulState
  split
  · exact mulBlastState_budget s
  · rw [mulBlastState_budget]
    change s.val.val.budget+3*s.val.val.rhs.length+1+(16*s.val.val.rhs.length+1)*(s.val.val.rhs.length-1)=_
    rw [s.property]
lemma mulState_length (s : BinaryState) : (mulState s).val.output.length=s.val.val.lhs.length := by
  have hh:=(mulState s).property.2.2
  rw [hh]
  unfold mulState
  split <;> rw [mulBlastState,mulStep_iterate_lhs]
  · rfl
  · exact s.property.symm

namespace Emission
noncomputable def binaryGraphP : Procedure binaryStateCode graphCode (fun s=>s.val.val.graph):=
  addGraphP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def binaryLhsP : Procedure binaryStateCode (listCode refCode) (fun s=>s.val.val.lhs):=
  addLhsP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def binaryRhsP : Procedure binaryStateCode (listCode refCode) (fun s=>s.val.val.rhs):=
  addRhsP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def zerosP : Procedure (listCode refCode) (listCode refCode)
    (fun xs=>List.replicate xs.length (0,false)) :=
  (listMap (0,false) (0,false) (Procedure.constant refCode refCode (0,false))).congrFun (by
    intro xs;exact List.map_const')
noncomputable def mulFirstInputP : Procedure binaryStateCode addStateCode mulFirstInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:BinaryState=>s.val.val)
  let c:=(listHead refCode (0,false)).comp binaryRhsP
  exact (packAddP.comp (b.pair (binaryGraphP.pair (binaryLhsP.pair ((zerosP.comp binaryLhsP).pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
    (by intro s;rfl)
noncomputable def mulFirstP : Procedure binaryStateCode addStateCode mulFirst:=ifVecStateP.comp mulFirstInputP
noncomputable def initializeMulP : Procedure binaryStateCode mulStateCode initializeMul := by
  let f:=mulFirstP
  let b:=unarySuccessor.comp ((((first unaryCode addTail1).comp addViewP).precompose
    (fun s:AddState=>s.val)).comp f)
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp f
  let out:=(addOutputP.precompose (fun s:AddState=>s.val)).comp f
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (binaryRhsP.pair
    ((Procedure.constant _ Nat.bits 1).pair ((Procedure.constant _ refCode (0,false)).pair out))))))).result
      (by intro s;rfl)
noncomputable def mulBlastStateP : Procedure binaryStateCode mulStateCode mulBlastState :=
  mulIterationP.comp ((unaryPred.comp ((listUnaryLength refCode (0,false)).comp binaryLhsP)).pair initializeMulP)
noncomputable def swapBinaryP : Procedure binaryStateCode binaryStateCode swapBinary :=
  (swapAddP.precompose (fun s:BinaryState=>s.val)).result (by intro s;rfl)
noncomputable def mulStateP : Procedure binaryStateCode mulStateCode mulState := by
  let lk:=countKnownP.comp (binaryGraphP.pair binaryLhsP)
  let rk:=countKnownP.comp (binaryGraphP.pair binaryRhsP)
  exact (conditional (binaryLt.comp (lk.pair rk)) mulBlastStateP
    (mulBlastStateP.comp swapBinaryP)).congrFun (by intro s;unfold mulState;split <;> simp_all)
noncomputable def mulP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>mul s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  (((addGraphP.pair addOutputP).precompose (fun s:MulState=>s.val)).comp mulStateP).congrFun mulState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGNot.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def notVec (xs : List Ref) : List Ref:=xs.map notRef
lemma notMap_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w) (out : AIG.RefVec g curr) :
    VecRel (r,eraseVec out++notVec ((eraseVec xs).drop curr))
      (AIG.RefVec.map.go g curr hc out xs AIG.mkNotCached) := by
  rw [AIG.RefVec.map.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hh:=notMap_rel hr xs (curr+1) (by omega) (out.push (xs.get curr hi).not)
    have hl : curr<(eraseVec xs).length:=by simpa only [eraseVec_length] using hi
    rw [List.drop_eq_getElem_cons hl]
    have he : (eraseVec xs)[curr]'hl=((xs.get curr hi).gate,(xs.get curr hi).invert):=by simp [eraseVec]
    rw [he]
    simpa only [notVec,List.map_cons,eraseVec_push,AIG.mkNotCached,AIG.RefVec.cast,AIG.RefVec.cast',AIG.Ref.not,AIG.Ref.flip,
      Bool.true_xor,notRef,List.append_assoc,List.singleton_append] using hh
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [List.drop_eq_nil_of_le (by rw [eraseVec_length])]
    simp only [notVec,List.map_nil,List.append_nil]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma notVec_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) : VecRel (r,notVec (eraseVec xs)) (blastNot g xs) := by
  simpa only [blastNot,AIG.RefVec.map,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,
    List.nil_append,List.drop_zero] using notMap_rel hr xs 0 (Nat.zero_le _) (.emptyWithCapacity w)
lemma notVec_length (xs : List Ref) : (notVec xs).length=xs.length:=List.length_map _
lemma notVec_refs {B : ℕ} {xs : List Ref} (h : RefsBound B xs) : RefsBound B (notVec xs) := by
  refine ⟨by simpa only [notVec_length] using h.1,?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
  exact h.2 b hb
namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def notVecP : Procedure (listCode refCode) (listCode refCode) notVec:=
  listMap (0,false) (0,false) notRefP
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGCarry.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def carryLoop : ℕ→Graph→List Ref→List Ref→ℕ→Ref→Graph×Ref
  | 0,r,_,_,_,cin=>(r,cin)
  | k+1,r,lhs,rhs,curr,cin=>
    let s:=fullCarry r ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false)) cin
    carryLoop k s.1 lhs rhs (curr+1) s.2
def overflow (r : Graph) (lhs rhs : List Ref) (cin : Ref) : Graph×Ref :=
  carryLoop lhs.length r lhs rhs 0 cin
def ult (r : Graph) (lhs rhs : List Ref) : Graph×Ref:=
  let s:=overflow r lhs (notVec rhs) (0,true)
  (s.1,notRef s.2)
lemma carryLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (cin : AIG.Ref g) :
    EPRel (carryLoop (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (cin.gate,cin.invert))
      (mkOverflowBit.go g lhs rhs curr cin) := by
  rw [mkOverflowBit.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,carryLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let ii : FullAdderInput g:=⟨lhs.get curr hi,rhs.get curr hi,cin⟩
    let cc:=mkFullAdderCarry g ii
    have hh:=fullCarry_rel hr ii
    let hle:=AIG.LawfulOperator.le_size (f:=mkFullAdderCarry) g ii
    have ht:=carryLoop_rel hh.1 (lhs.cast hle) (rhs.cast hle) (curr+1) cc.ref
    simp only [eraseVec_cast] at ht
    rw [←hh.2] at ht
    exact ht
  · rw [dite_eq_right hi,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi),carryLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma overflow_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : OverflowInput g) :
    EPRel (overflow r (eraseVec i.vec.lhs) (eraseVec i.vec.rhs) (i.cin.gate,i.cin.invert))
      (mkOverflowBit g i) := by
  cases i with
  | mk w v c=>
    simpa only [overflow,eraseVec_length,Nat.sub_zero,mkOverflowBit] using carryLoop_rel hr v.lhs v.rhs 0 c
lemma ult_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    EPRel (ult r (eraseVec i.lhs) (eraseVec i.rhs)) (Std.Tactic.BVDecide.BVPred.mkUlt g i) := by
  let nt:=blastNot g i.rhs
  have hn:=notVec_rel hr i.rhs
  let hle:=AIG.LawfulVecOperator.le_size (f:=blastNot) g i.rhs
  let oi : OverflowInput nt.aig:=⟨w,⟨i.lhs.cast hle,nt.vec⟩,nt.aig.mkConstCached true⟩
  have hh:=overflow_rel hn.1 oi
  change EPRel (overflow r (eraseVec i.lhs) (eraseVec nt.vec) (0,true)) (mkOverflowBit nt.aig oi) at hh
  rw [←hn.2] at hh
  refine ⟨hh.1,?_⟩
  simpa only [notRef,Std.Tactic.BVDecide.BVPred.mkUlt,AIG.mkNotCached,AIG.Ref.not,AIG.Ref.flip,
    Bool.true_xor,ult] using congrArg notRef hh.2
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGSub.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def oneVec (w : ℕ) : List Ref:=(List.range w).map (fun i=>(0,decide (i=0)))
lemma const_go {n w : ℕ} (g : AIG (Fin n)) (v : BitVec w) (curr : ℕ) (hc : curr≤w)
    (out : AIG.RefVec g curr) :
    eraseVec (blastConst.go g v curr out hc)=
      eraseVec out++(List.range' curr (w-curr)).map (fun i=>(0,v.getLsbD i)) := by
  rw [blastConst.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi,const_go,eraseVec_push]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,List.range'_succ,List.map_cons]
    simp only [AIG.mkConstCached,List.append_assoc,List.singleton_append]
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    simp
termination_by w-curr
lemma const_erase {n w : ℕ} (g : AIG (Fin n)) (v : BitVec w) :
    eraseVec (blastConst g v)=(List.range w).map (fun i=>(0,v.getLsbD i)) := by
  simpa only [blastConst,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,List.nil_append,Nat.sub_zero,
    List.range_eq_range'] using const_go g v 0 (Nat.zero_le _) (.emptyWithCapacity w)
lemma const_one {n w : ℕ} (g : AIG (Fin n)) :
    eraseVec (blastConst g (BitVec.ofNat w 1))=oneVec w := by
  rw [const_erase,oneVec]
  apply List.map_congr_left
  intro i hi
  have hw : 0<w:=by have:=List.mem_range.mp hi;omega
  simp [BitVec.getLsbD_one,hw]
lemma oneVec_length (w : ℕ) : (oneVec w).length=w:=by simp [oneVec]
lemma oneVec_refs {B w : ℕ} (h : w≤B) : RefsBound B (oneVec w) := by
  refine ⟨by simpa only [oneVec_length],?_⟩
  intro a ha
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  exact Nat.zero_le _

def neg (r : Graph) (xs : List Ref) : Graph×List Ref :=add r (notVec xs) (oneVec xs.length)
def sub (r : Graph) (lhs rhs : List Ref) : Graph×List Ref :=
  let s:=neg r rhs
  add s.1 lhs s.2
lemma neg_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) : VecRel (neg r (eraseVec xs)) (blastNeg g xs) := by
  let nt:=blastNot g xs
  have hn:=notVec_rel hr xs
  have hh:=add_rel hn.1 ⟨nt.vec,blastConst nt.aig (BitVec.ofNat w 1)⟩
  rw [const_one,←hn.2] at hh
  simpa only [neg,eraseVec_length,blastNeg,nt] using hh
lemma sub_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) : VecRel (sub r (eraseVec i.lhs) (eraseVec i.rhs)) (blastSub g i) := by
  let nr:=blastNeg g i.rhs
  have hn:=neg_rel hr i.rhs
  let hle:=AIG.LawfulVecOperator.le_size (f:=blastNeg) g i.rhs
  have hh:=add_rel hn.1 ⟨i.lhs.cast hle,nr.vec⟩
  simpa only [eraseVec_cast,nr,←hn.2,sub,blastSub] using hh
end ExactQuantumFactoring.NativeAIG

end


end OAI
