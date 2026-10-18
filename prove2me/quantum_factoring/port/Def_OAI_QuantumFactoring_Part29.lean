/-
Exact quantum factoring development (port of OpenAI's formalization), part 29 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: NativeAIGAdd.lean, NativeAIGBounds.lean, NativeAIGAddBounded.lean, Emission.lean, NativeAIGAddProcedure.lean, NativeAIGKnownProcedure.lean, NativeAIGAddWrapper.lean, BitStackListMapWith.lean, NetworkEmissionProcedures.lean, NetworkEmissionBasic.lean, NetworkEmissionBounds.lean, NetworkEmissionPack.lean, NetworkStackCompiler.lean, NetworkEmissionVector.lean, RawListRange.lean, BitStackTestBit.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part28

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGAdd.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
@[simp] lemma countKnown_nil (r : Graph) : countKnown r []=0 := rfl
lemma countKnown_cons (r : Graph) (a : Ref) (as : List Ref) :
    countKnown r (a::as)=(if known r a then 1 else 0)+countKnown r as := by
  simp only [countKnown,List.filter_cons]
  split <;> simp_all [Nat.add_comm]
lemma countKnown_go_eq {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (v : AIG.RefVec g w) (idx acc : ℕ) :
    AIG.RefVec.countKnown.go g v idx acc = acc+countKnown r ((eraseVec v).drop idx) := by
  rw [AIG.RefVec.countKnown.go]
  by_cases hi : idx<w
  · rw [dite_eq_left hi]
    have hl : idx<(eraseVec v).length:=by simpa only [eraseVec_length] using hi
    rw [List.drop_eq_getElem_cons hl,countKnown_cons]
    have he : (eraseVec v)[idx]'hl=((v.get idx hi).gate,(v.get idx hi).invert) := by
      simp [eraseVec]
    rw [he,known_eq hr]
    simp only [refVec_get_gate]
    cases g.decls[v.refs[idx].gate]'(v.hrefs hi) <;>
      simp only [Bool.false_eq_true,↓reduceIte] <;>
      rw [countKnown_go_eq hr v (idx+1)] <;> omega
  · rw [dite_eq_right hi,List.drop_eq_nil_of_le (by simpa only [eraseVec_length] using Nat.le_of_not_gt hi)]
    simp only [countKnown_nil,Nat.add_zero]
termination_by w-idx
@[simp] lemma countKnown_eq {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (v : AIG.RefVec g w) : AIG.RefVec.countKnown g v=countKnown r (eraseVec v) := by
  simpa only [AIG.RefVec.countKnown,List.drop_zero,Nat.zero_add] using countKnown_go_eq hr v 0 0

def addLoop : ℕ→Graph→List Ref→List Ref→ℕ→Ref→List Ref→Graph×List Ref
  | 0,r,_,_,_,_,out=>(r,out)
  | k+1,r,lhs,rhs,curr,cin,out=>
    let s:=full r ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false)) cin
    addLoop k s.1 lhs rhs (curr+1) s.2.2 (out++[s.2.1])
def addBlast (r : Graph) (lhs rhs : List Ref) : Graph×List Ref :=
  addLoop lhs.length r lhs rhs 0 (0,false) []
def add (r : Graph) (lhs rhs : List Ref) : Graph×List Ref :=
  if countKnown r lhs<countKnown r rhs then addBlast r lhs rhs else addBlast r rhs lhs

lemma addLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w) (cin : AIG.Ref g)
    (out : AIG.RefVec g curr) :
    VecRel (addLoop (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (cin.gate,cin.invert) (eraseVec out))
      (blastAdd.go g lhs rhs curr hc cin out) := by
  rw [blastAdd.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,addLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let i : FullAdderInput g:=⟨lhs.get curr hi,rhs.get curr hi,cin⟩
    let s:=mkFullAdder g i
    have hs:=full_rel hr i
    have hh:=addLoop_rel hs.1 (lhs.cast s.hle) (rhs.cast s.hle) (curr+1) (by omega)
      s.cout ((out.cast s.hle).push s.out)
    simp only [eraseVec_cast,eraseVec_push] at hh
    rw [hs.2]
    exact hh
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,addLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma addBlast_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (addBlast r (eraseVec i.lhs) (eraseVec i.rhs)) (blastAdd.blast g i) := by
  cases i with
  | mk lhs rhs=>
   simpa only [blastAdd.blast,addBlast,eraseVec_length,Nat.sub_zero,AIG.mkConstCached,
     AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty] using
    addLoop_rel hr lhs rhs 0 (Nat.zero_le _) (g.mkConstCached false) (.emptyWithCapacity w)
lemma add_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (add r (eraseVec i.lhs) (eraseVec i.rhs)) (blastAdd g i) := by
  cases i with
  | mk lhs rhs=>
    unfold add blastAdd
    rw [countKnown_eq hr,countKnown_eq hr]
    split
    · exact addBlast_rel hr ⟨lhs,rhs⟩
    · exact addBlast_rel hr ⟨rhs,lhs⟩
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGBounds.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def DeclBound (B : ℕ) : Decl→Prop
  | .zero=>True
  | .atom i=>i≤B
  | .gate a b=>a.1≤B ∧ b.1≤B
structure Bounded (B : ℕ) (r : Graph) : Prop where
  decl_length : r.decls.length≤B
  cache_length : r.cache.length≤B
  decls : ∀d∈r.decls,DeclBound B d
  cache : ∀e∈r.cache,e.1.1.1≤B ∧ e.1.2.1≤B ∧ e.2≤B
lemma DeclBound.mono {A B : ℕ} (h : A≤B) {d : Decl} (hd : DeclBound A d) : DeclBound B d := by
  cases d <;> simp only [DeclBound] at * <;> omega
lemma Bounded.mono {A B : ℕ} {r : Graph} (h : A≤B) (hr : Bounded A r) : Bounded B r :=
  ⟨hr.decl_length.trans h,hr.cache_length.trans h,fun d hd=>(hr.decls d hd).mono h,
    fun e he=>by have hh:=hr.cache e he;omega⟩
lemma lookup_bound {B : ℕ} {es : List (Key×ℕ)}
    (h : ∀e∈es,e.2≤B) (k : Key) {v : ℕ} (hv : lookup k es=some v) : v≤B := by
  induction es with
  | nil=>simp [lookup] at hv
  | cons e es ih=>
    simp only [lookup] at hv
    split_ifs at hv with he
    · cases hv;exact h e (by simp)
    · exact ih (fun a ha=>h a (by simp [ha])) hv
lemma addGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (addGate r a b).1 ∧ (addGate r a b).2.1≤B+1 := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · simp only [addGate,List.length_append,List.length_cons,List.length_nil];have:=h.decl_length;omega
  · simp only [addGate,List.length_cons];have:=h.cache_length;omega
  · intro d hd
    simp only [addGate,List.mem_append,List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact (h.decls d hd).mono (by omega)
    · simp only [DeclBound];omega
  · intro e he
    simp only [addGate,List.mem_cons] at he
    rcases he with rfl | he
    · dsimp only;have:=h.decl_length;omega
    · have:=h.cache e he;omega
  · exact h.decl_length.trans (by omega)
lemma go_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (go r a b).1 ∧ (go r a b).2.1≤B+1 := by
  have hg:=h.mono (Nat.le_add_right B 1)
  unfold go
  cases hl : lookup (a,b) r.cache with
  | some v=>
    dsimp only
    have hv:=lookup_bound (fun e he=>(h.cache e he).2.2) (a,b) hl
    exact ⟨hg,by omega⟩
  | none=>
    dsimp only
    cases hc : constant r a with
    | some a'=>
      cases a' <;> cases hd : constant r b with
      | none=>dsimp only;exact ⟨hg,by omega⟩
      | some b'=>cases b' <;> dsimp only <;> exact ⟨hg,by omega⟩
    | none=>
      cases hd : constant r b with
      | some b'=>cases b' <;> dsimp only <;> exact ⟨hg,by omega⟩
      | none=>
        dsimp only
        split_ifs
        · exact ⟨hg,ha.trans (by omega)⟩
        · exact ⟨hg,Nat.zero_le _⟩
        · exact addGate_bound h a b ha hb
lemma gate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (gate r a b).1 ∧ (gate r a b).2.1≤B+1 := by
  unfold gate;split <;> exact go_bound h _ _ (by omega) (by omega)
lemma orGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (orGate r a b).1 ∧ (orGate r a b).2.1≤B+1 :=
  gate_bound h (notRef a) (notRef b) ha hb
lemma xorGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+3) (xorGate r a b).1 ∧ (xorGate r a b).2.1≤B+3 := by
  have hs:=gate_bound h a b ha hb
  have ht:=gate_bound hs.1 (notRef a) (notRef b) (by exact ha.trans (by omega)) (by exact hb.trans (by omega))
  have hh:=gate_bound ht.1 (notRef (gate r a b).2)
    (notRef (gate (gate r a b).1 (notRef a) (notRef b)).2) (by exact hs.2.trans (by omega)) ht.2
  exact hh
lemma fullOut_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+6) (fullOut r a b c).1 ∧ (fullOut r a b c).2.1≤B+6 := by
  have hs:=xorGate_bound h a b ha hb
  exact xorGate_bound hs.1 _ c hs.2 (hc.trans (by omega))
lemma fullCarry_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+6) (fullCarry r a b c).1 ∧ (fullCarry r a b c).2.1≤B+6 := by
  have hs:=xorGate_bound h a b ha hb
  have ht:=gate_bound hs.1 _ c hs.2 (hc.trans (by omega))
  have hu:=gate_bound ht.1 a b (ha.trans (by omega)) (hb.trans (by omega))
  exact orGate_bound hu.1 _ _ (ht.2.trans (by omega)) hu.2
lemma full_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+12) (full r a b c).1 ∧
      (full r a b c).2.1.1≤B+12 ∧ (full r a b c).2.2.1≤B+12 := by
  have ho:=fullOut_bound h a b c ha hb hc
  have hk:=fullCarry_bound ho.1 a b c (ha.trans (by omega)) (hb.trans (by omega)) (hc.trans (by omega))
  exact ⟨hk.1,ho.2.trans (by omega),hk.2⟩
lemma nat_bits_length_bound (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
lemma refCode_length_bound {B : ℕ} (a : Ref) (ha : a.1≤B) : (refCode a).length≤2*B+2 := by
  have hn:=nat_bits_length_bound a.1
  simp only [refCode,prodCode,pairBits_length,boolCode,List.length_singleton]
  omega
lemma keyCode_length_bound {B : ℕ} (k : Key) (ha : k.1.1≤B) (hb : k.2.1≤B) :
    (keyCode k).length≤6*B+7 := by
  have h1:=refCode_length_bound k.1 ha
  have h2:=refCode_length_bound k.2 hb
  change (pairBits (refCode k.1) (refCode k.2)).length≤_
  rw [pairBits_length]
  omega
lemma declCode_length_bound {B : ℕ} (d : Decl) (hd : DeclBound B d) :
    (declCode d).length≤6*B+9 := by
  cases d with
  | zero=>simp [declCode,declView,sumCode,emptyCode]
  | atom i=>
    have hh:=nat_bits_length_bound i
    simp only [DeclBound] at hd
    simp only [declCode,declView,sumCode,List.length_cons];omega
  | gate a b=>
    have hh:=keyCode_length_bound (a,b) hd.1 hd.2
    simp only [declCode,declView,sumCode,List.length_cons];omega
lemma entryCode_length_bound {B : ℕ} (e : Key×ℕ) (h : e.1.1.1≤B ∧ e.1.2.1≤B ∧ e.2≤B) :
    (entryCode e).length≤13*B+15 := by
  have hk:=keyCode_length_bound e.1 h.1 h.2.1
  have hn:=nat_bits_length_bound e.2
  change (pairBits (keyCode e.1) e.2.bits).length≤_
  rw [pairBits_length]
  omega
lemma listCode_length_bound {α : Type} (e : α→List Bool) (xs : List α) (B : ℕ)
    (h : ∀x∈xs,(e x).length≤B) : (listCode e xs).length≤xs.length*(2*B+2)+1 := by
  simpa only [List.map_id] using listCode_length_map_bound e id xs B h
lemma graphCode_length_bound {B : ℕ} {r : Graph} (h : Bounded B r) :
    (graphCode r).length≤100*(B+1)^2 := by
  have hd:=listCode_length_bound declCode r.decls (6*B+9)
    (fun d hd=>declCode_length_bound d (h.decls d hd))
  have hc:=listCode_length_bound entryCode r.cache (13*B+15)
    (fun e he=>entryCode_length_bound e (h.cache e he))
  have hdm:=Nat.mul_le_mul_right (2*(6*B+9)+2) h.decl_length
  have hcm:=Nat.mul_le_mul_right (2*(13*B+15)+2) h.cache_length
  change (pairBits (listCode declCode r.decls) (listCode entryCode r.cache)).length≤_
  rw [pairBits_length]
  nlinarith
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGAddBounded.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def RefsBound (B : ℕ) (xs : List Ref) : Prop := xs.length≤B ∧ ∀a∈xs,a.1≤B
lemma RefsBound.mono {A B : ℕ} {xs : List Ref} (h : A≤B) (hx : RefsBound A xs) : RefsBound B xs :=
  ⟨hx.1.trans h,fun a ha=>(hx.2 a ha).trans h⟩
lemma RefsBound.get {B : ℕ} {xs : List Ref} (hx : RefsBound B xs) (i : ℕ) :
    ((xs.drop i).headD (0,false)).1≤B := by
  cases he : (xs.drop i).head? with
  | none=>simp only [List.headD_eq_head?_getD,he,Option.getD_none];omega
  | some a=>
    rw [List.headD_eq_head?_getD,he,Option.getD_some]
    exact hx.2 a (List.mem_of_mem_drop (List.mem_of_head? he))
lemma RefsBound.push {B : ℕ} {xs : List Ref} (hx : RefsBound B xs) (a : Ref) (ha : a.1≤B+13) :
    RefsBound (B+13) (xs++[a]) := by
  refine ⟨?_,?_⟩
  · simp only [List.length_append,List.length_singleton];have:=hx.1;omega
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hx.2 r hr).trans (by omega)
    · have he : r=a:=List.mem_singleton.mp hr
      simpa only [he] using ha
lemma refsCode_bound {B : ℕ} {xs : List Ref} (h : RefsBound B xs) :
    (listCode refCode xs).length≤10*(B+1)^2 := by
  have hh:=listCode_length_bound refCode xs (2*B+2) (fun a ha=>refCode_length_bound a (h.2 a ha))
  have hm : xs.length*(2*(2*B+2)+2)≤B*(2*(2*B+2)+2) := Nat.mul_le_mul_right _ h.1
  nlinarith
structure AddData where
  budget : ℕ
  graph : Graph
  lhs : List Ref
  rhs : List Ref
  curr : ℕ
  cin : Ref
  output : List Ref

def AddOK (s : AddData) : Prop :=
  Bounded s.budget s.graph ∧ RefsBound s.budget s.lhs ∧ RefsBound s.budget s.rhs ∧
  s.curr≤ s.budget ∧ s.cin.1≤ s.budget ∧ RefsBound s.budget s.output
abbrev AddState := {s : AddData // AddOK s}
def addStepData (s : AddData) : AddData :=
  let r:=full s.graph ((s.lhs.drop s.curr).headD (0,false)) ((s.rhs.drop s.curr).headD (0,false)) s.cin
  ⟨s.budget+13,r.1,s.lhs,s.rhs,s.curr+1,r.2.2,s.output++[r.2.1]⟩
lemma addStep_ok (s : AddState) : AddOK (addStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=full_bound hg _ _ s.val.cin (hl.get s.val.curr) (hr.get s.val.curr) hci
  unfold AddOK
  dsimp only [addStepData]
  refine ⟨hh.1.mono (by omega),hl.mono (by omega),hr.mono (by omega),by omega,
    hh.2.2.trans (by omega),?_⟩
  exact ho.push _ (hh.2.1.trans (by omega))
def addStep (s : AddState) : AddState := ⟨addStepData s.val,addStep_ok s⟩
def addDataView (s : AddData) := (s.budget,(s.graph,(s.lhs,(s.rhs,(s.curr,(s.cin,s.output))))))
def addDataCode (s : AddData) : List Bool :=
  prodCode unaryCode (prodCode graphCode (prodCode (listCode refCode)
    (prodCode (listCode refCode) (prodCode Nat.bits (prodCode refCode (listCode refCode)))))) (addDataView s)
def addStateCode (s : AddState) : List Bool := addDataCode s.val
lemma addStateCode_bound (s : AddState) : (addStateCode s).length≤300*(s.val.budget+1)^2 := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have h1:=graphCode_length_bound hg
  have h2:=refsCode_bound hl
  have h3:=refsCode_bound hr
  have h4:=(nat_bits_length_bound s.val.curr).trans hc
  have h5:=refCode_length_bound s.val.cin hci
  have h6:=refsCode_bound ho
  simp only [refCode,prodCode,pairBits_length] at h5
  simp only [addStateCode,addDataCode,addDataView,prodCode,pairBits_length,unaryCode,List.length_replicate]
  nlinarith
lemma budget_le_code (s : AddState) : s.val.budget≤(addStateCode s).length := by
  simp only [addStateCode,addDataCode,addDataView,prodCode,pairBits_length,unaryCode,List.length_replicate]
  omega
lemma addStep_budget (s : AddState) : (addStep s).val.budget=s.val.budget+13 := rfl
lemma addStep_iterate_budget (s : AddState) (k : ℕ) :
    ((addStep^[k]) s).val.budget=s.val.budget+13*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,addStep_budget];omega
lemma addStep_iterate_loop (s : AddState) (k : ℕ) :
    (((addStep^[k]) s).val.graph,((addStep^[k]) s).val.output)=
      addLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.cin s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih]
    rfl
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/Emission.lean =====
namespace OAI

section
namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

namespace Emission
open BitStackProgram BitStackProgram.Procedure
def tripleCode : Triple→List Bool:=prodCode refCode (prodCode refCode refCode)
noncomputable def fullOutP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>fullOut x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let a:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let b:=(first refCode refCode).comp bc
  let c:=(second refCode refCode).comp bc
  let s:=xorP.comp (r.pair (a.pair b))
  exact (xorP.comp (((first graphCode refCode).comp s).pair
    (((second graphCode refCode).comp s).pair c))).congrFun (by intro x;rfl)
noncomputable def fullCarryP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>fullCarry x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let a:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let b:=(first refCode refCode).comp bc
  let c:=(second refCode refCode).comp bc
  let s:=xorP.comp (r.pair (a.pair b))
  let t:=gateP.comp (((first graphCode refCode).comp s).pair
    (((second graphCode refCode).comp s).pair c))
  let u:=gateP.comp (((first graphCode refCode).comp t).pair (a.pair b))
  exact (orP.comp (((first graphCode refCode).comp u).pair
    (((second graphCode refCode).comp t).pair ((second graphCode refCode).comp u)))).congrFun (by intro x;rfl)
noncomputable def fullP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode keyCode)
    (fun x=>full x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let o:=fullOutP
  let abc:=second graphCode tripleCode
  let k:=fullCarryP.comp (((first graphCode refCode).comp o).pair abc)
  exact (((first graphCode refCode).comp k).pair
    (((second graphCode refCode).comp o).pair ((second graphCode refCode).comp k))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGAddProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
namespace Emission
abbrev addTail5 := prodCode refCode (listCode refCode)
abbrev addTail4 := prodCode Nat.bits addTail5
abbrev addTail3 := prodCode (listCode refCode) addTail4
abbrev addTail2 := prodCode (listCode refCode) addTail3
abbrev addTail1 := prodCode graphCode addTail2
abbrev addPayload := prodCode unaryCode addTail1
noncomputable def addViewP : Procedure addDataCode addPayload addDataView :=
  ((identity addPayload).precompose addDataView)
noncomputable def packAddP : Procedure addPayload addDataCode
    (fun x=>AddData.mk x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2) :=
  (identity addPayload).result (by intro x;rfl)
noncomputable def addGraphP : Procedure addDataCode graphCode AddData.graph :=
  (first graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)
noncomputable def addLhsP : Procedure addDataCode (listCode refCode) AddData.lhs :=
  (first (listCode refCode) addTail3).comp ((second graphCode addTail2).comp
    ((second unaryCode addTail1).comp addViewP))
noncomputable def addRhsP : Procedure addDataCode (listCode refCode) AddData.rhs :=
  (first (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
    ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))
noncomputable def addCurrP : Procedure addDataCode Nat.bits AddData.curr :=
  (first Nat.bits addTail5).comp ((second (listCode refCode) addTail4).comp
    ((second (listCode refCode) addTail3).comp ((second graphCode addTail2).comp
      ((second unaryCode addTail1).comp addViewP))))
noncomputable def addCinP : Procedure addDataCode refCode AddData.cin :=
  (first refCode (listCode refCode)).comp ((second Nat.bits addTail5).comp
    ((second (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
      ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))))
noncomputable def addOutputP : Procedure addDataCode (listCode refCode) AddData.output :=
  (second refCode (listCode refCode)).comp ((second Nat.bits addTail5).comp
    ((second (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
      ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))))
noncomputable def addStepDataP : Procedure addDataCode addDataCode addStepData := by
  let budget:=(first unaryCode addTail1).comp addViewP
  let newBudget:=unaryAdd.comp (budget.pair (Procedure.constant _ unaryCode 13))
  let lhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=fullP.comp (addGraphP.pair (lhsBit.pair (rhsBit.pair addCinP)))
  let g:=(first graphCode keyCode).comp s
  let refs:=(second graphCode keyCode).comp s
  let outBit:=(first refCode refCode).comp refs
  let cin:=(second refCode refCode).comp refs
  let out:=(listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp outBit))
  exact (packAddP.comp (newBudget.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (cin.pair out))))))).congrFun (by intro s;rfl)
noncomputable def addStepP : Procedure addStateCode addStateCode addStep :=
  (addStepDataP.precompose Subtype.val).result (by intro s;rfl)
noncomputable def addIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(addStep^[x.1]) x.2) :=
  addStepP.iterate (Polynomial.C 50700*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((addStep^[i]) s)
    rw [addStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hb' : s.val.budget+13*i+1≤13*(n+(addStateCode s).length+1):=by omega
    have hs:=Nat.pow_le_pow_left hb' 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def addLoopP : Procedure (prodCode unaryCode addStateCode)
    (prodCode graphCode (listCode refCode))
    (fun x=>addLoop x.1 x.2.val.graph x.2.val.lhs x.2.val.rhs x.2.val.curr x.2.val.cin x.2.val.output) :=
  (((addGraphP.pair addOutputP).precompose Subtype.val).comp addIterationP).congrFun
    (fun x=>addStep_iterate_loop x.2 x.1)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGKnownProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def knownP : Procedure (prodCode graphCode refCode) boolCode
    (fun x=>known x.1 x.2) := by
  let r:=first graphCode refCode
  let a:=second graphCode refCode
  let idx:=(first Nat.bits boolCode).comp a
  let d:=(listGet declCode .zero).comp (idx.pair (decls.comp r))
  exact (zeroDecl.comp d).congrFun (by
    rintro ⟨g,⟨i,b⟩⟩
    simp only [Function.comp_apply]
    have he : (g.decls.drop i).headD Decl.zero=g.decls[i]?.getD Decl.zero := by
      rw [List.headD_eq_head?_getD,List.head?_drop]
    simp only [he]
    unfold known
    cases g.decls[i]?.getD Decl.zero <;> rfl)
def knownStep (x : Ref×(Graph×ℕ)) : Graph×ℕ :=
  (x.2.1,x.2.2+(if known x.2.1 x.1 then 1 else 0))
lemma knownStep_fold (xs : List Ref) (g : Graph) (acc : ℕ) :
    xs.foldl (fun s a=>knownStep (a,s)) (g,acc)=(g,acc+countKnown g xs) := by
  induction xs generalizing acc with
  | nil=>simp
  | cons a as ih=>
    rw [List.foldl_cons]
    change as.foldl (fun s a=>knownStep (a,s)) (g,acc+(if known g a then 1 else 0))=_
    rw [ih,countKnown_cons,Nat.add_assoc]
noncomputable def knownStepP : Procedure (prodCode refCode (prodCode graphCode unaryCode))
    (prodCode graphCode unaryCode) knownStep := by
  let a:=first refCode (prodCode graphCode unaryCode)
  let rest:=second refCode (prodCode graphCode unaryCode)
  let g:=(first graphCode unaryCode).comp rest
  let acc:=(second graphCode unaryCode).comp rest
  let test:=knownP.comp (g.pair a)
  exact (conditional test (g.pair (unarySuccessor.comp acc)) rest).congrFun (by
    intro x
    unfold knownStep
    split <;> simp_all)
noncomputable def countKnownUnaryP : Procedure (prodCode graphCode (listCode refCode)) unaryCode
    (fun x=>countKnown x.1 x.2) := by
  let fold:=foldList (0,false) knownStepP (Polynomial.C 2*Polynomial.X) (by
    rintro xs ⟨g,acc⟩ i
    rw [knownStep_fold]
    have hh : countKnown g (xs.take i)≤xs.length :=
      (List.length_filter_le _ _).trans (by simp only [List.length_take];omega)
    have hc:=list_length_le_code refCode xs
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega)
  let g:=first graphCode (listCode refCode)
  let xs:=second graphCode (listCode refCode)
  exact ((second graphCode unaryCode).comp (fold.comp (xs.pair
    (g.pair (Procedure.constant _ unaryCode 0))))).congrFun (by
      intro x
      change (x.2.foldl (fun s a=>knownStep (a,s)) (x.1,0)).2=countKnown x.1 x.2
      rw [knownStep_fold,Nat.zero_add])
noncomputable def countKnownP : Procedure (prodCode graphCode (listCode refCode)) Nat.bits
    (fun x=>countKnown x.1 x.2) := unaryToBits.comp countKnownUnaryP
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGAddWrapper.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def initializeAddData (s : AddData) : AddData:=⟨s.budget,s.graph,s.lhs,s.rhs,0,(0,false),[]⟩
lemma initializeAdd_ok (s : AddState) : AddOK (initializeAddData s.val) := by
  exact ⟨s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,
    ⟨Nat.zero_le _,by intro a ha;cases ha⟩⟩
def initializeAdd (s : AddState) : AddState:=⟨initializeAddData s.val,initializeAdd_ok s⟩
def swapAddData (s : AddData) : AddData:=⟨s.budget,s.graph,s.rhs,s.lhs,s.curr,s.cin,s.output⟩
def swapAdd (s : AddState) : AddState:=⟨swapAddData s.val,
  ⟨s.property.1,s.property.2.2.1,s.property.2.1,s.property.2.2.2⟩⟩
def addBlastState (s : AddState) : AddState:=(addStep^[s.val.lhs.length]) (initializeAdd s)
def addState (s : AddState) : AddState:=
  if countKnown s.val.graph s.val.lhs<countKnown s.val.graph s.val.rhs then
    addBlastState s else addBlastState (swapAdd s)
lemma addBlastState_value (s : AddState) :
    ((addBlastState s).val.graph,(addBlastState s).val.output)=addBlast s.val.graph s.val.lhs s.val.rhs :=
  addStep_iterate_loop (initializeAdd s) s.val.lhs.length
lemma addState_value (s : AddState) :
    ((addState s).val.graph,(addState s).val.output)=add s.val.graph s.val.lhs s.val.rhs := by
  unfold addState add
  split <;> exact addBlastState_value _
lemma addBlastState_budget (s : AddState) :
    (addBlastState s).val.budget=s.val.budget+13*s.val.lhs.length :=
  addStep_iterate_budget (initializeAdd s) s.val.lhs.length
lemma addState_budget (s : AddState) : (addState s).val.budget≤14*s.val.budget := by
  unfold addState
  split
  · rw [addBlastState_budget];have:=s.property.2.1.1;omega
  · rw [addBlastState_budget];change s.val.budget+13*s.val.rhs.length≤_
    have:=s.property.2.2.1.1;omega

namespace Emission
noncomputable def listUnaryLength {α : Type} (ea : α→List Bool) (d : α) :
    Procedure (listCode ea) unaryCode List.length := by
  let step:=unarySuccessor.comp (second ea unaryCode)
  let rep:=foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _=>n+1) n)).length≤_
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have hh:=list_length_le_code ea xs
    omega)
  let start:=(identity (listCode ea)).pair (Procedure.constant (listCode ea) unaryCode 0)
  exact (rep.comp start).congrFun (by
    intro xs;simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)
noncomputable def initializeAddDataP : Procedure addDataCode addDataCode initializeAddData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addLhsP.pair (addRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).congrFun (by intro x;rfl)
noncomputable def initializeAddP : Procedure addStateCode addStateCode initializeAdd :=
  (initializeAddDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def swapAddDataP : Procedure addDataCode addDataCode swapAddData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addRhsP.pair
    (addLhsP.pair (addCurrP.pair (addCinP.pair addOutputP))))))).congrFun (by intro x;rfl)
noncomputable def swapAddP : Procedure addStateCode addStateCode swapAdd :=
  (swapAddDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def addBlastStateP : Procedure addStateCode addStateCode addBlastState :=
  addIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeAddP)
noncomputable def addStateP : Procedure addStateCode addStateCode addState := by
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  let lk:=countKnownP.comp (g.pair lhs)
  let rk:=countKnownP.comp (g.pair rhs)
  let test:=binaryLt.comp (lk.pair rk)
  exact (conditional test addBlastStateP (addBlastStateP.comp swapAddP)).congrFun (by
    intro s;unfold addState
    split <;> simp_all)
noncomputable def addP : Procedure addStateCode (prodCode graphCode (listCode refCode))
    (fun s=>add s.val.graph s.val.lhs s.val.rhs) :=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp addStateP).congrFun addState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackListMapWith.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β γ : Type}
lemma map_range_getD (xs : List β) (d : β) (f : β→γ) :
    (List.range xs.length).map (fun i=>f ((xs.drop i).headD d))=xs.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_range]
    have hi : i<xs.length:=by simpa using h1
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→β→γ}
noncomputable def listMapWith (d : β) (e : γ)
    (p : Procedure (prodCode ea eb) ec (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea (listCode eb)) (listCode ec) (fun x=>x.2.map (f x.1)) := by
  let i:=unaryToBits.comp (first unaryCode (prodCode ea (listCode eb)))
  let env:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp env
  let xs:=(second ea (listCode eb)).comp env
  let get:=(listGet eb d).comp (i.pair xs)
  let step:=p.comp (a.pair get)
  let len:=(NativeAIG.Emission.listUnaryLength eb d).comp (second ea (listCode eb))
  exact ((tabulate (f:=fun (env : α×List β) i=>f env.1 ((env.2.drop i).headD d)) e step).comp (len.pair (identity (prodCode ea (listCode eb))))).congrFun (by
    intro x;exact map_range_getD x.2 d (f x.1))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionProcedures.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def nodeView : Node→ℕ×Bool×ℕ×ℕ
  | .constant b=>(0,b,0,0)
  | .copy i=>(1,false,i,0)
  | .neg i=>(2,false,i,0)
  | .conj i j=>(3,false,i,j)
def nodePayload:=prodCode Nat.bits (prodCode boolCode (prodCode Nat.bits Nat.bits))
def nodeCode (o : Node) : List Bool:=nodePayload (nodeView o)
def dataView (a : Data) := (a.inputs,a.nodes,a.outputs)
def dataPayload:=prodCode Nat.bits (prodCode (listCode nodeCode) (listCode Nat.bits))
def dataCode (a : Data) : List Bool:=dataPayload (dataView a)

namespace Emission
noncomputable def nodeViewP : Procedure nodeCode nodePayload nodeView:=
  (identity nodePayload).precompose nodeView
noncomputable def nodeTagP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).1):=
  (first Nat.bits _).comp nodeViewP
noncomputable def nodeBoolP : Procedure nodeCode boolCode (fun o=>(nodeView o).2.1):=
  (first boolCode _).comp ((second Nat.bits _).comp nodeViewP)
noncomputable def nodeLhsP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).2.2.1):=
  (first Nat.bits Nat.bits).comp ((second boolCode _).comp ((second Nat.bits _).comp nodeViewP))
noncomputable def nodeRhsP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).2.2.2):=
  (second Nat.bits Nat.bits).comp ((second boolCode _).comp ((second Nat.bits _).comp nodeViewP))
noncomputable def nodeConstP : Procedure boolCode nodeCode Node.constant:=
  ((Procedure.constant boolCode Nat.bits 0).pair ((identity boolCode).pair
    ((Procedure.constant boolCode Nat.bits 0).pair (Procedure.constant boolCode Nat.bits 0)))).result (by intro b;rfl)
noncomputable def nodeCopyP : Procedure Nat.bits nodeCode Node.copy:=
  ((Procedure.constant Nat.bits Nat.bits 1).pair ((Procedure.constant Nat.bits boolCode false).pair
    ((identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 0)))).result (by intro i;rfl)
noncomputable def nodeNegP : Procedure Nat.bits nodeCode Node.neg:=
  ((Procedure.constant Nat.bits Nat.bits 2).pair ((Procedure.constant Nat.bits boolCode false).pair
    ((identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 0)))).result (by intro i;rfl)
noncomputable def nodeConjP : Procedure (prodCode Nat.bits Nat.bits) nodeCode (fun x=>Node.conj x.1 x.2):=
  ((Procedure.constant _ Nat.bits 3).pair ((Procedure.constant _ boolCode false).pair (identity _))).result (by intro x;rfl)

noncomputable def nodeMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea nodeCode) nodeCode (fun x=>x.2.map (f x.1)) := by
  let a:=first ea nodeCode
  let o:=second ea nodeCode
  let tag:=nodeTagP.comp o
  let isTag:=(fun k=>binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits k)))
  let lhs:=p.comp (a.pair (nodeLhsP.comp o))
  let rhs:=p.comp (a.pair (nodeRhsP.comp o))
  let b:=nodeConstP.comp (nodeBoolP.comp o)
  let c:=nodeCopyP.comp lhs
  let n:=nodeNegP.comp lhs
  let g:=nodeConjP.comp (lhs.pair rhs)
  exact (conditional (isTag 0) b (conditional (isTag 1) c (conditional (isTag 2) n g))).congrFun (by
    rintro ⟨a,o⟩;cases o <;> rfl)
noncomputable def dataViewP : Procedure dataCode dataPayload dataView:=
  (identity dataPayload).precompose dataView
noncomputable def dataInputP : Procedure dataCode Nat.bits Data.inputs:=
  (first Nat.bits _).comp dataViewP
noncomputable def dataNodesP : Procedure dataCode (listCode nodeCode) Data.nodes:=
  (first (listCode nodeCode) _).comp ((second Nat.bits _).comp dataViewP)
noncomputable def dataOutputsP : Procedure dataCode (listCode Nat.bits) Data.outputs:=
  (second (listCode nodeCode) _).comp ((second Nat.bits _).comp dataViewP)
noncomputable def dataPackP : Procedure dataPayload dataCode (fun x=>Data.mk x.1 x.2.1 x.2.2):=
  (identity dataPayload).result (by intro x;rfl)
noncomputable def dataWidthP : Procedure dataCode Nat.bits (fun a=>a.inputs+a.nodes.length):=
  binaryAdd.comp (dataInputP.pair ((listLength nodeCode (.constant false)).comp dataNodesP))

abbrev indexCode:=prodCode Nat.bits (listCode Nat.bits)
noncomputable def attachIndexP : Procedure (prodCode indexCode Nat.bits) Nat.bits
    (fun x=>attachRawIndex x.1.1 x.1.2 x.2) := by
  let env:=first indexCode Nat.bits
  let width:=(first Nat.bits (listCode Nat.bits)).comp env
  let rho:=(second Nat.bits (listCode Nat.bits)).comp env
  let i:=second indexCode Nat.bits
  let len:=(listLength Nat.bits 0).comp rho
  let off:=binarySub.comp (i.pair len)
  let test:=binaryLt.comp (i.pair len)
  let get:=(listGet Nat.bits 0).comp (i.pair rho)
  exact (conditional test get (binaryAdd.comp (width.pair off))).congrFun (by
    intro x;unfold attachRawIndex;split <;> simp_all)
noncomputable def compP : Procedure (prodCode dataCode dataCode) dataCode
    (fun x=>comp x.1 x.2) := by
  let a:=first dataCode dataCode
  let b:=second dataCode dataCode
  let env:=(dataWidthP.comp a).pair (dataOutputsP.comp a)
  let ns:=(listMapWith (f:=fun (e : ℕ×List ℕ) (o : Node)=>o.map (attachRawIndex e.1 e.2)) (Node.constant false) (Node.constant false) (nodeMapWith (f:=fun (e : ℕ×List ℕ) i=>attachRawIndex e.1 e.2 i) attachIndexP)).comp
    (env.pair (dataNodesP.comp b))
  let nodes:=(listAppend nodeCode (.constant false)).comp ((dataNodesP.comp a).pair ns)
  let outs:=(listMapWith (f:=fun (e : ℕ×List ℕ) i=>attachRawIndex e.1 e.2 i) 0 0 attachIndexP).comp (env.pair (dataOutputsP.comp b))
  exact (dataPackP.comp ((dataInputP.comp a).pair (nodes.pair outs))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionBasic.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def bit (n i : ℕ) : Data:=select n [i]
def constant (n : ℕ) (b : Bool) : Data:=node n (.constant b)
def bnot (a : Data) : Data:=comp a (node 1 (.neg 0))
def band (a b : Data) : Data:=comp (pair a b) (node 2 (.conj 0 1))
def bor (a b : Data) : Data:=bnot (band (bnot a) (bnot b))
def bxor (a b : Data) : Data:=bor (band a (bnot b)) (band (bnot a) b)
def mux (c a b : Data) : Data:=bor (band c a) (band (bnot c) b)
lemma erase_bit {n : ℕ} (i : Fin n) : erase (BooleanNetwork.bit i)=bit n i.val := by
  simp [BooleanNetwork.bit,erase_select,bit,List.ofFn_succ]
lemma erase_constant {n : ℕ} (b : Bool) : erase (BooleanNetwork.constant (n:=n) b)=constant n b:=
  erase_node _
lemma erase_bnot {n : ℕ} (a : BooleanNetwork n 1) : erase a.bnot=bnot (erase a):=by
  rw [BooleanNetwork.bnot,erase_comp,erase_node];rfl
lemma erase_band {n : ℕ} (a b : BooleanNetwork n 1) : erase (a.band b)=band (erase a) (erase b):=by
  rw [BooleanNetwork.band,erase_comp,erase_pair,erase_node];rfl
lemma erase_bor {n : ℕ} (a b : BooleanNetwork n 1) : erase (a.bor b)=bor (erase a) (erase b):=by
  rw [BooleanNetwork.bor,erase_bnot,erase_band,erase_bnot,erase_bnot];rfl
lemma erase_bxor {n : ℕ} (a b : BooleanNetwork n 1) : erase (a.bxor b)=bxor (erase a) (erase b):=by
  rw [BooleanNetwork.bxor,erase_bor,erase_band,erase_band,erase_bnot,erase_bnot];rfl
lemma erase_mux {n : ℕ} (c a b : BooleanNetwork n 1) : erase (BooleanNetwork.mux c a b)=
    mux (erase c) (erase a) (erase b):=by
  rw [BooleanNetwork.mux,erase_bor,erase_band,erase_band,erase_bnot];rfl

namespace Emission
noncomputable def selectP : Procedure (prodCode Nat.bits (listCode Nat.bits)) dataCode
    (fun x=>select x.1 x.2):=
  (dataPackP.comp ((first Nat.bits (listCode Nat.bits)).pair
    ((Procedure.constant _ (listCode nodeCode) []).pair (second Nat.bits (listCode Nat.bits))))).congrFun (by intro x;rfl)
noncomputable def nodeP : Procedure (prodCode Nat.bits nodeCode) dataCode (fun x=>node x.1 x.2):=by
  let n:=first Nat.bits nodeCode
  let o:=second Nat.bits nodeCode
  let ns:=(listCons nodeCode).comp (o.pair (Procedure.constant _ (listCode nodeCode) []))
  let os:=(listCons Nat.bits).comp (n.pair (Procedure.constant _ (listCode Nat.bits) []))
  exact (dataPackP.comp (n.pair (ns.pair os))).congrFun (by intro x;rfl)
noncomputable def pairIndexP : Procedure (prodCode (prodCode Nat.bits Nat.bits) Nat.bits) Nat.bits
    (fun x=>pairIndex x.1.1 x.1.2 x.2):=by
  let e:=first (prodCode Nat.bits Nat.bits) Nat.bits
  let n:=(first Nat.bits Nat.bits).comp e
  let w:=(second Nat.bits Nat.bits).comp e
  let i:=second (prodCode Nat.bits Nat.bits) Nat.bits
  exact (conditional (binaryLt.comp (i.pair n)) i (binaryAdd.comp (w.pair (binarySub.comp (i.pair n))))).congrFun (by
    intro x;unfold pairIndex;split <;> simp_all)
noncomputable def pairP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>pair x.1 x.2):=by
  let a:=first dataCode dataCode
  let b:=second dataCode dataCode
  let env:=(dataInputP.comp a).pair (dataWidthP.comp a)
  let mp:=nodeMapWith (f:=fun (e : ℕ×ℕ) i=>pairIndex e.1 e.2 i) pairIndexP
  let ns:=(listMapWith (f:=fun (e : ℕ×ℕ) (o : Node)=>o.map (pairIndex e.1 e.2)) (.constant false) (.constant false) mp).comp
    (env.pair (dataNodesP.comp b))
  let os:=(listMapWith (f:=fun (e : ℕ×ℕ) i=>pairIndex e.1 e.2 i) 0 0 pairIndexP).comp
    (env.pair (dataOutputsP.comp b))
  let nn:=(listAppend nodeCode (.constant false)).comp ((dataNodesP.comp a).pair ns)
  let oo:=(listAppend Nat.bits 0).comp ((dataOutputsP.comp a).pair os)
  exact (dataPackP.comp ((dataInputP.comp a).pair (nn.pair oo))).congrFun (by intro x;rfl)
noncomputable def bitP : Procedure (prodCode Nat.bits Nat.bits) dataCode (fun x=>bit x.1 x.2):=
  (selectP.comp ((first Nat.bits Nat.bits).pair
    ((listCons Nat.bits).comp ((second Nat.bits Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))))).congrFun (by intro x;rfl)
noncomputable def constantP : Procedure (prodCode Nat.bits boolCode) dataCode (fun x=>constant x.1 x.2):=
  (nodeP.comp ((first Nat.bits boolCode).pair (nodeConstP.comp (second Nat.bits boolCode)))).congrFun (by intro x;rfl)
noncomputable def bnotP : Procedure dataCode dataCode bnot:=
  compP.comp ((identity dataCode).pair (Procedure.constant _ dataCode (node 1 (.neg 0))))
noncomputable def bandP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>band x.1 x.2):=
  compP.comp (pairP.pair (Procedure.constant _ dataCode (node 2 (.conj 0 1))))
noncomputable def borP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>bor x.1 x.2):=
  bnotP.comp (bandP.comp ((bnotP.comp (first dataCode dataCode)).pair (bnotP.comp (second dataCode dataCode))))
noncomputable def bxorP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>bxor x.1 x.2):=by
  let a:=first dataCode dataCode
  let b:=second dataCode dataCode
  exact borP.comp ((bandP.comp (a.pair (bnotP.comp b))).pair (bandP.comp ((bnotP.comp a).pair b)))
noncomputable def muxP : Procedure (prodCode dataCode (prodCode dataCode dataCode)) dataCode
    (fun x=>mux x.1 x.2.1 x.2.2):=by
  let c:=first dataCode (prodCode dataCode dataCode)
  let a:=(first dataCode dataCode).comp (second dataCode (prodCode dataCode dataCode))
  let b:=(second dataCode dataCode).comp (second dataCode (prodCode dataCode dataCode))
  exact borP.comp ((bandP.comp (c.pair a)).pair (bandP.comp ((bnotP.comp c).pair b)))
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionBounds.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def Node.Bound (B : ℕ) : Node→Prop
  | .constant _=>True
  | .copy i=>i≤B
  | .neg i=>i≤B
  | .conj i j=>i≤B ∧ j≤B
lemma Node.Bound.mono {A B : ℕ} {o : Node} (h : o.Bound A) (hab : A≤B) : o.Bound B:=by
  cases o <;> simp only [Node.Bound] at * <;> omega
lemma Node.Bound.map {A B : ℕ} {o : Node} (h : o.Bound A) (f : ℕ→ℕ)
    (hf : ∀i,i≤A→f i≤B) : (o.map f).Bound B:=by
  cases o with
  | constant=>trivial
  | copy i=>exact hf i h
  | neg i=>exact hf i h
  | conj i j=>exact ⟨hf i h.1,hf j h.2⟩
def Data.width (a : Data) : ℕ:=a.inputs+a.nodes.length
def Data.mass (a : Data) : ℕ:=a.width+a.outputs.length
def Data.Valid (a : Data) : Prop := (∀o∈a.nodes,o.Bound a.width) ∧ (∀i∈a.outputs,i≤a.width)
lemma eraseNode_bound {n : ℕ} (o : BoolNode n) : (eraseNode o).Bound n:=by
  cases o <;> simp only [eraseNode,Node.Bound] <;> omega
lemma eraseNet_nodes_bound {n k : ℕ} (p : BoolNet n k) : ∀o∈eraseNet p,o.Bound k:=by
  induction p with
  | input=>intro o ho;cases ho
  | @add k p op ih=>
    intro o ho
    simp only [eraseNet,List.mem_append,List.mem_singleton] at ho
    rcases ho with ho|rfl
    · exact (ih _ ho).mono (by omega)
    · exact (eraseNode_bound op).mono (by omega)
lemma erase_valid {n m : ℕ} (a : BooleanNetwork n m) : (erase a).Valid:=by
  have hw : (erase a).width=a.width:=by
    change n+(eraseNet a.net).length=a.width
    rw [eraseNet_length];exact a.net.width_eq.symm
  constructor
  · rw [hw];exact eraseNet_nodes_bound a.net
  · intro i hi
    change i∈List.ofFn (fun j=>(a.output j).val) at hi
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
    rw [hw];exact Nat.le_of_lt (a.output j).isLt
lemma valid_select (n : ℕ) (xs : List ℕ) (h : ∀i∈xs,i≤n) : (select n xs).Valid:=
by
  constructor
  · intro o ho;cases ho
  · exact h
lemma valid_node (n : ℕ) (o : Node) (h : o.Bound n) : (node n o).Valid:=by
  constructor
  · intro p hp
    have he : p=o:=by simpa only [node,List.mem_singleton] using hp
    subst p
    exact h.mono (by simp [Data.width,node])
  · intro i hi
    have he : i=n:=by simpa only [node,List.mem_singleton] using hi
    subst i;simp [Data.width,node]
lemma pairIndex_bound (n wa wb i : ℕ) (hn : n≤wa) (hi : i≤n+wb) :
    pairIndex n wa i≤wa+wb:=by unfold pairIndex;split <;> omega
lemma pair_valid {a b : Data} (ha : a.Valid) (hb : b.Valid) (he : a.inputs=b.inputs) : (pair a b).Valid:=by
  have hw : (pair a b).width=a.width+b.nodes.length:=by simp [Data.width,pair,Nat.add_assoc]
  have hf : ∀i,i≤b.width→pairIndex a.inputs a.width i≤(pair a b).width:=by
    intro i hi
    rw [hw]
    apply pairIndex_bound
    · exact Nat.le_add_right _ _
    · simpa only [Data.width,←he] using hi
  constructor
  · intro o ho
    simp only [pair,List.mem_append,List.mem_map] at ho
    rcases ho with ho|⟨p,hp,rfl⟩
    · exact (ha.1 _ ho).mono (by rw [hw];omega)
    · exact (hb.1 _ hp).map _ hf
  · intro i hi
    simp only [pair,List.mem_append,List.mem_map] at hi
    rcases hi with hi|⟨j,hj,rfl⟩
    · exact (ha.2 _ hi).trans (by rw [hw];omega)
    · exact hf _ (hb.2 _ hj)
lemma headD_drop_bound {xs : List ℕ} {B : ℕ} (h : ∀j∈xs,j≤B) (i : ℕ) :
    (xs.drop i).headD 0≤B:=by
  cases hh : (xs.drop i).head? with
  | none=>simp [List.headD_eq_head?_getD,hh]
  | some j=>
    rw [List.headD_eq_head?_getD,hh,Option.getD_some]
    exact h _ (List.mem_of_mem_drop (List.mem_of_head? hh))
lemma attachRawIndex_bound {xs : List ℕ} {wa wb : ℕ} (h : ∀j∈xs,j≤wa)
    (i : ℕ) (hi : i≤xs.length+wb) : attachRawIndex wa xs i≤wa+wb:=by
  unfold attachRawIndex
  split
  · exact (headD_drop_bound h i).trans (by omega)
  · omega
lemma comp_valid {a b : Data} (ha : a.Valid) (hb : b.Valid) (he : a.outputs.length=b.inputs) :
    (comp a b).Valid:=by
  have hw : (comp a b).width=a.width+b.nodes.length:=by simp [Data.width,comp,Nat.add_assoc]
  have hf : ∀i,i≤b.width→attachRawIndex a.width a.outputs i≤(comp a b).width:=by
    intro i hi
    rw [hw]
    apply attachRawIndex_bound ha.2
    simpa only [Data.width,←he] using hi
  constructor
  · intro o ho
    simp only [comp,List.mem_append,List.mem_map] at ho
    rcases ho with ho|⟨p,hp,rfl⟩
    · exact (ha.1 _ ho).mono (by rw [hw];omega)
    · exact (hb.1 _ hp).map _ hf
  · intro i hi
    simp only [comp,List.mem_map] at hi
    obtain ⟨j,hj,rfl⟩:=hi
    exact hf _ (hb.2 _ hj)
lemma pair_mass (a b : Data) : (pair a b).mass≤a.mass+b.mass:=by
  simp only [Data.mass,Data.width,pair,List.length_append,List.length_map];omega
lemma comp_mass (a b : Data) : (comp a b).mass≤a.mass+b.mass:=by
  simp only [Data.mass,Data.width,comp,List.length_append,List.length_map];omega
lemma nat_bits_length_bound (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
lemma listCode_length_bound {α : Type} (ea : α→List Bool) (xs : List α) (B : ℕ)
    (h : ∀a∈xs,(ea a).length≤B) : (listCode ea xs).length≤xs.length*(2*B+2)+1:=by
  induction xs with
  | nil=>simp [listCode]
  | cons a xs ih=>
    have ha:=h a (by simp)
    have hh:=ih (by intro b hb;exact h b (by simp [hb]))
    simp only [listCode_length_cons,List.length_cons]
    nlinarith
lemma nodeCode_bound {o : Node} {B : ℕ} (h : o.Bound B) : (nodeCode o).length≤8*B+30:=by
  have h0 : (Nat.bits 0).length=0:=rfl
  have h1 : (Nat.bits 1).length=1:=rfl
  have h2 : (Nat.bits 2).length=2:=rfl
  have h3 : (Nat.bits 3).length=2:=rfl
  cases o <;> simp only [Node.Bound] at h
  · simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0]
    omega
  · rename_i i
    have hi:=(nat_bits_length_bound i).trans h
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0,h1]
    omega
  · rename_i i
    have hi:=(nat_bits_length_bound i).trans h
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0,h2]
    omega
  · rename_i i j
    have hi:=(nat_bits_length_bound i).trans h.1
    have hj:=(nat_bits_length_bound j).trans h.2
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h3]
    omega
lemma dataCode_bound {a : Data} {B : ℕ} (ha : a.Valid) (hm : a.mass≤B) :
    (dataCode a).length≤100*(B+1)^2:=by
  have hn : a.inputs≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hw : a.width≤B:=by dsimp [Data.mass] at hm;omega
  have hnl : a.nodes.length≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hol : a.outputs.length≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hb:=(nat_bits_length_bound a.inputs).trans hn
  have hns:=listCode_length_bound nodeCode a.nodes (8*B+30) (fun o ho=>nodeCode_bound ((ha.1 _ ho).mono hw))
  have hos:=listCode_length_bound Nat.bits a.outputs B (fun i hi=>(nat_bits_length_bound i).trans ((ha.2 _ hi).trans hw))
  simp only [dataCode,dataPayload,dataView,prodCode,pairBits_length]
  have h1:=Nat.mul_le_mul_right (2*(8*B+30)+2) hnl
  have h2:=Nat.mul_le_mul_right (2*B+2) hol
  nlinarith
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionPack.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
structure PackData where
  budget : ℕ
  value : Data
abbrev Pack:={s : PackData // s.value.Valid ∧ s.value.mass ≤ s.budget}
def packCode (s : Pack) : List Bool:=prodCode unaryCode dataCode (s.val.budget,s.val.value)
def pairPack (a b : Pack) : Pack:=
  ⟨⟨a.val.budget+b.val.budget,if a.val.value.inputs=b.val.value.inputs then pair a.val.value b.val.value else a.val.value⟩,by
    split
    · rename_i h
      exact ⟨pair_valid a.property.1 b.property.1 h,(pair_mass _ _).trans (Nat.add_le_add a.property.2 b.property.2)⟩
    · exact ⟨a.property.1,a.property.2.trans (Nat.le_add_right _ _)⟩⟩
def compPack (a b : Pack) : Pack:=
  ⟨⟨a.val.budget+b.val.budget,if a.val.value.outputs.length=b.val.value.inputs then comp a.val.value b.val.value else a.val.value⟩,by
    split
    · rename_i h
      exact ⟨comp_valid a.property.1 b.property.1 h,(comp_mass _ _).trans (Nat.add_le_add a.property.2 b.property.2)⟩
    · exact ⟨a.property.1,a.property.2.trans (Nat.le_add_right _ _)⟩⟩
lemma pairPack_inputs (a b : Pack) : (pairPack a b).val.value.inputs=a.val.value.inputs:=by
  unfold pairPack;split <;> rfl
lemma compPack_inputs (a b : Pack) : (compPack a b).val.value.inputs=a.val.value.inputs:=by
  unfold compPack;split <;> rfl
lemma pairPack_value (a b : Pack) (h : a.val.value.inputs=b.val.value.inputs) :
    (pairPack a b).val.value=pair a.val.value b.val.value:=by simp only [pairPack,ite_eq_left h]
lemma compPack_value (a b : Pack) (h : a.val.value.outputs.length=b.val.value.inputs) :
    (compPack a b).val.value=comp a.val.value b.val.value:=by simp only [compPack,ite_eq_left h]
lemma packCode_bound (s : Pack) : (packCode s).length≤104*(s.val.budget+1)^2:=by
  have hh:=dataCode_bound s.property.1 s.property.2
  simp only [packCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
  nlinarith [Nat.zero_le s.val.budget]
lemma packBudget_le_code (s : Pack) : s.val.budget≤(packCode s).length:=by
  simp only [packCode,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
lemma packBudgets_le_code (xs : List Pack) : (xs.map (fun s=>s.val.budget)).sum≤(listCode packCode xs).length:=by
  induction xs with
  | nil=>simp
  | cons s xs ih=>
    have hh:=packBudget_le_code s
    simp only [List.map_cons,List.sum_cons,listCode_length_cons];omega
lemma fold_budget (f : Pack→Pack→Pack) (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget)
    (xs : List Pack) (a : Pack) : (xs.foldl f a).val.budget=a.val.budget+(xs.map (fun s=>s.val.budget)).sum:=by
  induction xs generalizing a with
  | nil=>simp
  | cons s xs ih=>rw [List.foldl_cons,ih,h,List.map_cons,List.sum_cons];omega

def selectPack (n : ℕ) (xs : List ℕ) (h : ∀i∈xs,i≤n) : Pack:=
  ⟨⟨n+xs.length,select n xs⟩,valid_select n xs h,by simp [Data.mass,Data.width,select]⟩
def emptyPack : Pack:=selectPack 0 [] (by simp)
def nodePack (n : ℕ) (o : Node) (h : o.Bound n) : Pack:=
  ⟨⟨n+2,node n o⟩,valid_node n o h,by simp [Data.mass,Data.width,node]⟩
def erasePack {n m : ℕ} (a : BooleanNetwork n m) : Pack:=
  ⟨⟨n+a.net.count+m,erase a⟩,erase_valid a,by simp only [Data.mass,Data.width,erase,eraseNet_length,List.length_ofFn];rfl⟩
namespace Emission
noncomputable def packViewP : Procedure packCode (prodCode unaryCode dataCode)
    (fun s=>(s.val.budget,s.val.value)):=(identity _).precompose _
noncomputable def packBudgetP : Procedure packCode unaryCode (fun s=>s.val.budget):=
  (first unaryCode dataCode).comp packViewP
noncomputable def packValueP : Procedure packCode dataCode (fun s=>s.val.value):=
  (second unaryCode dataCode).comp packViewP
noncomputable def pairPackP : Procedure (prodCode packCode packCode) packCode (fun x=>pairPack x.1 x.2):=by
  let a:=first packCode packCode
  let b:=second packCode packCode
  let av:=packValueP.comp a
  let bv:=packValueP.comp b
  let test:=binaryEq.comp ((dataInputP.comp av).pair (dataInputP.comp bv))
  let val:=conditional test (pairP.comp (av.pair bv)) av
  let bud:=unaryAdd.comp ((packBudgetP.comp a).pair (packBudgetP.comp b))
  exact (bud.pair val).result (by intro x;unfold pairPack packCode;split <;> simp_all)
noncomputable def compPackP : Procedure (prodCode packCode packCode) packCode (fun x=>compPack x.1 x.2):=by
  let a:=first packCode packCode
  let b:=second packCode packCode
  let av:=packValueP.comp a
  let bv:=packValueP.comp b
  let len:=(listLength Nat.bits 0).comp (dataOutputsP.comp av)
  let test:=binaryEq.comp (len.pair (dataInputP.comp bv))
  let val:=conditional test (compP.comp (av.pair bv)) av
  let bud:=unaryAdd.comp ((packBudgetP.comp a).pair (packBudgetP.comp b))
  exact (bud.pair val).result (by intro x;unfold compPack packCode;split <;> simp_all)
noncomputable def foldPack {f : Pack→Pack→Pack}
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget)
    (p : Procedure (prodCode packCode packCode) packCode (fun x=>f x.1 x.2)) :
    Procedure (prodCode (listCode packCode) packCode) packCode (fun x=>x.1.foldl f x.2):=
  foldList emptyPack (p.comp ((second packCode packCode).pair (first packCode packCode)))
    (Polynomial.C 104*(Polynomial.X+1)^2) (by
      intro xs a i
      have hh:=packCode_bound ((xs.take i).foldl f a)
      rw [fold_budget f h] at hh
      have hb:=packBudget_le_code a
      have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
      have hp:=Nat.pow_le_pow_left (by omega :
        a.val.budget+((xs.take i).map (fun s=>s.val.budget)).sum+1≤
          (listCode packCode xs).length+(packCode a).length+1) 2
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one]
      change (packCode ((xs.take i).foldl f a)).length≤104*((listCode packCode xs).length+(packCode a).length+1)^2
      exact hh.trans (Nat.mul_le_mul_left _ hp))
noncomputable def foldPairP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl pairPack x.2):=foldPack (by intros;rfl) pairPackP
noncomputable def foldCompP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl compPack x.2):=foldPack (by intros;rfl) compPackP
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkStackCompiler.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
abbrev StackOp := Pack ⊕ Bool
def stackOpCode : StackOp→List Bool:=sumCode packCode boolCode
def stackStep (o : StackOp) (s : List Pack) : List Pack:=match o with
  | .inl a=>a::s
  | .inr b=>let a:=s.tail.headD emptyPack;let c:=s.headD emptyPack
    (if b then compPack a c else pairPack a c)::s.tail.tail
def stackBudget (s : List Pack) : ℕ:=(s.map (fun a=>a.val.budget)).sum
def opWeight : StackOp→ℕ | .inl a=>a.val.budget | .inr _=>0
lemma stackStep_budget (o : StackOp) (s : List Pack) :
    stackBudget (stackStep o s)≤ stackBudget s+opWeight o:=by
  cases o with
  | inl a=>simp [stackStep,stackBudget,opWeight,Nat.add_comm]
  | inr b=>
    cases s with
    | nil=>cases b <;> simp [stackStep,stackBudget,opWeight,emptyPack,selectPack,pairPack,compPack]
    | cons a s=>cases s with
      | nil=>cases b <;> simp [stackStep,stackBudget,opWeight,emptyPack,selectPack,pairPack,compPack]
      | cons c s=>cases b <;> simp [stackStep,stackBudget,opWeight,pairPack,compPack,Nat.add_comm,Nat.add_assoc]
lemma stackStep_length (o : StackOp) (s : List Pack) : (stackStep o s).length≤ s.length+1:=by
  cases o <;> simp [stackStep,List.length_tail];omega
lemma stackFold_budget (ops : List StackOp) (s : List Pack) :
    stackBudget (ops.foldl (fun s o=>stackStep o s) s)≤ stackBudget s+(ops.map opWeight).sum:=by
  induction ops generalizing s with
  | nil=>simp
  | cons o ops ih=>
    have hs:=stackStep_budget o s
    have hh:=ih (stackStep o s)
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    omega
lemma stackFold_length (ops : List StackOp) (s : List Pack) :
    (ops.foldl (fun s o=>stackStep o s) s).length≤ s.length+ops.length:=by
  induction ops generalizing s with
  | nil=>simp
  | cons o ops ih=>
    have hs:=stackStep_length o s
    have hh:=ih (stackStep o s)
    simp only [List.foldl_cons,List.length_cons];omega
lemma opWeight_le_code (o : StackOp) : opWeight o≤(stackOpCode o).length:=by
  cases o with
  | inl a=>have h:=packBudget_le_code a;simp only [stackOpCode,sumCode,List.length_cons,opWeight];omega
  | inr b=>simp [opWeight]
lemma opWeights_le_code (ops : List StackOp) : (ops.map opWeight).sum≤(listCode stackOpCode ops).length:=by
  induction ops with
  | nil=>simp
  | cons o ops ih=>
    have hh:=opWeight_le_code o
    simp only [List.map_cons,List.sum_cons,listCode_length_cons];omega
lemma stackCode_bound (s : List Pack) :
    (listCode packCode s).length≤ s.length*(208*(stackBudget s+1)^2+2)+1:=by
  have hh:=listCode_length_bound packCode s (104*(stackBudget s+1)^2) (by
    intro a ha
    have hb : a.val.budget≤ stackBudget s:=List.single_le_sum (fun _ _=>Nat.zero_le _) _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    exact (packCode_bound a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
  convert hh using 1; ring

end ExactQuantumFactoring.NetworkEmission
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkEmissionVector.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def emptyAt (n : ℕ) : Pack:=selectPack n [] (by simp)
def bitPack (n i : ℕ) : Pack:=selectPack n [min n i] (by simp)
def constantPack (n : ℕ) (b : Bool) : Pack:=nodePack n (.constant b) trivial
def bnotPack (a : Pack) : Pack:=compPack a (nodePack 1 (.neg 0) (by simp [Node.Bound]))
def bandPack (a b : Pack) : Pack:=compPack (pairPack a b) (nodePack 2 (.conj 0 1) (by simp [Node.Bound]))
def vectorPack (n : ℕ) (xs : List Pack) : Pack:=xs.foldl pairPack (emptyAt n)
lemma vectorPack_inputs (n : ℕ) (xs : List Pack) : (vectorPack n xs).val.value.inputs=n:=by
  unfold vectorPack
  suffices ∀a:Pack,(xs.foldl pairPack a).val.value.inputs=a.val.value.inputs by exact this _
  intro a
  induction xs generalizing a with
  | nil=>rfl
  | cons b xs ih=>rw [List.foldl_cons,ih,pairPack_inputs]
lemma vectorPack_value {n m : ℕ} (f : Fin m→BooleanNetwork n 1) (p : Fin m→Pack)
    (hp : ∀i,(p i).val.value=erase (f i)) :
    (vectorPack n (List.ofFn p)).val.value=erase (BooleanNetwork.vector f):=by
  induction m with
  | zero=>rfl
  | succ m ih=>
    rw [BooleanNetwork.vector,erase_pair,List.ofFn_succ_last]
    change ((List.ofFn (fun i:Fin m=>p i.castSucc)++[p (Fin.last m)]).foldl pairPack (emptyAt n)).val.value=_
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (pairPack (vectorPack n (List.ofFn fun i:Fin m=>p i.castSucc)) (p (Fin.last m))).val.value=_
    rw [pairPack_value,ih (fun i=>f i.castSucc) (fun i=>p i.castSucc) (fun i=>hp i.castSucc),hp]
    rw [vectorPack_inputs,hp];rfl
lemma bitPack_value {n : ℕ} (i : Fin n) : (bitPack n i.val).val.value=erase (BooleanNetwork.bit i):=by
  rw [erase_bit]
  simp only [bitPack,selectPack,min_eq_right (Nat.le_of_lt i.isLt),bit]
lemma constantPack_value (n : ℕ) (b : Bool) : (constantPack n b).val.value=erase (BooleanNetwork.constant (n:=n) b):=by
  rw [erase_constant];rfl
lemma bnotPack_value {n : ℕ} (a : Pack) (f : BooleanNetwork n 1) (h : a.val.value=erase f) :
    (bnotPack a).val.value=erase f.bnot:=by
  rw [erase_bnot,bnotPack,compPack_value]
  · rw [h];rfl
  · rw [h];simp [erase,nodePack,node]
lemma bandPack_value {n : ℕ} (a b : Pack) (f g : BooleanNetwork n 1)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (bandPack a b).val.value=erase (f.band g):=by
  have hp : (pairPack a b).val.value=erase (f.pair g):=by
    rw [pairPack_value,ha,hb,erase_pair]
    rw [ha,hb];rfl
  rw [erase_band,bandPack,compPack_value]
  · rw [hp,erase_pair];rfl
  · rw [hp];simp [erase,nodePack,node]
namespace Emission
noncomputable def emptyAtP : Procedure unaryCode packCode emptyAt:=by
  let v:=selectP.comp (unaryToBits.pair (Procedure.constant _ (listCode Nat.bits) []))
  exact ((identity unaryCode).pair v).result (by intro n;rfl)
noncomputable def bitPackP : Procedure (prodCode unaryCode Nat.bits) packCode (fun x=>bitPack x.1 x.2):=by
  let n:=first unaryCode Nat.bits
  let i:=second unaryCode Nat.bits
  let nb:=unaryToBits.comp n
  let idx:=conditional (binaryLt.comp (nb.pair i)) nb i
  let v:=bitP.comp (nb.pair idx)
  exact ((unarySuccessor.comp n).pair v).result (by
    intro x
    simp only [Function.comp_apply,id_eq,decide_eq_true_eq]
    by_cases h : x.1<x.2
    · simp only [h,↓reduceIte,bitPack,selectPack,packCode,bit,prodCode,
        min_eq_left (Nat.le_of_lt h),List.length_singleton,Nat.succ_eq_add_one]
    · simp only [h,↓reduceIte,bitPack,selectPack,packCode,bit,prodCode,
        min_eq_right (by omega : x.2≤x.1),List.length_singleton,Nat.succ_eq_add_one])
noncomputable def constantPackP : Procedure (prodCode unaryCode boolCode) packCode (fun x=>constantPack x.1 x.2):=by
  let n:=first unaryCode boolCode
  let v:=constantP.comp ((unaryToBits.comp n).pair (second unaryCode boolCode))
  let b:=unaryAdd.comp (n.pair (Procedure.constant _ unaryCode 2))
  exact (b.pair v).result (by intro x;rfl)
noncomputable def bnotPackP : Procedure packCode packCode bnotPack:=
  compPackP.comp ((identity packCode).pair (Procedure.constant _ packCode (nodePack 1 (.neg 0) (by simp [Node.Bound]))))
noncomputable def bandPackP : Procedure (prodCode packCode packCode) packCode (fun x=>bandPack x.1 x.2):=
  compPackP.comp (pairPackP.pair (Procedure.constant _ packCode (nodePack 2 (.conj 0 1) (by simp [Node.Bound]))))
noncomputable def vectorPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>vectorPack x.1 x.2):=
  foldPairP.comp ((second unaryCode (listCode packCode)).pair (emptyAtP.comp (first unaryCode (listCode packCode))))
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RawListRange.lean =====
namespace OAI



section
namespace ExactQuantumFactoring
lemma ofFn_val_range (n : ℕ) : (List.ofFn fun i : Fin n => i.val) = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackTestBit.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def dropWord : Procedure (prodCode unaryCode (id : List Bool→List Bool)) id
    (fun x=>x.2.drop x.1):=by
  refine (tail.iterate Polynomial.X ?_).congrFun ?_
  · intro n xs i hi
    have h : (List.tail^[i] xs).length≤xs.length:=by
      induction i with
      | zero=>rfl
      | succ i ih=>
        rw [Function.iterate_succ_apply']
        simp only [List.length_tail]
        omega
    simp only [Polynomial.eval_X,id_eq]
    exact h.trans (Nat.le_add_left _ _)
  · rintro ⟨n,xs⟩
    change List.tail^[n] xs=xs.drop n
    induction n with
    | zero=>rfl
    | succ n ih=> rw [Function.iterate_succ_apply',ih,List.tail_drop]
noncomputable def testBit : Procedure (prodCode Nat.bits unaryCode) boolCode
    (fun x=>x.1.testBit x.2):=by
  let p:=head.comp (dropWord.comp
    ((second Nat.bits unaryCode).pair ((identity (id : List Bool→List Bool)).precompose Nat.bits |>.comp
      (first Nat.bits unaryCode))))
  refine p.congrFun ?_
  intro x
  change (x.1.bits.drop x.2).headD false=x.1.testBit x.2
  rw [Nat.testBit_eq_inth,List.headD_eq_head?_getD,List.head?_drop]
  rfl
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
