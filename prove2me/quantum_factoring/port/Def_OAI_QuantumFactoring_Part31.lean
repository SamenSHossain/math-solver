/-
Exact quantum factoring development (port of OpenAI's formalization), part 31 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: NativeAIGExtend.lean, NativeAIGZipFold.lean, NativeAIGDiv.lean, NativeAIGMod.lean, NativeAIGInputs.lean, NativeAIGSubProcedure.lean, EmissionFurther2.lean, NativeAIGZipFoldProcedure.lean, NativeAIGEqProcedure.lean, NativeAIGCarryProcedure.lean, NativeAIGDivBounded.lean, NativeAIGDivOperations.lean, NativeAIGDivProcedure.lean, NativeAIGDivWrapper.lean, NativeAIGModWrapper.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part30

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGExtend.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

lemma eraseVec_getD {n w : ℕ} {g : AIG (Fin n)} (xs : AIG.RefVec g w) (i : ℕ) :
    ((eraseVec xs).drop i).headD (0,false)=
    ((xs.getD i (g.mkConstCached false)).gate,(xs.getD i (g.mkConstCached false)).invert) := by
  by_cases hi : i<w
  · rw [AIG.RefVec.get_in_bound _ _ _ hi,eraseVec_get xs hi]
  · rw [AIG.RefVec.get_out_bound _ _ _ (by omega),List.drop_eq_nil_of_le (by rw [eraseVec_length];omega)]
    rfl
lemma eraseVec_append {n w v : ℕ} {g : AIG (Fin n)} (lhs : AIG.RefVec g w) (rhs : AIG.RefVec g v) :
    eraseVec (lhs.append rhs)=eraseVec lhs++eraseVec rhs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [eraseVec,List.getElem_ofFn]
    rw [AIG.RefVec.get_append,List.getElem_append]
    by_cases hh : i<w
    · simp only [List.length_ofFn,hh,dite_eq_left,List.getElem_ofFn]
    · simp [hh]

def extend (xs : List Ref) (w : ℕ) : List Ref:=
  (List.range w).map (fun i=>(xs.drop i).headD (0,false))
lemma extend_length (xs : List Ref) (w : ℕ) : (extend xs w).length=w:=by simp [extend]
lemma extend_refs {B : ℕ} {xs : List Ref} (h : RefsBound B xs) {w : ℕ} (hw : w≤B) :
    RefsBound B (extend xs w) := by
  refine ⟨by simpa only [extend_length],?_⟩
  intro a ha
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  exact h.get _
lemma extend_go_rel {n w v : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤v) (out : AIG.RefVec g curr) :
    VecRel (r,eraseVec out++(List.range' curr (v-curr)).map (fun i=>((eraseVec xs).drop i).headD (0,false)))
      (blastZeroExtend.go g w xs v curr hc out) := by
  rw [blastZeroExtend.go]
  by_cases hi : curr<v
  · rw [dite_eq_left hi]
    have hd : v-curr=(v-(curr+1))+1:=by omega
    rw [hd,List.range'_succ,List.map_cons]
    by_cases he : curr<w
    · rw [dite_eq_left he,eraseVec_get xs he]
      simpa only [eraseVec_push,List.append_assoc,List.singleton_append] using
        extend_go_rel hr xs (curr+1) (by omega) (out.push (xs.get curr he))
    · rw [dite_eq_right he,List.drop_eq_nil_of_le (by rw [eraseVec_length];omega)]
      simpa only [eraseVec_push,List.append_assoc,List.singleton_append,AIG.mkConstCached,List.headD_nil] using
        extend_go_rel hr xs (curr+1) (by omega) (out.push (g.mkConstCached false))
  · rw [dite_eq_right hi]
    have he : curr=v:=by omega
    subst curr
    simp only [Nat.sub_self,List.range'_zero,List.map_nil,List.append_nil]
    exact ⟨hr,rfl⟩
termination_by v-curr
lemma extend_rel {n w v : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) : VecRel (r,extend (eraseVec xs) v) (blastZeroExtend (newWidth:=v) g ⟨w,xs⟩) := by
  simpa only [blastZeroExtend,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,List.nil_append,
    extend,Nat.sub_zero,List.range_eq_range'] using
    extend_go_rel (v:=v) hr xs 0 (Nat.zero_le _) (.emptyWithCapacity v)
def shiftConcat (xs : List Ref) (a : Ref) : List Ref:=extend (a::xs) xs.length
lemma shiftConcat_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (a : AIG.Ref g) :
    VecRel (r,shiftConcat (eraseVec xs) (a.gate,a.invert)) (blastUdiv.blastShiftConcat g ⟨xs,a⟩) := by
  have hh:=extend_rel (v:=w) hr ((AIG.RefVec.empty.push a).append xs)
  simpa only [eraseVec_append,eraseVec_push,eraseVec_empty,List.nil_append,List.singleton_append,
    shiftConcat,eraseVec_length,blastUdiv.blastShiftConcat,AIG.RefVec.emptyWithCapacity_eq] using hh
lemma shiftConcat_length (xs : List Ref) (a : Ref) : (shiftConcat xs a).length=xs.length:=extend_length _ _
lemma shiftConcat_refs {B : ℕ} {xs : List Ref} {a : Ref} (hx : RefsBound B xs) (ha : a.1≤B) :
    RefsBound B (shiftConcat xs a) := by
  refine ⟨by simpa only [shiftConcat_length] using hx.1,?_⟩
  intro b hb
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hb
  cases i with
  | zero=>simpa using ha
  | succ i=>simpa using hx.get i
namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def extendP : Procedure (prodCode unaryCode (listCode refCode)) (listCode refCode)
    (fun x=>extend x.2 x.1):=
  tabulate (f:=fun (xs : List Ref) i=>(xs.drop i).headD (0,false)) (0,false)
    ((listGet refCode (0,false)).comp
      ((unaryToBits.comp (first unaryCode (listCode refCode))).pair (second unaryCode (listCode refCode))))
noncomputable def shiftConcatP : Procedure (prodCode (listCode refCode) refCode) (listCode refCode)
    (fun x=>shiftConcat x.1 x.2) := by
  let xs:=first (listCode refCode) refCode
  let a:=second (listCode refCode) refCode
  exact extendP.comp (((listUnaryLength refCode (0,false)).comp xs).pair
    ((listCons refCode).comp (a.pair xs)))
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGZipFold.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

abbrev BinOp:=Graph→Ref→Ref→Graph×Ref
def zipLoop (op : BinOp) : ℕ→Graph→List Ref→List Ref→ℕ→List Ref→Graph×List Ref
  | 0,r,_,_,_,out=>(r,out)
  | k+1,r,lhs,rhs,curr,out=>
    let s:=op r ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false))
    zipLoop op k s.1 lhs rhs (curr+1) (out++[s.2])
def zipVec (op : BinOp) (r : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  zipLoop op lhs.length r lhs rhs 0 []
def foldLoop (op : BinOp) : ℕ→Graph→List Ref→ℕ→Ref→Graph×Ref
  | 0,r,_,_,acc=>(r,acc)
  | k+1,r,xs,curr,acc=>
    let s:=op r acc ((xs.drop curr).headD (0,false))
    foldLoop op k s.1 xs (curr+1) s.2
def foldVec (op : BinOp) (r : Graph) (xs : List Ref) : Graph×Ref:=
  foldLoop op xs.length r xs 0 (0,true)

section Relations
variable {n : ℕ} (op : BinOp)
variable (f : (g : AIG (Fin n))→AIG.BinaryInput g→AIG.Entrypoint (Fin n))
variable [AIG.LawfulOperator (Fin n) AIG.BinaryInput f]
variable (hf : ∀{r : Graph} {g : AIG (Fin n)},Rel r g→∀i : AIG.BinaryInput g,
  EPRel (op r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)) (f g i))
include hf
lemma zipLoop_rel [AIG.RefVec.LawfulZipOperator (Fin n) f]
    {w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w) (out : AIG.RefVec g curr) :
    VecRel (zipLoop op (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (eraseVec out))
      (AIG.RefVec.zip.go g curr out hc lhs rhs f) := by
  rw [AIG.RefVec.zip.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,zipLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let ii : AIG.BinaryInput g:=⟨lhs.get curr hi,rhs.get curr hi⟩
    let ss:=f g ii
    have hs:=hf hr ii
    let hle:=AIG.LawfulOperator.le_size (f:=f) g ii
    have ht:=zipLoop_rel hs.1 (lhs.cast hle) (rhs.cast hle) (curr+1) (by omega)
      ((out.cast hle).push ss.ref)
    simp only [eraseVec_push,eraseVec_cast] at ht
    rw [←hs.2] at ht
    exact ht
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,zipLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma zipVec_rel [AIG.RefVec.LawfulZipOperator (Fin n) f]
    {w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (i : AIG.BinaryRefVec g w) :
    VecRel (zipVec op r (eraseVec i.lhs) (eraseVec i.rhs)) (AIG.RefVec.zip g i f) := by
  simpa only [zipVec,eraseVec_length,AIG.RefVec.zip,Nat.sub_zero,AIG.RefVec.emptyWithCapacity_eq,
    eraseVec_empty] using zipLoop_rel op f hf hr i.lhs i.rhs 0 (Nat.zero_le _) (.emptyWithCapacity w)
lemma foldLoop_rel {w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (curr : ℕ) (acc : AIG.Ref g) :
    EPRel (foldLoop op (w-curr) r (eraseVec xs) curr (acc.gate,acc.invert))
      (AIG.RefVec.fold.go g acc curr w xs f) := by
  rw [AIG.RefVec.fold.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,foldLoop,eraseVec_get xs hi]
    let ii : AIG.BinaryInput g:=⟨acc,xs.get curr hi⟩
    let ss:=f g ii
    have hs:=hf hr ii
    let hle:=AIG.LawfulOperator.le_size (f:=f) g ii
    have ht:=foldLoop_rel hs.1 (xs.cast hle) (curr+1) ss.ref
    simp only [eraseVec_cast] at ht
    rw [←hs.2] at ht
    exact ht
  · rw [dite_eq_right hi,Nat.sub_eq_zero_of_le (by omega),foldLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma foldVec_rel {w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (xs : AIG.RefVec g w) :
    EPRel (foldVec op r (eraseVec xs)) (AIG.RefVec.fold g xs f) := by
  simpa only [foldVec,eraseVec_length,AIG.RefVec.fold,Nat.sub_zero,AIG.mkConstCached] using
    foldLoop_rel op f hf hr xs 0 (g.mkConstCached true)
end Relations

def eqGate (r : Graph) (a b : Ref) : Graph×Ref:=xorGate r a (notRef b)
lemma eqGate_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (eqGate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)) (g.mkBEqCached i) := by
  let j:=i.invert false true
  let s:=g.mkGateCached j
  let sr:=gate r (i.lhs.gate,i.lhs.invert) (notRef (i.rhs.gate,i.rhs.invert))
  have hs : EPRel sr s:=by
    simpa only [sr,s,j,notRef,AIG.BinaryInput.invert,AIG.Ref.flip,Bool.false_xor,Bool.true_xor]
      using gate_rel hr j
  let i':=i.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) g j)
  let t:=s.aig.mkGateCached (i'.invert true false)
  let tr:=gate sr.1 (notRef (i.lhs.gate,i.lhs.invert)) (i.rhs.gate,i.rhs.invert)
  have ht : EPRel tr t:=by
    simpa only [tr,t,i',notRef,AIG.BinaryInput.cast,AIG.BinaryInput.invert,
      AIG.Ref.cast,AIG.Ref.flip,Bool.true_xor,Bool.false_xor] using gate_rel hs.1 (i'.invert true false)
  let a:=s.ref.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) s.aig (i'.invert true false))
  have hh:=gate_rel ht.1 (⟨a.not,t.ref.not⟩ : AIG.BinaryInput t.aig)
  have ha : (a.not.gate,a.not.invert)=notRef sr.2:=by
    simpa only [a,AIG.Ref.cast,AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef]
      using congrArg notRef hs.2.symm
  have hb : (t.ref.not.gate,t.ref.not.invert)=notRef tr.2:=by
    simpa only [AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef] using congrArg notRef ht.2.symm
  change EPRel (gate tr.1 (a.not.gate,a.not.invert) (t.ref.not.gate,t.ref.not.invert)) _ at hh
  rw [ha,hb] at hh
  have hn : t.aig.mkGateCached ⟨a.not,t.ref.not⟩ = g.mkBEqCached i := by rfl
  rw [hn] at hh
  simpa only [eqGate,xorGate,tr,sr,notRef,Bool.not_not] using hh

def eqVec (r : Graph) (lhs rhs : List Ref) : Graph×Ref:=
  let s:=zipVec eqGate r lhs rhs
  foldVec gate s.1 s.2
lemma eqVec_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (i : AIG.BinaryRefVec g w) :
    EPRel (eqVec r (eraseVec i.lhs) (eraseVec i.rhs)) (Std.Tactic.BVDecide.BVPred.mkEq g i) := by
  have hs:=zipVec_rel eqGate AIG.mkBEqCached (fun h i=>eqGate_rel h i) hr i
  have ht:=foldVec_rel gate AIG.mkAndCached (fun h i=>gate_rel h i) hs.1
    (AIG.RefVec.zip g i AIG.mkBEqCached).vec
  rw [←hs.2] at ht
  exact ht
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGDiv.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.BVExpr.bitblast

def divStep (g : Graph) (lhs rhs : List Ref) (wn : ℕ) (q rem : List Ref) : Graph×(List Ref×List Ref):=
  let r':=shiftConcat rem ((lhs.drop (wn-1)).headD (0,false))
  let posQ:=shiftConcat q (0,false)
  let negQ:=shiftConcat q (0,true)
  let negR:=sub g r' rhs
  let discr:=ult negR.1 r' rhs
  let nextQ:=ifVec discr.1 discr.2 posQ negQ
  let nextR:=ifVec nextQ.1 discr.2 r' negR.2
  (nextR.1,nextQ.2,nextR.2)
def divLoop : ℕ→Graph→List Ref→List Ref→ℕ→List Ref→List Ref→Graph×(List Ref×List Ref)
  | 0,g,_,_,_,q,rem=>(g,q,rem)
  | k+1,g,lhs,rhs,wn,q,rem=>
    let s:=divStep g lhs rhs wn q rem
    divLoop k s.1 lhs rhs (wn-1) s.2.1 s.2.2
def divide (g : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  let zero:=List.replicate lhs.length (0,false)
  let d:=eqVec g rhs zero
  let out:=divLoop lhs.length d.1 lhs rhs lhs.length zero zero
  ifVec out.1 d.2 zero out.2.1

lemma divStep_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (wn wr : ℕ) (q rem : AIG.RefVec g w) :
    let sr:=divStep r (eraseVec lhs) (eraseVec rhs) wn (eraseVec q) (eraseVec rem)
    let sn:=blastUdiv.blastDivSubtractShift g lhs rhs wn wr q rem
    Rel sr.1 sn.aig ∧ sr.2.1=eraseVec sn.q ∧ sr.2.2=eraseVec sn.r := by
  let ri : blastUdiv.ShiftConcatInput g w:=⟨rem,lhs.getD (wn-1) (g.mkConstCached false)⟩
  let rs:=blastUdiv.blastShiftConcat g ri
  have hrs:=shiftConcat_rel hr rem ri.bit
  change VecRel (r,shiftConcat (eraseVec rem)
    ((lhs.getD (wn-1) (g.mkConstCached false)).gate,(lhs.getD (wn-1) (g.mkConstCached false)).invert)) rs at hrs
  rw [←eraseVec_getD] at hrs
  let h₁:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) g ri
  let qi : blastUdiv.ShiftConcatInput rs.aig w:=⟨q.cast h₁,rs.aig.mkConstCached false⟩
  let qs:=blastUdiv.blastShiftConcat rs.aig qi
  have hqs:=shiftConcat_rel hrs.1 qi.lhs qi.bit
  change VecRel (r,shiftConcat (eraseVec q) (0,false)) qs at hqs
  let h₂:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) rs.aig qi
  let ni : blastUdiv.ShiftConcatInput qs.aig w:=⟨(q.cast h₁).cast h₂,qs.aig.mkConstCached true⟩
  let ns:=blastUdiv.blastShiftConcat qs.aig ni
  have hns:=shiftConcat_rel hqs.1 ni.lhs ni.bit
  change VecRel (r,shiftConcat (eraseVec q) (0,true)) ns at hns
  let h₃:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) qs.aig ni
  let si : AIG.BinaryRefVec ns.aig w:=⟨(rs.vec.cast h₂).cast h₃,((rhs.cast h₁).cast h₂).cast h₃⟩
  let ss:=blastSub ns.aig si
  have hss:=sub_rel hns.1 si
  change VecRel (sub r (eraseVec rs.vec) (eraseVec rhs)) ss at hss
  rw [←hrs.2] at hss
  let h₄:=AIG.LawfulVecOperator.le_size (f:=blastSub) ns.aig si
  let ui : AIG.BinaryRefVec ss.aig w:=⟨((rs.vec.cast h₂).cast h₃).cast h₄,
    (((rhs.cast h₁).cast h₂).cast h₃).cast h₄⟩
  let us:=BVPred.mkUlt ss.aig ui
  have hus:=ult_rel hss.1 ui
  change EPRel (ult _ (eraseVec rs.vec) (eraseVec rhs)) us at hus
  rw [←hrs.2] at hus
  let h₅:=AIG.LawfulOperator.le_size (f:=BVPred.mkUlt) ss.aig ui
  let qi' : AIG.RefVec.IfInput us.aig w:=⟨us.ref,((qs.vec.cast h₃).cast h₄).cast h₅,
    (ns.vec.cast h₄).cast h₅⟩
  let qs':=AIG.RefVec.ite us.aig qi'
  have hqs':=ifVec_rel hus.1 qi'
  change VecRel (ifVec _ (us.ref.gate,us.ref.invert) (eraseVec qs.vec) (eraseVec ns.vec)) qs' at hqs'
  rw [←hus.2,←hqs.2,←hns.2] at hqs'
  let h₆:=AIG.LawfulVecOperator.le_size (f:=AIG.RefVec.ite) us.aig qi'
  let ri' : AIG.RefVec.IfInput qs'.aig w:=⟨us.ref.cast h₆,
    (((rs.vec.cast h₂).cast h₃).cast h₄ |>.cast h₅).cast h₆,(ss.vec.cast h₅).cast h₆⟩
  let rs':=AIG.RefVec.ite qs'.aig ri'
  have hrs':=ifVec_rel hqs'.1 ri'
  change VecRel (ifVec _ (us.ref.gate,us.ref.invert) (eraseVec rs.vec) (eraseVec ss.vec)) rs' at hrs'
  rw [←hus.2,←hrs.2,←hss.2] at hrs'
  exact ⟨hrs'.1,hqs'.2,hrs'.2⟩

lemma divLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (k wn wr : ℕ) (q rem : AIG.RefVec g w) :
    let sr:=divLoop k r (eraseVec lhs) (eraseVec rhs) wn (eraseVec q) (eraseVec rem)
    let sn:=blastUdiv.go g k lhs rhs wn wr q rem
    Rel sr.1 sn.aig ∧ sr.2.1=eraseVec sn.q ∧ sr.2.2=eraseVec sn.r := by
  induction k generalizing r g wn wr with
  | zero=>exact ⟨hr,rfl,rfl⟩
  | succ k ih=>
    let ss:=blastUdiv.blastDivSubtractShift g lhs rhs wn wr q rem
    have hs:=divStep_rel hr lhs rhs wn wr q rem
    have ht:=ih hs.1 (lhs.cast ss.hle) (rhs.cast ss.hle) ss.wn ss.wr ss.q ss.r
    simp only [eraseVec_cast] at ht
    rw [←hs.2.1,←hs.2.2] at ht
    exact ht
lemma divide_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (divide r (eraseVec i.lhs) (eraseVec i.rhs)) (blastUdiv g i) := by
  let zi:=blastConst g (0 : BitVec w)
  let ei : AIG.BinaryRefVec g w:=⟨i.rhs,zi⟩
  let es:=BVPred.mkEq g ei
  have hes:=eqVec_rel hr ei
  change EPRel (eqVec r (eraseVec i.rhs) (eraseVec zi)) es at hes
  rw [show eraseVec zi=List.replicate w (0,false) from const_zero g] at hes
  let h₁:=AIG.LawfulOperator.le_size (f:=BVPred.mkEq) g ei
  let ds:=blastUdiv.go es.aig w (i.lhs.cast h₁) (i.rhs.cast h₁) w 0 (zi.cast h₁) (zi.cast h₁)
  have hds:=divLoop_rel hes.1 (i.lhs.cast h₁) (i.rhs.cast h₁) w w 0 (zi.cast h₁) (zi.cast h₁)
  simp only [eraseVec_cast] at hds
  rw [show eraseVec zi=List.replicate w (0,false) from const_zero g] at hds
  let h₂:=blastUdiv.go_le_size es.aig w (i.lhs.cast h₁) (i.rhs.cast h₁) w 0 (zi.cast h₁) (zi.cast h₁)
  let qi : AIG.RefVec.IfInput ds.aig w:=⟨es.ref.cast h₂,(zi.cast h₁).cast h₂,ds.q⟩
  have hq:=ifVec_rel hds.1 qi
  change VecRel (ifVec _ (es.ref.gate,es.ref.invert) (eraseVec zi) (eraseVec ds.q)) _ at hq
  rw [←hes.2,←hds.2.1,show eraseVec zi=List.replicate w (0,false) from const_zero g] at hq
  have hn : AIG.RefVec.ite ds.aig qi = blastUdiv g i := by rfl
  change VecRel _ (AIG.RefVec.ite ds.aig qi) at hq
  rw [hn] at hq
  simpa only [divide,eraseVec_length] using hq
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGMod.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.BVExpr.bitblast

def remainder (g : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  let zero:=List.replicate lhs.length (0,false)
  let d:=eqVec g rhs zero
  let out:=divLoop lhs.length d.1 lhs rhs lhs.length zero zero
  ifVec out.1 d.2 lhs out.2.2

lemma remainder_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (remainder r (eraseVec i.lhs) (eraseVec i.rhs)) (blastUmod g i) := by
  let zi:=blastConst g (0 : BitVec w)
  let ei : AIG.BinaryRefVec g w:=⟨i.rhs,zi⟩
  let es:=BVPred.mkEq g ei
  have hes:=eqVec_rel hr ei
  change EPRel (eqVec r (eraseVec i.rhs) (eraseVec zi)) es at hes
  rw [show eraseVec zi=List.replicate w (0,false) from const_zero g] at hes
  let h₁:=AIG.LawfulOperator.le_size (f:=BVPred.mkEq) g ei
  let ds:=blastUdiv.go es.aig w (i.lhs.cast h₁) (i.rhs.cast h₁) w 0 (zi.cast h₁) (zi.cast h₁)
  have hds:=divLoop_rel hes.1 (i.lhs.cast h₁) (i.rhs.cast h₁) w w 0 (zi.cast h₁) (zi.cast h₁)
  simp only [eraseVec_cast] at hds
  rw [show eraseVec zi=List.replicate w (0,false) from const_zero g] at hds
  let h₂:=blastUdiv.go_le_size es.aig w (i.lhs.cast h₁) (i.rhs.cast h₁) w 0 (zi.cast h₁) (zi.cast h₁)
  let qi : AIG.RefVec.IfInput ds.aig w:=⟨es.ref.cast h₂,(i.lhs.cast h₁).cast h₂,ds.r⟩
  have hq:=ifVec_rel hds.1 qi
  change VecRel (ifVec _ (es.ref.gate,es.ref.invert) (eraseVec i.lhs) (eraseVec ds.r)) _ at hq
  rw [←hes.2,←hds.2.2] at hq
  have hn : AIG.RefVec.ite ds.aig qi = blastUmod g i := by rfl
  change VecRel _ (AIG.RefVec.ite ds.aig qi) at hq
  rw [hn] at hq
  simpa only [remainder,eraseVec_length] using hq
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGInputs.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
def rawInputs (n : ℕ) : Graph := ⟨.zero::(List.range n).map Decl.atom,[]⟩
lemma rawInputs_succ (n : ℕ) : rawInputs (n+1)=(atom (rawInputs n) n).1 := by
  simp [rawInputs,atom,List.range_succ]
lemma inputsPrefix_rel (n k : ℕ) (h : k≤n) : Rel (rawInputs k) (AIGCompiler.inputsPrefix n k h).1 := by
  induction k with
  | zero=>exact empty_rel n
  | succ k ih=>
    rw [rawInputs_succ]
    exact (atom_rel (ih (by omega)) ⟨k,by omega⟩).1
lemma inputs_rel (n : ℕ) : Rel (rawInputs n) (AIGCompiler.inputs n).1 := inputsPrefix_rel n n le_rfl
lemma inputsPrefix_ref (n k : ℕ) (h : k≤n) (i : Fin k) :
    (((AIGCompiler.inputsPrefix n k h).2 i).gate,
      ((AIGCompiler.inputsPrefix n k h).2 i).invert)=(i.val+1,false) := by
  induction k with
  | zero=>exact Fin.elim0 i
  | succ k ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [AIGCompiler.inputsPrefix,Fin.snoc_last,AIG.mkAtom,AIGCompiler.inputsPrefix_size]
      rfl
    · simp only [AIGCompiler.inputsPrefix,Fin.snoc_castSucc]
      exact ih (by omega) j
lemma inputs_ref (n : ℕ) (i : Fin n) :
    (((AIGCompiler.inputs n).2 i).gate,((AIGCompiler.inputs n).2 i).invert)=(i.val+1,false) :=
  inputsPrefix_ref n n le_rfl i

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def inputsP : Procedure unaryCode graphCode rawInputs := by
  let p : Procedure (prodCode unaryCode emptyCode) declCode (fun x=>Decl.atom x.1):=
    atomDecl.comp (unaryToBits.comp (first unaryCode emptyCode))
  let ds:=(tabulate (f:=fun (_ : Unit) i=>Decl.atom i) Decl.zero p).comp ((identity unaryCode).pair (Procedure.constant _ emptyCode ()))
  exact (packGraph.comp (((listCons declCode).comp
    ((Procedure.constant _ declCode Decl.zero).pair ds)).pair
      (Procedure.constant _ (listCode entryCode) []))).congrFun (by intro n;rfl)
noncomputable def inputRefP : Procedure unaryCode refCode (fun n=>(n+1,false)) :=
  ((successor.comp unaryToBits).pair (Procedure.constant _ boolCode false))
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGSubProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

lemma neg_bound {B : ℕ} {g : Graph} {xs : List Ref} (hg : Bounded B g) (hx : RefsBound B xs) :
    Bounded (B+13*xs.length) (neg g xs).1 ∧
    RefsBound (B+13*xs.length) (neg g xs).2 ∧ (neg g xs).2.length=xs.length := by
  simpa only [notVec_length,neg] using add_bound hg (notVec_refs hx) (oneVec_refs hx.1)
    (by rw [notVec_length,oneVec_length])
lemma sub_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) (he : lhs.length=rhs.length) :
    Bounded (B+26*lhs.length) (sub g lhs rhs).1 ∧
    RefsBound (B+26*lhs.length) (sub g lhs rhs).2 ∧ (sub g lhs rhs).2.length=lhs.length := by
  have hn:=neg_bound hg hr
  have hh:=add_bound hn.1 (hl.mono (by omega)) hn.2.1 (he.trans hn.2.2.symm)
  have hb : B+13*rhs.length+13*lhs.length=B+26*lhs.length:=by omega
  simpa only [hb,sub] using hh

def negInput (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,notVec s.val.rhs,oneVec s.val.rhs.length,
    0,(0,false),[]⟩,
  s.property.1,notVec_refs s.property.2.2.1,oneVec_refs s.property.2.2.1.1,
    Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def negState (s : AddState) : AddState:=addState (negInput s)
lemma negState_value (s : AddState) : ((negState s).val.graph,(negState s).val.output)=
    neg s.val.graph s.val.rhs:=addState_value _
lemma negState_budget (s : AddState) : (negState s).val.budget=s.val.budget+13*s.val.rhs.length := by
  have hh:=addState_budget_eq (negInput s) (by dsimp only [negInput];rw [notVec_length,oneVec_length])
  simpa only [negState,negInput,notVec_length] using hh
lemma negState_length (s : AddState) : (negState s).val.output.length=s.val.rhs.length := by
  have hh:=addState_length (negInput s) (by dsimp only [negInput];rw [notVec_length,oneVec_length])
  simpa only [negState,negInput,notVec_length] using hh

def subNext (s : BinaryState) : AddState:=⟨⟨(negState s.val).val.budget,(negState s.val).val.graph,
  s.val.val.lhs,(negState s.val).val.output,0,(0,false),[]⟩,
  (negState s.val).property.1,s.val.property.2.1.mono (by dsimp only;rw [negState_budget];omega),
  (negState s.val).property.2.2.2.2.2,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def subState (s : BinaryState) : AddState:=addState (subNext s)
lemma subState_value (s : BinaryState) : ((subState s).val.graph,(subState s).val.output)=
    sub s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=addState_value (subNext s)
  change _=add (negState s.val).val.graph s.val.val.lhs (negState s.val).val.output at hh
  rw [show (negState s.val).val.graph=(neg s.val.val.graph s.val.val.rhs).1 from
    congrArg Prod.fst (negState_value s.val),show (negState s.val).val.output=(neg s.val.val.graph s.val.val.rhs).2 from
    congrArg Prod.snd (negState_value s.val)] at hh
  exact hh
lemma subState_budget (s : BinaryState) : (subState s).val.budget=s.val.val.budget+26*s.val.val.lhs.length := by
  have hh:=addState_budget_eq (subNext s) (by
    change s.val.val.lhs.length=(negState s.val).val.output.length
    rw [negState_length];exact s.property)
  change (subState s).val.budget=(negState s.val).val.budget+13*s.val.val.lhs.length at hh
  rw [hh,negState_budget,←s.property];omega
lemma subState_length (s : BinaryState) : (subState s).val.output.length=s.val.val.lhs.length:=
  addState_length (subNext s) (by
    change s.val.val.lhs.length=(negState s.val).val.output.length
    rw [negState_length];exact s.property)

end ExactQuantumFactoring.NativeAIG
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionFurther2.lean =====
namespace OAI

section
namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def oneVecP : Procedure unaryCode (listCode refCode) oneVec := by
  let oneBit:=(Procedure.constant (prodCode unaryCode boolCode) Nat.bits 0).pair
    (unaryZero.comp (first unaryCode boolCode))
  exact ((tabulate (f:=fun (_ : Bool) i => (0,decide (i=0))) (0,false) oneBit).comp
    ((identity unaryCode).pair (Procedure.constant unaryCode boolCode false))).congrFun (by intro w;rfl)
noncomputable def negInputP : Procedure addStateCode addStateCode negInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  let one:=oneVecP.comp ((listUnaryLength refCode (0,false)).comp rhs)
  exact (packAddP.comp (b.pair (g.pair ((notVecP.comp rhs).pair (one.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def negStateP : Procedure addStateCode addStateCode negState:=addStateP.comp negInputP
noncomputable def subNextP : Procedure binaryStateCode addStateCode subNext := by
  let ns:=negStateP.precompose (fun s:BinaryState=>s.val)
  let b:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp ns
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp ns
  let rhs:=(addOutputP.precompose (fun s:AddState=>s.val)).comp ns
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def subStateP : Procedure binaryStateCode addStateCode subState:=addStateP.comp subNextP
noncomputable def subP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>sub s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp subStateP).congrFun subState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGZipFoldProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def BinBound (C : ℕ) (op : BinOp) : Prop:=∀{B : ℕ} {r : Graph},Bounded B r→∀a b,
  a.1≤B→b.1≤B→Bounded (B+C) (op r a b).1 ∧ (op r a b).2.1≤B+C

def binaryStepData (collect : Bool) (C : ℕ) (op : BinOp) (s : AddData) : AddData:=
  let a:=if collect then (s.lhs.drop s.curr).headD (0,false) else s.cin
  let ss:=op s.graph a ((s.rhs.drop s.curr).headD (0,false))
  ⟨s.budget+C+1,ss.1,s.lhs,s.rhs,s.curr+1,ss.2,if collect then s.output++[ss.2] else s.output⟩
lemma binaryStep_ok (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    AddOK (binaryStepData collect C op s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have ha : (if collect then ((s.val.lhs.drop s.val.curr).headD (0,false)) else s.val.cin).1 ≤ s.val.budget:=by
    cases collect <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> first | exact hci | exact hl.get _
  have hh:=hop hg _ _ ha (hr.get s.val.curr)
  dsimp only [AddOK,binaryStepData]
  refine ⟨hh.1.mono (by omega),hl.mono (by omega),hr.mono (by omega),by omega,hh.2.trans (by omega),?_⟩
  cases collect <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact ho.mono (by omega)
  · refine ⟨by simp only [List.length_append,List.length_singleton];have:=ho.1;omega,?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (ho.2 a ha).trans (by omega)
    · have he:=List.mem_singleton.mp ha
      rw [he];exact hh.2.trans (by omega)
def binaryStep (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  ⟨binaryStepData collect C op s.val,binaryStep_ok collect hop s⟩
lemma binaryStep_budget (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (binaryStep collect hop s).val.budget=s.val.budget+C+1:=rfl
lemma binaryStep_iterate_budget (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    ((binaryStep collect hop)^[k] s).val.budget=s.val.budget+(C+1)*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,binaryStep_budget];ring
lemma binaryStep_zipLoop {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    (((binaryStep true hop)^[k] s).val.graph,((binaryStep true hop)^[k] s).val.output)=
      zipLoop op k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma binaryStep_foldLoop {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    (((binaryStep false hop)^[k] s).val.graph,((binaryStep false hop)^[k] s).val.cin)=
      foldLoop op k s.val.graph s.val.rhs s.val.curr s.val.cin := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma binaryStep_zipLength {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    ((binaryStep true hop)^[k] s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih];simp only [binaryStep,binaryStepData,ite_true,
      List.length_append,List.length_singleton];omega

def zipState {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  (binaryStep true hop)^[s.val.lhs.length] (initializeAdd s)
lemma zipState_value {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    ((zipState hop s).val.graph,(zipState hop s).val.output)=zipVec op s.val.graph s.val.lhs s.val.rhs:=
  binaryStep_zipLoop hop _ _
lemma zipState_budget {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (zipState hop s).val.budget=s.val.budget+(C+1)*s.val.lhs.length:=binaryStep_iterate_budget _ _ _ _
lemma zipState_length {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (zipState hop s).val.output.length=s.val.lhs.length:=by
  unfold zipState
  rw [binaryStep_zipLength]
  simp only [initializeAdd,initializeAddData,List.length_nil,Nat.zero_add]

def initializeFold (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,s.val.lhs,s.val.rhs,0,(0,true),[]⟩,
  s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def foldState {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  (binaryStep false hop)^[s.val.rhs.length] (initializeFold s)
lemma foldState_value {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    ((foldState hop s).val.graph,(foldState hop s).val.cin)=foldVec op s.val.graph s.val.rhs:=
  binaryStep_foldLoop hop _ _
lemma foldState_budget {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (foldState hop s).val.budget=s.val.budget+(C+1)*s.val.rhs.length:=binaryStep_iterate_budget _ _ _ _

namespace Emission
noncomputable def binaryStepDataP (collect : Bool) (C : ℕ) {op : BinOp}
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addDataCode addDataCode (binaryStepData collect C op) := by
  let b:=(unaryAdd.comp (((first unaryCode addTail1).comp addViewP).pair (Procedure.constant _ unaryCode (C+1))))
  let a:=conditional (Procedure.constant _ boolCode collect)
    ((listGet refCode (0,false)).comp (addCurrP.pair addLhsP)) addCinP
  let rhs:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let ss:=p.comp (addGraphP.pair (a.pair rhs))
  let g:=(first graphCode refCode).comp ss
  let c:=(second graphCode refCode).comp ss
  let out:=conditional (Procedure.constant _ boolCode collect)
    ((listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp c))) addOutputP
  exact (packAddP.comp (b.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (c.pair out))))))).congrFun (by
      intro s;cases collect <;> simp only [binaryStepData,Nat.add_assoc,Function.comp_apply,
        Bool.false_eq_true,ite_true,ite_false,addDataView])
noncomputable def binaryStepP (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (binaryStep collect hop):=
  ((binaryStepDataP collect C p).precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def binaryIterationP (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure (prodCode unaryCode addStateCode) addStateCode (fun x=>(binaryStep collect hop)^[x.1] x.2):=
  (binaryStepP collect hop p).iterate (Polynomial.C (300*(C+1)^2)*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((binaryStep collect hop)^[i] s)
    rw [binaryStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hs : s.val.budget+1≤(C+1)*((addStateCode s).length+1):=by nlinarith
    have hn:=Nat.mul_le_mul_left (C+1) hi
    have h : s.val.budget+(C+1)*i+1≤(C+1)*(n+(addStateCode s).length+1):=by nlinarith
    have hp:=Nat.pow_le_pow_left h 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def zipStateP {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (zipState hop):=
  (binaryIterationP true hop p).comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeAddP)
noncomputable def initializeFoldP : Procedure addStateCode addStateCode initializeFold := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  exact (packAddP.comp (b.pair (g.pair (lhs.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def foldStateP {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (foldState hop):=
  (binaryIterationP false hop p).comp (((listUnaryLength refCode (0,false)).comp
    (addRhsP.precompose (fun s:AddState=>s.val))).pair initializeFoldP)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGEqProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma eqGate_bound : BinBound 3 eqGate:=fun h a b ha hb=>xorGate_bound h a (notRef b) ha hb
lemma andGate_bound : BinBound 1 gate:=fun h a b ha hb=>gate_bound h a b ha hb
lemma zipVec_bound {C B : ℕ} {op : BinOp} (hop : BinBound C op) {r : Graph} {lhs rhs : List Ref}
    (hg : Bounded B r) (hl : RefsBound B lhs) (hr : RefsBound B rhs) :
    Bounded (B+(C+1)*lhs.length) (zipVec op r lhs rhs).1 ∧
    RefsBound (B+(C+1)*lhs.length) (zipVec op r lhs rhs).2 ∧
    (zipVec op r lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,r,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hb:=zipState_budget hop s
  have ho:=(zipState hop s).property
  rw [←zipState_value hop s]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,zipState_length hop s⟩
lemma foldVec_bound {C B : ℕ} {op : BinOp} (hop : BinBound C op) {r : Graph} {xs : List Ref}
    (hg : Bounded B r) (hx : RefsBound B xs) :
    Bounded (B+(C+1)*xs.length) (foldVec op r xs).1 ∧
    (foldVec op r xs).2.1≤B+(C+1)*xs.length := by
  let s : AddState:=⟨⟨B,r,xs,xs,0,(0,false),[]⟩,
    hg,hx,hx,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hb:=foldState_budget hop s
  have ho:=(foldState hop s).property
  rw [←foldState_value hop s]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.1⟩
lemma eqVec_bound {B : ℕ} {r : Graph} {lhs rhs : List Ref}
    (hg : Bounded B r) (hl : RefsBound B lhs) (hr : RefsBound B rhs) :
    Bounded (B+6*lhs.length) (eqVec r lhs rhs).1 ∧ (eqVec r lhs rhs).2.1≤B+6*lhs.length := by
  have hz:=zipVec_bound eqGate_bound hg hl hr
  have hf:=foldVec_bound andGate_bound hz.1 hz.2.1
  rw [hz.2.2] at hf
  have he : B+(3+1)*lhs.length+(1+1)*lhs.length=B+6*lhs.length:=by omega
  simpa only [he,eqVec] using hf

def eqNext (s : AddState) : AddState:=
  let z:=zipState eqGate_bound s
  ⟨⟨z.val.budget,z.val.graph,z.val.output,z.val.output,0,(0,true),[]⟩,
  z.property.1,z.property.2.2.2.2.2,z.property.2.2.2.2.2,Nat.zero_le _,Nat.zero_le _,
    Nat.zero_le _,by intro a ha;cases ha⟩
def eqState (s : AddState) : AddState:=foldState andGate_bound (eqNext s)
lemma eqState_value (s : AddState) : ((eqState s).val.graph,(eqState s).val.cin)=
    eqVec s.val.graph s.val.lhs s.val.rhs := by
  have hf:=foldState_value andGate_bound (eqNext s)
  change _=foldVec gate (zipState eqGate_bound s).val.graph (zipState eqGate_bound s).val.output at hf
  rw [show (zipState eqGate_bound s).val.graph=(zipVec eqGate s.val.graph s.val.lhs s.val.rhs).1 from
    congrArg Prod.fst (zipState_value eqGate_bound s),
    show (zipState eqGate_bound s).val.output=(zipVec eqGate s.val.graph s.val.lhs s.val.rhs).2 from
    congrArg Prod.snd (zipState_value eqGate_bound s)] at hf
  exact hf
lemma eqState_budget (s : AddState) : (eqState s).val.budget=s.val.budget+6*s.val.lhs.length := by
  rw [eqState,foldState_budget]
  change (zipState eqGate_bound s).val.budget+(1+1)*(zipState eqGate_bound s).val.output.length=_
  rw [zipState_budget,zipState_length];omega
namespace Emission
noncomputable def eqGateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>eqGate x.1 x.2.1 x.2.2):=
  (xorP.comp ((first graphCode keyCode).pair
    ((((first refCode refCode).comp (second graphCode keyCode))).pair
      (notRefP.comp ((second refCode refCode).comp (second graphCode keyCode)))))).congrFun (by intro x;rfl)
noncomputable def eqNextP : Procedure addStateCode addStateCode eqNext := by
  let zp:=zipStateP eqGate_bound eqGateP
  let b:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp zp
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp zp
  let out:=(addOutputP.precompose (fun s:AddState=>s.val)).comp zp
  exact (packAddP.comp (b.pair (g.pair (out.pair (out.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def eqStateP : Procedure addStateCode addStateCode eqState:=
  (foldStateP andGate_bound gateP).comp eqNextP
noncomputable def eqP : Procedure addStateCode (prodCode graphCode refCode)
    (fun s=>eqVec s.val.graph s.val.lhs s.val.rhs):=
  (((addGraphP.pair addCinP).precompose (fun s:AddState=>s.val)).comp eqStateP).congrFun eqState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGCarryProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def carryStepData (s : AddData) : AddData:=
  let next:=fullCarry s.graph ((s.lhs.drop s.curr).headD (0,false))
    ((s.rhs.drop s.curr).headD (0,false)) s.cin
  ⟨s.budget+6,next.1,s.lhs,s.rhs,s.curr+1,next.2,s.output⟩
lemma carryStep_ok (s : AddState) : AddOK (carryStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=fullCarry_bound hg _ _ s.val.cin (hl.get s.val.curr) (hr.get s.val.curr) hci
  dsimp only [AddOK,carryStepData]
  exact ⟨hh.1,hl.mono (by omega),hr.mono (by omega),by omega,hh.2,ho.mono (by omega)⟩
def carryStep (s : AddState) : AddState:=⟨carryStepData s.val,carryStep_ok s⟩
lemma carryStep_budget (s : AddState) : (carryStep s).val.budget=s.val.budget+6:=rfl
lemma carryStep_iterate_budget (s : AddState) (k : ℕ) :
    ((carryStep^[k]) s).val.budget=s.val.budget+6*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,carryStep_budget];omega
lemma carryStep_iterate_loop (s : AddState) (k : ℕ) :
    (((carryStep^[k]) s).val.graph,((carryStep^[k]) s).val.cin)=
      carryLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.cin := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl

def overflowState (s : AddState) : AddState:=(carryStep^[s.val.lhs.length]) (initializeIf s)
lemma overflowState_value (s : AddState) : ((overflowState s).val.graph,(overflowState s).val.cin)=
    overflow s.val.graph s.val.lhs s.val.rhs s.val.cin:=carryStep_iterate_loop _ _
lemma overflowState_budget (s : AddState) : (overflowState s).val.budget=s.val.budget+6*s.val.lhs.length:=
  carryStep_iterate_budget _ _
def ultInput (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,s.val.lhs,notVec s.val.rhs,0,(0,true),[]⟩,
  s.property.1,s.property.2.1,notVec_refs s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,
  by intro a ha;cases ha⟩
def ultState (s : AddState) : AddState:=overflowState (ultInput s)
lemma ultState_value (s : AddState) : ((ultState s).val.graph,notRef (ultState s).val.cin)=
    ult s.val.graph s.val.lhs s.val.rhs :=by
  have hh:=overflowState_value (ultInput s)
  exact congrArg (fun x : Graph×Ref=>(x.1,notRef x.2)) hh
lemma ult_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) :
    Bounded (B+6*lhs.length) (ult g lhs rhs).1 ∧ (ult g lhs rhs).2.1≤B+6*lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hh:=(ultState s).property
  have hb:=overflowState_budget (ultInput s)
  rw [←ultState_value s]
  change Bounded (B+6*lhs.length) (ultState s).val.graph ∧ (ultState s).val.cin.1≤B+6*lhs.length
  change (ultState s).val.budget=B+6*lhs.length at hb
  rw [←hb]
  exact ⟨hh.1,hh.2.2.2.2.1⟩
namespace Emission
noncomputable def carryStepDataP : Procedure addDataCode addDataCode carryStepData := by
  let b:=unaryAdd.comp (((first unaryCode addTail1).comp addViewP).pair (Procedure.constant _ unaryCode 6))
  let lhs:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhs:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=fullCarryP.comp (addGraphP.pair (lhs.pair (rhs.pair addCinP)))
  let g:=(first graphCode refCode).comp s
  let c:=(second graphCode refCode).comp s
  exact (packAddP.comp (b.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (c.pair addOutputP))))))).congrFun (by intro s;rfl)
noncomputable def carryStepP : Procedure addStateCode addStateCode carryStep:=
  (carryStepDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def carryIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(carryStep^[x.1]) x.2):=
  carryStepP.iterate (Polynomial.C 10800*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((carryStep^[i]) s)
    rw [carryStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have h : s.val.budget+6*i+1 ≤ 6*(n+(addStateCode s).length+1):=by omega
    have hp:=Nat.pow_le_pow_left h 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def overflowStateP : Procedure addStateCode addStateCode overflowState:=
  carryIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeIfP)
noncomputable def ultInputP : Procedure addStateCode addStateCode ultInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=notVecP.comp (addRhsP.precompose (fun s:AddState=>s.val))
  exact (packAddP.comp (b.pair (g.pair (lhs.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def ultStateP : Procedure addStateCode addStateCode ultState:=overflowStateP.comp ultInputP
noncomputable def ultP : Procedure addStateCode (prodCode graphCode refCode)
    (fun s=>ult s.val.graph s.val.lhs s.val.rhs) :=
  ((((addGraphP.pair (notRefP.comp addCinP)).precompose (fun s:AddState=>s.val)).comp ultStateP)).congrFun
    ultState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGDivBounded.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma divStep_bound {B : ℕ} {g : Graph} {lhs rhs q rem : List Ref} (wn : ℕ)
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs)
    (hq : RefsBound B q) (hm : RefsBound B rem)
    (he : lhs.length=rhs.length) (hql : q.length=lhs.length) (hml : rem.length=lhs.length) :
    Bounded (B+38*lhs.length) (divStep g lhs rhs wn q rem).1 ∧
    RefsBound (B+38*lhs.length) (divStep g lhs rhs wn q rem).2.1 ∧
    RefsBound (B+38*lhs.length) (divStep g lhs rhs wn q rem).2.2 ∧
    (divStep g lhs rhs wn q rem).2.1.length=lhs.length ∧
    (divStep g lhs rhs wn q rem).2.2.length=lhs.length := by
  let r':=shiftConcat rem ((lhs.drop (wn-1)).headD (0,false))
  let posQ:=shiftConcat q (0,false)
  let negQ:=shiftConcat q (0,true)
  have hm' : RefsBound B r':=shiftConcat_refs hm (hl.get _)
  have hpq : RefsBound B posQ:=shiftConcat_refs hq (Nat.zero_le _)
  have hnq : RefsBound B negQ:=shiftConcat_refs hq (Nat.zero_le _)
  have hrlen : r'.length=lhs.length:=(shiftConcat_length _ _).trans hml
  have hplen : posQ.length=lhs.length:=(shiftConcat_length _ _).trans hql
  have hsub:=sub_bound hg hm' hr (hrlen.trans he)
  rw [hrlen] at hsub
  have hu:=ult_bound hsub.1 (hm'.mono (by omega)) (hr.mono (by omega))
  rw [hrlen] at hu
  have ht:=ifVec_bound hu.1 (hpq.mono (by omega)) (hnq.mono (by omega)) hu.2
  rw [hplen] at ht
  have ho:=ifVec_bound ht.1 (hm'.mono (by omega)) (hsub.2.1.mono (by omega)) (hu.2.trans (by omega))
  rw [hrlen] at ho
  have hB : B+26*lhs.length+6*lhs.length+3*lhs.length+3*lhs.length=B+38*lhs.length:=by omega
  rw [hB] at ho
  exact ⟨ho.1,ht.2.1.mono (by omega),ho.2.1,ht.2.2,ho.2.2⟩

structure DivData where
  base : AddData
  quotient : List Ref

def DivOK (s : DivData) : Prop:=
  AddOK s.base ∧ s.base.lhs.length=s.base.rhs.length ∧
    s.base.output.length=s.base.lhs.length ∧ RefsBound s.base.budget s.quotient ∧
    s.quotient.length=s.base.lhs.length
abbrev DivState:={s : DivData // DivOK s}
def divDataCode (s : DivData) : List Bool:=prodCode addDataCode (listCode refCode) (s.base,s.quotient)
def divStateCode (s : DivState) : List Bool:=divDataCode s.val

def divStepData (s : DivData) : DivData:=
  let ss:=divStep s.base.graph s.base.lhs s.base.rhs s.base.curr s.quotient s.base.output
  ⟨⟨s.base.budget+38*s.base.lhs.length,ss.1,s.base.lhs,s.base.rhs,s.base.curr-1,s.base.cin,ss.2.2⟩,ss.2.1⟩
lemma divStep_ok (s : DivState) : DivOK (divStepData s.val) := by
  obtain ⟨⟨hg,hl,hr,hc,hci,ho⟩,he,hm,hq,hql⟩:=s.property
  have hh:=divStep_bound s.val.base.curr hg hl hr hq ho he hql hm
  have hb : s.val.base.budget ≤ s.val.base.budget+38*s.val.base.lhs.length:=by omega
  exact ⟨⟨hh.1,hl.mono hb,hr.mono hb,by dsimp only [divStepData];omega,hci.trans hb,hh.2.2.1⟩,
    he,hh.2.2.2.2,hh.2.1,hh.2.2.2.1⟩
def divStepState (s : DivState) : DivState:=⟨divStepData s.val,divStep_ok s⟩
lemma divStepState_budget (s : DivState) :
    (divStepState s).val.base.budget=s.val.base.budget+38*s.val.base.lhs.length:=rfl
lemma divStepState_lhs (s : DivState) : (divStepState s).val.base.lhs=s.val.base.lhs:=rfl
lemma divStepState_iterate_lhs (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.lhs=s.val.base.lhs:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih,divStepState_lhs]
lemma divStepState_iterate_budget (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.budget=s.val.base.budget+38*s.val.base.lhs.length*k:=by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,divStepState_budget,divStepState_lhs];ring
lemma divStepState_iterate_loop (s : DivState) (k : ℕ) :
    (((divStepState^[k]) s).val.base.graph,((divStepState^[k]) s).val.quotient,
      ((divStepState^[k]) s).val.base.output)=
    divLoop k s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma divStateCode_bound (s : DivState) : (divStateCode s).length≤1000*(s.val.base.budget+1)^2 := by
  have ha:=addStateCode_bound ⟨s.val.base,s.property.1⟩
  have hq:=refsCode_bound s.property.2.2.2.1
  simp only [divStateCode,divDataCode,prodCode,pairBits_length]
  change _≤_ at hq
  dsimp only [addStateCode] at ha
  nlinarith [Nat.zero_le s.val.base.budget]
lemma divBudget_le_code (s : DivState) : s.val.base.budget≤(divStateCode s).length := by
  have ha:=budget_le_code ⟨s.val.base,s.property.1⟩
  simp only [divStateCode,divDataCode,prodCode,pairBits_length]
  dsimp only [addStateCode] at ha
  omega
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGDivOperations.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def divSubInput (s : DivState) : BinaryState:=
  ⟨⟨⟨s.val.base.budget,s.val.base.graph,
      shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
      s.val.base.rhs,0,(0,false),[]⟩,
    s.property.1.1,shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _),s.property.1.2.2.1,
    Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩,
    (shiftConcat_length _ _).trans (s.property.2.2.1.trans s.property.2.1)⟩
def divSubState (s : DivState) : AddState:=subState (divSubInput s)
lemma divSub_budget (s : DivState) :
    (divSubState s).val.budget=s.val.base.budget+26*s.val.base.lhs.length:=by
  rw [divSubState,subState_budget]
  change s.val.base.budget+26*(shiftConcat _ _).length=_
  rw [shiftConcat_length,s.property.2.2.1]
lemma divSub_length (s : DivState) : (divSubState s).val.output.length=s.val.base.lhs.length:=
  (subState_length _).trans ((shiftConcat_length _ _).trans s.property.2.2.1)
lemma divSub_value (s : DivState) : ((divSubState s).val.graph,(divSubState s).val.output)=
    sub s.val.base.graph
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs:=
  subState_value _
def divUltInput (s : DivState) : AddState:=
  ⟨⟨(divSubState s).val.budget,(divSubState s).val.graph,
    shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
    s.val.base.rhs,0,(0,false),[]⟩,
  (divSubState s).property.1,
  (shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _)).mono (by rw [divSub_budget];omega),
  s.property.1.2.2.1.mono (by rw [divSub_budget];omega),Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def divUltState (s : DivState) : AddState:=ultState (divUltInput s)
lemma ultState_budget (s : AddState) : (ultState s).val.budget=s.val.budget+6*s.val.lhs.length:=
  overflowState_budget (ultInput s)
lemma divUlt_budget (s : DivState) :
    (divUltState s).val.budget=s.val.base.budget+32*s.val.base.lhs.length:=by
  rw [divUltState,ultState_budget]
  change (divSubState s).val.budget+
    6*(shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))).length=_
  rw [divSub_budget,shiftConcat_length,s.property.2.2.1];omega
lemma divUlt_value (s : DivState) : ((divUltState s).val.graph,notRef (divUltState s).val.cin)=
    ult (sub s.val.base.graph
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs).1
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs:=by
  have hh:=ultState_value (divUltInput s)
  change _=ult (divSubState s).val.graph _ _ at hh
  rw [show (divSubState s).val.graph=_ from congrArg Prod.fst (divSub_value s)] at hh
  exact hh

def divQInput (s : DivState) : AddState:=
  ⟨⟨(divUltState s).val.budget,(divUltState s).val.graph,
    shiftConcat s.val.quotient (0,false),shiftConcat s.val.quotient (0,true),0,
    notRef (divUltState s).val.cin,[]⟩,
  (divUltState s).property.1,
  (shiftConcat_refs s.property.2.2.2.1 (Nat.zero_le _)).mono (by rw [divUlt_budget];omega),
  (shiftConcat_refs s.property.2.2.2.1 (Nat.zero_le _)).mono (by rw [divUlt_budget];omega),
  Nat.zero_le _,(divUltState s).property.2.2.2.2.1,Nat.zero_le _,by intro a ha;cases ha⟩
def divQState (s : DivState) : AddState:=ifVecState (divQInput s)
lemma divQ_budget (s : DivState) : (divQState s).val.budget=s.val.base.budget+35*s.val.base.lhs.length:=by
  rw [divQState,ifVecState_budget]
  change (divUltState s).val.budget+3*(shiftConcat s.val.quotient (0,false)).length=_
  rw [divUlt_budget,shiftConcat_length,s.property.2.2.2.2];omega
lemma divQ_length (s : DivState) : (divQState s).val.output.length=s.val.base.lhs.length:=
  (ifVecState_length _).trans ((shiftConcat_length _ _).trans s.property.2.2.2.2)
def divRInput (s : DivState) : AddState:=
  ⟨⟨(divQState s).val.budget,(divQState s).val.graph,
    shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
    (divSubState s).val.output,0,notRef (divUltState s).val.cin,[]⟩,
  (divQState s).property.1,
  (shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _)).mono (by rw [divQ_budget];omega),
  (divSubState s).property.2.2.2.2.2.mono (by rw [divSub_budget,divQ_budget];omega),Nat.zero_le _,
  (divUltState s).property.2.2.2.2.1.trans (by rw [divUlt_budget,divQ_budget];omega),
  Nat.zero_le _,by intro a ha;cases ha⟩
def divRState (s : DivState) : AddState:=ifVecState (divRInput s)
lemma divR_budget (s : DivState) : (divRState s).val.budget=s.val.base.budget+38*s.val.base.lhs.length:=by
  rw [divRState,ifVecState_budget]
  change (divQState s).val.budget+3*(shiftConcat s.val.base.output _).length=_
  rw [divQ_budget,shiftConcat_length,s.property.2.2.1];omega
lemma divR_length (s : DivState) : (divRState s).val.output.length=s.val.base.lhs.length:=
  (ifVecState_length _).trans ((shiftConcat_length _ _).trans s.property.2.2.1)
lemma divQR_value (s : DivState) :
    ((divRState s).val.graph,(divQState s).val.output,(divRState s).val.output)=
      divStep s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output:=by
  have hq:=ifVecState_value (divQInput s)
  have hr:=ifVecState_value (divRInput s)
  change ((divQState s).val.graph,(divQState s).val.output)=ifVec (divUltState s).val.graph
    (notRef (divUltState s).val.cin) (shiftConcat s.val.quotient (0,false)) (shiftConcat s.val.quotient (0,true)) at hq
  change ((divRState s).val.graph,(divRState s).val.output)=ifVec (divQState s).val.graph
    (notRef (divUltState s).val.cin)
    (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)))
    (divSubState s).val.output at hr
  have h2:=congrArg Prod.snd (divSub_value s)
  have h3:=congrArg Prod.fst (divUlt_value s)
  have h4:=congrArg Prod.snd (divUlt_value s)
  dsimp only [Prod.fst,Prod.snd] at h2 h3 h4
  rw [h3,h4] at hq
  rw [show (divQState s).val.graph=_ from congrArg Prod.fst hq,h4,h2] at hr
  dsimp only [divStep]
  apply Prod.ext
  · exact congrArg (fun x : Graph×List Ref=>x.1) hr
  · apply Prod.ext
    · exact congrArg (fun x : Graph×List Ref=>x.2) hq
    · exact congrArg (fun x : Graph×List Ref=>x.2) hr
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGDivProcedure.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG.Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def stateBudgetP : Procedure addStateCode unaryCode (fun s=>s.val.budget):=
  ((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
noncomputable def stateGraphP : Procedure addStateCode graphCode (fun s=>s.val.graph):=
  addGraphP.precompose (fun s:AddState=>s.val)
noncomputable def stateOutputP : Procedure addStateCode (listCode refCode) (fun s=>s.val.output):=
  addOutputP.precompose (fun s:AddState=>s.val)
noncomputable def stateNotCinP : Procedure addStateCode refCode (fun s=>notRef s.val.cin):=
  (notRefP.comp addCinP).precompose (fun s:AddState=>s.val)
noncomputable def divBaseP : Procedure divStateCode addDataCode (fun s=>s.val.base):=
  (first addDataCode (listCode refCode)).precompose (fun s:DivState=>(s.val.base,s.val.quotient))
noncomputable def divQuotientP : Procedure divStateCode (listCode refCode) (fun s=>s.val.quotient):=
  (second addDataCode (listCode refCode)).precompose (fun s:DivState=>(s.val.base,s.val.quotient))
noncomputable def divBudgetP : Procedure divStateCode unaryCode (fun s=>s.val.base.budget):=
  ((first unaryCode addTail1).comp addViewP).comp divBaseP
noncomputable def divGraphP : Procedure divStateCode graphCode (fun s=>s.val.base.graph):=addGraphP.comp divBaseP
noncomputable def divLhsP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.lhs):=addLhsP.comp divBaseP
noncomputable def divRhsP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.rhs):=addRhsP.comp divBaseP
noncomputable def divRemP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.output):=addOutputP.comp divBaseP
noncomputable def divCurrP : Procedure divStateCode Nat.bits (fun s=>s.val.base.curr):=addCurrP.comp divBaseP
noncomputable def divCinP : Procedure divStateCode refCode (fun s=>s.val.base.cin):=addCinP.comp divBaseP
noncomputable def divPredP : Procedure divStateCode Nat.bits (fun s=>s.val.base.curr-1):=
  binarySub.comp (divCurrP.pair (Procedure.constant _ Nat.bits 1))
noncomputable def divShiftRemP : Procedure divStateCode (listCode refCode)
    (fun s=>shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))):=
  shiftConcatP.comp (divRemP.pair ((listGet refCode (0,false)).comp (divPredP.pair divLhsP)))
noncomputable def divSubInputP : Procedure divStateCode binaryStateCode divSubInput := by
  exact (packAddP.comp (divBudgetP.pair (divGraphP.pair (divShiftRemP.pair (divRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divSubStateP : Procedure divStateCode addStateCode divSubState:=subStateP.comp divSubInputP
noncomputable def divUltInputP : Procedure divStateCode addStateCode divUltInput := by
  let b:=stateBudgetP.comp divSubStateP
  let g:=stateGraphP.comp divSubStateP
  exact (packAddP.comp (b.pair (g.pair (divShiftRemP.pair (divRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divUltStateP : Procedure divStateCode addStateCode divUltState:=ultStateP.comp divUltInputP
noncomputable def divQInputP : Procedure divStateCode addStateCode divQInput := by
  let b:=stateBudgetP.comp divUltStateP
  let g:=stateGraphP.comp divUltStateP
  let c:=stateNotCinP.comp divUltStateP
  let q0:=shiftConcatP.comp (divQuotientP.pair (Procedure.constant _ refCode (0,false)))
  let q1:=shiftConcatP.comp (divQuotientP.pair (Procedure.constant _ refCode (0,true)))
  exact (packAddP.comp (b.pair (g.pair (q0.pair (q1.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def divQStateP : Procedure divStateCode addStateCode divQState:=ifVecStateP.comp divQInputP
noncomputable def divRInputP : Procedure divStateCode addStateCode divRInput := by
  let b:=stateBudgetP.comp divQStateP
  let g:=stateGraphP.comp divQStateP
  let c:=stateNotCinP.comp divUltStateP
  let nr:=stateOutputP.comp divSubStateP
  exact (packAddP.comp (b.pair (g.pair (divShiftRemP.pair (nr.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def divRStateP : Procedure divStateCode addStateCode divRState:=ifVecStateP.comp divRInputP
noncomputable def divNextP : Procedure divStateCode
    (prodCode graphCode (prodCode (listCode refCode) (listCode refCode)))
    (fun s=>divStep s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output):=
  ((stateGraphP.comp divRStateP).pair ((stateOutputP.comp divQStateP).pair
    (stateOutputP.comp divRStateP))).congrFun divQR_value
noncomputable def divStepStateP : Procedure divStateCode divStateCode divStepState := by
  let ns:=divNextP
  let g:=(first graphCode _).comp ns
  let q:=(first (listCode refCode) (listCode refCode)).comp ((second graphCode _).comp ns)
  let r:=(second (listCode refCode) (listCode refCode)).comp ((second graphCode _).comp ns)
  let len:=(listUnaryLength refCode (0,false)).comp divLhsP
  let b:=unaryAdd.comp (divBudgetP.pair (unaryMul.comp ((Procedure.constant _ unaryCode 38).pair len)))
  let base:=packAddP.comp (b.pair (g.pair (divLhsP.pair (divRhsP.pair (divPredP.pair (divCinP.pair r))))))
  exact (base.pair q).result (by intro s;rfl)
noncomputable def divIterationP : Procedure (prodCode unaryCode divStateCode) divStateCode
    (fun x=>(divStepState^[x.1]) x.2):=
  divStepStateP.iterate (Polynomial.C 1521000*(Polynomial.X+1)^4) (by
    intro n s i hi
    have hh:=divStateCode_bound ((divStepState^[i]) s)
    rw [divStepState_iterate_budget] at hh
    have hb:=divBudget_le_code s
    have hl:=s.property.1.2.1.1
    let M:=n+(divStateCode s).length+1
    have hM : 1≤M:=by dsimp [M];omega
    have hB : s.val.base.budget+1≤M:=by dsimp [M];omega
    have hw : 38*s.val.base.lhs.length≤38*M:=by omega
    have hii : i≤M:=by dsimp [M];omega
    have hm:=Nat.mul_le_mul hw hii
    have hx : s.val.base.budget+38*s.val.base.lhs.length*i+1≤39*M^2:=by nlinarith
    have hp:=Nat.pow_le_pow_left hx 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    calc
      (divStateCode ((divStepState^[i]) s)).length≤1000*(s.val.base.budget+38*s.val.base.lhs.length*i+1)^2:=hh
      _ ≤ 1000*(39*M^2)^2:=Nat.mul_le_mul_left _ hp
      _ = 1521000*(n+(divStateCode s).length+1)^4:=by dsimp [M];ring)
end ExactQuantumFactoring.NativeAIG.Emission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGDivWrapper.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def divEqInput (s : BinaryState) : AddState:=
  ⟨⟨s.val.val.budget,s.val.val.graph,s.val.val.rhs,List.replicate s.val.val.lhs.length (0,false),
    0,(0,false),[]⟩,s.val.property.1,s.val.property.2.2.1,
    RefsBound.zeros s.val.property.2.1.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def divEqState (s : BinaryState) : AddState:=eqState (divEqInput s)
lemma divEq_budget (s : BinaryState) : (divEqState s).val.budget=s.val.val.budget+6*s.val.val.lhs.length:=by
  rw [divEqState,eqState_budget]
  change s.val.val.budget+6*s.val.val.rhs.length=_
  rw [s.property]
lemma divEq_value (s : BinaryState) : ((divEqState s).val.graph,(divEqState s).val.cin)=
    eqVec s.val.val.graph s.val.val.rhs (List.replicate s.val.val.lhs.length (0,false)):=eqState_value _
def initializeDiv (s : BinaryState) : DivState:=
  ⟨⟨⟨(divEqState s).val.budget,(divEqState s).val.graph,s.val.val.lhs,s.val.val.rhs,
    s.val.val.lhs.length,(divEqState s).val.cin,List.replicate s.val.val.lhs.length (0,false)⟩,
    List.replicate s.val.val.lhs.length (0,false)⟩,
  ⟨(divEqState s).property.1,s.val.property.2.1.mono (by rw [divEq_budget];omega),
    s.val.property.2.2.1.mono (by rw [divEq_budget];omega),by
      change s.val.val.lhs.length ≤ (divEqState s).val.budget
      have h:=s.val.property.2.1.1;rw [divEq_budget];omega,
    (divEqState s).property.2.2.2.2.1,RefsBound.zeros (by
      have h:=s.val.property.2.1.1;rw [divEq_budget];omega)⟩,
  s.property,by simp,RefsBound.zeros (by have h:=s.val.property.2.1.1;rw [divEq_budget];omega),by simp⟩
def divLoopState (s : BinaryState) : DivState:=(divStepState^[s.val.val.lhs.length]) (initializeDiv s)
lemma divStepState_iterate_cin (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.cin=s.val.base.cin:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma divLoop_budget (s : BinaryState) : (divLoopState s).val.base.budget=
    s.val.val.budget+6*s.val.val.lhs.length+38*s.val.val.lhs.length*s.val.val.lhs.length:=by
  rw [divLoopState,divStepState_iterate_budget]
  change (divEqState s).val.budget+38*s.val.val.lhs.length*s.val.val.lhs.length=_
  rw [divEq_budget]
lemma divLoop_lhs (s : BinaryState) : (divLoopState s).val.base.lhs=s.val.val.lhs:=
  divStepState_iterate_lhs _ _
lemma divLoop_cin (s : BinaryState) : (divLoopState s).val.base.cin=(divEqState s).val.cin:=
  divStepState_iterate_cin _ _
lemma divLoop_value (s : BinaryState) :
    ((divLoopState s).val.base.graph,(divLoopState s).val.quotient,(divLoopState s).val.base.output)=
    divLoop s.val.val.lhs.length (divEqState s).val.graph s.val.val.lhs s.val.val.rhs s.val.val.lhs.length
      (List.replicate s.val.val.lhs.length (0,false)) (List.replicate s.val.val.lhs.length (0,false)):=
  divStepState_iterate_loop _ _
def divideOutInput (s : BinaryState) : AddState:=
  ⟨⟨(divLoopState s).val.base.budget,(divLoopState s).val.base.graph,
    List.replicate s.val.val.lhs.length (0,false),(divLoopState s).val.quotient,0,
    (divLoopState s).val.base.cin,[]⟩,
  (divLoopState s).property.1.1,RefsBound.zeros (by
    have h:=(divLoopState s).property.1.2.1.1;rw [divLoop_lhs] at h;exact h),
  (divLoopState s).property.2.2.2.1,Nat.zero_le _,(divLoopState s).property.1.2.2.2.2.1,
  Nat.zero_le _,by intro a ha;cases ha⟩
def divideState (s : BinaryState) : AddState:=ifVecState (divideOutInput s)
lemma divideState_value (s : BinaryState) : ((divideState s).val.graph,(divideState s).val.output)=
    divide s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=ifVecState_value (divideOutInput s)
  change _=ifVec (divLoopState s).val.base.graph (divLoopState s).val.base.cin
    (List.replicate s.val.val.lhs.length (0,false)) (divLoopState s).val.quotient at hh
  rw [divLoop_cin] at hh
  have he:=divEq_value s
  have hl:=divLoop_value s
  rw [show (divEqState s).val.graph=_ from congrArg Prod.fst he] at hl
  rw [show (divEqState s).val.cin=_ from congrArg Prod.snd he,
    show (divLoopState s).val.base.graph=_ from congrArg Prod.fst hl,
    show (divLoopState s).val.quotient=_ from congrArg (fun x=>x.2.1) hl] at hh
  exact hh
lemma divideState_budget (s : BinaryState) : (divideState s).val.budget=
    s.val.val.budget+9*s.val.val.lhs.length+38*s.val.val.lhs.length*s.val.val.lhs.length:=by
  rw [divideState,ifVecState_budget]
  change (divLoopState s).val.base.budget+3*(List.replicate s.val.val.lhs.length (0,false)).length=_
  rw [divLoop_budget,List.length_replicate];omega
lemma divideState_length (s : BinaryState) : (divideState s).val.output.length=s.val.val.lhs.length:=
  (ifVecState_length _).trans (List.length_replicate ..)

namespace Emission
noncomputable def divEqInputP : Procedure binaryStateCode addStateCode divEqInput := by
  let b:=stateBudgetP.precompose (fun s:BinaryState=>s.val)
  exact (packAddP.comp (b.pair (binaryGraphP.pair (binaryRhsP.pair ((zerosP.comp binaryLhsP).pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divEqStateP : Procedure binaryStateCode addStateCode divEqState:=eqStateP.comp divEqInputP
noncomputable def initializeDivP : Procedure binaryStateCode divStateCode initializeDiv := by
  let b:=stateBudgetP.comp divEqStateP
  let g:=stateGraphP.comp divEqStateP
  let c:=(addCinP.precompose (fun s:AddState=>s.val)).comp divEqStateP
  let len:=(listLength refCode (0,false)).comp binaryLhsP
  let zs:=zerosP.comp binaryLhsP
  let s:=packAddP.comp (b.pair (g.pair (binaryLhsP.pair (binaryRhsP.pair (len.pair (c.pair zs))))))
  exact (s.pair zs).result (by intro s;rfl)
noncomputable def divLoopStateP : Procedure binaryStateCode divStateCode divLoopState:=
  divIterationP.comp (((listUnaryLength refCode (0,false)).comp binaryLhsP).pair initializeDivP)
noncomputable def divideOutInputP : Procedure binaryStateCode addStateCode divideOutInput := by
  let b:=divBudgetP.comp divLoopStateP
  let g:=divGraphP.comp divLoopStateP
  let c:=divCinP.comp divLoopStateP
  let q:=divQuotientP.comp divLoopStateP
  let zs:=zerosP.comp binaryLhsP
  exact (packAddP.comp (b.pair (g.pair (zs.pair (q.pair ((Procedure.constant _ Nat.bits 0).pair
    (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divideStateP : Procedure binaryStateCode addStateCode divideState:=ifVecStateP.comp divideOutInputP
noncomputable def divideP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>divide s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  ((stateGraphP.pair stateOutputP).comp divideStateP).congrFun divideState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NativeAIGModWrapper.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def remainderOutInput (s : BinaryState) : AddState:=
  ⟨⟨(divLoopState s).val.base.budget,(divLoopState s).val.base.graph,
    s.val.val.lhs,(divLoopState s).val.base.output,0,(divLoopState s).val.base.cin,[]⟩,
  (divLoopState s).property.1.1,by
    have h:=(divLoopState s).property.1.2.1;rw [divLoop_lhs] at h;exact h,
  (divLoopState s).property.1.2.2.2.2.2,Nat.zero_le _,(divLoopState s).property.1.2.2.2.2.1,
  Nat.zero_le _,by intro a ha;cases ha⟩
def remainderState (s : BinaryState) : AddState:=ifVecState (remainderOutInput s)
lemma remainderState_value (s : BinaryState) : ((remainderState s).val.graph,(remainderState s).val.output)=
    remainder s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=ifVecState_value (remainderOutInput s)
  change _=ifVec (divLoopState s).val.base.graph (divLoopState s).val.base.cin
    s.val.val.lhs (divLoopState s).val.base.output at hh
  rw [divLoop_cin] at hh
  have he:=divEq_value s
  have hl:=divLoop_value s
  rw [show (divEqState s).val.graph=_ from congrArg Prod.fst he] at hl
  rw [show (divEqState s).val.cin=_ from congrArg Prod.snd he,
    show (divLoopState s).val.base.graph=_ from congrArg Prod.fst hl,
    show (divLoopState s).val.base.output=_ from congrArg (fun x=>x.2.2) hl] at hh
  exact hh
lemma remainderState_budget (s : BinaryState) : (remainderState s).val.budget=
    s.val.val.budget+9*s.val.val.lhs.length+38*s.val.val.lhs.length*s.val.val.lhs.length:=by
  rw [remainderState,ifVecState_budget]
  change (divLoopState s).val.base.budget+3*s.val.val.lhs.length=_
  rw [divLoop_budget];omega
lemma remainderState_length (s : BinaryState) : (remainderState s).val.output.length=s.val.val.lhs.length:=
  ifVecState_length _
namespace Emission
noncomputable def remainderOutInputP : Procedure binaryStateCode addStateCode remainderOutInput := by
  let b:=divBudgetP.comp divLoopStateP
  let g:=divGraphP.comp divLoopStateP
  let c:=divCinP.comp divLoopStateP
  let rem:=divRemP.comp divLoopStateP
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (rem.pair ((Procedure.constant _ Nat.bits 0).pair
    (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def remainderStateP : Procedure binaryStateCode addStateCode remainderState:=ifVecStateP.comp remainderOutInputP
noncomputable def remainderP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>remainder s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  ((stateGraphP.pair stateOutputP).comp remainderStateP).congrFun remainderState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
