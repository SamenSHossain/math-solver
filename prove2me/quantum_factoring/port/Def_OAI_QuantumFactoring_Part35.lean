/-
Exact quantum factoring development (port of OpenAI's formalization), part 35 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: ExpressionPowerEmission.lean, CoveringPowerEmission.lean, RationalTemplateEmission.lean, PolynomialTemplateEmission.lean, ProgressionTemplateEmission.lean, MajorantTemplateEmission.lean, RetentionTemplateEmission.lean, RootCircuitEmission.lean, GcdEmission.lean, TrialControlEmission.lean, ContinuedFractionEmission.lean, ProperDivisorEmission.lean, ModularSumEmission.lean, CyclicEmission.lean, CyclicPowerEmission.lean, CyclicTestEmission.lean, PrimalityEmission.lean, StackEmission.lean, CleanPermutationEmission.lean, TriangularProgramEmission.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part34

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionPowerEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type} (ev : v→List Bool)
lemma exprCode_length (a : NatExpr v) :
    (exprCode ev a).length=2*a.size+2*a.maxConst.bits.length+(listCode (exprTokenCode ev) (exprTokens a)).length+2:=by
  simp only [exprCode,exprPayload,exprView,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
lemma exprCode_const (a : ℕ) : (exprCode ev (NatExpr.const a)).length=4*a.bits.length+11:=by
  rw [exprCode_length]
  simp only [NatExpr.size,NatExpr.maxConst,exprTokens,listCode_length_cons,exprTokenCode,sumCode,List.length_cons]
  have hz : (listCode (sumCode ev (sumCode Nat.bits Nat.bits)) []).length=1:=rfl
  rw [hz];omega
lemma exprCode_mul_le (a b : NatExpr v) :
    (exprCode ev (.mul a b)).length≤(exprCode ev a).length+(exprCode ev b).length+24:=by
  have hm : (max a.maxConst b.maxConst).bits.length≤a.maxConst.bits.length+b.maxConst.bits.length:=by
    rcases le_total a.maxConst b.maxConst with h|h
    · rw [max_eq_right h];omega
    · rw [max_eq_left h];omega
  have h1:=listCode_length_append (exprTokenCode ev) (exprTokens a) (exprTokens b)
  have h2:=listCode_length_append (exprTokenCode ev) (exprTokens a++exprTokens b) [pairToken]
  have h3:=listCode_length_append (exprTokenCode ev) (exprTokens a++exprTokens b++[pairToken]) [opToken 1,compToken]
  rw [exprCode_length,exprCode_length,exprCode_length]
  simp only [NatExpr.size,NatExpr.maxConst,exprTokens]
  have hx : (listCode (exprTokenCode ev) [pairToken]).length=7:=rfl
  have hy : (listCode (exprTokenCode ev) [opToken 1,compToken]).length=19:=rfl
  rw [hx] at h2;rw [hy] at h3
  omega

def exprPowerStep (s : NatExpr v×NatExpr v) : NatExpr v×NatExpr v:=(s.1,.mul s.2 s.1)
lemma exprPowerStep_fst (s : NatExpr v×NatExpr v) (i : ℕ) : ((exprPowerStep^[i]) s).1=s.1:=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply'];exact ih
lemma exprPowerStep_bound (s : NatExpr v×NatExpr v) (i : ℕ) :
    (exprCode ev ((exprPowerStep^[i]) s).2).length≤(exprCode ev s.2).length+i*((exprCode ev s.1).length+24):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    have hh:=exprCode_mul_le ev ((exprPowerStep^[i]) s).2 ((exprPowerStep^[i]) s).1
    rw [exprPowerStep_fst] at hh
    change (exprCode ev (.mul _ _)).length≤_
    rw [exprPowerStep_fst]
    nlinarith
lemma exprPowerStep_start (a : NatExpr v) (i : ℕ) :
    (exprPowerStep^[i]) (a,.const 1)=(a,a.pow i):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',ih];rfl
namespace Emission
noncomputable def exprPowerP : Procedure (prodCode unaryCode (exprCode ev)) (exprCode ev)
    (fun x=>x.2.pow x.1):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let step : Procedure (prodCode (exprCode ev) (exprCode ev)) (prodCode (exprCode ev) (exprCode ev)) exprPowerStep:=
    a.pair ((exprMulP ev).comp (b.pair a))
  let rep:=step.iterate (Polynomial.X^2+Polynomial.C 25*Polynomial.X) (by
    intro n s i hi
    have hh:=exprPowerStep_bound ev s i
    simp only [prodCode,pairBits_length,exprPowerStep_fst,Polynomial.eval_add,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    nlinarith)
  let e:=first unaryCode (exprCode ev)
  let a:=second unaryCode (exprCode ev)
  exact ((second (exprCode ev) (exprCode ev)).comp
    (rep.comp (e.pair (a.pair (Procedure.constant _ (exprCode ev) (.const 1)))))).congrFun (by
      intro x;change ((exprPowerStep^[x.1]) (x.2,.const 1)).2=_
      rw [exprPowerStep_start])
end Emission
namespace Emits
open BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma npow {a : α→NatExpr v} {k : α→ℕ} (ha : BitStackProgram.Emits ea (exprCode ev) a)
    (hk : BitStackProgram.Emits ea unaryCode k) : BitStackProgram.Emits ea (exprCode ev) (fun x=>(a x).pow (k x)):=
  (ofProcedure (Emission.exprPowerP ev)).comp (hk.pair ha)
lemma iSignedPower {a : α→IntExpr v} {k : α→ℕ} (ha : BitStackProgram.Emits ea (intExprCode ev) a)
    (hk : BitStackProgram.Emits ea unaryCode k) : BitStackProgram.Emits ea (intExprCode ev) (fun x=>(a x).signedPower (k x)):=by
  have hM:=iOfNat (npow (iNatAbs ha) hk)
  exact ((hk.unaryNat.natEven).conditional hM (iIte (ineg ha) (ipos ha) hM (iNeg hM))).congr (by
    intro x;simp only [IntExpr.signedPower,decide_eq_true_eq])
lemma rSignedPower {a : α→RatExpr v} {k : α→ℕ} (ha : BitStackProgram.Emits ea (ratExprCode ev) a)
    (hk : BitStackProgram.Emits ea unaryCode k) : BitStackProgram.Emits ea (ratExprCode ev) (fun x=>(a x).signedPower (k x)):=
  rmk (iSignedPower (rnum ha) hk) (npow (rden ha) hk)
lemma repeatedSuccess {a : α→RatExpr v} {k : α→ℕ} (ha : BitStackProgram.Emits ea (ratExprCode ev) a)
    (hk : BitStackProgram.Emits ea unaryCode k) : BitStackProgram.Emits ea (ratExprCode ev) (fun x=>(a x).repeatedSuccess (k x)):=
  rSub (const _ _ (RatExpr.const 1)) (rSignedPower (rSub (const _ _ (RatExpr.const 1)) ha) hk)
end Emits
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CoveringPowerEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type} (ev : v→List Bool)
lemma bits_length_max_le (a b : ℕ) : (max a b).bits.length≤a.bits.length+b.bits.length:=by
  rcases le_total a b with h|h
  · rw [max_eq_right h];omega
  · rw [max_eq_left h];omega
lemma tokenCode_length_append (a b : List (ExprToken v)) :
    (listCode (exprTokenCode ev) (a++b)).length=(listCode (exprTokenCode ev) a).length+(listCode (exprTokenCode ev) b).length-1:=by
  have h:=listCode_length_append (exprTokenCode ev) a b;omega
lemma exprCode_ite_le (a b c d : NatExpr v) :
    (exprCode ev (.iteLe a b c d)).length≤(exprCode ev a).length+(exprCode ev b).length+
      (exprCode ev c).length+(exprCode ev d).length+100:=by
  have h1:=bits_length_max_le a.maxConst b.maxConst
  have h2:=bits_length_max_le c.maxConst d.maxConst
  have h3:=bits_length_max_le (max a.maxConst b.maxConst) (max c.maxConst d.maxConst)
  simp only [exprCode_length,NatExpr.size,NatExpr.maxConst,exprTokens,muxTokens,leTokens]
  have hpair : (listCode (exprTokenCode ev) [pairToken]).length=7:=rfl
  have ho5 : (listCode (exprTokenCode ev) [opToken 5,compToken]).length=21:=rfl
  have ho6 : (listCode (exprTokenCode ev) [opToken 6,compToken]).length=23:=rfl
  have ho7 : (listCode (exprTokenCode ev) [opToken 7,compToken]).length=23:=rfl
  simp only [tokenCode_length_append,hpair,ho5,ho6,ho7]
  omega

def coveringStep (s : ℕ×(NatExpr v×NatExpr v)) : ℕ×(NatExpr v×NatExpr v):=
  (s.1*2,s.2.1,.iteLe s.2.1 (.const s.1) s.2.2 (.const (s.1*2)))
lemma coveringStep_pow (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    ((coveringStep^[i]) s).1=s.1*2^i:=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply'];change ((coveringStep^[i]) s).1*2=_
               rw [ih,pow_succ,Nat.mul_assoc]
lemma coveringStep_base (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    ((coveringStep^[i]) s).2.1=s.2.1:=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply'];exact ih
lemma coveringStep_pow_size (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    (((coveringStep^[i]) s).1).bits.length≤(s.1).bits.length+2*i+1:=by
  rw [coveringStep_pow]
  have hm:=bits_length_mul s.1 (2^i)
  have hp:=bits_length_pow 2 i
  have ht : (2:ℕ).bits.length=2:=rfl
  rw [ht] at hp;omega
lemma coveringStep_expr_bound (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    (exprCode ev ((coveringStep^[i]) s).2.2).length≤(exprCode ev s.2.2).length+
      i*((exprCode ev s.2.1).length+8*(s.1).bits.length+16*i+200):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    have hh:=exprCode_ite_le ev ((coveringStep^[i]) s).2.1 (.const ((coveringStep^[i]) s).1)
      ((coveringStep^[i]) s).2.2 (.const (((coveringStep^[i]) s).1*2))
    rw [exprCode_const,exprCode_const,coveringStep_base] at hh
    have hp:=coveringStep_pow_size s i
    have h2:=bits_length_mul ((coveringStep^[i]) s).1 2
    have ht : (2:ℕ).bits.length=2:=rfl
    rw [ht] at h2
    rw [Function.iterate_succ_apply']
    change (exprCode ev (.iteLe _ _ _ _)).length≤_
    rw [coveringStep_base]
    nlinarith
lemma coveringStep_start (d : NatExpr v) (i : ℕ) :
    (coveringStep^[i]) (1,d,.const 1)=(2^i,d,OrderTrial.Expressions.coveringPow d i):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',ih];simp only [coveringStep,pow_succ,OrderTrial.Expressions.coveringPow]
namespace Emission
noncomputable def coveringPowP : Procedure (prodCode unaryCode (exprCode ev)) (exprCode ev)
    (fun x=>OrderTrial.Expressions.coveringPow x.2 x.1):=by
  let ecode:=prodCode (exprCode ev) (exprCode ev)
  let scode:=prodCode Nat.bits ecode
  let p:=first Nat.bits ecode
  let r:=second Nat.bits ecode
  let d:=(first (exprCode ev) (exprCode ev)).comp r
  let a:=(second (exprCode ev) (exprCode ev)).comp r
  let p2:=binaryMul.comp (p.pair (Procedure.constant scode Nat.bits 2))
  let expr:=(exprIteP ev).comp (d.pair (((exprConstP ev).comp p).pair
    (a.pair ((exprConstP ev).comp p2))))
  let step : Procedure scode scode coveringStep:=p2.pair (d.pair expr)
  let rep:=step.iterate (Polynomial.C 100*Polynomial.X^2+Polynomial.C 205*Polynomial.X+2) (by
    intro n s i hi
    have hp:=coveringStep_pow_size s i
    have he:=coveringStep_expr_bound ev s i
    simp only [scode,ecode,prodCode,pairBits_length,coveringStep_base,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,
      Polynomial.eval_ofNat]
    nlinarith)
  let k:=first unaryCode (exprCode ev)
  let d:=second unaryCode (exprCode ev)
  let start:=(Procedure.constant _ Nat.bits 1).pair (d.pair (Procedure.constant _ (exprCode ev) (.const 1)))
  let out:=(second (exprCode ev) (exprCode ev)).comp (second Nat.bits ecode)
  exact (out.comp (rep.comp (k.pair start))).congrFun (by
    intro x;change ((coveringStep^[x.1]) (1,x.2,.const 1)).2.2=_
    rw [coveringStep_start])
end Emission
namespace Emits
open BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma coveringPow {d : α→NatExpr v} {k : α→ℕ} (hd : BitStackProgram.Emits ea (exprCode ev) d)
    (hk : BitStackProgram.Emits ea unaryCode k) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>OrderTrial.Expressions.coveringPow (d x) (k x)):=
  (ofProcedure (Emission.coveringPowP ev)).comp (hk.pair hd)
end Emits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RationalTemplateEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma nMin {a b : α→NatExpr v} (ha : NEm a) (hb : NEm b) : NEm (fun x=>NatExpr.min (a x) (b x)):=nite ha hb ha hb
lemma nMax {a b : α→NatExpr v} (ha : NEm a) (hb : NEm b) : NEm (fun x=>NatExpr.max (a x) (b x)):=nite ha hb hb ha
lemma nPow {a : α→NatExpr v} (ha : NEm a) (k : ℕ) : NEm (fun x=>NatExpr.pow (a x) k):=by
  induction k with
  | zero=>exact const _ _ (NatExpr.const 1)
  | succ k ih=>exact nmul ih ha
lemma rSum {a : α→ℕ→RatExpr v} (ha : ∀i,REm (fun x=>a x i)) (k : ℕ) :
    REm (fun x=>RatExpr.sum (a x) k):=by
  induction k with
  | zero=>exact const _ _ (RatExpr.const 0)
  | succ k ih=>exact rAdd ih (ha k)
lemma rSumList {β : Type} {a : α→β→RatExpr v} (ha : ∀i,REm (fun x=>a x i)) (l : List β) :
    REm (fun x=>RatExpr.sumList (a x) l):=by
  induction l with
  | nil=>exact const _ _ (RatExpr.const 0)
  | cons b bs ih=>exact rAdd (ha b) ih
end ExactQuantumFactoring.NetworkEmission.Emits
namespace ExactQuantumFactoring
syntax "rat_emit" : tactic
macro_rules
  | `(tactic| rat_emit) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact BitStackProgram.Emits.const _ _ _
    | (apply NetworkEmission.Emits.rOfInt;rat_emit)
    | (apply NetworkEmission.Emits.rOfNat;rat_emit)
    | (apply NetworkEmission.Emits.rConst;rat_emit)
    | (apply NetworkEmission.Emits.rIfEq <;> rat_emit)
    | (apply NetworkEmission.Emits.rIfLt <;> rat_emit)
    | (apply NetworkEmission.Emits.rIfLe <;> rat_emit)
    | (apply NetworkEmission.Emits.rIfIntLe <;> rat_emit)
    | (apply NetworkEmission.Emits.rIfNatLe <;> rat_emit)
    | (apply NetworkEmission.Emits.rMax <;> rat_emit)
    | (apply NetworkEmission.Emits.rMin <;> rat_emit)
    | (apply NetworkEmission.Emits.rAdd <;> rat_emit)
    | (apply NetworkEmission.Emits.rSub <;> rat_emit)
    | (apply NetworkEmission.Emits.rMul <;> rat_emit)
    | (apply NetworkEmission.Emits.rDiv <;> rat_emit)
    | (apply NetworkEmission.Emits.rNeg;rat_emit)
    | (apply NetworkEmission.Emits.rInv;rat_emit)
    | (apply NetworkEmission.Emits.rPow;rat_emit)
    | (apply NetworkEmission.Emits.rCeil;rat_emit)
    | (apply NetworkEmission.Emits.rFloor;rat_emit)
    | (apply NetworkEmission.Emits.rCeilNat;rat_emit)
    | (apply NetworkEmission.Emits.nMin <;> rat_emit)
    | (apply NetworkEmission.Emits.nMax <;> rat_emit)
    | (apply NetworkEmission.Emits.nPow;rat_emit)
    | (apply NetworkEmission.Emits.nadd <;> rat_emit)
    | (apply NetworkEmission.Emits.nsub <;> rat_emit)
    | (apply NetworkEmission.Emits.nmul <;> rat_emit)
    | (apply NetworkEmission.Emits.ndiv <;> rat_emit)
    | (apply NetworkEmission.Emits.nmod <;> rat_emit))
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PolynomialTemplateEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
/-- A fixed polynomial syntax skeleton transports literal coefficient emitters
through substitution. The outer polynomial's depth is fixed; input coefficients
are generated by the supplied charged Boolean-stack procedures. -/
def PolyEmits (ea : α→List Bool) (ev : v→List Bool) (f : α→PolyExpr v) : Prop:=
  ∀(g : α→PolyExpr v), (∀k,BitStackProgram.Emits ea (ratExprCode ev) (fun x=>(g x).coeff k))→
    ∀k,BitStackProgram.Emits ea (ratExprCode ev) (fun x=>((f x).comp (g x)).coeff k)
namespace PolyEmits
lemma C {f : α→RatExpr v} (hf : BitStackProgram.Emits ea (ratExprCode ev) f) :
    PolyEmits ea ev (fun x=>PolyExpr.C (f x)):=by
  intro g hg k;change BitStackProgram.Emits _ _ (fun x=>if k=0 then f x else RatExpr.const 0)
  by_cases h:k=0
  · simpa only [ite_eq_left h] using hf
  · simpa only [ite_eq_right h] using (const ea (ratExprCode ev) (RatExpr.const 0))
lemma X : PolyEmits ea ev (fun _=>PolyExpr.X):=by intro g hg k;exact hg k
lemma add {f g : α→PolyExpr v} (hf : PolyEmits ea ev f) (hg : PolyEmits ea ev g) :
    PolyEmits ea ev (fun x=>PolyExpr.add (f x) (g x)):=by
  intro b hb k;exact rAdd (hf b hb k) (hg b hb k)
lemma neg {f : α→PolyExpr v} (hf : PolyEmits ea ev f) :
    PolyEmits ea ev (fun x=>PolyExpr.negation (f x)):=by
  intro b hb k;exact rNeg (hf b hb k)
lemma sub {f g : α→PolyExpr v} (hf : PolyEmits ea ev f) (hg : PolyEmits ea ev g) :
    PolyEmits ea ev (fun x=>PolyExpr.sub (f x) (g x)):=hf.add hg.neg
lemma mul {f g : α→PolyExpr v} (hf : PolyEmits ea ev f) (hg : PolyEmits ea ev g) :
    PolyEmits ea ev (fun x=>PolyExpr.mul (f x) (g x)):=by
  intro b hb k;exact rSum (fun i=>rMul (hf b hb i) (hg b hb (k-i))) (k+1)
lemma constant (q : ℚ) : PolyEmits ea ev (fun _=>PolyExpr.const q):=C (const _ _ (RatExpr.const q))
lemma pow {f : α→PolyExpr v} (hf : PolyEmits ea ev f) (k : ℕ) :
    PolyEmits ea ev (fun x=>PolyExpr.pow (f x) k):=by
  induction k with
  | zero=>exact constant 1
  | succ k ih=>exact ih.mul hf
lemma literal (p : PolyExpr v) : PolyEmits ea ev (fun _=>p):=by
  induction p with
  | C r=>exact C (const _ _ r)
  | X=>exact X
  | add a b ha hb=>exact ha.add hb
  | negation a ha=>exact ha.neg
  | mul a b ha hb=>exact ha.mul hb
lemma comp_comp (a b c : PolyExpr v) : (a.comp b).comp c=a.comp (b.comp c):=by
  induction a with
  | C r=>rfl
  | X=>rfl
  | add a b ha hb=>simp only [PolyExpr.comp,ha,hb]
  | negation a ha=>simp only [PolyExpr.comp,ha]
  | mul a b ha hb=>simp only [PolyExpr.comp,ha,hb]
lemma comp {f g : α→PolyExpr v} (hf : PolyEmits ea ev f) (hg : PolyEmits ea ev g) :
    PolyEmits ea ev (fun x=>(f x).comp (g x)):=by
  intro b hb k
  exact (hf (fun x=>(g x).comp (b x)) (hg b hb) k).congr (by intro x;rw [comp_comp])
lemma comp_X (a : PolyExpr v) : a.comp .X=a:=by
  induction a with
  | C r=>rfl
  | X=>rfl
  | add a b ha hb=>simp only [PolyExpr.comp,ha,hb]
  | negation a ha=>simp only [PolyExpr.comp,ha]
  | mul a b ha hb=>simp only [PolyExpr.comp,ha,hb]
lemma coeff {f : α→PolyExpr v} (hf : PolyEmits ea ev f) (k : ℕ) :
    BitStackProgram.Emits ea (ratExprCode ev) (fun x=>(f x).coeff k):=
  (hf (fun _=>.X) (fun i=>const _ _ (PolyExpr.coeff .X i)) k).congr (by intro x;rw [comp_X])
end PolyEmits
end ExactQuantumFactoring.NetworkEmission
namespace ExactQuantumFactoring
syntax "poly_emit" : tactic
macro_rules
  | `(tactic| poly_emit) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact NetworkEmission.PolyEmits.X
    | exact NetworkEmission.PolyEmits.constant _
    | (apply NetworkEmission.PolyEmits.add <;> poly_emit)
    | (apply NetworkEmission.PolyEmits.sub <;> poly_emit)
    | (apply NetworkEmission.PolyEmits.mul <;> poly_emit)
    | (apply NetworkEmission.PolyEmits.neg;poly_emit)
    | (apply NetworkEmission.PolyEmits.pow;poly_emit)
    | (apply NetworkEmission.PolyEmits.comp <;> poly_emit)
    | (apply NetworkEmission.PolyEmits.C;rat_emit))
end ExactQuantumFactoring

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ProgressionTemplateEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits OrderTrial.Expressions
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma powerSumE {M : α→RatExpr v} (hM : REm M) (q : ℕ) : REm (fun x=>powerSum q (M x)):=by
  rcases q with _|_|_|_|_|q <;> simp only [powerSum] <;> rat_emit
lemma fiveTermE {a : α→ℕ→RatExpr v} {lo hi : α→NatExpr v}
    (ha : ∀q,REm (fun x=>a x q)) (hl : NEm lo) (hh : NEm hi) :
    REm (fun x=>fiveTerm (a x) (lo x) (hi x)):=by
  exact rIfNatLe hl hh (rSum (fun q=>rMul (ha q) (rSub (powerSumE (rOfNat hh) q)
    (powerSumE (rOfNat hl) q))) 5) (const _ _ 0)
lemma linearE {a b : α→RatExpr v} {lo hi : α→NatExpr v}
    (ha : REm a) (hb : REm b) (hl : NEm lo) (hh : NEm hi) :
    REm (fun x=>linear (a x) (b x) (lo x) (hi x)):=by
  apply fiveTermE _ hl hh
  intro q;by_cases h0:q=0
  · simpa only [ite_eq_left h0] using ha
  · by_cases h1:q=1
    · simpa only [ite_eq_right h0,ite_eq_left h1] using hb
    · simpa only [ite_eq_right h0,ite_eq_right h1] using (const ea (ratExprCode ev) (0:RatExpr v))
lemma rampE {a b : α→RatExpr v} {M : α→NatExpr v}
    (ha : REm a) (hb : REm b) (hM : NEm M) : REm (fun x=>ramp (a x) (b x) (M x)):=by
  have hc:=rCeilNat (rDiv (rNeg ha) hb)
  exact rIfLt (const _ _ 0) hb (linearE ha hb hc hM)
    (rIfLt hb (const _ _ 0) (linearE ha hb (const _ _ (NatExpr.const 0)) (nMin hM hc))
      (rMul (rOfNat hM) (rMax (const _ _ 0) ha)))
lemma phaseReE {a b : α→RatExpr v} {M : α→NatExpr v}
    (ha : REm a) (hb : REm b) (hM : NEm M) : REm (fun x=>phaseRe (a x) (b x) (M x)):=by
  have hl:=linearE (rAdd ha (const _ _ (1/2))) hb (const _ _ (NatExpr.const 0)) hM
  have hr:=rampE ha hb hM
  have hs:=rampE (rSub ha (const _ _ (1/2))) hb hM
  have ht:=rampE (rSub ha (const _ _ 1)) hb hM
  unfold phaseRe;rat_emit
lemma phaseImE {a b : α→RatExpr v} {M : α→NatExpr v}
    (ha : REm a) (hb : REm b) (hM : NEm M) : REm (fun x=>phaseIm (a x) (b x) (M x)):=by
  have hl:=linearE (rAdd ha (const _ _ (1/2))) hb (const _ _ (NatExpr.const 0)) hM
  have hr:=rampE (rAdd ha (const _ _ (1/4))) hb hM
  have hs:=rampE (rSub ha (const _ _ (1/4))) hb hM
  have ht:=rampE (rSub ha (const _ _ (3/4))) hb hM
  have hu:=rampE (rSub ha (const _ _ (5/4))) hb hM
  unfold phaseIm;rat_emit
lemma binExpr {Q d j : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) :
    NEm (fun x=>binE (Q x) (d x) (j x)):=by unfold binE;rat_emit
lemma errorE {Q d j : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>error (Q x) (d x) (j x)):=by
  have h:=binExpr hQ hd hj
  unfold error;rat_emit
lemma offsetE {Q d j t : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) (ht : NEm t) :
    REm (fun x=>offset (Q x) (d x) (j x) (t x)):=by
  have h:=errorE hQ hd hj
  unfold offset;rat_emit
lemma slopeE {Q d j : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>OrderTrial.Expressions.slope (Q x) (d x) (j x)):=by
  have h:=errorE hQ hd hj
  unfold OrderTrial.Expressions.slope;rat_emit
lemma countE {Q d t : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (ht : NEm t) :
    NEm (fun x=>count (Q x) (d x) (t x)):=by unfold count;rat_emit
lemma probabilityE {Q d j t : α→NatExpr v} (hQ : NEm Q) (hd : NEm d) (hj : NEm j) (ht : NEm t) :
    REm (fun x=>probability (Q x) (d x) (j x) (t x)):=by
  have hr:=phaseReE (offsetE hQ hd hj ht) (slopeE hQ hd hj) (countE hQ hd ht)
  have hi:=phaseImE (offsetE hQ hd hj ht) (slopeE hQ hd hj) (countE hQ hd ht)
  unfold probability;rat_emit
end ExactQuantumFactoring.NetworkEmission.Emits

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/MajorantTemplateEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits OrderTrial.Expressions
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "IEm" => BitStackProgram.Emits ea (intExprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
local notation "PEm" => PolyEmits ea ev
lemma linearPolyE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) :
    PEm (fun x=>linearPoly (d x) (e x)):=by unfold linearPoly;poly_emit
lemma integralZeroE {d : α→NatExpr v} {a : α→PolyExpr v} (hd : NEm d) (ha : PEm a) :
    PEm (fun x=>integralZero (d x) (a x)):=by
  have h:=linearPolyE hd (const _ _ 0)
  exact (PolyEmits.C (rInv (rOfNat hd))).mul (ha.comp h)
lemma integralSlopeE {d : α→NatExpr v} {e : α→RatExpr v} {a b : α→PolyExpr v}
    (hd : NEm d) (he : REm e) (ha : PEm a) (hb : PEm b) :
    PEm (fun x=>integralSlope (d x) (e x) (a x) (b x)):=by
  exact (PolyEmits.C (rInv (rMul (rOfNat hd) he))).mul
    ((hb.comp (linearPolyE hd he)).sub (ha.comp (linearPolyE hd (const _ _ 0))))
lemma massZeroE {d : α→NatExpr v} (hd : NEm d) (q : ℤ) :
    PEm (fun x=>massZero (d x) q):=by
  exact ((integralZeroE hd (PolyEmits.literal (phaseRePoly q))).pow 2).add
    ((integralZeroE hd (PolyEmits.literal (phaseImPoly q))).pow 2)
lemma massSlopeE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) (q r : ℤ) :
    PEm (fun x=>massSlope (d x) (e x) q r):=by
  exact ((integralSlopeE hd he (PolyEmits.literal (splineRePoly q)) (PolyEmits.literal (splineRePoly r))).pow 2).add
    ((integralSlopeE hd he (PolyEmits.literal (splineImPoly q)) (PolyEmits.literal (splineImPoly r))).pow 2)
lemma massCoeffE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) (q r : ℤ) (k : ℕ) :
    REm (fun x=>massCoeff (d x) (e x) q r k):=
  rIfEq he (const _ _ 0) ((massZeroE hd q).coeff k) ((massSlopeE hd he q r).coeff k)
lemma roundedE {D : α→NatExpr v} {a : α→RatExpr v} (hD : NEm D) (ha : REm a) :
    REm (fun x=>rounded (D x) (a x)):=by unfold rounded;rat_emit
lemma roundingDenE {Q B : α→NatExpr v} (hQ : NEm Q) (hB : NEm B) :
    NEm (fun x=>roundingDen (Q x) (B x)):=nmul hQ (nPow hB 8)
lemma lowE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) (q : ℤ×ℤ) :
    NEm (fun x=>low (d x) (e x) q):=by unfold low;rat_emit
lemma highE {d : α→NatExpr v} {e : α→RatExpr v} (hd : NEm d) (he : REm e) (q : ℤ×ℤ) :
    NEm (fun x=>high (d x) (e x) q):=by unfold high;rat_emit
lemma pieceSumE {Q B d j : α→NatExpr v} (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) (q : ℤ×ℤ) :
    REm (fun x=>pieceSum (Q x) (B x) (d x) (j x) q):=by
  have he:=errorE hQ hd hj
  have hl:=lowE hd he q;have hh:=highE hd he q
  exact rAdd (fiveTermE (fun k=>roundedE (roundingDenE hQ hB) (massCoeffE hd he q.1 q.2 k)) hl hh)
    (rMul (rOfNat (nsub hh hl)) (rDiv (const _ _ 64) (rOfNat hQ)))
lemma majorantSumExpr {Q B d j : α→NatExpr v} (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>majorantSumE (Q x) (B x) (d x) (j x)):=
  rDiv (rSumList (fun q=>pieceSumE hQ hB hd hj q) quarterList) (const _ _ 2)
lemma dynamicRampE {q : α→IntExpr v} (hq : IEm q) (a : ℤ) :
    PEm (fun x=>dynamicRamp (q x) a):=by unfold dynamicRamp;poly_emit
lemma dynamicRampLinE {q : α→IntExpr v} (hq : IEm q) (a : ℤ) :
    PEm (fun x=>dynamicRampLin (q x) a):=by unfold dynamicRampLin;poly_emit
lemma dynamicSplineReE {q : α→IntExpr v} (hq : IEm q) : PEm (fun x=>dynamicSplineRe (q x)):=by
  have h0:=dynamicRampE hq 0;have h2:=dynamicRampE hq 2;have h4:=dynamicRampE hq 4
  unfold dynamicSplineRe;poly_emit
lemma dynamicSplineImE {q : α→IntExpr v} (hq : IEm q) : PEm (fun x=>dynamicSplineIm (q x)):=by
  have h0:=dynamicRampE hq (-1);have h2:=dynamicRampE hq 1;have h4:=dynamicRampE hq 3;have h5:=dynamicRampE hq 5
  unfold dynamicSplineIm;poly_emit
lemma dynamicPhaseReE {q : α→IntExpr v} (hq : IEm q) : PEm (fun x=>dynamicPhaseRe (q x)):=by
  have h0:=dynamicRampLinE hq 0;have h2:=dynamicRampLinE hq 2;have h4:=dynamicRampLinE hq 4
  unfold dynamicPhaseRe;poly_emit
lemma dynamicPhaseImE {q : α→IntExpr v} (hq : IEm q) : PEm (fun x=>dynamicPhaseIm (q x)):=by
  have h0:=dynamicRampLinE hq (-1);have h2:=dynamicRampLinE hq 1;have h4:=dynamicRampLinE hq 3;have h5:=dynamicRampLinE hq 5
  unfold dynamicPhaseIm;poly_emit
lemma dynamicMassZeroE {d : α→NatExpr v} {q : α→IntExpr v} (hd : NEm d) (hq : IEm q) :
    PEm (fun x=>dynamicMassZero (d x) (q x)):=
  ((integralZeroE hd (dynamicPhaseReE hq)).pow 2).add ((integralZeroE hd (dynamicPhaseImE hq)).pow 2)
lemma dynamicMassSlopeE {d : α→NatExpr v} {e : α→RatExpr v} {q r : α→IntExpr v}
    (hd : NEm d) (he : REm e) (hq : IEm q) (hr : IEm r) :
    PEm (fun x=>dynamicMassSlope (d x) (e x) (q x) (r x)):=
  ((integralSlopeE hd he (dynamicSplineReE hq) (dynamicSplineReE hr)).pow 2).add
    ((integralSlopeE hd he (dynamicSplineImE hq) (dynamicSplineImE hr)).pow 2)
lemma dynamicMassCoeffE {d : α→NatExpr v} {e : α→RatExpr v} {q r : α→IntExpr v}
    (hd : NEm d) (he : REm e) (hq : IEm q) (hr : IEm r) (k : ℕ) :
    REm (fun x=>dynamicMassCoeff (d x) (e x) (q x) (r x) k):=
  rIfEq he (const _ _ 0) ((dynamicMassZeroE hd hq).coeff k) ((dynamicMassSlopeE hd he hq hr).coeff k)
lemma quarterE {a : α→RatExpr v} (ha : REm a) : IEm (fun x=>quarter (a x)):=by unfold quarter;rat_emit
lemma majorantExpr {Q B d j u : α→NatExpr v} (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) (hu : NEm u) :
    REm (fun x=>majorantE (Q x) (B x) (d x) (j x) (u x)):=by
  have he:=errorE hQ hd hj
  have ha:=rDiv (rOfNat hu) (rOfNat hd)
  exact rAdd (rSum (fun k=>rMul (roundedE (roundingDenE hQ hB)
    (dynamicMassCoeffE hd he (quarterE ha) (quarterE (rAdd ha he)) k)) (rPow (rOfNat hu) k)) 5)
      (rDiv (const _ _ 64) (rOfNat hQ))
end ExactQuantumFactoring.NetworkEmission.Emits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetentionTemplateEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits OrderTrial.Expressions
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma powTwo {n : α→ℕ} (hn : BitStackProgram.Emits ea unaryCode n) :
    BitStackProgram.Emits ea Nat.bits (fun x=>2^(n x)):=
  (ofProcedure Procedure.binaryPow).comp (hn.pair (const _ _ 2))
lemma lambdaExpr {n : α→ℕ} {d : α→NatExpr v} (hn : BitStackProgram.Emits ea unaryCode n) (hd : NEm d) :
    REm (fun x=>lambdaE (n x) (d x)):=by
  have h:=coveringPow hd hn
  unfold lambdaE;rat_emit
lemma coefficientExpr {n : α→ℕ} {Q B d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>coefficientE (n x) (Q x) (B x) (d x) (j x)):=by
  have hN:=nconst (ev:=ev) (powTwo ((const _ _ 10).unaryMul hn))
  have hl:=lambdaExpr hn hd
  have hm:=majorantSumExpr hQ hB hd hj
  unfold coefficientE;rat_emit
lemma remainderExpr {n : α→ℕ} {Q B d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>remainderE (n x) (Q x) (B x) (d x) (j x)):=
  rSub (lambdaExpr hn hd) (rMul (coefficientExpr hn hQ hB hd hj) (majorantSumExpr hQ hB hd hj))
lemma discrepancyExpr {n : α→ℕ} {Q B d j t : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) (ht : NEm t) :
    REm (fun x=>discrepancyE (n x) (Q x) (B x) (d x) (j x) (t x)):=by
  have hm:=majorantExpr hQ hB hd hj (nmod (nmul hj ht) hd)
  have hp:=probabilityE hQ hd hj ht
  have hc:=coefficientExpr hn hQ hB hd hj
  unfold discrepancyE;rat_emit
lemma thirdRetentionExpr {n : α→ℕ} {Q B d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hQ : NEm Q) (hB : NEm B) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>thirdRetentionE (n x) (Q x) (B x) (d x) (j x)):=by
  have hr:=remainderExpr hn hQ hB hd hj
  unfold thirdRetentionE;rat_emit
lemma sampleB {n : α→ℕ} (hn : BitStackProgram.Emits ea unaryCode n) : NEm (fun x=>.const (2^(n x))):=
  nconst (powTwo hn)
lemma sampleQ {n : α→ℕ} (hn : BitStackProgram.Emits ea unaryCode n) : NEm (fun x=>.const ((2^(n x))^16)):=by
  have h:=(ofProcedure Procedure.binaryPow).comp ((const ea unaryCode 16).pair (powTwo hn))
  exact nconst h
lemma firstExpr {n : α→ℕ} {d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>firstE (n x) (d x) (j x)):=coefficientExpr hn (sampleQ hn) (sampleB hn) hd hj
lemma secondExpr {n : α→ℕ} {d j t : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hd : NEm d) (hj : NEm j) (ht : NEm t) :
    REm (fun x=>secondE (n x) (d x) (j x) (t x)):=discrepancyExpr hn (sampleQ hn) (sampleB hn) hd hj ht
lemma lastExpr {n : α→ℕ} {d j : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hd : NEm d) (hj : NEm j) :
    REm (fun x=>lastE (n x) (d x) (j x)):=thirdRetentionExpr hn (sampleQ hn) (sampleB hn) hd hj
end ExactQuantumFactoring.NetworkEmission.Emits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RootCircuitEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {w e k : α→ℕ}
lemma rootModulus (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.rootModulus (w x)):=
  selectSlice (hw.unaryAdd hw) hw (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma rootGuess (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.rootGuess (w x)):=
  selectSlice (hw.unaryAdd hw) hw hw.unaryNat _ (by intros;rfl)
lemma staticPower (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e) :
    NetEmits ea (fun x=>BitArithmetic.staticPower (w x) (e x)):=by
  have hs:=((rootModulus hw).pair (mul hw)).iterate (hw.unaryAdd hw) he
  exact ((identity hw).pair (wordConst hw hw (const _ _ 1))).comp
    (hs.rewireSlice hw hw.unaryNat _ (by intros;rfl))
lemma rootNext (hw : Emits ea unaryCode w) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.rootNext (w x) (k x)):=by
  have h2 : Emits ea Nat.bits (fun x=>2^(k x)):=
    (ofProcedure Procedure.binaryPow).comp (hk.pair (const _ _ 2))
  exact ((rootGuess hw).pair (wordConst (hw.unaryAdd hw) hw h2)).comp (add hw)
lemma rootStep (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.rootStep (w x) (e x) (k x)):=by
  have hn:=rootNext hw hk
  have hg:=rootGuess hw
  have hm:=rootModulus hw
  exact hm.pair (wordMux ((hn.comp (staticPower hw he)).wordLe hm hw) hn hg hw)
end NetEmits
lemma rootPrefix_emission : NetEmits (prodCode unaryCode (prodCode unaryCode unaryCode))
    (fun x=>rootPrefix x.2.1 x.2.2 x.1):=by
  let ea:=prodCode unaryCode (prodCode unaryCode unaryCode)
  have hx:=BitStackProgram.Emits.id ea
  have hk:=hx.fst
  have hw:=hx.snd.fst
  have he:=hx.snd.snd
  have hj:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  obtain ⟨p,hp,ep⟩:=NetEmits.rootStep (hw.comp hj.snd) (he.comp hj.snd) hj.fst
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=fun x i=>p (i,x)) emptyPack pp)).comp (hk.pair hx)
  let q:=fun x j=>((List.range j).map (fun i=>p (i,x))).foldl (fun a b=>compPack b a) (identityPack (x.2.1+x.2.1))
  have hq : Emits ea packCode (fun x=>q x x.1):=
    (ofProcedure Emission.foldReverseCompP).comp (hps.pair ((ofProcedure Emission.identityPackP).comp (hw.unaryAdd hw)))
  refine ⟨fun x=>q x x.1,hq,?_⟩
  intro x
  suffices ∀j,(q x j).val.value=erase (rootPrefix x.2.1 x.2.2 j) from this x.1
  intro j
  induction j with
  | zero=>exact identityPack_value _
  | succ j ih=>
    dsimp only [q]
    rw [List.range_succ,List.map_append,List.foldl_append,List.map_singleton,List.foldl_cons,List.foldl_nil]
    exact compPack_spec _ _ _ _ (ep (j,x)) ih
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n e : α→ℕ}
lemma rootPrefix {w k : α→ℕ} (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.rootPrefix (w x) (e x) (k x)):=
  rootPrefix_emission.input (hk.pair (hw.pair he))
lemma boundedRoot (hn : Emits ea unaryCode n) (he : Emits ea unaryCode e) :
    NetEmits ea (fun x=>boundedRootNet (n x) (e x)):=by
  have hw:=(hn.unaryMul hn).unarySucc
  exact ((identity hw).pair (wordConst hw hw (const _ _ 0))).comp
    ((rootPrefix hw he hn).rewireSlice hw hw.unaryNat _ (by intros;rfl))
lemma rootCheck {w : α→ℕ} (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e) :
    NetEmits ea (fun x=>BitArithmetic.rootCheck (w x) (e x)):=by
  have hg:=rootGuess hw
  exact ((wordConst (hw.unaryAdd hw) hw (const _ _ 2)).wordLe hg hw).band
    ((hg.comp (staticPower hw he)).equalOn (rootModulus hw) hw)
lemma exponentCheck (hn : Emits ea unaryCode n) (he : Emits ea unaryCode e) :
    NetEmits ea (fun x=>BitArithmetic.exponentCheck (n x) (e x)):=by
  have hw:=(hn.unaryMul hn).unarySucc
  exact ((identity hw).pair (boundedRoot hn he)).comp (rootCheck hw he)
lemma perfectPower (hn : Emits ea unaryCode n) :
    NetEmits ea (fun x=>perfectPowerNet (n x)):=by
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hN:=hn.comp hx.snd
  have hE:=hx.fst
  have hc:=(hE.unaryNat.natLt (const _ _ 2)).boolNot
  have hf:=ite hc (exponentCheck hN hE) (constant (hN.unaryMul hN).unarySucc (const _ _ false))
  exact (anyRange (f:=fun x i=>if !(decide (i<2)) then BitArithmetic.exponentCheck (n x) i else BooleanNetwork.constant false) (hn.unaryMul hn).unarySucc hf hn.unarySucc).congr (by
    intro x;unfold perfectPowerNet;congr 1;apply congrArg List.ofFn;funext i
    simp only [Bool.not_eq_true',decide_eq_false_iff_not,not_lt])
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/GcdEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {w K : α→ℕ}
lemma euclidStep (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.euclidStep (w x)):=by
  have hz:=wordConst (hw.unaryAdd hw) hw (const _ _ 0)
  have hd:=(rootGuess hw).equalOn hz hw
  exact (hd.wordMux (rootModulus hw) (rootGuess hw) hw).pair (hd.wordMux hz (mod hw) hw)
lemma euclidPrefix (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K) :
    NetEmits ea (fun x=>BitArithmetic.euclidPrefix (w x) (K x)):=by
  apply ((euclidStep hw).iterate (hw.unaryAdd hw) hK).congr
  intro x
  have h : ∀j,BooleanNetwork.iterate (BitArithmetic.euclidStep (w x)) j=BitArithmetic.euclidPrefix (w x) j:=by
    intro j;induction j with
    | zero=>rfl
    | succ j ih=>simpa only [BooleanNetwork.iterate, List.replicate_succ, BooleanNetwork.sequence, BitArithmetic.euclidPrefix] using congrArg (BooleanNetwork.comp (BitArithmetic.euclidStep (w x))) ih
  exact h _
lemma gcd (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.gcdNet (w x)):=
  (euclidPrefix hw ((const _ _ 2).unaryMul hw)).comp (rootModulus hw)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TrialControlEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.TrialControlEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits OrderTrial
variable {α : Type} {ea : α→List Bool} {k w n : α→ℕ}
def decodeEquiv : Fin 4 ≃ DecodeVar where
  toFun := ![.den,.num,.residue,.coin]
  invFun | .den=>0 | .num=>1 | .residue=>2 | .coin=>3
  left_inv i:=by fin_cases i <;> rfl
  right_inv i:=by cases i <;> rfl
lemma first {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (hd : NetEmits ea d) (hj : NetEmits ea j) (ht : NetEmits ea t) (hc : NetEmits ea c) :
    NetEmits ea (fun x=>firstRetNet (n x) (d x) (j x) (t x) (c x)):=by
  apply retention decodeEquiv hk hw (BitStackProgram.Emits.retentionBits hn)
    (NetworkEmission.Emits.firstExpr hn (const _ _ (.var .den)) (const _ _ (.var .num))) (const _ _ (.var .coin))
  intro i;cases i
  · exact hd
  · exact hj
  · exact ht
  · exact hc
lemma second {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (hd : NetEmits ea d) (hj : NetEmits ea j) (ht : NetEmits ea t) (hc : NetEmits ea c) :
    NetEmits ea (fun x=>secondRetNet (n x) (d x) (j x) (t x) (c x)):=by
  apply retention decodeEquiv hk hw (BitStackProgram.Emits.retentionBits hn)
    (NetworkEmission.Emits.secondExpr hn (const _ _ (.var .den)) (const _ _ (.var .num)) (const _ _ (.var .residue))) (const _ _ (.var .coin))
  intro i;cases i
  · exact hd
  · exact hj
  · exact ht
  · exact hc
lemma third {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (hd : NetEmits ea d) (hj : NetEmits ea j) (ht : NetEmits ea t) (hc : NetEmits ea c) :
    NetEmits ea (fun x=>thirdRetNet (n x) (d x) (j x) (t x) (c x)):=by
  apply retention decodeEquiv hk hw (BitStackProgram.Emits.retentionBits hn)
    (NetworkEmission.Emits.lastExpr hn (const _ _ (.var .den)) (const _ _ (.var .num))) (const _ _ (.var .coin))
  intro i;cases i
  · exact hd
  · exact hj
  · exact ht
  · exact hc
lemma reverse {e : ∀x,BooleanNetwork (k x) (w x)}
    (hw : Emits ea unaryCode w) (he : NetEmits ea e) :
    NetEmits ea (fun x=>(e x).rewire Fin.rev):=by
  apply he.rewire (fun _=>Fin.rev)
  apply ofFnDep 0 hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (w a)=>(x.2.val,x.1))
  exact (((hw.comp hx.snd).unaryNat.natSub (const _ _ 1)).natSub hx.fst.unaryNat).congr (by intro x; change w x.1 - 1 - x.2.val = w x.1 - (x.2.val+1); omega)
lemma powOn {a m e : ∀x,BooleanNetwork (k x) (w x)}
    (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m) (he : NetEmits ea e) :
    NetEmits ea (fun x=>BitArithmetic.powOn (a x) (m x) (e x)):=
  ((ha.pair hm).pair (reverse hw he)).comp (modularPower hw hw)
lemma labelValid {a m d j : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hd : NetEmits ea d) (hj : NetEmits ea j) :
    NetEmits ea (fun x=>labelValidNet (n x) (a x) (m x) (d x) (j x)):=
  ((wordConst hk hw (const _ _ 0)).wordLt hd hw).band
    ((hd.wordLt (wordConst hk hw (NetworkEmission.Emits.powTwo hn)) hw).band
      ((hj.wordLt hd hw).band
        ((((hj.pair hd).comp (gcd hw)).equalOn (wordConst hk hw (const _ _ 1)) hw).band
          ((powOn hw ha hm hd).equalOn (wordConst hk hw (const _ _ 1)) hw))))
lemma accept {a m mode d j t c : ∀x,BooleanNetwork (k x) (w x)} {selected : ∀x,BooleanNetwork (k x) 1}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hmode : NetEmits ea mode)
    (hd : NetEmits ea d) (hj : NetEmits ea j) (ht : NetEmits ea t) (hc : NetEmits ea c) (hs : NetEmits ea selected) :
    NetEmits ea (fun x=>trialAcceptOn (n x) (a x) (m x) (mode x) (d x) (j x) (t x) (c x) (selected x)):=
  (labelValid hk hw hn ha hm hd hj).band
    (((hmode.wordLt (wordConst hk hw (const _ _ 2)) hw).band (hs.band (first hk hw hn hd hj ht hc))).bor
      (((hmode.equalOn (wordConst hk hw (const _ _ 2)) hw).band
        ((ht.wordLt hd hw).band (second hk hw hn hd hj ht hc))).bor
          ((hmode.equalOn (wordConst hk hw (const _ _ 3)) hw).band (third hk hw hn hd hj ht hc))))
end ExactQuantumFactoring.TrialControlEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ContinuedFractionEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {w K : α→ℕ}
lemma div (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.div (w x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.divide (w x),
    (ofProcedure AIGNetworkEmission.Emission.divPackP).comp hw,fun x=>AIGNetworkEmission.divPack_value (w x)⟩
lemma cfHead (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfHead (w x)):=
  selectSlice (hw.unaryAdd (hw.unaryAdd hw)) hw (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma cfTail (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfTail (w x)):=
  selectSlice (hw.unaryAdd (hw.unaryAdd hw)) (hw.unaryAdd hw) hw.unaryNat _ (by intros;rfl)
lemma cfP (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfP (w x)):=
  (cfTail hw).comp (rootModulus hw)
lemma cfQ (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfQ (w x)):=
  (cfTail hw).comp (rootGuess hw)
lemma cfProduct (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfProduct (w x)):=
  ((((cfHead hw).pair (cfP hw)).comp (mul hw)).pair (cfQ hw)).comp (add hw)
lemma cfCombine (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfCombine (w x)):=by
  have hd:=cfP hw
  have hc:=hd.equalOn (wordConst (hw.unaryAdd (hw.unaryAdd hw)) hw (const _ _ 0)) hw
  exact (hc.wordMux (cfHead hw) (cfProduct hw) hw).pair
    (hc.wordMux (wordConst (hw.unaryAdd (hw.unaryAdd hw)) hw (const _ _ 1)) hd hw)
lemma convergent (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K) :
    NetEmits ea (fun x=>BitArithmetic.convergentNet (w x) (K x)):=by
  apply boundedStages hK (f:=fun x j=>BitArithmetic.convergentNet (w x) j)
  · exact (div hw).pair (wordConst (hw.unaryAdd hw) hw (const _ _ 1))
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (BitArithmetic.convergentNet (w x.1) x.2.val))))
    have h:=hw.comp hx.fst
    exact (((div h).pair ((rootGuess h).pair (mod h))).comp
      ((cfHead h).pair ((cfTail h).comp (ofCanonical hx.snd.snd)))).comp (cfCombine h)
  · exact (hw.unaryPoly.add hw.unaryPoly).pull (fun x:Σa,Fin (K a+1)=>x.1)
  · exact (hw.unaryPoly.add hw.unaryPoly).pull (fun x:Σa,Fin (K a+1)=>x.1)
  · exact NetworkAt.convergentNet (hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      ((hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)).of_le (by intro x;have:=x.2.isLt;omega))
end ExactQuantumFactoring.NetworkEmission.NetEmits

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ProperDivisorEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k w e : α→ℕ}
lemma zeroWord {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.zeroWord (a x)):=
  ha.equalOn (by simpa only [BitVec.ofNat_eq_ofNat] using wordConst hk hw (const _ _ 0)) hw
lemma evenOn {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.evenOn (a x)):=
  zeroWord hk hw ((ha.pair (wordConst hk hw (const _ _ 2))).comp (mod hw))
lemma halfWord {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.halfWord (a x)):=
  (ha.pair (wordConst hk hw (const _ _ 2))).comp (div hw)
lemma properOn {a d : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hd : NetEmits ea d) :
    NetEmits ea (fun x=>BitArithmetic.properOn (a x) (d x)):=
  (((wordConst hk hw (const _ _ 1)).wordLt hd hw).band (hd.wordLt ha hw)).band
    (zeroWord hk hw ((ha.pair hd).comp (mod hw)))
lemma halfPowerBits {a m : ∀x,BooleanNetwork (k x) (w x)} {d : ∀x,BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hd : NetEmits ea d) :
    NetEmits ea (fun x=>BitArithmetic.halfPowerBits (a x) (m x) (d x)):=
  ((ha.pair hm).pair (TrialControlEmission.reverse he (halfWord hk he hd))).comp (modularPower hw he)
lemma shiftedHalfBits {a m : ∀x,BooleanNetwork (k x) (w x)} {d : ∀x,BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hd : NetEmits ea d) :
    NetEmits ea (fun x=>BitArithmetic.shiftedHalfBits (a x) (m x) (d x)):=
  ((((halfPowerBits hk hw he ha hm hd).pair hm).comp (add hw)).pair (wordConst hk hw (const _ _ 1))).comp (sub hw)
lemma candidateBits {a m : ∀x,BooleanNetwork (k x) (w x)} {d : ∀x,BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hd : NetEmits ea d) :
    NetEmits ea (fun x=>BitArithmetic.candidateBits (a x) (m x) (d x)):=
  ((zeroWord hk he hd).bnot.band (evenOn hk he hd)).wordMux
    (((shiftedHalfBits hk hw he ha hm hd).pair hm).comp (gcd hw))
    (by simpa only [BitVec.ofNat_eq_ofNat] using wordConst hk hw (const _ _ 0)) hw
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ModularSumEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w k : α→ℕ}
lemma sumModOfFn {m : ∀x,BooleanNetwork (n x) (w x)}
    {f : ∀x,Fin (k x)→BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode w) (hk : Emits ea unaryCode k)
    (hm : NetEmits ea m)
    (hf : NetEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>sumMod (m x) (List.ofFn (f x))):=by
  let F:=fun x j=>sumMod (m x) ((List.ofFn (f x)).drop (k x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=
    (wordConst hn hw (const _ _ 0)).congr (by
      intro x
      change wordConstant _=sumMod _ ((List.ofFn (f x)).drop (k x-0))
      have hd : (List.ofFn (f x)).drop (k x-0)=[]:=by
        apply List.drop_eq_nil_iff.mpr
        simp only [List.length_ofFn,Nat.sub_zero,le_refl]
      rw [hd];rfl)
  have hs : NetEmits
      (fun x:Σa,Fin (k a)=>prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.val,erasePack (F x.1 x.2.val))))
      (fun x=>F x.1 (x.2.val+1)):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (k a)=>(x.1,(x.2.val,erasePack (F x.1 x.2.val))))
    have hi:=((hk.comp hx.fst).unaryNat.natSub hx.snd.fst.unarySucc.unaryNat).boundedUnary
      (hk.comp hx.fst) (by intro x;exact Nat.sub_le _ _)
    let ix:=fun x:Σa,Fin (k a)=>(⟨k x.1-(x.2.val+1),by have:=x.2.isLt;omega⟩ : Fin (k x.1))
    have he : Emits _ (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1))
        (fun x=>⟨x.1,ix x⟩):=
      (hi.pair hx.fst).result (by intro x;rfl)
    have ha:=hf.input he
    have hb:=ofCanonical hx.snd.snd
    have hadd:=addMod ha hb (hm.input hx.fst) (hw.comp hx.fst)
    exact hadd.congr (by
      intro x
      dsimp only [F,ix]
      have hlt : k x.1-(x.2.val+1)<(List.ofFn (f x.1)).length:=by simpa only [List.length_ofFn] using (show k x.1-(x.2.val+1)<k x.1 by have:=x.2.isLt;omega)
      rw [List.drop_eq_getElem_cons hlt]
      simp only [sumMod,List.getElem_ofFn]
      have hlen : (List.ofFn (f x.1)).length=k x.1:=List.length_ofFn
      have := x.2.isLt
      congr 3
      all_goals omega)
  have hcp:=countPolyIndexed hk hf
  obtain ⟨p,hp⟩:=hcp
  let len:=fun x:Σa,Fin (k a+1)=>(ea x.1).length
  have hwP:=hw.unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)
  have hkP:=hk.unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)
  have hmP:=hm.countPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)
  have hpP : PolyAt len (fun x=>p.eval (ea x.1).length):=⟨p,fun _=>le_rfl⟩
  have hwp:=hwP.add (PolyAt.const _ 1)
  have hbound : NetworkAt len (fun x:Σa,Fin (k a+1)=>F x.1 x.2.val):=by
    apply (hwP.add (hkP.mul (((((hpP.add hmP).add ((PolyAt.const _ 216).mul (hwp.pow 2))).add
      ((PolyAt.const _ 142).mul hwp)).add (PolyAt.const _ 15))))).of_le
    intro x
    have h:=sumMod_count (m x.1) ((List.ofFn (f x.1)).drop (k x.1-x.2.val)) (c:=p.eval (ea x.1).length) (by
      intro a ha
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop ha)
      exact hp ⟨x.1,i⟩)
    have hlen : ((List.ofFn (f x.1)).drop (k x.1-x.2.val)).length≤k x.1:=by
      simp only [List.length_drop,List.length_ofFn];omega
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _)
  exact (boundedStages hk h0 hs (hn.unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)) hwP hbound).congr
    (by intro x;simp only [F,Nat.sub_self,List.drop_zero])
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w : α→ℕ}
lemma cyclicMul {a b : ∀x,BooleanNetwork (n x) (s x*w x)}
    {m : ∀x,BooleanNetwork (n x) (w x)} [∀x,NeZero (s x)]
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>cyclicMulNet (a x) (b x) (m x)):=by
  apply wordBlocks hn hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  apply sumModOfFn (hn.comp hx.snd) (hw.comp hx.snd) (hs.comp hx.snd) (hm.input hx.snd)
  have hy:=(BitStackProgram.Emits.id (prodCode unaryCode (fun x:Σa,Fin (s a)=>prodCode unaryCode ea (x.2.val,x.1)))).precompose
    (fun x:Σa:Σa,Fin (s a),Fin (s a.1)=>(x.2.val,x.1))
  have ho:=hx.snd.comp hy.snd
  have hS:=hs.comp ho
  have hW:=hw.comp ho
  have hi:=hy.fst.unaryNat
  have hk:=hx.fst.comp hy.snd
  have hj:=((hS.unaryNat.natSub hi).natAdd hk.unaryNat).natMod hS.unaryNat
  have hleft:=blockNet hS hW (fun x=>x.2) hi
  have hright:=blockNet hS hW (fun x=>x.1.2-x.2) hj
  exact mulMod ((ha.input ho).comp hleft) ((hb.input ho).comp hright) (hm.input ho) hW
lemma cyclicOne (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s)
    (hw : Emits ea unaryCode w) [∀x,NeZero (s x)] :
    NetEmits ea (fun x=>BitArithmetic.cyclicOne (n:=n x) (s x) (w x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hc:=hx.fst.unaryNat.natEq (const _ _ 0)
  apply arrayConstant hn hs hw
  exact (hc.ite (const _ _ 1) (const _ _ 0)).congr (by intro x;simp only [Fin.ext_iff,Fin.val_zero,decide_eq_true_eq])
lemma cyclicAdd {a b : ∀x,BooleanNetwork (n x) (s x*w x)}
    {m : ∀x,BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>cyclicAddNet (a x) (b x) (m x)):=by
  apply wordBlocks hn hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hp:=blockNet (hs.comp hx.snd) (hw.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
  exact addMod ((ha.input hx.snd).comp hp) ((hb.input hx.snd).comp hp) (hm.input hx.snd) (hw.comp hx.snd)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicPowerEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {s w b : α→ℕ} [∀x,NeZero (s x)]
lemma cyclicStep (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b)
    (i : ∀x,Fin (b x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>BitArithmetic.cyclicStep (s x) (w x) (i x)):=by
  have hA:=hs.unaryMul hw
  have hI:=(hA.unaryAdd hw).unaryAdd hb
  have hW:=hI.unaryAdd hA
  have hbase : NetEmits ea (fun x=>cyclicBase (s x) (w x) (b x)):=
    selectSlice hW hA (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  have hmod : NetEmits ea (fun x=>cyclicMod (s x) (w x) (b x)):=
    selectSlice hW hw hA.unaryNat _ (by intros;simp only [Fin.val_castAdd,Fin.val_natAdd])
  have hacc : NetEmits ea (fun x=>cyclicAcc (s x) (w x) (b x)):=
    selectSlice hW hA hI.unaryNat _ (by intros;simp only [Fin.val_natAdd])
  have hbit : NetEmits ea (fun x=>cyclicBit (s x) (w x) (i x)):=
    bit hW _ ((hA.unaryAdd hw).unaryNat.natAdd hi)
  have hkeep : NetEmits ea (fun x=>BooleanNetwork.select
      (Fin.castAdd (s x*w x) : Fin ((s x*w x+w x)+b x)→Fin (cyclicPowerWidth (s x) (w x) (b x)))):=
    selectSlice hW hI (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  have hsq:=cyclicMul hW hs hw hacc hacc hmod
  have hprod:=cyclicMul hW hs hw hsq hbase hmod
  exact hkeep.pair (wordMux hbit hprod hsq hA)
lemma cyclicPrefix (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BitArithmetic.cyclicPrefix (s x) (w x) (b x) (b x) le_rfl):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (b a)=>(x.2.val,x.1))
  obtain ⟨p,hp,ep⟩:=cyclicStep (hs.comp hx.snd) (hw.comp hx.snd) (hb.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
  obtain ⟨q,hq,eq⟩:=extendPack hb p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hb.pair (id ea))
  have hA:=hs.unaryMul hw
  have hW:=((hA.unaryAdd hw).unaryAdd hb).unaryAdd hA
  let Q:=fun x j=>((List.range j).map (q x)).foldl compPack (identityPack (cyclicPowerWidth (s x) (w x) (b x)))
  have hQ : Emits ea packCode (fun x=>Q x (b x)):=
    (ofProcedure Emission.foldCompP).comp (hps.pair ((ofProcedure Emission.identityPackP).comp hW))
  refine ⟨fun x=>Q x (b x),hQ,?_⟩
  intro x
  suffices ∀j (hj:j≤b x),(Q x j).val.value=erase (BitArithmetic.cyclicPrefix (s x) (w x) (b x) j hj) from this _ le_rfl
  intro j
  induction j with
  | zero=>intro hj;exact identityPack_value _
  | succ j ih=>
    intro hj
    dsimp only [Q]
    rw [List.range_succ,List.map_append,List.foldl_append,List.map_singleton,List.foldl_cons,List.foldl_nil]
    apply compPack_spec _ _ _ _ (ih (by omega))
    rw [eq x ⟨j,by omega⟩]
    exact ep ⟨x,⟨j,by omega⟩⟩
lemma cyclicPower (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BitArithmetic.cyclicPower (s x) (w x) (b x)):=by
  have hA:=hs.unaryMul hw
  have hI:=(hA.unaryAdd hw).unaryAdd hb
  have hstart:=(identity hI).pair (cyclicOne hI hs hw)
  exact hstart.comp ((cyclicPrefix hs hw hb).rewireSlice hA hI.unaryNat _ (by intros;rfl))
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CyclicTestEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma ofFnNat (d : β) {k : α→ℕ} {f : α→ℕ→β}
    (hk : Emits ea unaryCode k) (hf : Emits (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Emits ea (listCode eb) (fun x=>List.ofFn (fun i:Fin (k x)=>f x i.val)):=by
  obtain ⟨p⟩:=hf
  exact ((ofProcedure (Procedure.tabulate (f:=f) d p)).comp (hk.pair (id ea))).congr
    (by intro x;exact (NetworkEmission.ofFn_nat_eq_map _ _).symm)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w a : α→ℕ}
lemma reverseWord {f : ∀x,BooleanNetwork (n x) (w x)} (hf : NetEmits ea f)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>(f x).rewire Fin.rev):=by
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hi:=(hw.comp hx.snd).unaryNat.natSub hx.fst.unarySucc.unaryNat
  exact hf.rewire _ (ofFnNat (eb:=Nat.bits) (f:=fun x i=>w x-(i+1)) 0 hw hi)
lemma cyclicX (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    [∀x,NeZero (s x)] : NetEmits ea (fun x=>cyclicXNet (n:=n x) (s x) (w x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hc:=hx.fst.unaryNat.natEq ((const _ _ 1).natMod (hs.comp hx.snd).unaryNat)
  apply arrayConstant hn hs hw
  exact (hc.ite (const _ _ 1) (const _ _ 0)).congr (by intro x;simp only [Fin.ext_iff,Fin.val_one',decide_eq_true_eq])
lemma cyclicC (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : Emits ea Nat.bits a) [∀x,NeZero (s x)] : NetEmits ea (fun x=>cyclicCNet (n:=n x) (s x) (w x) (a x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hc:=hx.fst.unaryNat.natEq (const _ _ 0)
  apply arrayConstant hn hs hw
  exact (hc.ite (ha.comp hx.snd) (const _ _ 0)).congr (by intro x;simp only [Fin.ext_iff,Fin.val_zero,decide_eq_true_eq])
lemma cyclicPowerOn {b : α→ℕ} {f : ∀x,BooleanNetwork (n x) (s x*w x)}
    {m : ∀x,BooleanNetwork (n x) (w x)} {e : ∀x,BooleanNetwork (n x) (b x)}
    [∀x,NeZero (s x)] (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b)
    (hf : NetEmits ea f) (hm : NetEmits ea m) (he : NetEmits ea e) :
    NetEmits ea (fun x=>BitArithmetic.cyclicPowerOn (f x) (m x) (e x)):=
  ((hf.pair hm).pair he).comp (cyclicPower hs hw hb)
lemma cyclicTest (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (ha : Emits ea Nat.bits a)
    [∀x,NeZero (s x)] : NetEmits ea (fun x=>BitArithmetic.cyclicTest (s x) (w x) (a x)):=by
  have hm:=identity hw
  have he:=hm.reverseWord hw
  have hX:=cyclicX hw hs hw
  have hC:=cyclicC hw hs hw ha
  have hl:=cyclicPowerOn hs hw hw (cyclicAdd hw hs hw hX hC hm) hm he
  have hr:=cyclicAdd hw hs hw (cyclicPowerOn hs hw hw hX hm he) hC hm
  exact hl.equalOn hr (hs.unaryMul hw)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimalityEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w k : α→ℕ}
lemma splitOn {a b : α→ℕ} {f : ∀x,BooleanNetwork (a x) (b x)}
    (c : α→Prop) [DecidablePred c] (hc : Emits ea Procedure.boolCode (fun x=>decide (c x)))
    (hy : NetEmits (fun x:{a // c a}=>ea x.val) (fun x=>f x.val))
    (hz : NetEmits (fun x:{a // ¬c a}=>ea x.val) (fun x=>f x.val)) : NetEmits ea f:=
  ofCanonical (BitStackProgram.Emits.splitOn c hc hy.canonical hz.canonical)
lemma constMod (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) :
    NetEmits ea (fun x=>BitArithmetic.constMod (w x) (s x)):=
  ((identity hw).pair (wordConst hw hw hs)).comp (mod hw)
lemma divides (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) :
    NetEmits ea (fun x=>dividesNet (w x) (s x)):=
  (constMod hw hs).equalOn (wordConst hw hw (const _ _ 0)) hw
lemma constPowMod (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) (hk : Emits ea Nat.bits k) :
    NetEmits ea (fun x=>BitArithmetic.constPowMod (w x) (s x) (k x)):=
  (((identity hw).pair (wordConst hw hw hs)).pair ((wordConst hw hw hk).reverseWord hw)).comp (modularPower hw hw)
lemma powerOne (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) (hk : Emits ea Nat.bits k) :
    NetEmits ea (fun x=>powerOneNet (w x) (s x) (k x)):=
  (constPowMod hw hs hk).equalOn (wordConst hw hw (const _ _ 1)) hw
lemma orderTests (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.orderTests (w x) (s x) (k x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (k a)=>(x.2.val,x.1))
  exact allOfFn hw hk (powerOne (hw.comp hx.snd) (hs.comp hx.snd) hx.fst.unarySucc.unaryNat).bnot
lemma properDivisor (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) :
    NetEmits ea (fun x=>BitArithmetic.properDivisor (w x) (s x)):=
  (divides hw hs).band ((wordConst hw hw hs).wordLt (identity hw) hw)
lemma noSmallDivisor (hw : Emits ea unaryCode w) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.noSmallDivisor (w x) (k x)):=by
  have hJ:=(hk.unaryNat.natSub (const _ _ 1)).boundedUnary hk (by intro x;exact Nat.sub_le _ _)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (k a-1)=>(x.2.val,x.1))
  exact allOfFn hw hJ (properDivisor (hw.comp hx.snd) (hx.fst.unaryNat.natAdd (const _ _ 2))).bnot
lemma allCongruences (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) [∀x,NeZero (s x)] :
    NetEmits ea (fun x=>BitArithmetic.allCongruences (s x) (w x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (8*s a)=>(x.2.val,x.1))
  exact allOfFn hw ((const _ _ 8).unaryMul hs) (cyclicTest (hs.comp hx.snd) (hw.comp hx.snd) hx.fst.unarySucc.unaryNat)
lemma aksBranch (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) [∀x,NeZero (s x)] :
    NetEmits ea (fun x=>BitArithmetic.aksBranch (n x) (s x)):=by
  have hw:=(hn.unaryMul hn).unarySucc
  exact ((divides hw hs.unaryNat).bnot.band (orderTests hw hs.unaryNat (hn.unaryPow 2))).band
    ((noSmallDivisor hw ((const _ _ 8).unaryMul hs)).band (allCongruences hs hw))
lemma aksStaticBranch (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) :
    NetEmits ea (fun x=>BitArithmetic.aksStaticBranch (n x) (s x)):=by
  apply splitOn (fun x=>(s x).Prime) hs.unaryPrime
  · have : ∀x:{a:α // (s a).Prime},NeZero (s x.val):=fun x=>⟨x.property.ne_zero⟩
    exact (aksBranch (hn.precompose Subtype.val) (hs.precompose Subtype.val)).congr
      (by intro x;simp only [BitArithmetic.aksStaticBranch,dite_eq_left x.property])
  · have hN:=hn.precompose (fun x:{a:α // ¬(s a).Prime}=>x.val)
    exact (constant (hN.unaryMul hN).unarySucc (const _ _ false)).congr
      (by intro x;simp only [BitArithmetic.aksStaticBranch,dite_eq_right x.property])
lemma primality (hn : Emits ea unaryCode n) :
    NetEmits ea (fun x=>primalityNet (n x)):=by
  have hK:=(hn.unaryPow 8).unarySucc
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (n a^8+1)=>(x.2.val,x.1))
  exact (perfectPower hn).bnot.band (anyOfFn (hn.unaryMul hn).unarySucc hK
    (aksStaticBranch (hn.comp hx.snd) hx.fst))
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/StackEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k s w : α→ℕ}
lemma stackPop (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) :
    NetEmits ea (fun x=>BitArithmetic.stackPop (s x) (w x)):=by
  unfold BitArithmetic.stackPop
  apply wordBlocks (hs.unaryMul hw) hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hS:=hs.comp hx.snd
  have hW:=hw.comp hx.snd
  apply splitOn (fun x=>x.2.val+1<s x.1) (hx.fst.unarySucc.unaryNat.natLt hS.unaryNat)
  · let inc : {x : Σa,Fin (s a) // x.2.val+1<s x.1} → (Σa,Fin (s a)) := Subtype.val
    have hb:=blockNet (hS.precompose inc) (hW.precompose inc)
      (fun x=>⟨x.val.2.val+1,x.property⟩) (hx.fst.unarySucc.unaryNat.precompose inc)
    exact hb.congr (by intro x;rw [dite_eq_left x.property])
  · let inc : {x : Σa,Fin (s a) // ¬x.2.val+1<s x.1} → (Σa,Fin (s a)) := Subtype.val
    have hz:=wordConst ((hS.unaryMul hW).precompose inc) (hW.precompose inc) (const _ _ 0)
    exact hz.congr (by intro x;rw [dite_eq_right x.property];rfl)
lemma stackPush {a : ∀x,BooleanNetwork (k x) (w x)} {v : ∀x,BooleanNetwork (k x) (s x*w x)}
    (hk : Emits ea unaryCode k) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : NetEmits ea a) (hv : NetEmits ea v) :
    NetEmits ea (fun x=>BitArithmetic.stackPush (a x) (v x)):=by
  unfold BitArithmetic.stackPush
  apply wordBlocks hk hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  apply splitOn (fun x=>x.2.val=0) (hx.fst.unaryNat.natEq (const _ _ 0))
  · exact ((ha.compInput hx.snd).precompose Subtype.val).congr (by intro x;rw [dite_eq_left x.property])
  · let inc : {x : Σa,Fin (s a) // ¬x.2.val=0} → (Σa,Fin (s a)) := Subtype.val
    have hb:=blockNet ((hs.comp hx.snd).precompose inc) ((hw.comp hx.snd).precompose inc)
      (fun x=>⟨x.val.2.val-1,by dsimp only [inc];have:=x.val.2.isLt;omega⟩)
      ((hx.fst.unaryNat.natSub (const _ _ 1)).precompose inc)
    exact (((hv.compInput hx.snd).precompose inc).comp hb).congr (by intro x;rw [dite_eq_right x.property])
lemma primeWord (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.primeWord (w x)):=
  ((wordConst hw hw (const _ _ 2)).wordLe (identity hw) hw).band
    ((resize hw (hw.unaryMul hw).unarySucc).comp (primality hw))
end ExactQuantumFactoring.NetworkEmission.NetEmits

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CleanPermutationEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

def swapOps (n i : ℕ) : List Op:=[cnotOp i (n+i),cnotOp (n+i) i,cnotOp i (n+i)]
lemma erase_swapPrefix (n r k : ℕ) (h : k≤n) :
    (BooleanNetwork.swapPrefix n r k h).map eraseOp=((List.range k).map (swapOps n)).flatten:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [BooleanNetwork.swapPrefix,List.map_append,ih,List.range_succ,List.map_append,List.flatten_append]
    rfl
noncomputable def swapOpsP : Procedure (prodCode Nat.bits Nat.bits) (listCode opCode) (fun x=>swapOps x.1 x.2):=by
  have hx:=BitStackProgram.Emits.id (prodCode Nat.bits Nat.bits)
  have hi:=hx.snd
  have hj:=hx.fst.natAdd hi
  have ha:=(ofProcedure Emission.cnotOpP).comp (hi.pair hj)
  have hb:=(ofProcedure Emission.cnotOpP).comp (hj.pair hi)
  exact Classical.choice (ha.listCons (hb.listCons (ha.listCons (const _ _ []))))
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {n r : α→ℕ}
lemma swapBlocks (hn : Emits ea unaryCode n) :
    OpsEmits ea (fun x=>BooleanNetwork.swapPrefix (n x) (r x) (n x) le_rfl):=by
  have h:=(ofProcedure (Procedure.listMapWith (f:=swapOps) 0 [] swapOpsP)).comp (hn.unaryNat.pair hn.range)
  exact (h.flatten (⟨plainGate .not,[]⟩ : Op)).congr (fun _=>(erase_swapPrefix _ _ _ _).symm)
lemma cleanPermutation {f g : ∀x,BooleanNetwork (n x) (n x)}
    (hf : NetworkEmission.NetEmits ea f) (hg : NetworkEmission.NetEmits ea g)
    (hn : Emits ea unaryCode n) (h : ∀x,(f x).net.count≤r x) (j : ∀x,(g x).net.count≤r x) :
    OpsEmits ea (fun x=>BooleanNetwork.cleanPermutation (f x) (g x) (h x) (j x)):=
  ((oracleOn hf h).append (swapBlocks hn)).append (oracleOn hg j)
lemma singletonHadamard (i : ∀x,Fin (n x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    OpsEmits ea (fun x=>[hadamardAt (i x)]):=
  ((ofProcedure Emission.hadamardOpP).comp hi).listCons (const _ _ [])
lemma singletonPhase (i : ∀x,Fin (n x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    OpsEmits ea (fun x=>[phaseAt (i x)]):=
  ((ofProcedure Emission.phaseOpP).comp hi).listCons (const _ _ [])
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TriangularProgramEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.TriangularEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {b a : α→ℕ}
lemma work (hb : Emits ea unaryCode b) : Emits ea unaryCode (fun x=>Triangular.work (b x)):=
  ((const _ _ 159).unaryMul hb).unaryAdd (const _ _ 6)
lemma width (hb : Emits ea unaryCode b) : Emits ea unaryCode (fun x=>Triangular.width (b x)):=
  ((hb.unaryAdd hb).unaryAdd (hb.unaryAdd hb)).unaryAdd (work hb)
lemma preparePhase (hb : Emits ea unaryCode b) (h : ∀x,2≤b x) :
    OpsEmits ea (fun x=>ExactQuantumFactoring.preparePhase (b x) (h x)):=by
  have hOne:=(ofProcedure CircuitEmission.Emission.phaseOpP).comp (hb.unaryNat.natSub (const _ _ 1))
  have hTwo:=(ofProcedure CircuitEmission.Emission.phaseOpP).comp (hb.unaryNat.natSub (const _ _ 2))
  exact ((OpsEmits.hadamards hb (fun _=>le_rfl)).listAppend (⟨plainGate .not,[]⟩ : Op)
    (hOne.listCons (hOne.listCons (hTwo.listCons (const _ _ []))))).congr (by
      intro x;simp only [ExactQuantumFactoring.preparePhase,List.map_append,List.map_cons,List.map_nil];rfl)
lemma preparation (ha : Emits ea unaryCode a) :
    OpsEmits ea (fun x=>Triangular.preparation (a x)):=by
  have hb:=ha.unaryAdd (const _ _ 2)
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (preparePhase hb (by intro x;omega)).place (fun x=>Triangular.phaseRegister (a x+2))
    (fun x i=>a x+2+i) (by intros;rfl) ((hb.comp hx.fst).unaryNat.natAdd hx.snd)
lemma row (hb : Emits ea unaryCode b) (j : ∀x,Fin (b x))
    (hj : Emits ea Nat.bits (fun x=>(j x).val)) : OpsEmits ea (fun x=>Triangular.rowCircuit (j x)):=by
  have hR:=triangularRow hb j hj
  exact (OpsEmits.singletonHadamard (fun x=>Triangular.dataWire (j x)) hj).append
    (OpsEmits.cleanPermutation (translateForward hR hb hb) (translateBackward hR hb hb) (hb.unaryAdd hb)
      (fun x=>Triangular.translation_count_forward (j x)) (fun x=>Triangular.translation_count_backward (j x)))
lemma triPrefix_eq (b k : ℕ) (h : k≤b) :
    Triangular.triPrefix b k h=(List.ofFn (fun i:Fin k=>Triangular.rowCircuit (i.castLE h))).flatten:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [Triangular.triPrefix,ih (by omega),List.ofFn_succ',List.concat_eq_append,List.flatten_append]
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
    apply congrArg₂ List.append
    · apply congrArg List.flatten
      apply congrArg List.ofFn
      funext i
      apply congrArg Triangular.rowCircuit
      apply Fin.ext
      rfl
    · apply congrArg Triangular.rowCircuit
      apply Fin.ext
      rfl
lemma fullPrefix (hb : Emits ea unaryCode b) : OpsEmits ea (fun x=>Triangular.triPrefix (b x) (b x) le_rfl):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σz,Fin (b z)=>(x.2.val,x.1))
  have h:=OpsEmits.concat (p:=fun x (i:Fin (b x))=>Triangular.rowCircuit i) hb (row (hb.comp hx.snd) (fun x:Σz,Fin (b z)=>x.2) hx.fst.unaryNat)
  exact h.congr (by intro x;rw [triPrefix_eq];rfl)
lemma transform (ha : Emits ea unaryCode a) : OpsEmits ea (fun x=>Triangular.transform (a x)):=
  ((preparation ha).append (fullPrefix (ha.unaryAdd (const _ _ 2)))).append (preparation ha).reverse
lemma uniform (hb : Emits ea unaryCode b) : OpsEmits ea (fun x=>Triangular.uniformPreparation (b x)):=by
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (OpsEmits.hadamards hb (fun _=>le_rfl)).place (fun x=>Triangular.dataRegister (b x))
    (fun _ i=>i) (by intros;rfl) hx.snd
end ExactQuantumFactoring.TriangularEmission

end



end OAI
