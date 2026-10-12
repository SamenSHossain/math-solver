/-
Exact quantum factoring development (port of OpenAI's formalization), part 34 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: BitStackIntegers.lean, BitStackGCD.lean, ProcedureFurther.lean, BitStackRationals.lean, SignedSyntaxEmission.lean, ArithmeticSyntaxEmission.lean, NetworkFiniteExpressionEmission.lean, RetentionEmission.lean, EmissionDependentLists.lean, NetworkCanonicalEmission.lean, NetworkRecursionEmission.lean, CircuitPreparationEmission.lean, EmissionLengthBounds.lean, CircuitEncodingSize.lean, CircuitRecursionEmission.lean, OpsEmits.lean, TensorEmission.lean, MachineWiringEmission.lean, CompletionEmission.lean, CompletionPreparationEmission.lean, ListSamplerEmission.lean, PhysicalListEmission.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part33

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackIntegers.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def intData (z : ℤ) : Bool×ℕ := (decide (z<0),z.natAbs)
def intCode (z : ℤ) : List Bool := prodCode Procedure.boolCode Nat.bits (intData z)
def intOfSign (x : Bool×ℕ) : ℤ := if x.1 then -(x.2 : ℤ) else (x.2 : ℤ)

lemma intOfSign_data (z : ℤ) : intOfSign (intData z)=z := by
  by_cases h : z<0
  · simp only [intData,intOfSign,h,decide_true,ite_true]
    exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · simp only [intData,intOfSign,h,decide_false,Bool.false_eq_true,ite_false]
    exact Int.natAbs_of_nonneg (le_of_not_gt h)

lemma intData_ofSign (x : Bool×ℕ) :
    intData (intOfSign x)=(x.1 && decide (x.2≠0),x.2) := by
  rcases x with ⟨s,n⟩
  cases s <;> simp [intData,intOfSign,Nat.pos_iff_ne_zero]

def signedAdd (x : (Bool×ℕ)×(Bool×ℕ)) : Bool×ℕ :=
  if x.1.1=x.2.1 then (x.1.1,x.1.2+x.2.2)
  else if x.1.2≤x.2.2 then (x.2.1,x.2.2-x.1.2) else (x.1.1,x.1.2-x.2.2)

lemma signedAdd_value (x : (Bool×ℕ)×(Bool×ℕ)) :
    intOfSign (signedAdd x)=intOfSign x.1+intOfSign x.2 := by
  rcases x with ⟨⟨s,a⟩,⟨t,b⟩⟩
  cases s <;> cases t <;> simp only [signedAdd,intOfSign,Bool.false_eq_true,
    Bool.true_eq_false,ite_true,ite_false,Int.natCast_add]
  all_goals first | omega | (split <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> omega)

lemma signedMul_value (x : (Bool×ℕ)×(Bool×ℕ)) :
    intOfSign (xor x.1.1 x.2.1,x.1.2*x.2.2)=intOfSign x.1*intOfSign x.2 := by
  rcases x with ⟨⟨s,a⟩,⟨t,b⟩⟩
  cases s <;> cases t <;> simp [intOfSign]

lemma intOfSign_not (x : Bool×ℕ) : intOfSign (!x.1,x.2) = -intOfSign x := by
  rcases x with ⟨s,n⟩
  cases s <;> simp [intOfSign]

namespace Procedure
noncomputable def intSign : Procedure intCode boolCode (fun z=>decide (z<0)) :=
  (first boolCode Nat.bits).precompose intData
noncomputable def intAbs : Procedure intCode Nat.bits Int.natAbs :=
  (second boolCode Nat.bits).precompose intData

noncomputable def signedInt : Procedure (prodCode boolCode Nat.bits) intCode intOfSign := by
  let s:=first boolCode Nat.bits
  let a:=second boolCode Nat.bits
  let nz:=boolNot.comp (binaryZero.comp a)
  exact ((boolAnd.comp (s.pair nz)).pair a).result (by
    intro x
    change prodCode boolCode Nat.bits (x.1 && !decide (x.2=0),x.2)=intCode (intOfSign x)
    rw [intCode,intData_ofSign]
    simp only [decide_not])

noncomputable def natToInt : Procedure Nat.bits intCode (fun n=>(n : ℤ)) :=
  (signedInt.comp ((constant Nat.bits boolCode false).pair (identity Nat.bits))).congrFun (by intro n;rfl)

noncomputable def intNeg : Procedure intCode intCode Neg.neg :=
  (signedInt.comp ((boolNot.comp intSign).pair intAbs)).congrFun (by
    intro z
    change intOfSign (!(intData z).1,(intData z).2) = -z
    rw [intOfSign_not,intOfSign_data])

noncomputable def signedAddP : Procedure
    (prodCode (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits))
    (prodCode boolCode Nat.bits) signedAdd := by
  let a:=first (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits)
  let b:=second (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits)
  let s:=(first boolCode Nat.bits).comp a
  let t:=(first boolCode Nat.bits).comp b
  let m:=(second boolCode Nat.bits).comp a
  let n:=(second boolCode Nat.bits).comp b
  let eqs:=boolNot.comp (boolXor.comp (s.pair t))
  let same:=s.pair (binaryAdd.comp (m.pair n))
  let le:=binaryLe.comp (m.pair n)
  let small:=t.pair (binarySub.comp (n.pair m))
  let large:=s.pair (binarySub.comp (m.pair n))
  exact (conditional eqs same (conditional le small large)).congrFun (by
    rintro ⟨⟨s,m⟩,⟨t,n⟩⟩
    cases s <;> cases t <;> simp [signedAdd,Function.comp_apply])

noncomputable def intAdd : Procedure (prodCode intCode intCode) intCode (fun x=>x.1+x.2) :=
  ((signedInt.comp signedAddP).precompose (fun x : ℤ×ℤ=>(intData x.1,intData x.2))).congrFun
    (by intro x;change intOfSign (signedAdd (intData x.1,intData x.2))=x.1+x.2
        rw [signedAdd_value,intOfSign_data,intOfSign_data])

noncomputable def intSub : Procedure (prodCode intCode intCode) intCode (fun x=>x.1-x.2) :=
  (intAdd.comp ((first intCode intCode).pair (intNeg.comp (second intCode intCode)))).congrFun
    (by intro x;rfl)

noncomputable def intMul : Procedure (prodCode intCode intCode) intCode (fun x=>x.1*x.2) := by
  let a:=first intCode intCode
  let b:=second intCode intCode
  let sign:=boolXor.comp ((intSign.comp a).pair (intSign.comp b))
  let mag:=binaryMul.comp ((intAbs.comp a).pair (intAbs.comp b))
  exact (signedInt.comp (sign.pair mag)).congrFun (by
    intro x
    change intOfSign (xor (intData x.1).1 (intData x.2).1,
      (intData x.1).2*(intData x.2).2)=x.1*x.2
    rw [signedMul_value (intData x.1,intData x.2),intOfSign_data,intOfSign_data])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackGCD.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def gcdStep (x : ℕ×ℕ) : ℕ×ℕ := if x.2=0 then x else (x.2,x.1%x.2)
def gcdRound (x : ℕ×ℕ) : ℕ×ℕ := gcdStep (gcdStep x)

lemma gcdStep_value (x : ℕ×ℕ) : (gcdStep x).1.gcd (gcdStep x).2=x.1.gcd x.2 := by
  unfold gcdStep
  split
  · rfl
  · dsimp only
    rw [Nat.gcd_comm x.2]
    exact (Nat.gcd_rec x.2 x.1).symm.trans (Nat.gcd_comm x.2 x.1)

lemma mod_half {b r : ℕ} (hr : 0<r) (hlt : r<b) : b%r≤b/2 := by
  by_cases h : 2*r≤b
  · have ht:=Nat.mod_lt b hr
    omega
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega : b-r<r)]
    omega

lemma gcdRound_half (x : ℕ×ℕ) : (gcdRound x).2≤x.2/2 := by
  by_cases hb : x.2=0
  · simp [gcdRound,gcdStep,hb]
  · have hp : 0<x.2:=by omega
    have hr:=Nat.mod_lt x.1 hp
    by_cases hz : x.1%x.2=0
    · simp [gcdRound,gcdStep,hb,hz]
    · simp only [gcdRound,gcdStep,hb,ite_false,hz]
      exact mod_half (by omega) hr

lemma gcdRound_value (x : ℕ×ℕ) : (gcdRound x).1.gcd (gcdRound x).2=x.1.gcd x.2 := by
  rw [gcdRound,gcdStep_value,gcdStep_value]

lemma gcdRound_iterate_bound (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).2≤x.2/2^i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    calc
      (gcdRound (gcdRound^[i] x)).2≤(gcdRound^[i] x).2/2:=gcdRound_half _
      _≤(x.2/2^i)/2:=Nat.div_le_div_right ih
      _=x.2/2^(i+1):=by rw [Nat.div_div_eq_div_mul,pow_succ]

lemma gcdRound_iterate_value (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).1.gcd (gcdRound^[i] x).2=x.1.gcd x.2 := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',gcdRound_value,ih]

lemma gcdRound_result (x : ℕ×ℕ) : (gcdRound^[x.2.bits.length] x).1=x.1.gcd x.2 := by
  have hz : (gcdRound^[x.2.bits.length] x).2=0:=by
    have hh:=gcdRound_iterate_bound x.2.bits.length x
    have hzdiv : x.2/2^x.2.bits.length=0:=by
      rw [Nat.size_eq_bits_len];exact Nat.div_eq_of_lt (Nat.lt_size_self x.2)
    rw [hzdiv] at hh
    omega
  simpa only [hz,Nat.gcd_zero_right] using gcdRound_iterate_value x.2.bits.length x

lemma gcdStep_sizeSum (x : ℕ×ℕ) :
    (gcdStep x).1.bits.length+(gcdStep x).2.bits.length≤x.1.bits.length+x.2.bits.length := by
  have hm:=bits_length_mono (Nat.mod_le x.1 x.2)
  unfold gcdStep
  split
  · exact le_rfl
  · change x.2.bits.length+(x.1%x.2).bits.length≤x.1.bits.length+x.2.bits.length
    omega

lemma gcdRound_iterate_sizeSum (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).1.bits.length+(gcdRound^[i] x).2.bits.length≤
      x.1.bits.length+x.2.bits.length := by
  induction i with
  | zero=>rfl
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    exact ((gcdStep_sizeSum _).trans (gcdStep_sizeSum _)).trans ih


end ExactQuantumFactoring.BitStackProgram
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ProcedureFurther.lean =====
namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def gcdStepP : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) gcdStep :=
  (conditional (binaryZero.comp (second Nat.bits Nat.bits))
    (identity (prodCode Nat.bits Nat.bits)) ((second Nat.bits Nat.bits).pair binaryMod)).congrFun
      (by intro x;simp only [gcdStep,Function.comp_apply,id_eq,decide_eq_true_eq])

noncomputable def binaryGcd : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun x=>x.1.gcd x.2) := by
  let p:=(gcdStepP.comp gcdStepP).congrFun (g:=gcdRound) (by intro x;rfl)
  let rep:=p.iterate (Polynomial.C 2*Polynomial.X+1) (by
    intro n x i _
    have hh:=gcdRound_iterate_sizeSum i x
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let len:=(length.precompose Nat.bits).comp (second Nat.bits Nat.bits)
  exact ((first Nat.bits Nat.bits).comp (rep.comp (len.pair (identity (prodCode Nat.bits Nat.bits))))).congrFun
    (by intro x;exact gcdRound_result x)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitStackRationals.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def ratCode (q : ℚ) : List Bool := prodCode intCode Nat.bits (q.num,q.den)

def ratData (x : ℤ×ℕ) : ℤ×ℕ :=
  if x.2=0 then (0,1) else
    (intOfSign (decide (x.1<0),x.1.natAbs/(x.2.gcd x.1.natAbs)),
      x.2/(x.2.gcd x.1.natAbs))

lemma intOfSign_div (z : ℤ) (d : ℕ) (hd : d∣z.natAbs) :
    intOfSign (decide (z<0),z.natAbs/d)=z/(d : ℤ) := by
  by_cases h : z<0
  · have hz := Int.eq_neg_natAbs_of_nonpos (le_of_lt h)
    have hdiv : (d : ℤ) ∣ (z.natAbs : ℤ) := Int.ofNat_dvd.mpr hd
    simp only [h,decide_true,intOfSign,ite_true]
    conv_rhs => rw [hz,Int.neg_ediv_of_dvd hdiv]
    rw [Int.natCast_ediv]
  · simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false]
    conv_rhs => rw [←Int.natAbs_of_nonneg (le_of_not_gt h)]
    rw [Int.natCast_ediv]

lemma ratData_spec (x : ℤ×ℕ) : ratData x=((mkRat x.1 x.2).num,(mkRat x.1 x.2).den) := by
  rw [Rat.num_mkRat,Rat.den_mkRat]
  unfold ratData
  split
  · rfl
  · rw [intOfSign_div _ _ (Nat.gcd_dvd_right _ _)]

namespace Procedure
noncomputable def ratNum : Procedure ratCode intCode Rat.num :=
  (first intCode Nat.bits).precompose (fun q : ℚ=>(q.num,q.den))
noncomputable def ratDen : Procedure ratCode Nat.bits Rat.den :=
  (second intCode Nat.bits).precompose (fun q : ℚ=>(q.num,q.den))

noncomputable def makeRat : Procedure (prodCode intCode Nat.bits) ratCode
    (fun x=>mkRat x.1 x.2) := by
  let n:=first intCode Nat.bits
  let d:=second intCode Nat.bits
  let a:=intAbs.comp n
  let g:=binaryGcd.comp (d.pair a)
  let num:=signedInt.comp ((intSign.comp n).pair (binaryDiv.comp (a.pair g)))
  let den:=binaryDiv.comp (d.pair g)
  let zero:=constant (prodCode intCode Nat.bits) (prodCode intCode Nat.bits) (0,1)
  let p:=conditional (binaryZero.comp d) zero (num.pair den)
  exact p.result (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq]
    change prodCode intCode Nat.bits (ratData x)=ratCode (mkRat x.1 x.2)
    rw [ratData_spec];rfl)

noncomputable def intToRat : Procedure intCode ratCode (fun z=>(z : ℚ)) :=
  (makeRat.comp ((identity intCode).pair (constant intCode Nat.bits 1))).congrFun (by
    intro z; simp [Rat.mkRat_eq_div])
noncomputable def natToRat : Procedure Nat.bits ratCode (fun n=>(n : ℚ)) :=
  (intToRat.comp natToInt).congrFun (by intro n;simp)

noncomputable def ratNeg : Procedure ratCode ratCode Neg.neg :=
  (makeRat.comp ((intNeg.comp ratNum).pair ratDen)).congrFun (by
    intro q
    change mkRat (-q.num) q.den = -q
    rw [Rat.mkRat_eq_div,Int.cast_neg,neg_div,Rat.num_div_den])

noncomputable def ratAdd : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1+x.2) := by
  let a:=first ratCode ratCode
  let b:=second ratCode ratCode
  let an:=ratNum.comp a
  let bn:=ratNum.comp b
  let ad:=ratDen.comp a
  let bd:=ratDen.comp b
  let num:=intAdd.comp ((intMul.comp (an.pair (natToInt.comp bd))).pair
    (intMul.comp (bn.pair (natToInt.comp ad))))
  let den:=binaryMul.comp (ad.pair bd)
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.1.num * (x.2.den : ℤ) + x.2.num * (x.1.den : ℤ))
      (x.1.den*x.2.den) = x.1+x.2
    rw [←Rat.mkRat_add_mkRat _ _ x.1.den_nz x.2.den_nz]
    simp)

noncomputable def ratMul : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1*x.2) := by
  let a:=first ratCode ratCode
  let b:=second ratCode ratCode
  let num:=intMul.comp ((ratNum.comp a).pair (ratNum.comp b))
  let den:=binaryMul.comp ((ratDen.comp a).pair (ratDen.comp b))
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.1.num*x.2.num) (x.1.den*x.2.den)=x.1*x.2
    rw [←Rat.mkRat_mul_mkRat];simp)

noncomputable def ratSub : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1-x.2) :=
  (ratAdd.comp ((first ratCode ratCode).pair (ratNeg.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (sub_eq_add_neg _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SignedSyntaxEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
variable {v : Type}
def intExprView (a : IntExpr v):=(a.pos,a.neg)
def intExprCode (ev : v→List Bool) (a : IntExpr v):=prodCode (exprCode ev) (exprCode ev) (intExprView a)
def ratExprView (a : RatExpr v):=(a.num,a.den)
def ratExprCode (ev : v→List Bool) (a : RatExpr v):=prodCode (intExprCode ev) (exprCode ev) (ratExprView a)
namespace Emission
noncomputable def intToNatP : Procedure intCode Nat.bits Int.toNat:=
  (conditional intSign (Procedure.constant intCode Nat.bits 0) intAbs).congrFun (by
    intro z;cases z <;> simp)
noncomputable def intExprViewP (ev : v→List Bool) : Procedure (intExprCode ev)
    (prodCode (exprCode ev) (exprCode ev)) intExprView :=(identity _).precompose _
noncomputable def intExprPosP (ev : v→List Bool) : Procedure (intExprCode ev) (exprCode ev) IntExpr.pos:=
  (first _ _).comp (intExprViewP ev)
noncomputable def intExprNegP (ev : v→List Bool) : Procedure (intExprCode ev) (exprCode ev) IntExpr.neg:=
  (second _ _).comp (intExprViewP ev)
noncomputable def intExprMkP (ev : v→List Bool) : Procedure
    (prodCode (exprCode ev) (exprCode ev)) (intExprCode ev) (fun x=>IntExpr.mk x.1 x.2):=
  (identity _).result (by intro x;rfl)
noncomputable def ratExprViewP (ev : v→List Bool) : Procedure (ratExprCode ev)
    (prodCode (intExprCode ev) (exprCode ev)) ratExprView :=(identity _).precompose _
noncomputable def ratExprNumP (ev : v→List Bool) : Procedure (ratExprCode ev) (intExprCode ev) RatExpr.num:=
  (first _ _).comp (ratExprViewP ev)
noncomputable def ratExprDenP (ev : v→List Bool) : Procedure (ratExprCode ev) (exprCode ev) RatExpr.den:=
  (second _ _).comp (ratExprViewP ev)
noncomputable def ratExprMkP (ev : v→List Bool) : Procedure
    (prodCode (intExprCode ev) (exprCode ev)) (ratExprCode ev) (fun x=>RatExpr.mk x.1 x.2):=
  (identity _).result (by intro x;rfl)
end Emission
namespace Emits
variable {α : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma ipos {f : α→IntExpr v} (h : BitStackProgram.Emits ea (intExprCode ev) f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>(f x).pos):=(ofProcedure (Emission.intExprPosP ev)).comp h
lemma ineg {f : α→IntExpr v} (h : BitStackProgram.Emits ea (intExprCode ev) f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>(f x).neg):=(ofProcedure (Emission.intExprNegP ev)).comp h
lemma imk {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (intExprCode ev) (fun x=>IntExpr.mk (f x) (g x)):=
  (ofProcedure (Emission.intExprMkP ev)).comp (h.pair j)
lemma rnum {f : α→RatExpr v} (h : BitStackProgram.Emits ea (ratExprCode ev) f) :
    BitStackProgram.Emits ea (intExprCode ev) (fun x=>(f x).num):=(ofProcedure (Emission.ratExprNumP ev)).comp h
lemma rden {f : α→RatExpr v} (h : BitStackProgram.Emits ea (ratExprCode ev) f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>(f x).den):=(ofProcedure (Emission.ratExprDenP ev)).comp h
lemma rmk {f : α→IntExpr v} {g : α→NatExpr v} (h : BitStackProgram.Emits ea (intExprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (ratExprCode ev) (fun x=>RatExpr.mk (f x) (g x)):=
  (ofProcedure (Emission.ratExprMkP ev)).comp (h.pair j)
end Emits
end ExactQuantumFactoring.NetworkEmission

namespace ExactQuantumFactoring
syntax "expr_emit" : tactic
macro_rules
  | `(tactic| expr_emit) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact BitStackProgram.Emits.id _
    | exact BitStackProgram.Emits.const _ _ _
    | (apply NetworkEmission.Emits.ipos; expr_emit)
    | (apply NetworkEmission.Emits.ineg; expr_emit)
    | (apply NetworkEmission.Emits.rnum; expr_emit)
    | (apply NetworkEmission.Emits.rden; expr_emit)
    | (apply NetworkEmission.Emits.imk <;> expr_emit)
    | (apply NetworkEmission.Emits.rmk <;> expr_emit)
    | (apply NetworkEmission.Emits.nvar; expr_emit)
    | (apply NetworkEmission.Emits.nconst; expr_emit)
    | (apply NetworkEmission.Emits.nadd <;> expr_emit)
    | (apply NetworkEmission.Emits.nsub <;> expr_emit)
    | (apply NetworkEmission.Emits.nmul <;> expr_emit)
    | (apply NetworkEmission.Emits.ndiv <;> expr_emit)
    | (apply NetworkEmission.Emits.nmod <;> expr_emit)
    | (apply NetworkEmission.Emits.nite <;> expr_emit)
    | (apply BitStackProgram.Emits.fst; expr_emit)
    | (apply BitStackProgram.Emits.snd; expr_emit)
    | (apply BitStackProgram.Emits.pair <;> expr_emit)
    | (apply BitStackProgram.Emits.natAdd <;> expr_emit)
    | (apply BitStackProgram.Emits.natSub <;> expr_emit)
    | (apply BitStackProgram.Emits.natMul <;> expr_emit)
    | (apply BitStackProgram.Emits.natDiv <;> expr_emit)
    | (apply BitStackProgram.Emits.natMod <;> expr_emit)
    | (apply BitStackProgram.Emits.natMax <;> expr_emit))
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ArithmeticSyntaxEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "IEm" => BitStackProgram.Emits ea (intExprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma iOfNat {a : α→NatExpr v} (ha : NEm a) : IEm (fun x=>IntExpr.ofNat (a x)):=
  imk ha (const _ _ (NatExpr.const 0))
lemma iOfInt {a : α→ℤ} (ha : BitStackProgram.Emits ea intCode a) : IEm (fun x=>IntExpr.ofInt (a x)):=by
  exact imk (nconst ((ofProcedure Emission.intToNatP).comp ha))
    (nconst ((ofProcedure Emission.intToNatP).comp ((ofProcedure Procedure.intNeg).comp ha)))
lemma iAdd {a b : α→IntExpr v} (ha : IEm a) (hb : IEm b) : IEm (fun x=>(a x).add (b x)):=
  imk (nadd (ipos ha) (ipos hb)) (nadd (ineg ha) (ineg hb))
lemma iNeg {a : α→IntExpr v} (ha : IEm a) : IEm (fun x=>(a x).negation):=imk (ineg ha) (ipos ha)
lemma iSub {a b : α→IntExpr v} (ha : IEm a) (hb : IEm b) : IEm (fun x=>(a x).sub (b x)):=iAdd ha (iNeg hb)
lemma iMul {a b : α→IntExpr v} (ha : IEm a) (hb : IEm b) : IEm (fun x=>(a x).mul (b x)):=by
  unfold IntExpr.mul;expr_emit
lemma iScale {a : α→IntExpr v} {b : α→NatExpr v} (ha : IEm a) (hb : NEm b) :
    IEm (fun x=>(a x).scale (b x)):=iMul ha (iOfNat hb)
lemma iToNat {a : α→IntExpr v} (ha : IEm a) : NEm (fun x=>(a x).toNat):=nsub (ipos ha) (ineg ha)
lemma iNatAbs {a : α→IntExpr v} (ha : IEm a) : NEm (fun x=>(a x).natAbs):=
  nadd (nsub (ipos ha) (ineg ha)) (nsub (ineg ha) (ipos ha))
lemma iIte {a b : α→NatExpr v} {c d : α→IntExpr v} (ha : NEm a) (hb : NEm b) (hc : IEm c) (hd : IEm d) :
    IEm (fun x=>IntExpr.iteLe (a x) (b x) (c x) (d x)):=by unfold IntExpr.iteLe;expr_emit
lemma iIfLe {a b c d : α→IntExpr v} (ha : IEm a) (hb : IEm b) (hc : IEm c) (hd : IEm d) :
    IEm (fun x=>IntExpr.ifLe (a x) (b x) (c x) (d x)):=
  iIte (nadd (ipos ha) (ineg hb)) (nadd (ipos hb) (ineg ha)) hc hd
lemma rOfInt {a : α→IntExpr v} (ha : IEm a) : REm (fun x=>RatExpr.ofInt (a x)):=rmk ha (const _ _ (NatExpr.const 1))
lemma rOfNat {a : α→NatExpr v} (ha : NEm a) : REm (fun x=>RatExpr.ofNat (a x)):=rOfInt (iOfNat ha)
lemma rConst {a : α→ℚ} (ha : BitStackProgram.Emits ea ratCode a) : REm (fun x=>RatExpr.const (a x)):=
  rmk (iOfInt ((ofProcedure Procedure.ratNum).comp ha)) (nconst ((ofProcedure Procedure.ratDen).comp ha))
lemma rNormalize {a : α→RatExpr v} (ha : REm a) : REm (fun x=>(a x).normalize):=
  rmk (iIte (rden ha) (const _ _ (NatExpr.const 0)) (const _ _ (IntExpr.ofInt 0)) (rnum ha))
    (nite (rden ha) (const _ _ (NatExpr.const 0)) (const _ _ (NatExpr.const 1)) (rden ha))
lemma rAdd {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>(a x).add (b x)):=by
  have hc:=rNormalize ha;have hd:=rNormalize hb
  exact rmk (iAdd (iScale (rnum hc) (rden hd)) (iScale (rnum hd) (rden hc))) (nmul (rden hc) (rden hd))
lemma rNeg {a : α→RatExpr v} (ha : REm a) : REm (fun x=>(a x).negation):=rmk (iNeg (rnum ha)) (rden ha)
lemma rSub {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>(a x).sub (b x)):=rAdd ha (rNeg hb)
lemma rMul {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>(a x).mul (b x)):=
  rmk (iMul (rnum ha) (rnum hb)) (nmul (rden ha) (rden hb))
lemma rInv {a : α→RatExpr v} (ha : REm a) : REm (fun x=>(a x).inverse):=
  rmk (iScale (rnum ha) (rden ha)) (nmul (iNatAbs (rnum ha)) (iNatAbs (rnum ha)))
lemma rDiv {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>(a x).div (b x)):=rMul ha (rInv hb)
lemma rPow {a : α→RatExpr v} (ha : REm a) (k : ℕ) : REm (fun x=>(a x).pow k):=by
  induction k with
  | zero=>exact const _ _ (RatExpr.const 1)
  | succ k ih=>exact rMul ih ha
lemma rIfNatLe {a b : α→NatExpr v} {c d : α→RatExpr v} (ha : NEm a) (hb : NEm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifNatLe (a x) (b x) (c x) (d x)):=
  rmk (iIte ha hb (rnum hc) (rnum hd)) (nite ha hb (rden hc) (rden hd))
lemma rIfIntLe {a b : α→IntExpr v} {c d : α→RatExpr v} (ha : IEm a) (hb : IEm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifIntLe (a x) (b x) (c x) (d x)):=
  rIfNatLe (nadd (ipos ha) (ineg hb)) (nadd (ipos hb) (ineg ha)) hc hd
lemma rIfLe {a b c d : α→RatExpr v} (ha : REm a) (hb : REm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifLe (a x) (b x) (c x) (d x)):=by
  have he:=rNormalize ha;have hf:=rNormalize hb
  exact rIfIntLe (iScale (rnum he) (rden hf)) (iScale (rnum hf) (rden he)) hc hd
lemma rIfLt {a b c d : α→RatExpr v} (ha : REm a) (hb : REm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifLt (a x) (b x) (c x) (d x)):=rIfLe hb ha hd hc
lemma rIfEq {a b c d : α→RatExpr v} (ha : REm a) (hb : REm b) (hc : REm c) (hd : REm d) :
    REm (fun x=>RatExpr.ifEq (a x) (b x) (c x) (d x)):=rIfLe ha hb (rIfLe hb ha hc hd) hd
lemma rMax {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>RatExpr.max (a x) (b x)):=rIfLe ha hb hb ha
lemma rMin {a b : α→RatExpr v} (ha : REm a) (hb : REm b) : REm (fun x=>RatExpr.min (a x) (b x)):=rIfLe ha hb ha hb
lemma iCeilRatio {a : α→IntExpr v} {b : α→NatExpr v} (ha : IEm a) (hb : NEm b) :
    NEm (fun x=>(a x).ceilRatioNat (b x)):=ndiv (nsub (nadd (iToNat ha) hb) (const _ _ (NatExpr.const 1))) hb
lemma iFloorRatio {a : α→IntExpr v} {b : α→NatExpr v} (ha : IEm a) (hb : NEm b) :
    IEm (fun x=>(a x).floorRatio (b x)):=iSub (iOfNat (ndiv (iToNat ha) hb)) (iOfNat (iCeilRatio (iNeg ha) hb))
lemma rCeilNat {a : α→RatExpr v} (ha : REm a) : NEm (fun x=>(a x).ceilNat):=iCeilRatio (rnum ha) (rden ha)
lemma rFloor {a : α→RatExpr v} (ha : REm a) : IEm (fun x=>(a x).floor):=iFloorRatio (rnum ha) (rden ha)
lemma rCeil {a : α→RatExpr v} (ha : REm a) : IEm (fun x=>(a x).ceil):=iNeg (rFloor (rNeg ha))
end ExactQuantumFactoring.NetworkEmission.Emits

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkFiniteExpressionEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α v : Type} {ea : α→List Bool} {n w b : α→ℕ}
lemma compileFinite {k : ℕ} (en : Fin k ≃ v) {e : α→NatExpr v}
    (he : BitStackProgram.Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hw : BitStackProgram.Emits ea unaryCode w)
    {fs : ∀x,v→BooleanNetwork (n x) (w x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).compile (fs x)):=by
  classical
  choose p hp ep using hf
  let ps (x:α):=List.ofFn (fun i=>p (en i) x)
  have hps : BitStackProgram.Emits ea (listCode packCode) ps:=BitStackProgram.Emits.ofFn (fun i=>hp (en i))
  let out (x:α):=exprPack (n x) (w x) (fun i:v=>Emission.envVars (ps x) (en.symm i).val) (e x)
  refine ⟨out,(ofProcedure (Emission.genericExprPackP (fun i:v=>(en.symm i).val))).comp
    ((hn.pair (hw.pair hps)).pair he),?_⟩
  intro x
  apply exprPack_value
  intro i
  have hh : Emission.envVars (ps x) (en.symm i).val=p i x:=by
    simp [Emission.envVars,ps,List.headD_eq_head?_getD,List.head?_drop,(en.symm i).isLt]
  rw [hh];exact ep i x
lemma templateFinite {k : ℕ} (en : Fin k ≃ v) {e : α→NatExpr v}
    (he : BitStackProgram.Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    {fs : ∀x,v→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).template (fs x)):=by
  have hw : BitStackProgram.Emits ea unaryCode (fun x=>(e x).templateWidth (b x)):=
    (ofProcedure (Emission.exprWidthP _)).comp (hb.pair he)
  exact compileFinite en he hn hw (fun i=>(hf i).comp (resize hb hw))
lemma isOneFinite {k : ℕ} (en : Fin k ≃ v) {e : α→NatExpr v}
    (he : BitStackProgram.Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    {fs : ∀x,v→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).isOne (fs x)):=by
  have hw : BitStackProgram.Emits ea unaryCode (fun x=>(e x).templateWidth (b x)):=
    (ofProcedure (Emission.exprWidthP _)).comp (hb.pair he)
  exact (templateFinite en he hn hb hf).equalOn (wordConst hn hw (const _ _ 1)) hw
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetentionEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma threshold {T : α→ℕ} {p : α→RatExpr v} {coin : α→NatExpr v}
    (hT : BitStackProgram.Emits ea unaryCode T)
    (hp : BitStackProgram.Emits ea (ratExprCode ev) p)
    (hc : BitStackProgram.Emits ea (exprCode ev) coin) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>thresholdExpr (T x) (p x) (coin x)):=by
  have ht : BitStackProgram.Emits ea Nat.bits (fun x=>2^(T x)):=
    (ofProcedure Procedure.binaryPow).comp (hT.pair (const _ _ 2))
  exact nite (nadd hc (const _ _ (NatExpr.const (v:=v) 1)))
    (iToNat (rFloor (rMul hp (rOfNat (nconst ht))))) (const _ _ (NatExpr.const (v:=v) 1)) (const _ _ (NatExpr.const (v:=v) 0))
end Emits
namespace NetEmits
variable {α v : Type} {ea : α→List Bool} {n b T : α→ℕ}
lemma retention {k : ℕ} (en : Fin k ≃ v) {p : α→RatExpr v} {coin : α→NatExpr v}
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    (hT : BitStackProgram.Emits ea unaryCode T)
    (hp : BitStackProgram.Emits ea (ratExprCode (fun i:v=>(en.symm i).val.bits)) p)
    (hc : BitStackProgram.Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) coin)
    {fs : ∀x,v→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>retentionNet (T x) (p x) (coin x) (fs x)):=
  isOneFinite en (Emits.threshold hT hp hc) hn hb hf
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionDependentLists.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {k : α→ℕ}
lemma ofFnDep (d : β) {f : ∀x,Fin (k x)→β} (hk : Emits ea unaryCode k)
    (hf : Emits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) eb (fun x=>f x.1 x.2)) :
    Emits ea (listCode eb) (fun x=>List.ofFn (f x)):=by
  let c:=fun x:ℕ×α=>x.1<k x.2
  let g:=fun x i=>if h:i<k x then f x ⟨i,h⟩ else d
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hc:=hx.fst.unaryNat.natLt (hk.comp hx.snd).unaryNat
  have hy : Emits (fun x:{a:ℕ×α // c a}=>prodCode unaryCode ea x.val) eb (fun x=>g x.val.2 x.val.1):=by
    exact (hf.precompose (fun x:{a:ℕ×α // c a}=>(⟨x.val.2,⟨x.val.1,x.property⟩⟩ : Σa,Fin (k a)))).congr
      (by intro x;dsimp only [g];rw [dite_eq_left x.property])
  have hn : Emits (fun x:{a:ℕ×α // ¬c a}=>prodCode unaryCode ea x.val) eb (fun x=>g x.val.2 x.val.1):=by
    exact (const _ _ d).congr (by intro x;dsimp only [g];rw [dite_eq_right x.property])
  obtain ⟨p⟩:=splitOn (f:=fun x:ℕ×α=>g x.2 x.1) c hc hy hn
  exact ((ofProcedure (Procedure.tabulate (f:=g) d p)).comp (hk.pair (id ea))).congr (by
    intro x;rw [←NetworkEmission.ofFn_nat_eq_map];congr 1;funext i;simp only [g,i.isLt,dite_eq_left])
lemma flatten (d : β) {f : α→List (List β)} (hf : Emits ea (listCode (listCode eb)) f) :
    Emits ea (listCode eb) (fun x=>(f x).flatten):=
  (ofProcedure (Procedure.listFlatten eb d)).comp hf
end ExactQuantumFactoring.BitStackProgram.Emits
namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma concat {p : ∀x,Fin (k x)→List (Instruction (q x))} (hk : Emits ea unaryCode k)
    (hp : OpsEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>p x.1 x.2)) :
    OpsEmits ea (fun x=>(List.ofFn (p x)).flatten):=by
  exact ((ofFnDep (f:=fun x i=>(p x i).map eraseOp) [] hk hp).flatten (⟨plainGate .not,[]⟩ : Op)).congr (by
    intro x;simp only [List.map_flatten,List.map_ofFn];rfl)
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkCanonicalEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emission
open Procedure
noncomputable def massP : Procedure dataCode Nat.bits Data.mass:=
  binaryAdd.comp (dataWidthP.pair ((listLength Nat.bits 0).comp dataOutputsP))
def canonicalPack (p : Pack) : Pack:=⟨⟨p.val.value.mass,p.val.value⟩,p.property.1,le_rfl⟩
noncomputable def canonicalPackP : Procedure packCode packCode canonicalPack:=by
  let hv:=packValueP
  let hmass:=boundedUnary (massP.comp hv) packBudgetP (fun x=>x.property.2)
  exact (hmass.pair hv).result (by intro x;rfl)
lemma canonicalPack_erase {n m : ℕ} (p : Pack) (a : BooleanNetwork n m)
    (h : p.val.value=erase a) : canonicalPack p=erasePack a:=by
  apply Subtype.ext
  change PackData.mk _ _=PackData.mk _ _
  congr 1
  · rw [h]
    simp only [Data.mass,Data.width,erase,eraseNet_length,List.length_ofFn]
end Emission
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m : α→ℕ} {f : ∀x,BooleanNetwork (n x) (m x)}
lemma canonical (hf : NetEmits ea f) : Emits ea packCode (fun x=>erasePack (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ((ofProcedure Emission.canonicalPackP).comp hp).congr
    (fun x=>Emission.canonicalPack_erase _ _ (he x))
lemma ofCanonical (hf : Emits ea packCode (fun x=>erasePack (f x))) : NetEmits ea f:=
  ⟨fun x=>erasePack (f x),hf,fun _=>rfl⟩
lemma canonicalLength (hf : NetworkAt (fun x=>(ea x).length) f)
    (hn : PolyAt (fun x=>(ea x).length) n) (hm : PolyAt (fun x=>(ea x).length) m) :
    PolyAt (fun x=>(ea x).length) (fun x=>(packCode (erasePack (f x))).length):=by
  exact ((PolyAt.const _ 104).mul ((((hn.add hf).add hm).add (PolyAt.const _ 1)).pow 2)).of_le
    (fun x=>packCode_bound _)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkRecursionEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {K : α→ℕ} {n m : α→ℕ→ℕ}
    {f : ∀x j,BooleanNetwork (n x j) (m x j)}
/-- Saturation makes the loop's intermediate-state bound valid for every
possible invocation, not merely for the one starting at stage zero. -/
lemma boundedStages (hK : Emits ea unaryCode K)
    (h0 : NetEmits ea (fun x=>f x 0))
    (hs : NetEmits
      (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
        (x.1,(x.2.val,erasePack (f x.1 x.2.val))))
      (fun x=>f x.1 (x.2.val+1)))
    (hn : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>n x.1 x.2.val))
    (hm : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>m x.1 x.2.val))
    (hc : NetworkAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>f x.1 x.2.val)) :
    NetEmits ea (fun x=>f x (K x)):=by
  let F:=fun x j=>erasePack (f x j)
  let ec:=recursionCode (ea:=ea) (eb:=packCode) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) packCode
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.canonical.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>
      (⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;dsimp only [F];rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) packCode
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  have ht : Emits ec packCode (fun x=>F x.1 (min (x.2.val+1) (K x.1))):=
    BitStackProgram.Emits.splitOn c htest hy hz
  have hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(packCode (F x.1 x.2.val)).length):=
    ((PolyAt.const _ 104).mul ((((hn.add hc).add hm).add (PolyAt.const _ 1)).pow 2)).of_le
      (fun x=>packCode_bound _)
  exact ofCanonical (BitStackProgram.Emits.boundedRecursion K F hK h0.canonical ht hb)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitPreparationEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

def hadamardOp (i : ℕ) : Op:=⟨plainGate .hadamard,[i]⟩
lemma erase_hadamardAt {q : ℕ} (i : Fin q) : eraseOp (hadamardAt i)=hadamardOp i.val:=rfl
lemma erase_hadamardPrefix (q k : ℕ) (h : k≤q) :
    (hadamardPrefix q k h).map eraseOp=(List.range k).map hadamardOp:=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [hadamardPrefix,List.map_append,ih,List.range_succ,List.map_append];rfl
namespace Emission
open Procedure
noncomputable def hadamardOpP : Procedure Nat.bits opCode hadamardOp:=by
  let wires:=(listCons Nat.bits).comp ((identity Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .hadamard)).pair wires)
noncomputable def hadamardPrefixP : Procedure unaryCode (listCode opCode)
    (fun k=>(List.range k).map hadamardOp):=
  (listMap 0 (hadamardOp 0) hadamardOpP).comp NetworkEmission.Emission.rangeP
end Emission
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q r m : α→ℕ}
lemma hadamards {k : α→ℕ} (hk : Emits ea unaryCode k) (h : ∀x,k x≤q x) :
    OpsEmits ea (fun x=>hadamardPrefix (q x) (k x) (h x)):=
  ((ofProcedure Emission.hadamardPrefixP).comp hk).congr (fun _=>(erase_hadamardPrefix _ _ _).symm)
lemma left {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (r : α→ℕ) :
    OpsEmits ea (fun x=>leftProgram (r x) (p x)):=by
  exact place hp (fun x=>leftRegister (q x) (r x)) (fun _ i=>i) (by intros;rfl)
    (BitStackProgram.Emits.id (prodCode ea Nat.bits)).snd
lemma right {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hr : Emits ea unaryCode r) :
    OpsEmits ea (fun x=>rightProgram (r x) (p x)):=by
  have he:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact place hp (fun x=>rightRegister (r x) (q x)) (fun x i=>r x+i) (by intros;rfl)
    ((hr.comp he.fst).unaryNat.natAdd he.snd)
lemma parallel {p : ∀x,List (Instruction (q x))} {s : ∀x,List (Instruction (r x))}
    (hp : OpsEmits ea p) (hs : OpsEmits ea s) (hq : Emits ea unaryCode q) :
    OpsEmits ea (fun x=>parallelProgram (p x) (s x)):=
  (hp.left r).append (hs.right hq)
lemma target {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hm : Emits ea unaryCode m) (r : α→ℕ) :
    OpsEmits ea (fun x=>targetProgram (m x) (r x) (p x)):=by
  have he:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact place hp (fun x=>targetRegister (m x) (q x) (r x)) (fun x i=>m x+i) (by intros;rfl)
    ((hm.comp he.fst).unaryNat.natAdd he.snd)
lemma prepared {f : ∀x,BooleanNetwork (m x) (q x)} (hf : NetworkEmission.NetEmits ea f)
    (hm : Emits ea unaryCode m) (h : ∀x,(f x).net.count≤r x)
    {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) :
    OpsEmits ea (fun x=>preparedOracle (f x) (h x) (p x)):=
  (oracleOn hf h).append (hp.target hm r)
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/EmissionLengthBounds.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.PolyAt
variable {α : Sort*} {l k f : α→ℕ}
lemma rebase (hf : PolyAt k f) (hk : PolyAt l k) : PolyAt l f:=by
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hk
  exact ⟨p.comp q,fun x=>by
    simpa only [Polynomial.eval_comp] using (hp x).trans (PolyBound.eval_mono p (hq x))⟩
end ExactQuantumFactoring.PolyAt

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma lengthPoly {f : α→β} (hf : Emits ea eb f) :
    PolyAt (fun x=>(ea x).length) (fun x=>(eb (f x)).length):=by
  obtain ⟨p⟩:=hf
  exact ⟨Polynomial.X+p.bound,fun x=>by simpa using p.output_length_le x⟩
lemma unaryPoly {f : α→ℕ} (hf : Emits ea unaryCode f) :
    PolyAt (fun x=>(ea x).length) f:=by
  simpa only [unaryCode,List.length_replicate] using hf.lengthPoly
lemma indexCode_poly {k : α→ℕ} (hk : Emits ea unaryCode k) :
    PolyAt (fun x:Σa,Fin (k a)=>(ea x.1).length)
      (fun x=> (prodCode unaryCode ea (x.2.val,x.1)).length):=by
  have hb:=hk.unaryPoly.pull (fun x:Σa,Fin (k a)=>x.1)
  exact (((PolyAt.const _ 2).mul hb).add (PolyAt.self _)).add (PolyAt.const _ 2) |>.of_le (by
    intro x
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate]
    have := x.2.isLt
    omega)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma countPoly {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    NetworkAt (fun x=>(ea x).length) f:=hf.count.unaryPoly
lemma countPolyIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) (m x)}
    (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetworkAt (fun x:Σa,Fin (k a)=>(ea x.1).length) (fun x=>f x.1 x.2):=
  hf.countPoly.rebase hk.indexCode_poly
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitEncodingSize.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma natWord_length (k : ℕ) : (natWord k).length=k+1 := by
  simp [natWord]

lemma Gate.arity_le (g : Gate) : g.arity≤4 := by
  rcases g with ⟨p,i,c⟩
  cases p <;> cases c <;> cases i <;> decide
lemma Primitive.code_le (p : Primitive) : p.code≤4 := by
  cases p <;> decide

lemma flatMap_length_bound {α β : Type*} (xs : List α) (f : α→List β) (b : ℕ)
    (h : ∀ x∈xs, (f x).length≤b) : (xs.flatMap f).length≤xs.length*b := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=h x (List.mem_cons_self)
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Addresses are unary in the frozen interface; bounded gate arity ensures
this encoding itself has only polynomial overhead in width and gate count. -/
lemma Instruction.encode_length {q : ℕ} (o : Instruction q) :
    o.encode.length≤7+4*q := by
  have h:=flatMap_length_bound (List.ofFn (fun i=> (o.wire i).val)) natWord q (by
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    rw [natWord_length]
    exact (o.wire i).isLt)
  rw [List.length_ofFn] at h
  have ha:=Nat.mul_le_mul_right q (Gate.arity_le o.gate)
  have hc:=Primitive.code_le o.gate.primitive
  simp only [Instruction.encode,List.length_append,natWord_length,List.length_cons,List.length_nil]
  omega

lemma Circuit.encode_length (c : Circuit) :
    c.encode.length≤c.qubits+2+c.instructions.length*(8+4*c.qubits) := by
  have h:=flatMap_length_bound c.instructions Instruction.encode (7+4*c.qubits)
    (fun x _=>Instruction.encode_length x)
  simp only [Circuit.encode,List.length_append,natWord_length]
  nlinarith

end ExactQuantumFactoring




end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitRecursionEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits
lemma gateCode_bound (g : Gate) : (gateCode g).length≤20:=by
  have h:=Primitive.code_le g.primitive
  simp only [gateCode,gatePayload,gateView,prodCode, pairBits_length,primitiveCode,unaryCode,List.length_replicate,
    Procedure.boolCode,List.length_cons,List.length_nil]
  omega
lemma opCode_bound {q : ℕ} (o : Instruction q) : (opCode (eraseOp o)).length≤100+16*q:=by
  have h:=NativeAIG.listCode_length_bound Nat.bits (List.ofFn (fun i=>(o.wire i).val)) q (by
    intro i hi
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
    exact (NativeAIG.nat_bits_length_bound _).trans (Nat.le_of_lt (o.wire j).isLt))
  rw [List.length_ofFn] at h
  have hg:=gateCode_bound o.gate
  have ha:=Gate.arity_le o.gate
  change (prodCode gateCode (listCode Nat.bits) (o.gate,List.ofFn (fun i=>(o.wire i).val))).length≤_
  simp only [prodCode, pairBits_length]
  nlinarith
lemma opsCode_bound {q : ℕ} (p : List (Instruction q)) :
    (listCode opCode (p.map eraseOp)).length≤p.length*(202+32*q)+1:=by
  have h:=NativeAIG.listCode_length_bound opCode (p.map eraseOp) (100+16*q) (by
    intro o ho;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ho;exact opCode_bound i)
  simp only [List.length_map] at h
  nlinarith

end ExactQuantumFactoring.CircuitEmission
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OpsEmits.lean =====
namespace OAI

section
namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {K : α→ℕ} {q : α→ℕ→ℕ}
    {f : ∀x j,List (Instruction (q x j))}
lemma lengthPoly {w : α→ℕ} {p : ∀x,List (Instruction (w x))} (hp : OpsEmits ea p) :
    PolyAt (fun x=>(ea x).length) (fun x=>(p x).length):=by
  exact (BitStackProgram.Emits.lengthPoly hp).of_le (fun x=>by
    simpa only [List.length_map] using list_length_le_code opCode ((p x).map eraseOp))
lemma boundedStages (hK : Emits ea unaryCode K)
    (h0 : OpsEmits ea (fun x=>f x 0))
    (hs : OpsEmits
      (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode (listCode opCode))
        (x.1,(x.2.val,(f x.1 x.2.val).map eraseOp)))
      (fun x=>f x.1 (x.2.val+1)))
    (hq : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>q x.1 x.2.val))
    (hl : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>(f x.1 x.2.val).length)) :
    OpsEmits ea (fun x=>f x (K x)):=by
  let F:=fun x j=>(f x j).map eraseOp
  let ec:=recursionCode (ea:=ea) (eb:=listCode opCode) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) (listCode opCode)
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>(⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;dsimp only [F];rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) (listCode opCode)
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  have ht : Emits ec (listCode opCode) (fun x=>F x.1 (min (x.2.val+1) (K x.1))):=
    BitStackProgram.Emits.splitOn c htest hy hz
  have hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(listCode opCode (F x.1 x.2.val)).length):=
    ((hl.mul ((PolyAt.const _ 202).add ((PolyAt.const _ 32).mul hq))).add (PolyAt.const _ 1)).of_le
      (fun x=>opsCode_bound _)
  exact BitStackProgram.Emits.boundedRecursion K F hK h0 ht hb
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TensorEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma tensorWidth (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k) :
    Emits ea unaryCode (fun x=>ExactQuantumFactoring.tensorWidth (q x) (k x)):=
  (hk.unaryMul hq).congr (fun _=>(tensorWidth_eq _ _).symm)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma tensorWire_val (q K : ℕ) (i : Fin K) (j : Fin q) :
    (tensorWire q K i j).val=q*i.val+j.val:=by
  induction K with
  | zero=>exact Fin.elim0 i
  | succ K ih=>
    refine Fin.cases ?_ (fun i=>?_) i
    · simp only [tensorWire,Fin.cases_zero,Fin.val_castAdd,Fin.val_zero,Nat.mul_zero,Nat.zero_add]
    · simp only [tensorWire,Fin.cases_succ,Fin.val_natAdd,ih,Fin.val_succ,Nat.mul_add,Nat.mul_one];omega
lemma tensorPack_value {n q K : ℕ} (fs : Fin K→BooleanNetwork n q) (ps : Fin K→Pack)
    (h : ∀i,(ps i).val.value=erase (fs i)) :
    ((List.ofFn ps).foldr pairPack (emptyAt n)).val.value=erase (tensorNetwork fs):=by
  induction K with
  | zero=>simp only [List.ofFn_zero,List.foldr_nil,tensorNetwork,emptyAt,selectPack];rw [erase_select];rfl
  | succ K ih=>
    rw [List.ofFn_succ,List.foldr_cons,tensorNetwork]
    exact pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n q k : α→ℕ}
lemma tensorSelect (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k)
    (i : ∀x,Fin (k x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>ExactQuantumFactoring.tensorSelect (q x) (k x) (i x)):=
  selectSlice (hq.tensorWidth hk) hq (hq.unaryNat.natMul hi) _ (fun _ _=>tensorWire_val _ _ _ _)
lemma tensor {f : ∀x,Fin (k x)→BooleanNetwork (n x) (q x)}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>tensorNetwork (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨s,hs,es⟩:=extendPack hk p hp
  obtain ⟨pp⟩:=hs
  have hps:=(ofProcedure (Procedure.tabulate (f:=s) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (s x)).foldr pairPack (emptyAt (n x)),
    (ofProcedure (Emission.foldRightPack 0 (by intros;rfl) Emission.pairPackP)).comp
      (hps.pair ((ofProcedure Emission.emptyAtP).comp hn)),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact tensorPack_value _ _ (fun i=>by rw [es];exact he ⟨x,i⟩)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma tensor {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k) :
    OpsEmits ea (fun x=>tensorProgram (p x) (k x)):=by
  apply boundedStages hk (f:=fun x j=>tensorProgram (p x) j)
  · exact const _ _ []
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
      (fun x:Σa,Fin (k a)=>(x.1,(x.2.val,(tensorProgram (p x.1) x.2.val).map eraseOp)))
    exact parallel (hp.comp hx.fst) hx.snd.snd (hq.comp hx.fst)
  · exact ((hq.tensorWidth hk).unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hk.unaryPoly.mul hp.lengthPoly).pull (fun x:Σa,Fin (k a+1)=>x.1)).of_le (by
      intro x;rw [tensorProgram_length];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/MachineWiringEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n p q r : α→ℕ}
lemma firstSelect (hp : Emits ea unaryCode p) (hq : Emits ea unaryCode q) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.select (firstRegister (p x) (q x) (r x))):=
  selectSlice ((hp.unaryAdd hq).unaryAdd hr) hp (const _ _ 0) _ (by intros;simp only [Nat.zero_add];rfl)
lemma targetSelect (hp : Emits ea unaryCode p) (hq : Emits ea unaryCode q) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.select (targetRegister (p x) (q x) (r x))):=
  selectSlice ((hp.unaryAdd hq).unaryAdd hr) hq hp.unaryNat _ (by intros;rfl)
lemma zeros (hn : Emits ea unaryCode n) (hp : Emits ea unaryCode p) :
    NetEmits ea (fun x=>Completion.zeros (n x) (p x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (p a)=>(x.2.val,x.1))
  exact vectorOfFn hn hp (constant (hn.comp hx.snd) (const _ _ false))
lemma packNet {a : ∀x,BooleanNetwork (n x) (p x)} {b : ∀x,BooleanNetwork (n x) (q x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hn : Emits ea unaryCode n) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.packNet (r x) (a x) (b x)):=
  (ha.pair hb).pair (zeros hn hr)
end ExactQuantumFactoring.NetworkEmission.NetEmits

namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {p q r : α→ℕ}
lemma appendPrepared {a : ∀x,List (Instruction (p x))} {f : ∀x,BooleanNetwork (p x) (q x)}
    (ha : OpsEmits ea a) (hf : NetworkEmission.NetEmits ea f) (hp : Emits ea unaryCode p)
    (h : ∀x,(f x).net.count≤r x) {b : ∀x,List (Instruction (q x))} (hb : OpsEmits ea b) :
    OpsEmits ea (fun x=>ExactQuantumFactoring.appendPrepared (a x) (f x) (h x) (b x)):=
  (ha.first q r).append (prepared hf hp h hb)
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CompletionEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {W t d q : α→ℕ}
lemma coinBits (hW : Emits ea unaryCode W) (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    Emits ea unaryCode (fun x=>Completion.coinBits (W x) (t x) (d x)):=
  (((hW.unaryAdd ht).unaryAdd (const _ _ 2)).unaryAdd ht).unaryAdd hd
lemma completionWidth (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    Emits ea unaryCode (fun x=>Completion.totalWidth (q x) (W x) (t x) (d x)):=
  ht.unaryAdd (hq.unaryAdd (hW.unaryAdd (coinBits hW ht hd)))
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {q W t d : α→ℕ}
lemma rareWires (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.rareWires (q x) (W x) (t x) (d x)):=
  selectSlice (completionWidth hq hW ht hd) ht (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma ordinaryWires (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.ordinaryWires (q x) (W x) (t x) (d x)):=
  selectSlice (completionWidth hq hW ht hd) hq ht.unaryNat _ (by intros;rfl)
lemma guessWires (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.guessWires (q x) (W x) (t x) (d x)):=
  selectSlice (completionWidth hq hW ht hd) hW (ht.unaryNat.natAdd hq.unaryNat) _ (by intros;simp only [Fin.val_natAdd,Fin.val_castAdd];omega)
lemma retentionWires (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.retentionWires (q x) (W x) (t x) (d x)):=
  selectSlice (completionWidth hq hW ht hd) (coinBits hW ht hd)
    ((ht.unaryNat.natAdd hq.unaryNat).natAdd hW.unaryNat) _ (by intros;simp only [Fin.val_natAdd];omega)
lemma rareNet (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.rareNet (q x) (W x) (t x) (d x)):=
  (rareWires hq hW ht hd).equalOn (wordConst (completionWidth hq hW ht hd) ht (const _ _ 0)) ht
lemma completionOutput {f : ∀x,BooleanNetwork (q x) (W x)}
    (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) (hf : NetEmits ea f) :
    NetEmits ea (fun x=>Completion.outputNet (f x) (t x) (d x)):=
  wordMux (rareNet hq hW ht hd) (guessWires hq hW ht hd) ((ordinaryWires hq hW ht hd).comp hf) hW
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CompletionPreparationEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k q W t d : α→ℕ}
lemma completionInitial {f : ∀x,BooleanNetwork (k x) (q x)}
    (hk : Emits ea unaryCode k) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) (hf : NetEmits ea f) :
    NetEmits ea (fun x=>Completion.initialNet (f x) (W x) (t x) (d x)):=
  (zeros hk ht).pair (hf.pair ((zeros hk hW).pair (zeros hk (coinBits hW ht hd))))
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q W t d : α→ℕ}
lemma completion {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    OpsEmits ea (fun x=>Completion.program (p x) (W x) (t x) (d x)):=
  parallel (hadamards ht (fun _=>le_rfl)) (parallel hp
    (parallel (hadamards hW (fun _=>le_rfl)) (hadamards (coinBits hW ht hd) (fun _=>le_rfl)) hW) hq) ht
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ListSamplerEmission.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.ListSamplerEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>ListSampler.work (n x)):=
  hn.unaryMul (((const _ _ 49).unaryMul hn).unaryAdd (const _ _ 8))
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>ListSampler.width (n x)):=
  (hn.unaryAdd hn).unaryAdd (hn.unaryAdd (work hn))
lemma mask (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>listMaskNet (n x)):=by
  apply vectorOfFn hn hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact wordLt (wordConst hN hN ((const _ Nat.bits 2).natPow hx.fst)) (identity hN) hN

def maskOp (n i : ℕ) : Op:=⟨⟨.hadamard,false,true⟩,[i,n+i]⟩
lemma erase_maskGate (n : ℕ) (i : Fin n) : eraseOp (maskGate n i)=maskOp n i.val:=rfl
lemma erase_maskedPrefix (n k : ℕ) (h : k≤n) :
    (maskedPrefix n k h).map eraseOp=(List.range k).map (maskOp n):=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [maskedPrefix,List.map_append,ih,List.range_succ,List.map_append];rfl
noncomputable def maskOpP : Procedure (prodCode Nat.bits Nat.bits) opCode (fun x=>maskOp x.1 x.2):=by
  let he:=BitStackProgram.Emits.id (prodCode Nat.bits Nat.bits)
  have hwire:=he.snd.listCons ((he.fst.natAdd he.snd).listCons (const _ _ []))
  exact Classical.choice ((ofProcedure CircuitEmission.Emission.opPackP).comp ((const _ _ (⟨.hadamard,false,true⟩ : Gate)).pair hwire))
lemma masked (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>maskedPrefix (n x) (n x) le_rfl):=by
  have h:=(ofProcedure (Procedure.listMapWith (f:=maskOp) 0 (maskOp 0 0) maskOpP)).comp (hn.unaryNat.pair hn.range)
  exact h.congr (fun _=>(erase_maskedPrefix _ _ _).symm)
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>ListSampler.circuit (n x)):=by
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (OpsEmits.oracleOn (mask hn) (fun x=>(listMaskNet_count (n x)).trans (Nat.le_add_left _ _))).append
    (OpsEmits.place (masked hn) (fun x=>ListSampler.maskRegister (n x)) (fun x i=>n x+i)
      (fun _ _=>ListSampler.maskRegister_val _ _) ((hn.comp hx.fst).unaryNat.natAdd hx.snd))
lemma singleZero (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.singleZeroNet (n x)):=by
  let p : α→ℕ→Pack:=fun x i=>if i<n x then bitPack (n x) i else constantPack (n x) false
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hN:=hn.comp hx.snd
  have hi:=hx.fst.unaryNat
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1):=by
    exact ((hi.natLt hN.unaryNat).ite
      ((ofProcedure NetworkEmission.Emission.bitPackP).comp (hN.pair hi))
      ((ofProcedure NetworkEmission.Emission.constantPackP).comp (hN.pair (const _ _ false)))).congr
      (by intro x;simp only [p,decide_eq_true_eq])
  apply vectorIndexed hn (width hn) p hp
  intro x i
  dsimp only [p]
  split
  · rename_i hi
    exact bitPack_value (⟨i.val,hi⟩ : Fin (n x))
  · exact constantPack_value _ _
end ExactQuantumFactoring.ListSamplerEmission

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalListEmission.lean =====
namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma transitionWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>Completion.transitionWidth (n x)):=
  hn.unaryMul ((hn.unaryPow 5).unaryAdd (const _ _ 1))
lemma sampleExponent (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.sampleExponent (n x)):=by
  have h:=(const _ unaryCode 16).unaryMul hn
  exact (h.unaryNat.natSub (const _ _ 2)).boundedUnary h (fun _=>Nat.sub_le _ _)
lemma retentionBits (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderTrial.retentionBits (n x)):=
  ((const _ _ 80).unaryMul hn).unaryAdd (const _ _ 20)
end ExactQuantumFactoring.BitStackProgram.Emits
namespace ExactQuantumFactoring.PhysicalListEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma ordinaryWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.ordinaryWidth (n x)):=
  (ListSamplerEmission.width hn).tensorWidth (hn.unaryPow 5)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.width (n x)):=
  completionWidth (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalListSlots.program (n x)):=
  OpsEmits.completion (OpsEmits.tensor (ListSamplerEmission.program hn) (ListSamplerEmission.width hn) (hn.unaryPow 5))
    (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.initialNet (n x)):=by
  apply completionInitial hn (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
  apply tensor hn (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact ListSamplerEmission.singleZero (hn.comp hx.snd)
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.work (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (work hn)
lemma launch (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalListSlots.launch (n x)):=
  OpsEmits.prepared (initial hn) hn (fun _=>le_rfl) (program hn)
end ExactQuantumFactoring.PhysicalListEmission

end



end OAI
