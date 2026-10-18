/-
Exact quantum factoring development (port of OpenAI's formalization), part 24 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: PolySchemaPoly.lean, TrialExpressionResources.lean, StaticMajorantResources.lean, RetentionExpressionResources.lean, NetworkPolyResources.lean, NetworkPoly.lean, PolyAt.lean, NetworkAt.lean, ExpressionAt.lean, NetworkAtArithmetic.lean, RecoveryPolynomial.lean, PreparationPolynomial.lean, TrialNetworkPolynomial.lean, RawDecoderPolynomial.lean, OrderDecoderPolynomial.lean, NodeControlBounds.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part23

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PolySchemaPoly.lean =====
namespace OAI

section
namespace ExactQuantumFactoring

namespace PolySchemaPoly
variable {v : ℕ → Type*} {a b : ∀ n, PolyExpr (v n)}
lemma coeffs (ha : PolySchemaPoly a) : PolyExprPoly a := by
  simpa only [PolyExpr.comp_X] using ha (fun _=>PolyExpr.X) PolyExprPoly.X
lemma C {r : ∀ n, RatExpr (v n)} (hr : RatExprPoly r) : PolySchemaPoly (fun n => .C (r n)) :=
  fun _ _ => PolyExprPoly.C hr
lemma X : PolySchemaPoly (fun _ => PolyExpr.X : ∀ n, PolyExpr (v n)) := fun _ hb => hb
lemma constant (r : ℚ) : PolySchemaPoly (fun _ => PolyExpr.const r : ∀ n, PolyExpr (v n)) :=
  C (RatExprPoly.constant r)
lemma add (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).add (b n)) := fun c hc => (ha c hc).add (hb c hc)
lemma negation (ha : PolySchemaPoly a) : PolySchemaPoly (fun n => (a n).negation) :=
  fun c hc => (ha c hc).negation
lemma sub (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).sub (b n)) := ha.add hb.negation
lemma mul (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).mul (b n)) := fun c hc => (ha c hc).mul (hb c hc)
lemma pow (ha : PolySchemaPoly a) (k : ℕ) : PolySchemaPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
lemma comp (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).comp (b n)) := by
  intro c hc
  simpa only [PolyExpr.comp_comp] using ha (fun n => (b n).comp (c n)) (hb c hc)
end PolySchemaPoly

syntax "schema_poly" : tactic
macro_rules
  | `(tactic| schema_poly) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact PolySchemaPoly.X
    | exact PolySchemaPoly.constant _
    | (apply PolySchemaPoly.C; expr_poly)
    | (apply PolySchemaPoly.add <;> schema_poly)
    | (apply PolySchemaPoly.sub <;> schema_poly)
    | (apply PolySchemaPoly.mul <;> schema_poly)
    | (apply PolySchemaPoly.negation; schema_poly)
    | (apply PolySchemaPoly.pow; schema_poly)
    | (apply PolySchemaPoly.comp <;> schema_poly))

namespace OrderTrial.Expressions
variable {v : ℕ → Type*} {d Q B j u : ∀ n, NatExpr (v n)}
  {η : ∀ n, RatExpr (v n)} {q q₀ q₁ : ∀ n, IntExpr (v n)}
lemma dynamicRamp_poly (hq : IntExprPoly q) (a : ℤ) :
    PolySchemaPoly (fun n => dynamicRamp (q n) a) := by
  have ha : IntExprPoly (fun _=>IntExpr.ofInt a : ∀ n, IntExpr (v n)) :=
    IntExprPoly.ofInt (PolyBound.const _)
  unfold dynamicRamp
  schema_poly
lemma dynamicRampLin_poly (hq : IntExprPoly q) (a : ℤ) :
    PolySchemaPoly (fun n => dynamicRampLin (q n) a) := by
  have ha : IntExprPoly (fun _=>IntExpr.ofInt a : ∀ n, IntExpr (v n)) :=
    IntExprPoly.ofInt (PolyBound.const _)
  unfold dynamicRampLin
  schema_poly
lemma dynamicSplineRe_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicSplineRe (q n)) := by
  have h0 := dynamicRamp_poly hq 0
  have h2 := dynamicRamp_poly hq 2
  have h4 := dynamicRamp_poly hq 4
  unfold dynamicSplineRe
  schema_poly
lemma dynamicSplineIm_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicSplineIm (q n)) := by
  have h0 := dynamicRamp_poly hq (-1)
  have h2 := dynamicRamp_poly hq 1
  have h4 := dynamicRamp_poly hq 3
  have h5 := dynamicRamp_poly hq 5
  unfold dynamicSplineIm
  schema_poly
lemma dynamicPhaseRe_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicPhaseRe (q n)) := by
  have h0 := dynamicRampLin_poly hq 0
  have h2 := dynamicRampLin_poly hq 2
  have h4 := dynamicRampLin_poly hq 4
  unfold dynamicPhaseRe
  schema_poly
lemma dynamicPhaseIm_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicPhaseIm (q n)) := by
  have h0 := dynamicRampLin_poly hq (-1)
  have h2 := dynamicRampLin_poly hq 1
  have h4 := dynamicRampLin_poly hq 3
  have h5 := dynamicRampLin_poly hq 5
  unfold dynamicPhaseIm
  schema_poly
lemma linearPoly_poly (hd : NatExprPoly d) (hη : RatExprPoly η) :
    PolySchemaPoly (fun n => linearPoly (d n) (η n)) := by
  unfold linearPoly
  schema_poly
lemma integralZero_poly {A : ∀ n, PolyExpr (v n)} (hd : NatExprPoly d) (hA : PolySchemaPoly A) :
    PolySchemaPoly (fun n => integralZero (d n) (A n)) := by
  have hlin := linearPoly_poly hd (RatExprPoly.constant 0)
  unfold integralZero
  schema_poly
lemma integralSlope_poly {A C : ∀ n, PolyExpr (v n)} (hd : NatExprPoly d)
    (hη : RatExprPoly η) (hA : PolySchemaPoly A) (hC : PolySchemaPoly C) :
    PolySchemaPoly (fun n => integralSlope (d n) (η n) (A n) (C n)) := by
  have hlin := linearPoly_poly hd hη
  have hzero := linearPoly_poly hd (RatExprPoly.constant 0)
  unfold integralSlope
  schema_poly
lemma dynamicMassZero_poly (hd : NatExprPoly d) (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicMassZero (d n) (q n)) :=
  ((integralZero_poly hd (dynamicPhaseRe_poly hq)).pow 2).add
    ((integralZero_poly hd (dynamicPhaseIm_poly hq)).pow 2)
lemma dynamicMassSlope_poly (hd : NatExprPoly d) (hη : RatExprPoly η)
    (hq0 : IntExprPoly q₀) (hq1 : IntExprPoly q₁) :
    PolySchemaPoly (fun n => dynamicMassSlope (d n) (η n) (q₀ n) (q₁ n)) :=
  ((integralSlope_poly hd hη (dynamicSplineRe_poly hq0) (dynamicSplineRe_poly hq1)).pow 2).add
    ((integralSlope_poly hd hη (dynamicSplineIm_poly hq0) (dynamicSplineIm_poly hq1)).pow 2)
lemma dynamicMassCoeff_poly (hd : NatExprPoly d) (hη : RatExprPoly η)
    (hq0 : IntExprPoly q₀) (hq1 : IntExprPoly q₁) (k : ℕ) :
    RatExprPoly (fun n => dynamicMassCoeff (d n) (η n) (q₀ n) (q₁ n) k) :=
  hη.ifEq (RatExprPoly.constant 0) ((dynamicMassZero_poly hd hq0).coeffs k)
    ((dynamicMassSlope_poly hd hη hq0 hq1).coeffs k)
end OrderTrial.Expressions
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TrialExpressionResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
namespace NatExprPoly
variable {v : ℕ → Type*} {a b : ∀ n, NatExpr (v n)}
lemma min (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => (a n).min (b n)) := ha.iteLe hb ha hb
lemma max (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => (a n).max (b n)) := ha.iteLe hb hb ha
end NatExprPoly
namespace RatExprPoly
lemma sumList {v : ℕ → Type*} {α : Type*} {f : α → ∀ n, RatExpr (v n)}
    (hf : ∀ i, RatExprPoly (f i)) (xs : List α) :
    RatExprPoly (fun n => RatExpr.sumList (fun i => f i n) xs) := by
  induction xs with
  | nil => exact constant 0
  | cons i xs ih => exact (hf i).add ih
end RatExprPoly

namespace OrderTrial.Expressions
variable {v : ℕ → Type*} {a b η : ∀ n, RatExpr (v n)}
  {Q B d j t u lo hi : ∀ n, NatExpr (v n)}
lemma powerSum_poly (ha : RatExprPoly a) (q : ℕ) :
    RatExprPoly (fun n => powerSum q (a n)) := by
  rcases q with _|_|_|_|_|q <;> simp only [powerSum] <;> expr_poly
lemma fiveTerm_poly {f : ℕ → ∀ n, RatExpr (v n)} (hf : ∀ i, RatExprPoly (f i))
    (hl : NatExprPoly lo) (hh : NatExprPoly hi) :
    RatExprPoly (fun n => fiveTerm (fun i => f i n) (lo n) (hi n)) := by
  exact RatExprPoly.ifNatLe hl hh (RatExprPoly.sum (fun i => (hf i).mul
    ((powerSum_poly (RatExprPoly.ofNat hh) i).sub (powerSum_poly (RatExprPoly.ofNat hl) i))) 5) (RatExprPoly.constant 0)
lemma linear_poly (ha : RatExprPoly a) (hb : RatExprPoly b)
    (hl : NatExprPoly lo) (hh : NatExprPoly hi) :
    RatExprPoly (fun n => linear (a n) (b n) (lo n) (hi n)) := by
  apply fiveTerm_poly _ hl hh
  intro q
  exact RatExprPoly.ite (fun _=>q=0) ha
    (RatExprPoly.ite (fun _=>q=1) hb (RatExprPoly.constant 0))
lemma ramp_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => ramp (a n) (b n) (d n)) := by
  have hx := (ha.negation.div hb).ceilNat
  have h1 := linear_poly ha hb hx hd
  have h2 := linear_poly ha hb (NatExprPoly.constPoly (PolyBound.const 0)) (hd.min hx)
  unfold ramp
  expr_poly
lemma phaseRe_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => phaseRe (a n) (b n) (d n)) := by
  have h1 := linear_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb
    (NatExprPoly.constPoly (PolyBound.const 0)) hd
  have h2 := ramp_poly ha hb hd
  have h3 := ramp_poly (ha.sub ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb hd
  have h4 := ramp_poly (ha.sub (RatExprPoly.constant 1)) hb hd
  unfold phaseRe
  expr_poly
lemma phaseIm_poly (ha : RatExprPoly a) (hb : RatExprPoly b) (hd : NatExprPoly d) :
    RatExprPoly (fun n => phaseIm (a n) (b n) (d n)) := by
  have h1 := linear_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 2))) hb
    (NatExprPoly.constPoly (PolyBound.const 0)) hd
  have h2 := ramp_poly (ha.add ((RatExprPoly.constant 1).div (RatExprPoly.constant 4))) hb hd
  have h3 := ramp_poly (ha.sub ((RatExprPoly.constant 1).div (RatExprPoly.constant 4))) hb hd
  have h4 := ramp_poly (ha.sub ((RatExprPoly.constant 3).div (RatExprPoly.constant 4))) hb hd
  have h5 := ramp_poly (ha.sub ((RatExprPoly.constant 5).div (RatExprPoly.constant 4))) hb hd
  unfold phaseIm
  expr_poly
lemma binE_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    NatExprPoly (fun n => binE (Q n) (d n) (j n)) := by
  unfold binE
  expr_poly
lemma error_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n => error (Q n) (d n) (j n)) := by
  have h := binE_poly hQ hd hj
  unfold error
  expr_poly
lemma offset_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n => offset (Q n) (d n) (j n) (t n)) := by
  have h := error_poly hQ hd hj
  unfold offset
  expr_poly
lemma slope_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n => slope (Q n) (d n) (j n)) := by
  have h := error_poly hQ hd hj
  unfold slope
  expr_poly
lemma count_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (ht : NatExprPoly t) :
    NatExprPoly (fun n => count (Q n) (d n) (t n)) := by
  unfold count
  expr_poly
lemma probability_poly (hQ : NatExprPoly Q) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n => probability (Q n) (d n) (j n) (t n)) := by
  have ho := offset_poly hQ hd hj ht
  have hs := slope_poly hQ hd hj
  have hc := count_poly hQ hd ht
  have hr := phaseRe_poly ho hs hc
  have hi := phaseIm_poly ho hs hc
  unfold probability
  expr_poly
lemma rounded_poly (hd : NatExprPoly d) (ha : RatExprPoly a) :
    RatExprPoly (fun n => rounded (d n) (a n)) := by unfold rounded; expr_poly
lemma roundingDen_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) :
    NatExprPoly (fun n => roundingDen (Q n) (B n)) := hQ.mul (hB.pow (PolyBound.const 8))
lemma quarter_poly (ha : RatExprPoly a) : IntExprPoly (fun n => quarter (a n)) := by
  unfold quarter; expr_poly
lemma majorantE_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) (hu : NatExprPoly u) :
    RatExprPoly (fun n => majorantE (Q n) (B n) (d n) (j n) (u n)) := by
  have he := error_poly hQ hd hj
  have h0 := quarter_poly ((RatExprPoly.ofNat hu).div (RatExprPoly.ofNat hd))
  have h1 := quarter_poly (((RatExprPoly.ofNat hu).div (RatExprPoly.ofNat hd)).add he)
  have hs := RatExprPoly.sum (fun k =>
    (rounded_poly (roundingDen_poly hQ hB) (dynamicMassCoeff_poly hd he h0 h1 k)).mul
      ((RatExprPoly.ofNat hu).pow k)) 5
  unfold majorantE
  exact hs.add ((RatExprPoly.constant 64).div (RatExprPoly.ofNat hQ))
end OrderTrial.Expressions
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/StaticMajorantResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : ℕ → Type*} {d Q B j : ∀ n, NatExpr (v n)} {η : ∀ n, RatExpr (v n)}
lemma rampPoly_poly (q a : ℤ) :
    PolySchemaPoly (fun _ => rampPoly q a : ∀ n, PolyExpr (v n)) := by
  unfold rampPoly
  split <;> schema_poly
lemma rampLin_poly (q a : ℤ) :
    PolySchemaPoly (fun _ => rampLin q a : ∀ n, PolyExpr (v n)) := by
  unfold rampLin
  split <;> schema_poly
lemma splineRePoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => splineRePoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampPoly_poly (v:=v) q 0
  have h2 := rampPoly_poly (v:=v) q 2
  have h4 := rampPoly_poly (v:=v) q 4
  unfold splineRePoly
  schema_poly
lemma splineImPoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => splineImPoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampPoly_poly (v:=v) q (-1)
  have h2 := rampPoly_poly (v:=v) q 1
  have h4 := rampPoly_poly (v:=v) q 3
  have h5 := rampPoly_poly (v:=v) q 5
  unfold splineImPoly
  schema_poly
lemma phaseRePoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => phaseRePoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampLin_poly (v:=v) q 0
  have h2 := rampLin_poly (v:=v) q 2
  have h4 := rampLin_poly (v:=v) q 4
  unfold phaseRePoly
  schema_poly
lemma phaseImPoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => phaseImPoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampLin_poly (v:=v) q (-1)
  have h2 := rampLin_poly (v:=v) q 1
  have h4 := rampLin_poly (v:=v) q 3
  have h5 := rampLin_poly (v:=v) q 5
  unfold phaseImPoly
  schema_poly
lemma massZero_poly (hd : NatExprPoly d) (q : ℤ) :
    PolySchemaPoly (fun n => massZero (d n) q) :=
  ((integralZero_poly hd (phaseRePoly_poly q)).pow 2).add
    ((integralZero_poly hd (phaseImPoly_poly q)).pow 2)
lemma massSlope_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q₀ q₁ : ℤ) :
    PolySchemaPoly (fun n => massSlope (d n) (η n) q₀ q₁) :=
  ((integralSlope_poly hd hη (splineRePoly_poly q₀) (splineRePoly_poly q₁)).pow 2).add
    ((integralSlope_poly hd hη (splineImPoly_poly q₀) (splineImPoly_poly q₁)).pow 2)
lemma massCoeff_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q₀ q₁ : ℤ) (k : ℕ) :
    RatExprPoly (fun n => massCoeff (d n) (η n) q₀ q₁ k) :=
  hη.ifEq (RatExprPoly.constant 0) ((massZero_poly hd q₀).coeffs k)
    ((massSlope_poly hd hη q₀ q₁).coeffs k)
lemma low_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q : ℤ×ℤ) :
    NatExprPoly (fun n => low (d n) (η n) q) := by
  unfold low
  apply NatExprPoly.max <;> expr_poly
lemma high_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q : ℤ×ℤ) :
    NatExprPoly (fun n => high (d n) (η n) q) := by
  unfold high
  apply NatExprPoly.min hd
  apply NatExprPoly.min <;> expr_poly
lemma pieceSum_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) (q : ℤ×ℤ) :
    RatExprPoly (fun n => pieceSum (Q n) (B n) (d n) (j n) q) := by
  have he := error_poly hQ hd hj
  have hl := low_poly hd he q
  have hh := high_poly hd he q
  have hs := fiveTerm_poly
    (fun k => rounded_poly (roundingDen_poly hQ hB) (massCoeff_poly hd he q.1 q.2 k)) hl hh
  unfold pieceSum
  exact hs.add ((RatExprPoly.ofNat (hh.sub hl)).mul
    ((RatExprPoly.constant 64).div (RatExprPoly.ofNat hQ)))
lemma majorantSumE_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) :
    RatExprPoly (fun n => majorantSumE (Q n) (B n) (d n) (j n)) :=
  (RatExprPoly.sumList (fun q => pieceSum_poly hQ hB hd hj q) quarterList).div
    (RatExprPoly.constant 2)
end ExactQuantumFactoring.OrderTrial.Expressions

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetentionExpressionResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : ℕ→Type*} {d Q B j t : ∀ n,NatExpr (v n)} {f : ℕ→ℕ}
lemma lambdaE_poly (hf : PolyBound f) (hd : NatExprPoly d) :
    RatExprPoly (fun n=>lambdaE (f n) (d n)) := by
  have hh := coveringPow_poly hd hf
  unfold lambdaE
  expr_poly
lemma coefficientE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>coefficientE (f n) (Q n) (B n) (d n) (j n)) := by
  have hh := lambdaE_poly hf hd
  have hs := majorantSumE_poly hQ hB hd hj
  have hc : NatExprPoly (fun n=>NatExpr.const (2^(10*f n)) : ∀ n,NatExpr (v n)) :=
    NatExprPoly.const ((PolyBound.const 10).mul hf).twoPowSize
  unfold coefficientE
  expr_poly
lemma remainderE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>remainderE (f n) (Q n) (B n) (d n) (j n)) :=
  (lambdaE_poly hf hd).sub ((coefficientE_poly hf hQ hB hd hj).mul (majorantSumE_poly hQ hB hd hj))
lemma discrepancyE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) (ht : NatExprPoly t) :
    RatExprPoly (fun n=>discrepancyE (f n) (Q n) (B n) (d n) (j n) (t n)) := by
  have hm := majorantE_poly hQ hB hd hj ((hj.mul ht).mod hd)
  have hp := probability_poly hQ hd hj ht
  have hc := coefficientE_poly hf hQ hB hd hj
  unfold discrepancyE
  expr_poly
lemma thirdRetentionE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>thirdRetentionE (f n) (Q n) (B n) (d n) (j n)) := by
  have hr := remainderE_poly hf hQ hB hd hj
  unfold thirdRetentionE
  expr_poly
lemma firstE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>firstE (f n) (d n) (j n)) := by
  apply coefficientE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
lemma secondE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n=>secondE (f n) (d n) (j n) (t n)) := by
  apply discrepancyE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj ht
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
lemma lastE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>lastE (f n) (d n) (j n)) := by
  apply thirdRetentionE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
end ExactQuantumFactoring.OrderTrial.Expressions

namespace ExactQuantumFactoring
lemma thresholdExpr_poly {v : ℕ→Type*} {T : ℕ→ℕ} {p : ∀ n,RatExpr (v n)}
    {c : ∀ n,NatExpr (v n)} (hT : PolyBound T) (hp : RatExprPoly p) (hc : NatExprPoly c) :
    NatExprPoly (fun n=>thresholdExpr (T n) (p n) (c n)) := by
  have hh : NatExprPoly (fun n=>NatExpr.const (2^(T n)) : ∀ n,NatExpr (v n)) :=
    NatExprPoly.const hT.twoPowSize
  unfold thresholdExpr
  expr_poly
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkPolyResources.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork

def NetworkPoly {a b : ℕ→ℕ} (f : ∀ n,BooleanNetwork (a n) (b n)) : Prop :=
  PolyBound (fun n=>(f n).net.count)

def NetworkVarsPoly {v : ℕ→Type*} {a b : ℕ→ℕ}
    (f : ∀ n,v n→BooleanNetwork (a n) (b n)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n i,(f n i).net.count≤p.eval n


end ExactQuantumFactoring
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkPoly.lean =====
namespace OAI

section
namespace ExactQuantumFactoring
open BooleanNetwork

namespace NetworkPoly
variable {a b c : ℕ→ℕ}
lemma select (h : ∀ n,Fin (b n)→Fin (a n)) : NetworkPoly (fun n=>BooleanNetwork.select (h n)) := by
  simpa only [NetworkPoly,count_select] using PolyBound.const 0
lemma comp {f : ∀ n,BooleanNetwork (a n) (b n)} {g : ∀ n,BooleanNetwork (b n) (c n)}
    (hf : NetworkPoly f) (hg : NetworkPoly g) : NetworkPoly (fun n=>(f n).comp (g n)) := by
  simpa only [NetworkPoly,count_comp] using PolyBound.add hf hg
lemma pair {f : ∀ n,BooleanNetwork (a n) (b n)} {g : ∀ n,BooleanNetwork (a n) (c n)}
    (hf : NetworkPoly f) (hg : NetworkPoly g) : NetworkPoly (fun n=>(f n).pair (g n)) := by
  simpa only [NetworkPoly,count_pair] using PolyBound.add hf hg
lemma rewire {f : ∀ n,BooleanNetwork (a n) (b n)} (hf : NetworkPoly f)
    (h : ∀ n,Fin (c n)→Fin (b n)) : NetworkPoly (fun n=>(f n).rewire (h n)) := by
  simpa only [NetworkPoly,count_rewire] using hf
lemma constant (h : ℕ→Bool) : NetworkPoly (fun n=>BooleanNetwork.constant (n:=a n) (h n)) := by
  simpa only [NetworkPoly,count_constant] using PolyBound.const 1
lemma bnot {f : ∀ n,BooleanNetwork (a n) 1} (hf : NetworkPoly f) :
    NetworkPoly (fun n=>(f n).bnot) := by
  simpa only [NetworkPoly,count_bnot] using (PolyBound.add hf (PolyBound.const 1))
lemma band {f g : ∀ n,BooleanNetwork (a n) 1} (hf : NetworkPoly f) (hg : NetworkPoly g) :
    NetworkPoly (fun n=>(f n).band (g n)) := by
  simpa only [NetworkPoly,count_band] using ((PolyBound.add hf hg).add (PolyBound.const 1))
lemma bor {f g : ∀ n,BooleanNetwork (a n) 1} (hf : NetworkPoly f) (hg : NetworkPoly g) :
    NetworkPoly (fun n=>(f n).bor (g n)) := by
  simpa only [NetworkPoly,count_bor] using ((PolyBound.add hf hg).add (PolyBound.const 4))
lemma of_le {f : ∀ n,BooleanNetwork (a n) (b n)} {c : ℕ→ℕ} (hc : PolyBound c)
    (h : ∀ n,(f n).net.count≤c n) : NetworkPoly f := hc.of_le h
end NetworkPoly

namespace NatExprPoly
variable {v : ℕ→Type*} {e : ∀ n,NatExpr (v n)} {a b : ℕ→ℕ}
  {vars : ∀ n,v n→BooleanNetwork (a n) (b n)}
lemma sharedCost (he : NatExprPoly e) : PolyBound (fun n=>(e n).sharedCost) :=
  PolyBound.of_le he (fun n=>(e n).sharedCost_le_weight)
lemma operationBound {f : ℕ→ℕ} (hf : PolyBound f) :
    PolyBound (fun n=>NatExpr.operationBound (f n)) := by
  unfold NatExpr.operationBound
  poly_bound
lemma template (he : NatExprPoly e) (hb : PolyBound b) (hv : NetworkVarsPoly vars) :
    NetworkPoly (fun n=>(e n).template (vars n)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyBound (fun n=>p.eval n):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkPoly.of_le (he.sharedCost.mul (((operationBound hw).add hc).add hw))
  exact fun n=>(e n).template_shared_count (vars n) (hp n)
lemma isOne (he : NatExprPoly e) (hb : PolyBound b) (hv : NetworkVarsPoly vars) :
    NetworkPoly (fun n=>(e n).isOne (vars n)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyBound (fun n=>p.eval n):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkPoly.of_le
    (((he.sharedCost.mul (((operationBound hw).add hc).add hw)).add
      ((PolyBound.const 100).mul hw)).add (PolyBound.const 21))
  exact fun n=>(e n).isOne_shared_count (vars n) (hp n)
end NatExprPoly

lemma retentionNet_poly {v : ℕ→Type*} {a b T : ℕ→ℕ} {p : ∀ n,RatExpr (v n)}
    {c : ∀ n,NatExpr (v n)} {vars : ∀ n,v n→BooleanNetwork (a n) (b n)}
    (hT : PolyBound T) (hp : RatExprPoly p) (hc : NatExprPoly c) (hb : PolyBound b)
    (hv : NetworkVarsPoly vars) :
    NetworkPoly (fun n=>retentionNet (T n) (p n) (c n) (vars n)) :=
  (thresholdExpr_poly hT hp hc).isOne hb hv
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PolyAt.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
/-- Uniform polynomial bounds over arbitrary auxiliary parameters. Only the
chosen length is charged, so this also records worst-case bounds over all
finite loop indices and all networks satisfying a supplied count invariant. -/
def PolyAt {α : Sort*} (length : α→ℕ) (f : α→ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ a,f a≤p.eval (length a)
namespace PolyAt
variable {α : Sort*} {len f g : α→ℕ}
lemma const (len : α→ℕ) (c : ℕ) : PolyAt len (fun _=>c) :=
  ⟨Polynomial.C c,fun _=>by simp⟩
lemma self (len : α→ℕ) : PolyAt len len := ⟨Polynomial.X,fun _=>by simp⟩
lemma add (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a+g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p+q,fun a=>by simpa using Nat.add_le_add (hp a) (hq a)⟩
lemma mul (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a*g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p*q,fun a=>by simpa using Nat.mul_le_mul (hp a) (hq a)⟩
lemma pow (hf : PolyAt len f) (k : ℕ) : PolyAt len (fun a=>f a^k) := by
  obtain ⟨p,hp⟩:=hf
  exact ⟨p^k,fun a=>by simpa using Nat.pow_le_pow_left (hp a) k⟩
lemma of_le (hg : PolyAt len g) (h : ∀a,f a≤g a) : PolyAt len f := by
  obtain ⟨p,hp⟩:=hg
  exact ⟨p,fun a=>(h a).trans (hp a)⟩
lemma sub (hf : PolyAt len f) : PolyAt len (fun a=>f a-g a) := hf.of_le fun _=>Nat.sub_le _ _
lemma div (hf : PolyAt len f) : PolyAt len (fun a=>f a/g a) := hf.of_le fun _=>Nat.div_le_self _ _
lemma mod (hf : PolyAt len f) : PolyAt len (fun a=>f a%g a) := hf.of_le fun _=>Nat.mod_le _ _
lemma max (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>max (f a) (g a)) :=
  (hf.add hg).of_le fun _=>Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩
lemma ite (p : α→Prop) [∀a,Decidable (p a)] (hf : PolyAt len f) (hg : PolyAt len g) :
    PolyAt len (fun a=>if p a then f a else g a) :=
  (hf.max hg).of_le fun a=>by split_ifs <;> omega
lemma pull {β : Sort*} (hf : PolyAt len f) (g : β→α) :
    PolyAt (fun b=>len (g b)) (fun b=>f (g b)) := by
  obtain ⟨p,hp⟩:=hf; exact ⟨p,fun b=>hp (g b)⟩
lemma ofPoly {f : ℕ→ℕ} (hf : PolyBound f) (len : α→ℕ) :
    PolyAt len (fun a=>f (len a)) := PolyAt.pull hf len
lemma comp {h : ℕ→ℕ} (hh : PolyBound h) (hf : PolyAt len f) :
    PolyAt len (fun a=>h (f a)) := by
  obtain ⟨p,hp⟩:=hh; obtain ⟨q,hq⟩:=hf
  refine ⟨p.comp q,fun a=>?_⟩
  simpa only [Polynomial.eval_comp] using
    (hp (f a)).trans (PolyBound.eval_mono p (hq a))
lemma natSize (hf : PolyAt len f) : PolyAt len (fun a=>(f a).size) :=
  hf.of_le fun _=>Nat.size_le.mpr Nat.lt_two_pow_self
end PolyAt

syntax "poly_at" : tactic
macro_rules
  | `(tactic| poly_at) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact PolyAt.self _
    | exact PolyAt.const _ _
    | (apply PolyAt.add <;> poly_at)
    | (apply PolyAt.mul <;> poly_at)
    | (apply PolyAt.pow <;> poly_at)
    | (apply PolyAt.max <;> poly_at)
    | (apply PolyAt.sub <;> poly_at)
    | (apply PolyAt.div <;> poly_at)
    | (apply PolyAt.mod <;> poly_at)
    | (apply PolyAt.natSize <;> poly_at))
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkAt.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

def NetworkAt {α : Type*} (len : α→ℕ) {a b : α→ℕ}
    (f : ∀x,BooleanNetwork (a x) (b x)) : Prop := PolyAt len (fun x=>(f x).net.count)
namespace NetworkAt
variable {α : Type*} {len a b c : α→ℕ}
lemma select (h : ∀x,Fin (b x)→Fin (a x)) : NetworkAt len (fun x=>BooleanNetwork.select (h x)) := by
  simpa only [NetworkAt,count_select] using PolyAt.const len 0
lemma comp {f : ∀x,BooleanNetwork (a x) (b x)} {g : ∀x,BooleanNetwork (b x) (c x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) : NetworkAt len (fun x=>(f x).comp (g x)) := by
  simpa only [NetworkAt,count_comp] using PolyAt.add hf hg
lemma pair {f : ∀x,BooleanNetwork (a x) (b x)} {g : ∀x,BooleanNetwork (a x) (c x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) : NetworkAt len (fun x=>(f x).pair (g x)) := by
  simpa only [NetworkAt,count_pair] using PolyAt.add hf hg
lemma rewire {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (h : ∀x,Fin (c x)→Fin (b x)) : NetworkAt len (fun x=>(f x).rewire (h x)) := by
  simpa only [NetworkAt,count_rewire] using hf
lemma constant (h : α→Bool) : NetworkAt len (fun x=>BooleanNetwork.constant (n:=a x) (h x)) := by
  simpa only [NetworkAt,count_constant] using PolyAt.const len 1
lemma of_le {f : ∀x,BooleanNetwork (a x) (b x)} {bound : α→ℕ} (hb : PolyAt len bound)
    (h : ∀x,(f x).net.count≤bound x) : NetworkAt len f := hb.of_le h
lemma bnot {f : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) :
    NetworkAt len (fun x=>(f x).bnot) := by
  simpa only [NetworkAt,count_bnot] using PolyAt.add hf (PolyAt.const len 1)
lemma band {f g : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>(f x).band (g x)) := by
  simpa only [NetworkAt,count_band] using (PolyAt.add hf hg).add (PolyAt.const len 1)
lemma bor {f g : ∀x,BooleanNetwork (a x) 1} (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>(f x).bor (g x)) := by
  simpa only [NetworkAt,count_bor] using (PolyAt.add hf hg).add (PolyAt.const len 4)
lemma wordConstant (v : ∀x,BitVec (b x)) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordConstant (n:=a x) (v x)) := by
  simpa only [NetworkAt,wordConstant_count] using hb
lemma zeroWord {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.zeroWord (f x)) :=
  of_le ((PolyAt.add hf ((PolyAt.const len 97).mul hb)).add (PolyAt.const len 21))
    fun x=>zeroWord_count (f x)
lemma equalOn {f g : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (hg : NetworkAt len g) (hb : PolyAt len b) : NetworkAt len (fun x=>BitArithmetic.equalOn (f x) (g x)) :=
  of_le (((PolyAt.add hf hg).add ((PolyAt.const len 96).mul hb)).add (PolyAt.const len 21))
    fun x=>equalOn_count (f x) (g x)
lemma resizeWord (ha : PolyAt len a) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.resizeWord (a x) (b x)) := by
  apply of_le (PolyAt.add ha hb)
  intro x
  have h:=BitArithmetic.resizeWord_count (a x) (b x)
  omega
lemma all {ls : ∀x,List (BooleanNetwork (a x) 1)} (hl : PolyAt len (fun x=>(ls x).length))
    (h : ∃p : Polynomial ℕ,∀ x f, f∈ls x → f.net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>BooleanNetwork.all (ls x)) := by
  obtain ⟨p,hp⟩:=h
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  exact of_le ((hl.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
    fun x=>all_count (ls x) (hp x)
lemma all_ofFn {k : α→ℕ} {f : ∀x,Fin (k x)→BooleanNetwork (a x) 1} (hk : PolyAt len k)
    (hf : NetworkAt (fun xi : Σx,Fin (k x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>BooleanNetwork.all (List.ofFn (f x))) := by
  obtain ⟨p,hp⟩:=hf
  apply all (by simpa only [List.length_ofFn] using hk)
  refine ⟨p,?_⟩
  intro x g hg
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hg
  exact hp ⟨x,i⟩
lemma pull {β : Type*} {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (g : β→α) :
    NetworkAt (fun y=>len (g y)) (fun y=>f (g y)) := PolyAt.pull hf g
lemma ofPoly {a b : ℕ→ℕ} {f : ∀n,BooleanNetwork (a n) (b n)} (hf : NetworkPoly f)
    (len : α→ℕ) : NetworkAt len (fun x=>f (len x)) := PolyAt.ofPoly hf len
end NetworkAt
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionAt.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork

def NatExprAt {α : Type*} (len : α→ℕ) {v : α→Type*} (e : ∀x,NatExpr (v x)) :=
  PolyAt len (fun x=>(e x).weight)
namespace NatExprAt
variable {α : Type*} {len a b : α→ℕ} {v : α→Type*} {e : ∀x,NatExpr (v x)}
lemma ofPoly {v : ℕ→Type*} {e : ∀n,NatExpr (v n)} (he : NatExprPoly e) (len : α→ℕ) :
    NatExprAt len (fun x=>e (len x)) := PolyAt.ofPoly he len
lemma pull {β : Type*} (he : NatExprAt len e) (g : β→α) :
    NatExprAt (fun x=>len (g x)) (fun x=>e (g x)) := PolyAt.pull he g
lemma sharedCost (he : NatExprAt len e) : PolyAt len (fun x=>(e x).sharedCost) :=
  PolyAt.of_le he fun x=>(e x).sharedCost_le_weight
lemma templateWidth (he : NatExprAt len e) (hb : PolyAt len b) :
    PolyAt len (fun x=>(e x).templateWidth (b x)) :=
  PolyAt.of_le (((hb.add he).add (PolyAt.const len 1)).mul he)
    fun x=>(e x).templateWidth_le (b x)
lemma operationBound {f : α→ℕ} (hf : PolyAt len f) :
    PolyAt len (fun x=>NatExpr.operationBound (f x)) := by
  unfold NatExpr.operationBound
  poly_at
lemma template {vars : ∀x,v x→BooleanNetwork (a x) (b x)}
    (he : NatExprAt len e) (hb : PolyAt len b)
    (hv : ∃p : Polynomial ℕ,∀x i,(vars x i).net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>(e x).template (vars x)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkAt.of_le (he.sharedCost.mul (((operationBound hw).add hc).add hw))
  exact fun x=>(e x).template_shared_count (vars x) (hp x)
lemma isOne {vars : ∀x,v x→BooleanNetwork (a x) (b x)}
    (he : NatExprAt len e) (hb : PolyAt len b)
    (hv : ∃p : Polynomial ℕ,∀x i,(vars x i).net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>(e x).isOne (vars x)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkAt.of_le
    (((he.sharedCost.mul (((operationBound hw).add hc).add hw)).add
      ((PolyAt.const len 100).mul hw)).add (PolyAt.const len 21))
  exact fun x=>(e x).isOne_shared_count (vars x) (hp x)
end NatExprAt
end ExactQuantumFactoring

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NetworkAtArithmetic.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b c d : α→ℕ}
lemma wordMux {s : ∀x,BooleanNetwork (a x) 1} {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hs : NetworkAt len s) (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordMux (s x) (f x) (g x)) := by
  simpa only [NetworkAt,wordMux_count] using ((hs.add hf).add hg).add ((PolyAt.const len 7).mul hb)
lemma wordLt {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordLt (f x) (g x)) :=
  of_le (((hf.add hg).add ((PolyAt.const len 48).mul hb)).add (PolyAt.const len 8))
    fun x=>wordLt_count (f x) (g x)
lemma wordLe {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hf : NetworkAt len f) (hg : NetworkAt len g) (hb : PolyAt len b) :
    NetworkAt len (fun x=>BitArithmetic.wordLe (f x) (g x)) := (hg.wordLt hf hb).bnot
lemma toWidth {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f)
    (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>OrderTrial.toWidth (c x) (f x)) :=
  hf.comp (resizeWord hb hc)
lemma modularPower (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.modularPower (b x) (c x)) := by
  apply of_le (bound:=fun x=>b x+c x*(3672*b x*b x+436*b x+36))
  · exact hb.add (hc.mul (((PolyAt.const len 3672).mul hb |>.mul hb).add
      ((PolyAt.const len 436).mul hb) |>.add (PolyAt.const len 36)))
  · exact fun x=>modularPower_count (b x) (c x)
lemma gcdNet (hb : PolyAt len b) : NetworkAt len (fun x=>BitArithmetic.gcdNet (b x)) := by
  apply of_le (bound:=fun x=>2*b x*(216*b x*b x+300*b x+100))
  · exact ((PolyAt.const len 2).mul hb).mul
      ((((PolyAt.const len 216).mul hb).mul hb).add ((PolyAt.const len 300).mul hb) |>.add
        (PolyAt.const len 100))
  · exact fun x=>gcdNet_count (b x)
lemma convergentNet (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.convergentNet (b x) (c x)) := by
  apply of_le (bound:=fun x=>(c x+1)*(600*b x*b x+600*b x+120))
  · exact (hc.add (PolyAt.const len 1)).mul
      ((((PolyAt.const len 600).mul hb).mul hb).add ((PolyAt.const len 600).mul hb) |>.add
        (PolyAt.const len 120))
  · exact fun x=>convergentNet_count (b x) (c x)
lemma pairChoice (hb : PolyAt len b) : NetworkAt len (fun x=>OrderTrial.pairChoice (b x)) := by
  apply of_le (bound:=fun x=>120*b x+31)
  · poly_at
  · exact fun x=>OrderTrial.pairChoice_count (b x)
lemma boundedRootNet (hb : PolyAt len b) (hc : PolyAt len c) :
    NetworkAt len (fun x=>BitArithmetic.boundedRootNet (b x) (c x)) := by
  have hr : PolyAt len (fun x=>rootWidth (b x)) := by
    unfold rootWidth; poly_at
  apply of_le (bound:=fun x=>rootWidth (b x)+b x*(230*rootWidth (b x)+21+
      c x*(90*rootWidth (b x)*rootWidth (b x)+14*rootWidth (b x)+6)))
  · exact hr.add (hb.mul (((PolyAt.const len 230).mul hr |>.add (PolyAt.const len 21)).add
      (hc.mul ((((PolyAt.const len 90).mul hr).mul hr).add ((PolyAt.const len 14).mul hr) |>.add
        (PolyAt.const len 6)))))
  · exact fun x=>boundedRootNet_count (b x) (c x)
end NetworkAt
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RecoveryPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b : α→ℕ}
lemma varsFin {ι : Type*} [Fintype ι] {v : ∀x,ι→BooleanNetwork (a x) (b x)}
    (h : ∀i,NetworkAt len (fun x=>v x i)) :
    ∃p : Polynomial ℕ,∀x i,(v x i).net.count≤p.eval (len x) := by
  classical
  change ∀i,∃p : Polynomial ℕ,∀x,(v x i).net.count≤p.eval (len x) at h
  choose p hp using h
  refine ⟨∑i,p i,fun x i=>?_⟩
  rw [Polynomial.eval_finsetSum]
  exact (hp i x).trans (Finset.single_le_sum (f:=fun j=>(p j).eval (len x)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i))
end NetworkAt
namespace OrderTrial
variable {α : Type*} {len a w steps : α→ℕ}
lemma checkedConvergent_poly {Q B k : ∀x,BooleanNetwork (a x) (w x)}
    (hQ : NetworkAt len Q) (hB : NetworkAt len B) (hk : NetworkAt len k)
    (hw : PolyAt len w) (hi : PolyAt len steps) :
    NetworkAt len (fun x=>checkedConvergent (steps x) (Q x) (B x) (k x)) := by
  let cv := fun x=>(k x |>.pair (Q x)).comp (convergentNet (w x) (steps x))
  have hcv : NetworkAt len cv := (hk.pair hQ).comp (NetworkAt.convergentNet hw hi)
  have hd : NetworkAt len (fun x=>(cv x).comp (rootGuess (w x))) :=
    hcv.comp (NetworkAt.select _)
  have hj : NetworkAt len (fun x=>(cv x).comp (rootModulus (w x))) :=
    hcv.comp (NetworkAt.select _)
  have hv : ∃p : Polynomial ℕ,∀x i,
      (![Q x,B x,k x,(cv x).comp (rootGuess (w x)),(cv x).comp (rootModulus (w x))] i).net.count
        ≤p.eval (len x) := by
    apply NetworkAt.varsFin
    intro i; fin_cases i
    · exact hQ
    · exact hB
    · exact hk
    · exact hd
    · exact hj
  have he : NatExprAt len (fun _ : α=>binCheckExpr) := PolyAt.const len binCheckExpr.weight
  have hp := he.isOne hw hv
  have hz := NetworkAt.wordConstant (a:=a) (fun x=>BitVec.ofNat (w x) 0) hw
  exact (hp.wordMux hd hz hw).pair (hp.wordMux hj hz hw)

lemma recoveryNet_count_of_bound {n w K c : ℕ} (Q B k : BooleanNetwork n w)
    (hc : ∀i,i<K → (checkedConvergent i Q B k).net.count≤c) :
    (recoveryNet Q B k K).net.count≤2*w+K*(c+120*w+31) := by
  induction K with
  | zero => simp only [recoveryNet,count_pair,wordConstant_count,zero_mul,add_zero];omega
  | succ K ih =>
    have hh := ih (fun i hi=>hc i (by omega))
    have hi := hc K (by omega)
    have hp := pairChoice_count w
    simp only [recoveryNet,count_pair,count_comp]
    nlinarith

lemma recoveryNet_poly {Q B k : ∀x,BooleanNetwork (a x) (w x)}
    (hQ : NetworkAt len Q) (hB : NetworkAt len B) (hk : NetworkAt len k)
    (hw : PolyAt len w) (hsteps : PolyAt len steps) :
    NetworkAt len (fun x=>recoveryNet (Q x) (B x) (k x) (steps x)) := by
  let index : Type _ := Σx:α,Fin (steps x)
  let param : index→α := Sigma.fst
  have hi : PolyAt (fun z:index=>len z.1) (fun z=>z.2.val) :=
    (hsteps.pull param).of_le fun z=>z.2.isLt.le
  have hh:=checkedConvergent_poly (hQ.pull param) (hB.pull param) (hk.pull param)
    (hw.pull param) hi
  obtain ⟨p,hp⟩:=hh
  have hpoly : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le (bound:=fun x=>2*w x+steps x*(p.eval (len x)+120*w x+31))
  · exact ((PolyAt.const len 2).mul hw).add
      (hsteps.mul ((hpoly.add ((PolyAt.const len 120).mul hw)).add (PolyAt.const len 31)))
  · intro x
    exact recoveryNet_count_of_bound (Q x) (B x) (k x) (fun i hi=>hp ⟨x,⟨i,hi⟩⟩)
end OrderTrial
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PreparationPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
syntax "poly_fast" : tactic
macro_rules
  | `(tactic| poly_fast) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact PolyBound.id
    | exact PolyBound.const _
    | (apply PolyBound.add <;> poly_fast)
    | (apply PolyBound.mul <;> poly_fast)
    | (apply PolyBound.pow <;> poly_fast)
    | (apply PolyBound.max <;> poly_fast)
    | (apply PolyBound.sub <;> poly_fast)
    | (apply PolyBound.div <;> poly_fast)
    | (apply PolyBound.mod <;> poly_fast)
    | (apply PolyBound.natSize <;> poly_fast))
namespace PreparationPolynomial

lemma sampleExponent : PolyBound OrderSlots.sampleExponent := by
  unfold OrderSlots.sampleExponent; poly_fast
lemma retentionBits : PolyBound OrderTrial.retentionBits := by
  unfold OrderTrial.retentionBits; poly_fast
lemma transitionWidth : PolyBound Completion.transitionWidth := by
  unfold Completion.transitionWidth; poly_fast
lemma samplerWork : PolyBound ListSampler.work := by
  unfold ListSampler.work; poly_fast
lemma samplerWidth : PolyBound ListSampler.width := by
  change PolyBound (fun n=>n+n+(n+ListSampler.work n))
  have := samplerWork; poly_fast
lemma sampleScratch : PolyBound (fun n=>OrderSample.scratch n (OrderSlots.sampleExponent n+2)) := by
  unfold OrderSample.scratch
  have := sampleExponent; poly_fast
lemma sampleWidth : PolyBound (fun n=>OrderSample.width n (OrderSlots.sampleExponent n+2)) := by
  unfold OrderSample.width OrderSample.inputWidth
  have := sampleExponent; have := sampleScratch; poly_fast
lemma rawWidth : PolyBound (fun n=>OrderTrial.rawWidth n (OrderSlots.sampleExponent n) n) := by
  unfold OrderTrial.rawWidth OrderTrial.guessWidth
  have := sampleWidth; have := retentionBits; poly_fast
lemma listCoin : PolyBound (fun n=>Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)) := by
  unfold Completion.coinBits
  have := transitionWidth; poly_fast
lemma orderCoin : PolyBound OrderSlots.coinWidth := by
  unfold OrderSlots.coinWidth Completion.coinBits
  have := transitionWidth; poly_fast
lemma listWidth : PolyBound PhysicalListSlots.width := by
  unfold PhysicalListSlots.width PhysicalListSlots.ordinaryWidth
  simp only [tensorWidth_eq]
  have := samplerWidth; have := transitionWidth; have := listCoin; poly_fast
lemma orderWidth : PolyBound OrderSlots.width := by
  unfold OrderSlots.width OrderSlots.ordinaryWidth
  simp only [tensorWidth_eq]
  have := rawWidth; have := transitionWidth; have := orderCoin; poly_fast
lemma listOutput : PolyBound (fun n=>(PhysicalListSlots.outputNet n).net.count) := by
  apply PolyBound.of_le (g:=fun n=>8*Completion.transitionWidth n+194*n+21)
  · have := transitionWidth; poly_fast
  · exact PhysicalListSlots.outputNet_count
lemma listWork : PolyBound PhysicalListSlots.work := by
  apply PolyBound.of_le (g:=fun n=>n^5*ListSampler.width n+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5))
  · have := samplerWidth;have := transitionWidth;have:=listCoin;poly_fast
  · exact PhysicalListSlots.initialNet_count
lemma orderWork : PolyBound (fun n=>(OrderSlots.initialNet n).net.count) := by
  apply PolyBound.of_le (g:=fun n=>n^5*OrderTrial.rawWidth n (OrderSlots.sampleExponent n) n+
      2*n+Completion.transitionWidth n+OrderSlots.coinWidth n)
  · have := rawWidth;have:=transitionWidth;have:=orderCoin;poly_fast
  · exact OrderSlots.initialNet_count
lemma listSteps : PolyBound (fun n=>(PhysicalListSlots.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>n^5*(4*ListSampler.work n+3*n)+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5))
  · have:=samplerWork;have:=transitionWidth;have:=listCoin;poly_fast
  · exact PhysicalListSlots.program_length
lemma orderSteps : PolyBound (fun n=>(OrderSlots.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>n^5*(2+((OrderSlots.sampleExponent n+2)+
      4*OrderSample.scratch n (OrderSlots.sampleExponent n+2)+2*n+
      (OrderSlots.sampleExponent n+2)*(998*(OrderSlots.sampleExponent n+2)+49)+
      2*(OrderSlots.sampleExponent n+5))+3*n+OrderTrial.retentionBits n)+2*n+
      Completion.transitionWidth n+OrderSlots.coinWidth n)
  · have:=sampleExponent;have:=sampleScratch;have:=retentionBits
    have:=transitionWidth;have:=orderCoin;poly_fast
  · exact OrderSlots.program_length
lemma listLaunchWidth : PolyBound PhysicalListSlots.launchWidth := by
  unfold PhysicalListSlots.launchWidth
  have:=listWidth;have:=listWork;poly_fast
lemma listLaunchSteps : PolyBound (fun n=>(PhysicalListSlots.launch n).length) := by
  apply PolyBound.of_le (g:=fun n=>4*PhysicalListSlots.work n+2*PhysicalListSlots.width n+
      (PhysicalListSlots.program n).length)
  · have:=listWork;have:=listWidth;have:=listSteps;poly_fast
  · exact PhysicalListSlots.launch_length
lemma splitWork : PolyBound FixedSplit.work := by
  change PolyBound (fun n=>(FixedSplit.ordersInitialNet n).net.count)
  simp only [FixedSplit.ordersInitialNet_count]
  have:=listOutput;have:=orderWork;poly_fast
lemma ordersWidth : PolyBound FixedSplit.ordersWidth := by
  unfold FixedSplit.ordersWidth
  simp only [tensorWidth_eq]
  have:=orderWidth;poly_fast
lemma splitWidth : PolyBound FixedSplit.width := by
  unfold FixedSplit.width
  have:=listLaunchWidth;have:=ordersWidth;have:=splitWork;poly_fast
lemma splitSteps : PolyBound (fun n=>(FixedSplit.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>(PhysicalListSlots.launch n).length+4*FixedSplit.work n+
      2*FixedSplit.ordersWidth n+n^5*(OrderSlots.program n).length)
  · have:=listLaunchSteps;have:=splitWork;have:=ordersWidth;have:=orderSteps;poly_fast
  · exact FixedSplit.program_length
lemma splitInitial : PolyBound (fun n=>(FixedSplit.initialNet n).net.count) := by
  simp only [FixedSplit.initialNet_count]
  have:=listWidth;have:=listWork;have:=ordersWidth;have:=splitWork;poly_fast

end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TrialNetworkPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace OrderTrial
variable {α : Type*} {len k w : α→ℕ}
lemma decodeVars_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t) (hc : NetworkAt len c) :
    ∃p : Polynomial ℕ,∀x (i : DecodeVar),
      ((match i with | .den=>d x | .num=>j x | .residue=>t x | .coin=>c x) :
        BooleanNetwork (k x) (w x)).net.count≤p.eval (len x) := by
  obtain ⟨p,hp⟩:=((hd.add hj).add ht).add hc
  refine ⟨p,fun x i=>?_⟩
  have h:=hp x
  dsimp only at h
  cases i <;> dsimp only <;> omega

lemma firstRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>firstRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.firstE n (.var DecodeVar.den) (.var .num)) :=
    Expressions.firstE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma secondRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>secondRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.secondE n (.var DecodeVar.den) (.var .num) (.var .residue)) :=
    Expressions.secondE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma thirdRetNet_poly {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hw : PolyAt len w) :
    NetworkAt len (fun x=>thirdRetNet (len x) (d x) (j x) (t x) (c x)) := by
  have hE : RatExprPoly (fun n=>Expressions.lastE n (.var DecodeVar.den) (.var .num)) :=
    Expressions.lastE_poly PolyBound.id (NatExprPoly.var _) (NatExprPoly.var _)
  have hT:=thresholdExpr_poly PreparationPolynomial.retentionBits hE
    (NatExprPoly.var (fun _=>DecodeVar.coin))
  exact (NatExprAt.ofPoly hT len).isOne hw (decodeVars_poly hd hj ht hc)
lemma labelValidNet_poly {a m d j : ∀x,BooleanNetwork (k x) (w x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hd : NetworkAt len d)
    (hj : NetworkAt len j) (hw : PolyAt len w) :
    NetworkAt len (fun x=>labelValidNet (len x) (a x) (m x) (d x) (j x)) := by
  let c:=fun x=>(a x).net.count+(m x).net.count+(d x).net.count+(j x).net.count
  have hc : PolyAt len c:=((ha.add hm).add hd).add hj
  have hg : PolyAt len (fun x=>2*w x*(216*w x*w x+300*w x+100)) := by
    exact ((PolyAt.const len 2).mul hw).mul ((((PolyAt.const len 216).mul hw).mul hw).add
      ((PolyAt.const len 300).mul hw) |>.add (PolyAt.const len 100))
  have hp : PolyAt len (fun x=>w x+w x*(3672*w x*w x+436*w x+36)) := by
    exact hw.add (hw.mul ((((PolyAt.const len 3672).mul hw).mul hw).add
      ((PolyAt.const len 436).mul hw) |>.add (PolyAt.const len 36)))
  apply NetworkAt.of_le (bound:=fun x=>9*c x+
    (2*w x*(216*w x*w x+300*w x+100))+(w x+w x*(3672*w x*w x+436*w x+36))+344*w x+70)
  · poly_at
  · intro x
    have h:=labelValidNet_count (len x) (a x) (m x) (d x) (j x)
      (c:=c x) (by dsimp [c];omega) (by dsimp [c];omega)
      (by dsimp [c];omega) (by dsimp [c];omega)
    omega
lemma trialAcceptOn_poly {a m mode d j t c : ∀x,BooleanNetwork (k x) (w x)}
    {selected : ∀x,BooleanNetwork (k x) 1}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hmode : NetworkAt len mode)
    (hd : NetworkAt len d) (hj : NetworkAt len j) (ht : NetworkAt len t)
    (hc : NetworkAt len c) (hs : NetworkAt len selected) (hw : PolyAt len w) :
    NetworkAt len (fun x=>trialAcceptOn (len x) (a x) (m x) (mode x) (d x) (j x) (t x) (c x) (selected x)) := by
  have h2:=NetworkAt.wordConstant (a:=k) (fun x=>BitVec.ofNat (w x) 2) hw
  have h3:=NetworkAt.wordConstant (a:=k) (fun x=>BitVec.ofNat (w x) 3) hw
  have h1:=firstRetNet_poly hd hj ht hc hw
  have hsecond:=secondRetNet_poly hd hj ht hc hw
  have hthird:=thirdRetNet_poly hd hj ht hc hw
  exact (labelValidNet_poly ha hm hd hj hw).band
    (((hmode.wordLt h2 hw).band (hs.band h1)).bor
      (((hmode.equalOn h2 hw).band ((ht.wordLt hd hw).band hsecond)).bor
        ((hmode.equalOn h3 hw).band hthird)))
end OrderTrial
end ExactQuantumFactoring

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RawDecoderPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace OrderTrial
lemma rawMode_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawMode r).net.count=r.net.count := by
  simp only [rawMode,leftNet,count_comp,count_select,Nat.add_zero]
lemma rawSample_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawSample r).net.count=r.net.count := by
  simp only [rawSample,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawGuesses_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawGuesses r).net.count=r.net.count := by
  simp only [rawGuesses,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawDen_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawDen r).net.count=r.net.count := by
  simp only [rawDen,rawGuesses_count,leftNet,count_comp,count_select,Nat.add_zero]
lemma rawNum_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawNum r).net.count=r.net.count := by
  simp only [rawNum,rawGuesses_count,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawResidue_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawResidue r).net.count=r.net.count := by
  simp only [rawResidue,rawGuesses_count,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawCoin_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawCoin r).net.count=r.net.count := by
  simp only [rawCoin,rawGuesses_count,rightNet,count_comp,count_select,Nat.add_zero]
lemma decodeSteps_poly : PolyBound (fun n=>decodeSteps (OrderSlots.sampleExponent n)) := by
  unfold decodeSteps
  have:=PreparationPolynomial.sampleExponent
  poly_fast
lemma decodeWidth_poly : PolyBound (fun n=>decodeWidth n (OrderSlots.sampleExponent n) n) := by
  have hs:=PreparationPolynomial.sampleExponent
  have ht:=decodeSteps_poly
  have hcf : PolyBound (fun n=>cfWidth (OrderSlots.sampleExponent n+3) (decodeSteps (OrderSlots.sampleExponent n))) := by
    unfold cfWidth;poly_fast
  have hr:=PreparationPolynomial.retentionBits
  unfold decodeWidth;poly_fast

variable {α : Type*} {len k : α→ℕ}
  {r : ∀x,BooleanNetwork (k x) (rawWidth (len x) (OrderSlots.sampleExponent (len x)) (len x))}
lemma recoveredPairNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>recoveredPairNet (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hs:=PolyAt.ofPoly PreparationPolynomial.sampleExponent len
  have hrs : NetworkAt len (fun x=>rawSample (r x)) := by
    simpa only [NetworkAt,rawSample_count] using hr
  have hy : NetworkAt len (fun x=>(rawSample (r x)).comp (sampleYNet (len x) (OrderSlots.sampleExponent (len x)+2))) :=
    hrs.comp (NetworkAt.select _)
  exact recoveryNet_poly (NetworkAt.wordConstant _ hw) (NetworkAt.wordConstant _ hw)
    (hy.toWidth (hs.add (PolyAt.const len 2)) hw) hw (PolyAt.ofPoly decodeSteps_poly len)
lemma trialPairNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialPairNet (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hn:=PolyAt.self len
  have hm : NetworkAt len (fun x=>rawMode (r x)) := by
    simpa only [NetworkAt,rawMode_count] using hr
  have hd : NetworkAt len (fun x=>rawDen (r x)) := by
    simpa only [NetworkAt,rawDen_count] using hr
  have hj : NetworkAt len (fun x=>rawNum (r x)) := by
    simpa only [NetworkAt,rawNum_count] using hr
  exact ((hm.toWidth (PolyAt.const len 2) hw).wordLt (NetworkAt.wordConstant _ hw) hw).wordMux
    (recoveredPairNet_poly hr) ((hd.toWidth hn hw).pair (hj.toWidth hn hw)) (hw.add hw)
lemma trialDenNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialDenNet (r x)) :=
  (trialPairNet_poly hr).comp (NetworkAt.select _)
lemma trialNumNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialNumNet (r x)) :=
  (trialPairNet_poly hr).comp (NetworkAt.select _)

lemma samplerSelectedNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    {z : ∀x,BooleanNetwork (k x) (OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hz : NetworkAt len z) :
    NetworkAt len (fun x=>samplerSelectedNet (a x) (m x) (z x)) := by
  have hs := PolyAt.ofPoly PreparationPolynomial.sampleExponent len
  have hscratch := PolyAt.ofPoly PreparationPolynomial.sampleScratch len
  have hwidth := PolyAt.ofPoly PreparationPolynomial.sampleWidth len
  have hwork : PolyAt len (fun x=>Triangular.work (OrderSlots.sampleExponent (len x)+2)) := by
    unfold Triangular.work;poly_at
  have hrest : PolyAt len (fun x=>3*(OrderSlots.sampleExponent (len x)+2)+
      Triangular.work (OrderSlots.sampleExponent (len x)+2)+
      OrderSample.scratch (len x) (OrderSlots.sampleExponent (len x)+2)+
      98*OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2)+21) := by
    exact (((((PolyAt.const len 3).mul (hs.add (PolyAt.const len 2))).add hwork).add hscratch).add
      ((PolyAt.const len 98).mul hwidth)).add (PolyAt.const len 21)
  apply NetworkAt.of_le (bound:=fun x=>3*(z x).net.count+(a x).net.count+(m x).net.count+
      (3*(OrderSlots.sampleExponent (len x)+2)+Triangular.work (OrderSlots.sampleExponent (len x)+2)+
      OrderSample.scratch (len x) (OrderSlots.sampleExponent (len x)+2)+
      98*OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2)+21))
  · exact (((PolyAt.const len 3).mul hz).add ha |>.add hm).add hrest
  · intro x
    have h:=samplerSelectedNet_count (a x) (m x) (z x)
    omega
lemma rawAcceptNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>rawAcceptNet (a x) (m x) (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hn:=PolyAt.self len
  have hmode : NetworkAt len (fun x=>rawMode (r x)) := by
    simpa only [NetworkAt,rawMode_count] using hr
  have ht : NetworkAt len (fun x=>rawResidue (r x)) := by
    simpa only [NetworkAt,rawResidue_count] using hr
  have hc : NetworkAt len (fun x=>rawCoin (r x)) := by
    simpa only [NetworkAt,rawCoin_count] using hr
  have hs : NetworkAt len (fun x=>rawSample (r x)) := by
    simpa only [NetworkAt,rawSample_count] using hr
  exact trialAcceptOn_poly (ha.toWidth hn hw) (hm.toWidth hn hw)
    (hmode.toWidth (PolyAt.const len 2) hw) (trialDenNet_poly hr) (trialNumNet_poly hr)
    (ht.toWidth hn hw) (hc.toWidth (PolyAt.ofPoly PreparationPolynomial.retentionBits len) hw)
    (samplerSelectedNet_poly ha hm hs) hw
lemma trialValueNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>trialValueNet (a x) (m x) (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  exact (rawAcceptNet_poly ha hm hr).wordMux (trialDenNet_poly hr) (NetworkAt.wordConstant _ hw) hw
lemma trialSmallValueNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>trialSmallValueNet (a x) (m x) (r x)) :=
  (trialValueNet_poly ha hm hr).comp
    (NetworkAt.resizeWord (PolyAt.ofPoly decodeWidth_poly len) (PolyAt.self len))
end OrderTrial
end ExactQuantumFactoring

end


end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderDecoderPolynomial.lean =====
namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NetworkAt
variable {α : Type*} {len a w K : α→ℕ}
lemma minimumNet {f : ∀x,Fin (K x)→BooleanNetwork (a x) (w x)}
    (hK : PolyAt len K) (hw : PolyAt len w)
    (hf : NetworkAt (fun xi : Σx,Fin (K x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>OrderTrial.minimumNet (f x)) := by
  obtain ⟨p,hp⟩:=hf
  have hpoly : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le (bound:=fun x=>w x+K x*(p.eval (len x)+300*w x+60))
  · exact hw.add (hK.mul ((hpoly.add ((PolyAt.const len 300).mul hw)).add (PolyAt.const len 60)))
  · exact fun x=>minimumNet_count (f x) (fun i=>hp ⟨x,i⟩)
end NetworkAt
namespace OrderSlots
variable {α : Type*} {len k : α→ℕ} {a m : ∀x,BooleanNetwork (k x) (len x)}
lemma usableOn_poly (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>usableOn (a x) (m x)) := by
  have hn:=PolyAt.self len
  exact (ha.wordLt hm hn).band
    (((ha.pair hm).comp (NetworkAt.gcdNet hn)).equalOn (NetworkAt.wordConstant _ hn) hn)
lemma orderResultNet_poly {raw : ∀x,BooleanNetwork (k x) (ordinaryWidth (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>orderResultNet (a x) (m x) (raw x)) := by
  let ix := Σx:α,Fin ((len x)^5)
  let param : ix→α:=Sigma.fst
  have hs : NetworkAt (fun xi:ix=>len xi.1)
      (fun xi=>(raw xi.1).comp (tensorSelect (rawWidth (len xi.1)
        (sampleExponent (len xi.1)) (len xi.1)) ((len xi.1)^5) xi.2)) :=
    (hr.pull param).comp (NetworkAt.select _)
  exact NetworkAt.minimumNet ((PolyAt.self len).pow 5) (PolyAt.self len)
    (trialSmallValueNet_poly (ha.pull param) (hm.pull param) hs)
lemma ordinaryOn_poly {raw : ∀x,BooleanNetwork (k x) (ordinaryWidth (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>ordinaryOn (a x) (m x) (raw x)) := by
  have hn:=PolyAt.self len
  exact ((usableOn_poly ha hm).wordMux (orderResultNet_poly ha hm hr)
    (NetworkAt.wordConstant _ hn) hn).comp
      (NetworkAt.resizeWord hn (PolyAt.ofPoly PreparationPolynomial.transitionWidth len))
lemma outputOn_poly {raw : ∀x,BooleanNetwork (k x) (width (len x))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>outputOn (a x) (m x) (raw x)) := by
  have hw:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  have hra : NetworkAt len (fun x=>Completion.rareNet (ordinaryWidth (len x))
      (Completion.transitionWidth (len x)) (2*len x) ((len x+10)*(len x)^5)) := by
    apply NetworkAt.of_le (bound:=fun x=>97*(2*len x)+21)
    · poly_at
    · exact fun x=>Completion.rareNet_count ..
  exact (hr.comp hra).wordMux (hr.comp (NetworkAt.select _))
    (ordinaryOn_poly ha hm (hr.comp (NetworkAt.select _))) hw
end OrderSlots
end ExactQuantumFactoring

end



end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeControlBounds.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma properOn_count {k w : ℕ} (m d : BooleanNetwork k w) :
    (properOn m d).net.count ≤ 2*m.net.count+3*d.net.count+216*w*w+250*w+45 := by
  have h1 := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 1)) d
  have h2 := wordLt_count d m
  have h3 := zeroWord_count ((m.pair d).comp (mod w))
  have h4 := mod_count w
  simp only [wordConstant_count] at h1
  simp only [count_comp,count_pair] at h3
  simp only [properOn,count_band]
  omega

namespace NodeCircuit

def primeBound (w : ℕ) := 49*w+10+rootWidth w+primalityBound w
def guardBound (w : ℕ) := 216*w*w+250*w+45
def quotientBound (w : ℕ) := 216*w*w+56*w+6
def splitBound (s w : ℕ) := ((s+1)*w)*(((s+1)*w)*(quotientBound w+(s+1)*w*w))
def nextBound (s w : ℕ) := 97*w+21+primeBound w+(s+1)*w*w+guardBound w+
  splitBound s w+21*((s+1)*w)
def stepBound (s w : ℕ) := nextBound s w+2*primeBound w+guardBound w+105*w+26

@[simp] lemma pending_count (s w : ℕ) : (pending s w).net.count=0 := rfl
@[simp] lemma top_count (s w : ℕ) : (top s w).net.count=0 := rfl
@[simp] lemma divisor_count (s w : ℕ) : (divisor s w).net.count=0 := rfl
lemma popped_count (s w : ℕ) : (popped s w).net.count ≤ (s+1)*w*w := by
  simpa only [popped,count_comp,pending_count,zero_add] using stackPop_count (s+1) w
lemma quotient_count (s w : ℕ) : (quotient s w).net.count ≤ quotientBound w := by
  simpa only [quotient,quotientBound,count_comp,count_pair,top_count,divisor_count,zero_add]
    using div_count w
lemma isPrime_count (s w : ℕ) : (isPrime s w).net.count ≤ primeBound w := by
  simpa only [isPrime,primeBound,count_comp,top_count,zero_add] using primeWord_count w
lemma isDone_count (s w : ℕ) : (isDone s w).net.count ≤ 97*w+21 := by
  simpa only [isDone,top_count,zero_add] using zeroWord_count (top s w)
lemma isProper_count (s w : ℕ) : (isProper s w).net.count ≤ guardBound w := by
  simpa only [isProper,guardBound,top_count,divisor_count,mul_zero,zero_add] using
    properOn_count (top s w) (divisor s w)
lemma split_count (s w : ℕ) : (split s w).net.count ≤ splitBound s w := by
  have h1 := stackPush_count (quotient s w) (popped s w)
  have h2 := stackPush_count (divisor s w) (stackPush (quotient s w) (popped s w))
  rw [divisor_count,zero_add] at h2
  exact h2.trans (Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _
    (Nat.add_le_add (quotient_count s w) (popped_count s w)))))
lemma next_count (s w : ℕ) : (next s w).net.count ≤ nextBound s w := by
  have h1 := isDone_count s w
  have h2 := isPrime_count s w
  have h3 := isProper_count s w
  have h4 := popped_count s w
  have h5 := split_count s w
  simp only [next,wordMux_count,pending_count]
  dsimp only [nextBound]
  omega
lemma emitted_count (s w : ℕ) : (emitted s w).net.count ≤ primeBound w+8*w := by
  have h := isPrime_count s w
  simp only [emitted,wordMux_count,top_count,wordConstant_count]
  omega
lemma failed_count (s w : ℕ) : (failed s w).net.count ≤ 97*w+21+primeBound w+guardBound w+5 := by
  have h1 := isDone_count s w
  have h2 := isPrime_count s w
  have h3 := isProper_count s w
  simp only [failed,count_band,count_bnot]
  omega

/-- Explicit polynomial-size bound for the full guarded one-step controller. -/
theorem step_count (s w : ℕ) : (step s w).net.count ≤ stepBound s w := by
  have h1 := next_count s w
  have h2 := emitted_count s w
  have h3 := failed_count s w
  simp only [step,count_pair]
  dsimp only [stepBound]
  omega

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
