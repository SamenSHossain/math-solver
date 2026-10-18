import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

namespace TailRiskSharing.VaRTail

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.1 p. 5: `U` is a uniform random variable on `[0, 1]` with `F⁻¹_X(U) = X` a.s.
Here `F⁻¹_X(p) = TailRiskSharing.VaRConv.VaRL P (1 - p) X`. -/
def IsQuantileUniform (P : Measure Ω) (X U : Ω → ℝ) : Prop :=
  Measurable U ∧ P.map U = volume.restrict (Set.Icc (0:ℝ) 1) ∧
    ∀ᵐ ω ∂P, TailRiskSharing.VaRConv.VaRL P (1 - U ω) X = X ω

/-- §2.4 p. 8, display (6): `X_p =d Y_p`, i.e. `(F_X(x) - (1 - p))_+ = (F_Y(x) - (1 - p))_+`
for every `x`. -/
def TailEquiv (P : Measure Ω) (p : ℝ) (X Y : Ω → ℝ) : Prop :=
  ∀ x : ℝ, max (TailRiskSharing.VaRConv.distFn P X x - (1 - p)) 0 = max (TailRiskSharing.VaRConv.distFn P Y x - (1 - p)) 0

/-- §2.2 p. 5: monotone, `ρ(X) ≤ ρ(Y)` whenever `X ≤ Y` a.s. -/
def IsMonotone (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ᵐ ω ∂P, X ω ≤ Y ω) → ρ X ≤ ρ Y

/-- §2.2 p. 5: translation-invariant, `ρ(X - m) = ρ(X) - m`. -/
def IsTranslationInvariant (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ m : ℝ, ρ (fun ω => X ω - m) = ρ X - m

/-- §2.2 p. 5: monetary = monotone and translation-invariant. -/
def IsMonetary (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  IsMonotone P dom ρ ∧ IsTranslationInvariant dom ρ

/-- §2.2 p. 5: law-invariant. -/
def IsLawInvariant (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ x, TailRiskSharing.VaRConv.distFn P X x = TailRiskSharing.VaRConv.distFn P Y x) → ρ X = ρ Y

/-- Definition 1, p. 8, through (6): `ρ` is a `p`-tail risk measure. -/
def IsTailRiskMeasure (P : Measure Ω) (dom : Set (Ω → ℝ)) (p : ℝ) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, TailEquiv P p X Y → ρ X = ρ Y

/-- §2.2 p. 5 (range `[-∞, ∞)`, footnote 2): monotone, for an `EReal`-valued functional. -/
def IsMonotoneE (P : Measure Ω) (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ᵐ ω ∂P, X ω ≤ Y ω) → F X ≤ F Y

/-- §2.2 p. 5: translation-invariant, for an `EReal`-valued functional. -/
def IsTranslationInvariantE (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) : Prop :=
  ∀ X ∈ dom, ∀ m : ℝ, F (fun ω => X ω - m) = F X - (m : EReal)

/-- §2.2 p. 5: monetary, for an `EReal`-valued functional. -/
def IsMonetaryE (P : Measure Ω) (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) : Prop :=
  IsMonotoneE P dom F ∧ IsTranslationInvariantE dom F

/-- Definition 1, p. 8, through (6), for an `EReal`-valued functional. -/
def IsTailRiskMeasureE (P : Measure Ω) (dom : Set (Ω → ℝ)) (p : ℝ) (F : (Ω → ℝ) → EReal) :
    Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, TailEquiv P p X Y → F X = F Y

/-- Theorem 2, p. 13: `X^[α] = X 1{U ≤ 1-α} + VaR^R_{α+ε}(X) 1{U > 1-α}`. -/
noncomputable def cutAt (P : Measure Ω) (ε α : ℝ) (X U : Ω → ℝ) : Ω → ℝ :=
  fun ω => if U ω ≤ 1 - α then X ω else TailRiskSharing.VaRConv.VaRR P (α + ε) X

end TailRiskSharing.VaRTail
