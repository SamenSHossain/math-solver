import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting

namespace TailRiskSharing.RobustVaR

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §8.2 p. 28: the Wasserstein metric of order `k`,
`W_k(X, Y) = (∫₀¹ |F⁻¹_X(x) − F⁻¹_Y(x)|^k dx)^{1/k}`, with the quantile `F⁻¹_X(x) = VaR^L_{1-x}(X)`. -/
noncomputable def wassersteinK (P : Measure Ω) (k : ℝ) (X Y : Ω → ℝ) : ℝ :=
  (∫ x in (0:ℝ)..1, |TailRiskSharing.VaRConv.VaRL P (1 - x) X - TailRiskSharing.VaRConv.VaRL P (1 - x) Y| ^ k) ^ (1 / k)

/-- (32) p. 28: the values `ρ(Y)` over the Wasserstein ball `{Y ∈ L^∞ : W_k(Y, X) ≤ δ}`. -/
def robustSet (P : Measure Ω) (k δ : ℝ) (ρ : (Ω → ℝ) → ℝ) (X : Ω → ℝ) : Set ℝ :=
  {r | ∃ Y ∈ TailRiskSharing.TailConv.Linf P, wassersteinK P k Y X ≤ δ ∧ r = ρ Y}

/-- (32) p. 28: the robust version `[ρ]^k_δ(X) = sup {ρ(Y) : W_k(Y, X) ≤ δ}`, `X ∈ L^∞`. -/
noncomputable def robust (P : Measure Ω) (k δ : ℝ) (ρ : (Ω → ℝ) → ℝ) (X : Ω → ℝ) : ℝ :=
  sSup (robustSet P k δ ρ X)

end TailRiskSharing.RobustVaR
