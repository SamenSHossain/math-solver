import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting
import Definitions.Def_TailRiskSharing_VaRTail_Setting

namespace TailRiskSharing.ComonoConv

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §6 p. 19: `X` and `Y` are comonotonic, `X // Y`. -/
def Comonotone (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∃ Ω₀ : Set Ω, MeasurableSet Ω₀ ∧ P Ω₀ = 1 ∧
    ∀ ω ∈ Ω₀, ∀ ω' ∈ Ω₀, 0 ≤ (X ω - X ω') * (Y ω - Y ω')

/-- (22) p. 19: comonotonic allocations `A⁺_n(X)`: allocations of `X` whose every
component is comonotonic with `X`. -/
def ComonoAllocations (P : Measure Ω) (dom : Set (Ω → ℝ)) (n : ℕ) (X : Ω → ℝ) :
    Set (Fin n → Ω → ℝ) :=
  {Xs | Xs ∈ TailRiskSharing.VaRConv.Allocations dom n X ∧ ∀ i, Comonotone P (Xs i) X}

/-- (23) p. 19: the constrained (comonotonic) inf-convolution `⊞ ρᵢ`, valued in `EReal`. -/
noncomputable def comonoInfConv (P : Measure Ω) (dom : Set (Ω → ℝ)) {n : ℕ}
    (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) : EReal :=
  ⨅ Xs ∈ ComonoAllocations P dom n X, ((∑ i, ρ i (Xs i) : ℝ) : EReal)

/-- p. 8: the tail `X_p = F⁻¹_X(1 − p + p U)` for a given quantile uniform `U` of `X`,
written with `F⁻¹_X(q) = VaR^L_{1-q}(X)`. -/
noncomputable def tailRV (P : Measure Ω) (p : ℝ) (X U : Ω → ℝ) : Ω → ℝ :=
  fun ω => TailRiskSharing.VaRConv.VaRL P (p * (1 - U ω)) X

/-- p. 20: `ρstar` is a `p`-generator of `ρ`: a law-invariant risk measure with
`ρ(X) = ρstar(X_p)` for every `X` in the domain and every quantile uniform `U` of `X`. -/
def IsGenerator (P : Measure Ω) (dom : Set (Ω → ℝ)) (p : ℝ) (ρ ρstar : (Ω → ℝ) → ℝ) : Prop :=
  TailRiskSharing.VaRTail.IsLawInvariant P dom ρstar ∧
    ∀ X ∈ dom, ∀ U, TailRiskSharing.VaRTail.IsQuantileUniform P X U → ρ X = ρstar (tailRV P p X U)

end TailRiskSharing.ComonoConv
