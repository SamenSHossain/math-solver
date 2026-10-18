import Mathlib
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone
import Definitions.Def_TailRiskSharing_TailConv_Setting
import Definitions.Def_TailRiskSharing_VaRConv_Setting

namespace TailRiskSharing.RobustVaR

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- p. 19: an optimal constrained allocation of `X` for `(ρ₁, …, ρₙ)`. -/
def IsOptimalComonoAllocation (P : Measure Ω) (dom : Set (Ω → ℝ)) {n : ℕ}
    (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) (Xs : Fin n → Ω → ℝ) : Prop :=
  Xs ∈ TailRiskSharing.ComonoConv.ComonoAllocations P dom n X ∧ ((∑ i, ρ i (Xs i) : ℝ) : EReal) = TailRiskSharing.ComonoConv.comonoInfConv P dom ρ X

end TailRiskSharing.RobustVaR
