import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting
import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

namespace TailRiskSharing.RobustVaR

open MeasureTheory

theorem theorem6_robust_var_comonotonic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (X : Ω → ℝ) (hX : X ∈ TailRiskSharing.TailConv.Linf P) (Λ : TailRiskSharing.VaRConv.Side) (m : ℕ) :
    (∀ (δs : Fin (m + 1) → ℝ) (α : ℝ), 0 < δs 0 → Monotone δs → 0 < α → α < 1 →
      TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 (δs i) (TailRiskSharing.VaRConv.VaRS P Λ α)) X =
          ((robust P 1 (δs 0) (TailRiskSharing.VaRConv.VaRS P Λ α) X + ∑ i : Fin m, δs i.succ / α : ℝ) : EReal) ∧
        IsOptimalComonoAllocation P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 (δs i) (TailRiskSharing.VaRConv.VaRS P Λ α)) X
          (fun i => if i = 0 then X else 0)) ∧
    (∀ (αs : Fin (m + 1) → ℝ) (δ : ℝ), Antitone αs → αs 0 < 1 → 0 < αs (Fin.last m) → 0 < δ →
      TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs i))) X =
          ((robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs 0)) X + ∑ i : Fin m, δ / αs i.succ : ℝ) : EReal) ∧
        IsOptimalComonoAllocation P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs i))) X
          (fun i => if i = 0 then X else 0)) := by sorry

end TailRiskSharing.RobustVaR
