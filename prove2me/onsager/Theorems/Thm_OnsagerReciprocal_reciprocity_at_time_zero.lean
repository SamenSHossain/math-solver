import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem reciprocity_at_time_zero {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef)
    (hrev : ∀ t : ℝ, 0 ≤ t → ∀ i k : Fin n,
      timeCorrelation β lam t i k = timeCorrelation β lam t k i)
    (i k : Fin n) :
    ∑ l : Fin n, kineticCoeff β lam i l *
        fluctuationAverage β (fun x => conjugate β x l * x k) =
      ∑ l : Fin n, kineticCoeff β lam k l *
        fluctuationAverage β (fun x => conjugate β x l * x i) := by sorry
end OnsagerReciprocal
