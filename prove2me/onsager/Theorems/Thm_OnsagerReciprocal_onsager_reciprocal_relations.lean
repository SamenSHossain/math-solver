import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem onsager_reciprocal_relations {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef)
    (hrev : ∀ t : ℝ, 0 ≤ t → ∀ i k : Fin n,
      timeCorrelation β lam t i k = timeCorrelation β lam t k i) :
    ∀ i k : Fin n, kineticCoeff β lam i k = kineticCoeff β lam k i := by sorry
end OnsagerReciprocal
