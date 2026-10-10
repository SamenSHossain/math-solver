import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem kinetic_coefficients_relation {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (x : Fin n → ℝ) :
    -(lam *ᵥ x) = -(kineticCoeff β lam *ᵥ conjugate β x) := by sorry
end OnsagerReciprocal
