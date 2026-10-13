import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem meanFluctuation_dynamics {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (x₀ : Fin n → ℝ) :
    meanFluctuation lam 0 x₀ = x₀ ∧
      ∀ t : ℝ, HasDerivAt (fun s => meanFluctuation lam s x₀)
        (-(kineticCoeff β lam *ᵥ meanConjugate β lam t x₀)) t := by sorry
end OnsagerReciprocal
