import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
/-- Finiteness of the polynomial moments of the Gaussian fluctuation weight: for a positive
definite `β`, every function `x ↦ ‖x‖ ^ m * exp (-½ xᵀ β x)` is Lebesgue integrable on `ℝⁿ`. -/
theorem integrable_norm_pow_mul_fluctuationWeight {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (m : ℕ) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => ‖x‖ ^ m * fluctuationWeight β x) := by sorry
end OnsagerReciprocal
