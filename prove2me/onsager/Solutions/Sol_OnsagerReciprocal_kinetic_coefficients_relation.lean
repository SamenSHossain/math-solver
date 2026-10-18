import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix
set_option autoImplicit false

/-- `ẋ = -λx = -γX`: with `γ = λβ⁻¹` and `X = βx`, `γX = λβ⁻¹βx = λx` because a positive
definite matrix is invertible. -/
theorem solution {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (x : Fin n → ℝ) :
    -(lam *ᵥ x) = -(OnsagerReciprocal.kineticCoeff β lam *ᵥ OnsagerReciprocal.conjugate β x) := by
  have hinv : β⁻¹ * β = 1 := Matrix.nonsing_inv_mul β (isUnit_iff_ne_zero.mpr hβ.det_pos.ne')
  rw [OnsagerReciprocal.kineticCoeff, OnsagerReciprocal.conjugate, mulVec_mulVec, Matrix.mul_assoc,
    hinv, Matrix.mul_one]
