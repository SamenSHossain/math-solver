import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix
set_option autoImplicit false

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `ξ(t) = e^{-tλ}x₀` satisfies `ξ(0) = x₀` and `ξ̇(t) = -λξ(t) = -γΞ(t)`: the derivative of
`s ↦ exp (s • (-λ))` is `(-λ) exp (t • (-λ))`, applying a matrix to the fixed vector `x₀` is a
continuous linear map, and `γΞ = λβ⁻¹βξ = λξ`. -/
theorem solution {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (x₀ : Fin n → ℝ) :
    OnsagerReciprocal.meanFluctuation lam 0 x₀ = x₀ ∧
      ∀ t : ℝ, HasDerivAt (fun s => OnsagerReciprocal.meanFluctuation lam s x₀)
        (-(OnsagerReciprocal.kineticCoeff β lam *ᵥ OnsagerReciprocal.meanConjugate β lam t x₀)) t := by
  have hinv : β⁻¹ * β = 1 := Matrix.nonsing_inv_mul β (isUnit_iff_ne_zero.mpr hβ.det_pos.ne')
  refine ⟨?_, fun t => ?_⟩
  · simp [OnsagerReciprocal.meanFluctuation]
  · have hE : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • -lam))
        (-lam * NormedSpace.exp (t • -lam)) t :=
      hasDerivAt_exp_smul_const' (-lam) t
    -- `A ↦ A *ᵥ x₀` as a continuous linear map on matrices
    let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.applyₗ x₀).comp (Matrix.toLin' (R := ℝ) (m := Fin n) (n := Fin n)).toLinearMap)
    have hL : ∀ A : Matrix (Fin n) (Fin n) ℝ, L A = A *ᵥ x₀ := fun A => by
      simp [L, Matrix.toLin'_apply]
    have h := L.hasFDerivAt.comp_hasDerivAt t hE
    have hfun : (fun s => OnsagerReciprocal.meanFluctuation lam s x₀) =
        (fun s : ℝ => L (NormedSpace.exp (s • -lam))) := by
      funext s
      rw [hL, OnsagerReciprocal.meanFluctuation, neg_smul, smul_neg]
    rw [hfun]
    have h' : HasDerivAt (fun s : ℝ => L (NormedSpace.exp (s • -lam)))
        (L (-lam * NormedSpace.exp (t • -lam))) t := h
    refine h'.congr_deriv ?_
    rw [hL, OnsagerReciprocal.kineticCoeff, OnsagerReciprocal.meanConjugate,
      OnsagerReciprocal.meanFluctuation, mulVec_mulVec, mulVec_mulVec,
      Matrix.mul_assoc lam β⁻¹, hinv, Matrix.mul_one,
      neg_smul, smul_neg, Matrix.neg_mul, neg_mulVec]
