import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Eq. (2.9) (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, p. 7): for
`f ∈ C^{1,1}_L(ℝⁿ)` with gradient map `g = ∇f`, `f* = inf f`, an RSG run `x` from `x1` and
`N ≥ 1`, for every outcome `ω` (with `δ_k = G(x_k, ξ_k) − ∇f(x_k)`):
`Σ_{k=1}^N (γ_k − (L/2)γ_k²)‖∇f(x_k)‖² ≤ f(x_1) − f(x_{N+1}) − Σ_{k=1}^N (γ_k − Lγ_k²)⟨∇f(x_k), δ_k⟩ + (L/2)Σ_{k=1}^N γ_k²‖δ_k‖²`,
and the same with `f(x_{N+1})` replaced by `f*`. Pathwise. -/
theorem eq_2_9 {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (γ : ℕ → ℝ) (x1 : E n) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x) (N : ℕ) (hN : 1 ≤ N) (ω : Ω) :
    (∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2 ≤
      f x1 - f (x (N + 1) ω)
        - ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
        + L / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2) ∧
    ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2 ≤
      f x1 - fstar
        - ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
        + L / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2 := by sorry

end GhadimiLan.RSG
