import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Eq. (2.8) (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, p. 6): for
`f ∈ C^{1,1}_L(ℝⁿ)` with gradient map `g = ∇f` and an RSG run `x` (recursion (2.2)), for every
`k ≥ 1` and every outcome `ω`, with `δ_k = G(x_k, ξ_k) − ∇f(x_k)`,
`f(x_{k+1}) ≤ f(x_k) − (γ_k − (L/2)γ_k²)‖∇f(x_k)‖² − (γ_k − Lγ_k²)⟨∇f(x_k), δ_k⟩ + (L/2)γ_k²‖δ_k‖²`.
This is a pathwise (deterministic) inequality. -/
theorem eq_2_8 {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (γ : ℕ → ℝ) (x1 : E n) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x) (k : ℕ) (hk : 1 ≤ k) (ω : Ω) :
    f (x (k + 1) ω) ≤
      f (x k ω) - (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2
        - (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
        + L / 2 * γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2 := by sorry

end GhadimiLan.RSG
