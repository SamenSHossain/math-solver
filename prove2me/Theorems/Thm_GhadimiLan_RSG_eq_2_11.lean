import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Eq. (2.11) (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, p. 7): for
`f ∈ C^{1,1}_L(ℝⁿ)` (`L > 0`) bounded below with `f* = inf f`, stepsizes `0 < γ_k < 2/L`
(`k = 1, …, N`, `N ≥ 1`) and an RSG run under Assumption A1, each `‖∇f(x_k)‖²` is integrable
and `Σ_{k=1}^N (γ_k − (L/2)γ_k²) E‖∇f(x_k)‖² ≤ f(x_1) − f* + (Lσ²/2) Σ_{k=1}^N γ_k²`. -/
theorem eq_2_11 {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) :
    (∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ) ∧
    ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ ≤
      f x1 - fstar + L * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 := by sorry

end GhadimiLan.RSG
