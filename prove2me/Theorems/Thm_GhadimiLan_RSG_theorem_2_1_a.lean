import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Theorem 2.1 a), Eq. (2.4) (Ghadimi & Lan, arXiv:1309.5549v1, p. 6). Let `f ∈ C^{1,1}_L(ℝⁿ)`
(`L > 0`) have gradient map `g = ∇f` and be bounded below with `f* = inf f`. Run the RSG method
(2.2) from `x1` with a Borel oracle `G` satisfying Assumption A1 (noise level `σ`), stepsizes
`0 < γ_k < 2/L` for `k = 1, …, N` (`N ≥ 1`), and an output index `R` with mass function (2.3)
drawn independently of the noise. Then `‖∇f(x_R)‖²` is integrable and
`(1/L) E‖∇f(x_R)‖² ≤ (D_f² + σ² Σ_{k=1}^N γ_k²) / Σ_{k=1}^N (2γ_k − Lγ_k²)`, where
`D_f = [2(f(x_1) − f*)/L]^{1/2}` and the expectation is over both `R` and the noise. -/
theorem theorem_2_1_a {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ)
    (R : Ω → ℕ) (hR : IsRandomOutputIndex μ R L γ N)
    (hRind : IndepFun R (fun ω k => ξ k ω) μ) :
    Integrable (fun ω => ‖g (x (R ω) ω)‖ ^ 2) μ ∧
    1 / L * ∫ ω, ‖g (x (R ω) ω)‖ ^ 2 ∂μ ≤
      (Df f x1 fstar L ^ 2 + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) /
        ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by sorry

end GhadimiLan.RSG
