import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Second-moment bound along an RSG run (Ghadimi & Lan, arXiv:1309.5549v1, proof of
Theorem 2.1, p. 7, where `E‖∇f(x_k)‖²` is used; the paper does not state integrability):
for `f ∈ C^{1,1}_L(ℝⁿ)`, a Borel oracle `G` and an RSG run under Assumption A1, `‖∇f(x_k)‖²`
is integrable for every `k ≥ 1`. The proof is an induction along the recursion:
`‖∇f(x_{k+1})‖ ≤ (1 + L|γ_k|)‖∇f(x_k)‖ + L|γ_k|‖δ_k‖` with `‖δ_k‖ ∈ L²` by (1.3), and
`∇f(x_1)` is constant. -/
theorem grad_sq_integrable {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ := by sorry

end GhadimiLan.RSG
