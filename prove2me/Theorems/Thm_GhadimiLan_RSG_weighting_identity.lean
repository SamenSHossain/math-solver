import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- The weighting identity in the proof of Theorem 2.1 (Ghadimi & Lan, arXiv:1309.5549v1, p. 7,
display after "Dividing both sides"): if the output index `R` has the mass function (2.3) on
`{1, …, N}` and is independent of the noise sequence `(ξ_k)`, and each `‖∇f(x_k)‖²`
(`k = 1, …, N`) is integrable, then `‖∇f(x_R)‖²` is integrable and
`E‖∇f(x_R)‖² = Σ_{k=1}^N (2γ_k − Lγ_k²) E‖∇f(x_k)‖² / Σ_{k=1}^N (2γ_k − Lγ_k²)`. -/
theorem weighting_identity {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (hξ : ∀ k, Measurable (ξ k))
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (R : Ω → ℕ) (hR : IsRandomOutputIndex μ R L γ N)
    (hRind : IndepFun R (fun ω k => ξ k ω) μ)
    (hint : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ) :
    Integrable (fun ω => ‖g (x (R ω) ω)‖ ^ 2) μ ∧
    ∫ ω, ‖g (x (R ω) ω)‖ ^ 2 ∂μ =
      (∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ) /
        ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by sorry

end GhadimiLan.RSG
