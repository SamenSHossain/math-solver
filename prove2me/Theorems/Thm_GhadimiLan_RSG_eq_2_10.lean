import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Eq. (2.10) (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1, p. 7): under Assumption
A1 along an RSG run, for every `k ≥ 1` the scalar `⟨∇f(x_k), δ_k⟩` (with
`δ_k = G(x_k, ξ_k) − ∇f(x_k)`) is integrable and `E[⟨∇f(x_k), δ_k⟩ | ℱ_{k-1}] = 0` almost surely.
No integrability of `∇f(x_k)` is assumed: it is part of the claim. -/
theorem eq_2_10 {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ) μ ∧
    μ[fun ω => ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ | ℱ (k - 1)] =ᵐ[μ] 0 := by sorry

end GhadimiLan.RSG
