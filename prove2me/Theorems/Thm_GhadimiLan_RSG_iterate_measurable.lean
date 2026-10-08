import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Measurability of the RSG iterates (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1,
p. 7: "the search point `x_k` is a function of the history `ξ_[k−1]`"): if the oracle `G` is
Borel and the noise `ξ_k` is `ℱ_k`-measurable for every `k ≥ 1`, then along an RSG run the
iterate `x_k` is `ℱ_{k-1}`-measurable for every `k ≥ 1` (`x_1 = x1` is constant, hence
`ℱ_0`-measurable). -/
theorem iterate_measurable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n)
    (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ)
    (hξ : ∀ k : ℕ, 1 ≤ k → Measurable[ℱ k] (ξ k))
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (k : ℕ) (hk : 1 ≤ k) :
    Measurable[ℱ (k - 1)] (x k) := by sorry

end GhadimiLan.RSG
