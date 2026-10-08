import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Eq. (2.12) (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1 b), p. 7): for a convex
`f ∈ C^{1,1}_L(ℝⁿ)` (`L > 0`) with gradient map `g = ∇f` and a point `x*` with
`∇f(x*) = 0`, every `y` satisfies `(1/L)‖∇f(y)‖² ≤ ⟨∇f(y), y − x*⟩`. The paper states it at
the iterate `y = x_k`; the claim does not depend on how `y` was produced. -/
theorem eq_2_12 {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (hconv : ConvexOn ℝ Set.univ f) (xstar : E n) (hxstar : g xstar = 0) (y : E n) :
    1 / L * ‖g y‖ ^ 2 ≤ ⟪g y, y - xstar⟫_ℝ := by sorry

end GhadimiLan.RSG
