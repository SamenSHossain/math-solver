import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Eq. (3.6) (Bubeck, arXiv:1405.4980v2, p. 269): the gradient of a convex β-smooth `f` on `ℝⁿ`
(β > 0) is co-coercive, `(∇f(x) − ∇f(y))⊤(x − y) ≥ (1/β)‖∇f(x) − ∇f(y)‖²` for all `x, y`. -/
theorem eq_3_6 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    1 / β * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ := by sorry

end ConvexOptAlg.SmoothGD
