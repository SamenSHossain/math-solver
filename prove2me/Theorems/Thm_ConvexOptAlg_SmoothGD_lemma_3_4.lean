import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Lemma 3.4 (Bubeck, arXiv:1405.4980v2, p. 267): for a β-smooth `f` on `ℝⁿ` with gradient map
`g`, `|f(x) − f(y) − ∇f(y)⊤(x − y)| ≤ (β/2)‖x − y‖²` for all `x, y`. No convexity. -/
theorem lemma_3_4 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    |f x - f y - ⟪g y, x - y⟫_ℝ| ≤ β / 2 * ‖x - y‖ ^ 2 := by sorry

end ConvexOptAlg.SmoothGD
