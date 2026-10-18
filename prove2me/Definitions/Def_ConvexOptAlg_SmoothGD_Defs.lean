import Mathlib

namespace ConvexOptAlg.SmoothGD

/-- β-smoothness (Bubeck, arXiv:1405.4980v2, §3.2, p. 266): `f : ℝⁿ → ℝ` is differentiable with
gradient map `g` (`∇f(x) = g x` for every `x`), with `β ≥ 0` and gradient β-Lipschitz,
`‖∇f(x) − ∇f(y)‖ ≤ β‖x − y‖` for all `x, y`. Continuity of the gradient (the book's
"continuously differentiable") follows from the Lipschitz bound. This is the book's definition;
the quadratic upper bound (3.4) is a consequence (Lemma 3.4), not the definition. -/
def IsBetaSmooth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) : Prop :=
  0 ≤ β ∧ (∀ x, HasGradientAt f (g x) x) ∧ ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖

/-- A run of gradient descent (Bubeck, arXiv:1405.4980v2, Eq. (3.1), p. 262) with gradient map
`g` and fixed step size `η > 0`: `x (t + 1) = x t − η • g (x t)` for every `t ≥ 1`. The book's
first iterate `x₁` is `x 1`; index `0` is unused and carries no hypothesis. -/
def IsGDRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (η : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  0 < η ∧ ∀ t : ℕ, 1 ≤ t → x (t + 1) = x t - η • g (x t)

end ConvexOptAlg.SmoothGD
