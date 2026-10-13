import Mathlib

import Mathlib

theorem lindelof_hypothesis :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta (1/2 + t * Complex.I)‖ ≤ C * t ^ eps := by
  sorry