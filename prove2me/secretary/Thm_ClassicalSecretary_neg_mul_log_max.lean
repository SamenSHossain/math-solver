import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem neg_mul_log_max :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, -x * Real.log x ≤ Real.exp (-1)) ∧
    -Real.exp (-1) * Real.log (Real.exp (-1)) = Real.exp (-1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, -x * Real.log x = Real.exp (-1) → x = Real.exp (-1)) := by sorry

end ClassicalSecretary
