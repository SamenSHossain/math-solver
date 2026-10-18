import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem successProb_cutoffRule (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n) :
    successProb n (cutoffRule r) =
      ((r : ℝ) - 1) / (n : ℝ) * ∑ i ∈ Icc r n, 1 / ((i : ℝ) - 1) := by sorry

end ClassicalSecretary
