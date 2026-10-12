import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem successProb_cutoffRule_one (n : ℕ) (hn : 1 ≤ n) :
    successProb n (cutoffRule 1) = 1 / (n : ℝ) := by sorry

end ClassicalSecretary
