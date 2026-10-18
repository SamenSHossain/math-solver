import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem exists_optimal_cutoffRule (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ n ∧ successProb n (cutoffRule r) = optimalProb n := by sorry

end ClassicalSecretary
