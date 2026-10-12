import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem exp_neg_one_le_optimalProb (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-1) ≤ optimalProb n := by sorry

end ClassicalSecretary
