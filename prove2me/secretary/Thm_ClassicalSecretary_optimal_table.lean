import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem optimal_table :
    (successProb 1 (cutoffRule 1) = optimalProb 1 ∧ optimalProb 1 = 1) ∧
    (successProb 2 (cutoffRule 1) = optimalProb 2 ∧ optimalProb 2 = 1 / 2) ∧
    (successProb 3 (cutoffRule 2) = optimalProb 3 ∧ optimalProb 3 = 1 / 2) ∧
    (successProb 4 (cutoffRule 2) = optimalProb 4 ∧ optimalProb 4 = 11 / 24) ∧
    (successProb 5 (cutoffRule 3) = optimalProb 5 ∧ optimalProb 5 = 13 / 30) ∧
    (successProb 6 (cutoffRule 3) = optimalProb 6 ∧ optimalProb 6 = 77 / 180) ∧
    (successProb 7 (cutoffRule 3) = optimalProb 7 ∧ optimalProb 7 = 29 / 70) ∧
    (successProb 8 (cutoffRule 4) = optimalProb 8 ∧ optimalProb 8 = 459 / 1120) ∧
    (successProb 9 (cutoffRule 4) = optimalProb 9 ∧ optimalProb 9 = 341 / 840) ∧
    (successProb 10 (cutoffRule 4) = optimalProb 10 ∧ optimalProb 10 = 3349 / 8400) := by sorry

end ClassicalSecretary
