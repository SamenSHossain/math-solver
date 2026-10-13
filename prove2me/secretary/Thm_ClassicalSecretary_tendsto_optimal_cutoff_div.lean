import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem tendsto_optimal_cutoff_div (r : ℕ → ℕ)
    (hr : ∀ n : ℕ, 1 ≤ n →
      1 ≤ r n ∧ r n ≤ n ∧ successProb n (cutoffRule (r n)) = optimalProb n) :
    Tendsto (fun n : ℕ => (r n : ℝ) / (n : ℝ)) atTop (𝓝 (Real.exp (-1))) := by sorry

end ClassicalSecretary
