import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem tendsto_successProb_cutoffRule (r : ℕ → ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hr : ∀ᶠ n in atTop, 1 ≤ r n ∧ r n ≤ n)
    (hlim : Tendsto (fun n : ℕ => (r n : ℝ) / (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => successProb n (cutoffRule (r n))) atTop
      (𝓝 (-x * Real.log x)) := by sorry

end ClassicalSecretary
