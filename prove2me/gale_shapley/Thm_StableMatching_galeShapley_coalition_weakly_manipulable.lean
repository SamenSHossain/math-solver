import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_coalition_weakly_manipulable :
    ∃ (n : ℕ) (I I' : Instance n) (C : Finset (Fin n)) (μ μ' : Matching n),
      I.MenDeviation I' C ∧ I.IsGSOutcome μ ∧ I'.IsGSOutcome μ' ∧
      (∀ m ∈ C, μ' m = μ m ∨ I.manPrefers m (μ' m) (μ m)) ∧
      ∃ m ∈ C, I.manPrefers m (μ' m) (μ m) := by sorry

end StableMatching
