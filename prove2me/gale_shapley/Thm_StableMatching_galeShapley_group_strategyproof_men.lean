import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_group_strategyproof_men {n : ℕ} (I I' : Instance n) (C : Finset (Fin n))
    (hC : C.Nonempty) (hdev : I.MenDeviation I' C) (μ μ' : Matching n)
    (hμ : I.IsGSOutcome μ) (hμ' : I'.IsGSOutcome μ') :
    ¬ ∀ m ∈ C, I.manPrefers m (μ' m) (μ m) := by sorry

end StableMatching
