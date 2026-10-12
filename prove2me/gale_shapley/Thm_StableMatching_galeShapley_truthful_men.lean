import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_truthful_men {n : ℕ} (I I' : Instance n) (m : Fin n)
    (hdev : I.MenDeviation I' {m}) (μ μ' : Matching n)
    (hμ : I.IsGSOutcome μ) (hμ' : I'.IsGSOutcome μ') :
    ¬ I.manPrefers m (μ' m) (μ m) := by sorry

end StableMatching
