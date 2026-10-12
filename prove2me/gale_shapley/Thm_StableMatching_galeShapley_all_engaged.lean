import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_all_engaged {n : ℕ} (I : Instance n) :
    ∀ m : Fin n, (I.gsRun (n ^ 2)).IsEngaged m := by sorry

end StableMatching
