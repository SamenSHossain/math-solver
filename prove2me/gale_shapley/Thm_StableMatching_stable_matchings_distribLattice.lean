import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem stable_matchings_distribLattice {n : ℕ} (I : Instance n) :
    ∃ L : DistribLattice {μ : Matching n // I.IsStable μ},
      ∀ μ ν : {μ : Matching n // I.IsStable μ},
        L.le μ ν ↔ ∀ m : Fin n, I.manRank m (μ.1 m) ≤ I.manRank m (ν.1 m) := by sorry

end StableMatching
