import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic
import Theorems.Thm_StabilityConjecture_mane_C1_stability

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open StabilityConjecture ClosingLemma

theorem solution {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : Diff n M 1) (hf : IsStructurallyStable 1 f) :
    closure (Function.periodicPts f) = PughClosingLemma.nonwanderingSet f :=
  (mane_C1_stability f hf).2
