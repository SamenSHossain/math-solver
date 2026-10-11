import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

/-- **The open case of the `C^r` stability conjecture: `r ≥ 2`.** A `C^r` structurally stable
diffeomorphism of a closed manifold, `r ≥ 2`, satisfies Axiom A. -/
theorem cr_stability_conjecture_two_le {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 2 ≤ r) (f : Diff n M r) (hf : IsStructurallyStable r f) :
    SatisfiesAxiomA f := by sorry

end StabilityConjecture
