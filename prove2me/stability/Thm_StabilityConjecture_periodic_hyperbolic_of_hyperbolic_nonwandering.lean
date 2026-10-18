import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

/-- **Periodic orbits inside a hyperbolic nonwandering set are hyperbolic.** If `Ω(f)` is a
hyperbolic set of `f`, then every periodic point of `f` is a hyperbolic periodic point: its orbit
is a finite invariant subset of `Ω(f)`, and the hyperbolic splitting of `Ω(f)` restricts to it. -/
theorem periodic_hyperbolic_of_hyperbolic_nonwandering {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {r : ℕ} (f : Diff n M r) (hΩ : IsHyperbolicSet f (PughClosingLemma.nonwanderingSet f)) :
    ∀ p ∈ Function.periodicPts f, IsHyperbolicPeriodicPt f p := by sorry

end StabilityConjecture
