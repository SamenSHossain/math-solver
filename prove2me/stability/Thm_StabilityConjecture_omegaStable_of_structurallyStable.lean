import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

/-- **Structural stability implies `Ω`-stability.** A topological conjugacy `h ∘ f = g ∘ h` of the
whole manifold maps the nonwandering set `Ω(f)` homeomorphically onto `Ω(g)`, so a `C^r`
structurally stable diffeomorphism is `C^r` `Ω`-stable. -/
theorem omegaStable_of_structurallyStable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (f : Diff n M r) (hf : IsStructurallyStable r f) :
    IsOmegaStable r f := by sorry

end StabilityConjecture
