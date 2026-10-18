import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Core construction.** A computable compiler of velocity programs and a compact set `K`
such that, for every well-formed machine `M` and valid input `w`, the compiled velocity field
is smooth, supported in `K`, rapidly decaying, divergence-free, starts from rest, and the
trajectory of the observed particle `(-1,0,0)` enters `{x₁ > 0}` exactly when `M` halts on `w`. -/
theorem velocity_construction :
    ∃ (U : Machine × List ℕ → Velocity) (compileVelocity : Machine × List ℕ → FieldProgram)
      (K : Set Space),
      Computable compileVelocity ∧ IsCompact K ∧
      ∀ (M : Machine) (w : List ℕ), M.WellFormed → M.ValidInput w →
        ProgramFor (compileVelocity (M, w)) (U (M, w)) ∧
        Smooth (U (M, w)) ∧ SupportedIn (U (M, w)) K ∧ Rapid (U (M, w)) ∧
        (∀ x, U (M, w) 0 x = 0) ∧
        (∀ t, 0 ≤ t → ∀ x, div (U (M, w)) t x = 0) ∧
        ∀ γ : ℝ → Space, IsTrajectory (U (M, w)) observedParticle γ →
          ((∃ t : ℝ, 0 ≤ t ∧ 0 < γ t 0) ↔ M.Halts w) := by
  sorry

end AlternatingNS
end OAI
