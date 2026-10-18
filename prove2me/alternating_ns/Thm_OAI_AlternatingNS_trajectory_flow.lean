import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Global particle trajectories.** A smooth, rapidly decaying velocity field (in particular
bounded and uniformly Lipschitz in space) has, from every initial point, a trajectory defined for
all `t ≥ 0`, and it is unique on `[0, ∞)`. -/
theorem trajectory_flow (U : Velocity) (hU : Smooth U) (hr : Rapid U) :
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory U a (X a)) ∧
      (∀ a γ, IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) := by
  sorry

end AlternatingNS
end OAI
