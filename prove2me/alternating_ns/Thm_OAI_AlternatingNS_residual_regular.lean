import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **The Navier–Stokes residual inherits regularity.** If `U` is smooth, rapidly decaying and
spatially supported in a compact set `K`, then so is the force `f = ∂ₜU + (U·∇)U − νΔU`. -/
theorem residual_regular (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U) :
    Smooth (residual ν U) ∧ SupportedIn (residual ν U) K ∧ Rapid (residual ν U) := by
  sorry

end AlternatingNS
end OAI
