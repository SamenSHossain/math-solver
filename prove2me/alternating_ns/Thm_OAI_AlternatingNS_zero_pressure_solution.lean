import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Zero-pressure classical solution in the energy class.** A smooth, rapidly decaying,
compactly supported, divergence-free velocity field starting from rest solves the forced
Navier–Stokes equation with zero pressure and force `f = ∂ₜU + (U·∇)U − νΔU`, and lies in the
energy class. -/
theorem zero_pressure_solution (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U) (h0 : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    NavierStokes ν (residual ν U) U (fun _ _ => 0) ∧ EnergyClass U (fun _ _ => 0) := by
  sorry

end AlternatingNS
end OAI
