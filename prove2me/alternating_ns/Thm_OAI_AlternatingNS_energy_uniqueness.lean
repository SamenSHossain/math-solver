import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Weak–strong uniqueness.** Let `U` be a smooth, rapidly decaying, compactly supported
zero-pressure solution of the forced Navier–Stokes equation with `ν > 0` in the energy class.
Every classical solution `(v, p)` with the same force and zero initial velocity in the
competitor energy class coincides with `(U, 0)` for all `t ≥ 0`. -/
theorem energy_uniqueness (ν : ℝ) (hν : 0 < ν) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U)
    (hNS : NavierStokes ν (residual ν U) U (fun _ _ => 0)) (hE : EnergyClass U (fun _ _ => 0))
    (v : Velocity) (p : Pressure) (hv : NavierStokes ν (residual ν U) v p)
    (hc : CompetitorEnergyClass v p) :
    ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = 0 := by
  sorry

end AlternatingNS
end OAI
