import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

namespace StrategicPolicy.NonMonotone

/-- Section 5, page 9: an optimum exists, and none obeys outcome monotonicity. -/
theorem no_outcome_monotonic_optimum :
    (∃ π : Fin 3 → ℝ, π ∈ StrategicPolicy.MonotoneBinary.Policies 3 ∧ IsMaxOn (StrategicPolicy.MonotoneBinary.u p q γ c) (StrategicPolicy.MonotoneBinary.Policies 3) π) ∧
    (∀ π : Fin 3 → ℝ, π ∈ StrategicPolicy.MonotoneBinary.Policies 3 → IsMaxOn (StrategicPolicy.MonotoneBinary.u p q γ c) (StrategicPolicy.MonotoneBinary.Policies 3) π →
      ¬ StrategicPolicy.MonotoneBinary.OMPolicy q π) := by sorry

end StrategicPolicy.NonMonotone
