import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

namespace StrategicPolicy.NonMonotone

/-- Section 5, page 9: each policy in the printed family is optimal and moves the second mass to the first feature. -/
theorem optimal_family (π : Fin 3 → ℝ) (hπ : π ∈ StrategicPolicy.MonotoneBinary.Policies 3)
    (h0 : π 0 = 1) (h1 : π 1 ≤ 7 / 10) (h2 : π 2 = 1) :
    IsMaxOn (StrategicPolicy.MonotoneBinary.u p q γ c) (StrategicPolicy.MonotoneBinary.Policies 3) π ∧ br c q π 1 = 0 := by sorry

end StrategicPolicy.NonMonotone
