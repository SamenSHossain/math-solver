import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

namespace StrategicPolicy.NonMonotone

/-- Section 5, page 9: the example's cost violates outcome monotonicity. -/
theorem cost_not_om : ¬ StrategicPolicy.StochasticOpt.OMCost q c := by sorry

end StrategicPolicy.NonMonotone
