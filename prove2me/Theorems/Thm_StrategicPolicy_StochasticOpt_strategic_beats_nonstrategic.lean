import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Example
namespace StrategicPolicy.StochasticOpt
theorem strategic_beats_nonstrategic :
    uNS p0 q0 γ0 (fun _ => 1) < u p0 q0 γ0 c0 ![1, 7 / 10, 0] ∧
      u p0 q0 γ0 c0 (fun _ => 1) < u p0 q0 γ0 c0 ![1, 7 / 10, 0] := by sorry
end StrategicPolicy.StochasticOpt
