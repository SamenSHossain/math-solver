import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
namespace StrategicPolicy.StochasticOpt
/-- `γ = 0.1` (§3, p. 5). -/
noncomputable def γ0 : ℝ := 1 / 10
/-- `P(x) = (0.1, 0.4, 0.5)` for `x = 1, 2, 3`, i.e. indices `0, 1, 2`. -/
noncomputable def p0 : Fin 3 → ℝ := ![1 / 10, 2 / 5, 1 / 2]
/-- `P(y = 1 | x) = (1.0, 0.7, 0.4)` for `x = 1, 2, 3`. -/
noncomputable def q0 : Fin 3 → ℝ := ![1, 7 / 10, 2 / 5]
/-- The cost matrix of p. 5: row `i` is the origin `x_i`, column `j` the destination `x_j`. -/
noncomputable def c0 : Fin 3 → Fin 3 → ℝ :=
  ![![0, 0, 0], ![3 / 10, 0, 0], ![6 / 5, 3 / 10, 0]]
end StrategicPolicy.StochasticOpt
