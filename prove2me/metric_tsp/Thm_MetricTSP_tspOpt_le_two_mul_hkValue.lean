import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem tspOpt_le_two_mul_hkValue (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 2 * (1 - 1 / (n : ℝ)) * hkValue c := by sorry

end MetricTSP
