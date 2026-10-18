import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem tspOpt_le_three_halves_hkValue (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 3 / 2 * hkValue c := by sorry

end MetricTSP
