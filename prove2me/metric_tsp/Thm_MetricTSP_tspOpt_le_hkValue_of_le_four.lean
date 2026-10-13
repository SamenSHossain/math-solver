import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem tspOpt_le_hkValue_of_le_four (n : ℕ) (hn : 3 ≤ n) (hn4 : n ≤ 4)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ hkValue c := by sorry

end MetricTSP
