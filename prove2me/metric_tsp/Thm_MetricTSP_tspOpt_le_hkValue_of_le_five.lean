import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem tspOpt_le_hkValue_of_le_five (n : ℕ) (hn : 3 ≤ n) (hn5 : n ≤ 5)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ hkValue c := by sorry

end MetricTSP
