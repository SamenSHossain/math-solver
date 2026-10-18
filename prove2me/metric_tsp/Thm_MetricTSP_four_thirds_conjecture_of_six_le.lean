import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem four_thirds_conjecture_of_six_le (n : ℕ) (hn : 6 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 4 / 3 * hkValue c := by sorry

end MetricTSP
