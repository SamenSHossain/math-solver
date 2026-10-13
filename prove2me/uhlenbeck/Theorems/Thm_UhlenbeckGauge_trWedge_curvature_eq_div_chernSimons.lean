import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem trWedge_curvature_eq_div_chernSimons {n : ℕ} (A : Connection n)
    (hA : IsSUConnection A) (x : R4) :
    trWedge (curvature A x) =
      ∑ μ : Fin 4, fderiv ℝ (chernSimonsCurrent A μ) x (Pi.single μ 1) := by sorry

end UhlenbeckGauge
