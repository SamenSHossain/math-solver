import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem integral_trWedge_eq_boundaryChernSimons {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A : Connection n) (hA : IsSUConnection A) :
    ∫ x in Set.Icc a b, trWedge (curvature A x) = boundaryChernSimons a b A := by sorry

end UhlenbeckGauge
