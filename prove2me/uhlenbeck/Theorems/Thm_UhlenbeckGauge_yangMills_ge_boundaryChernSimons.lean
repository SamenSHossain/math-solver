import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem yangMills_ge_boundaryChernSimons {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A : Connection n) (hA : IsSUConnection A) :
    -(boundaryChernSimons a b A).re ≤ yangMills a b A ∧
      (boundaryChernSimons a b A).re ≤ yangMills a b A := by sorry

end UhlenbeckGauge
