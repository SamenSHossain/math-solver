import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem yangMills_eq_boundaryChernSimons_iff {n : ℕ} (a b : R4) (hab : ∀ μ, a μ < b μ)
    (A : Connection n) (hA : IsSUConnection A) :
    (yangMills a b A = -(boundaryChernSimons a b A).re ↔
        ∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∧
      (yangMills a b A = (boundaryChernSimons a b A).re ↔
        ∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x)) := by sorry

end UhlenbeckGauge
