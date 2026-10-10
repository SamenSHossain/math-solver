import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem selfDual_absolute_minimizer {n : ℕ} (a b : R4) (A B : Connection n)
    (hA : IsSUConnection A) (hB : IsSUConnection B)
    (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x)
    (hdual : (∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∨
      (∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x))) :
    yangMills a b A ≤ yangMills a b B := by sorry

end UhlenbeckGauge
