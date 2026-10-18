import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

/-- The curvature of an `SU(n)`-connection is, at every point, an antisymmetric `su(n)`-valued
two-form (Uhlenbeck, *Equations of Gauge Theory*, notes by Fredrickson, §3.1, p. 31, where the
curvature `F_A` is treated as a Lie-algebra-valued two-form in Lemma 3.1.2): for every `x`,
`(F_A)_{νμ}(x) = −(F_A)_{μν}(x)`, and each `(F_A)_{μν}(x)` is skew-Hermitian with trace zero. -/
theorem curvature_isAntisymm_isSuNValued {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (x : R4) : IsAntisymm (curvature A x) ∧ IsSuNValued (curvature A x) := by sorry

end UhlenbeckGauge
