import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

/-- The Chern–Simons boundary term depends only on the boundary data of the connection
(Uhlenbeck, *Equations of Gauge Theory*, notes by Fredrickson, §3.1, proof of Proposition 3.1.1,
p. 31: the lower bound for the Yang–Mills functional is "a term depending only on the topology
of the `G`-bundle `P` and the boundary data of the connection"). If `a ≤ b` and two smooth
`SU(n)`-connections agree at every point of the boundary of the box `[a, b]`, then their
Chern–Simons boundary integrals `∫_{∂[a,b]} CS` coincide. -/
theorem boundaryChernSimons_eq_of_eq_on_boundary {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A B : Connection n) (hA : IsSUConnection A) (hB : IsSUConnection B)
    (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x) :
    boundaryChernSimons a b A = boundaryChernSimons a b B := by sorry

end UhlenbeckGauge
