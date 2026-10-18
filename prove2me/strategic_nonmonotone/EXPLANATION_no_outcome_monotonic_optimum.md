**Complete, self-contained proof (no `sorry`, standard axioms only; imports no other platform theorem).** The utility is bounded by $0.6$ on all of $[0,1]^3$; the policy $(1,0,1)$ attains it, and any maximizer must have $\pi(x_3)=1$ and send $x_2$ to $x_1$, which forces $\pi(x_2)\le0.7<\pi(x_3)$ and so violates outcome monotonicity.

The proof is self-contained: it imports only Mathlib and the two NonMonotone Definitions files. Throughout, B(ρ,i) := MonotoneBinary.br c q ρ i, with p = (1/10, 2/5, 1/2), q = (1, 7/10, 2/5), γ = 1/10 and c the given matrix.

Basic facts about B, proved for any ρ and i:
- br_mem: B(ρ,i) ∈ bestOutcome c q ρ i. Proof: unfold br, then use Finset.min'_mem.
- br_argmax: for every l, ρ l − c i l ≤ ρ B − c i B. This comes from Finset.mem_filter applied first to bestOutcome and then to argmax.
- br_eq_zero: if 0 ∈ argmax c ρ i, then B(ρ,i) = 0. The outcome tie-break gives q 0 ≤ q B, i.e. 1 ≤ q B. Case-splitting on B (fin_cases), B = 1 gives 1 ≤ 7/10 and B = 2 gives 1 ≤ 2/5, both false.

(L1) br_two: for ρ ∈ Policies 3, B(ρ,2) = 2. Apply br_argmax with i = l = 2, so ρ 2 ≤ ρ B − c 2 B. If B = 0 this reads ρ 2 ≤ ρ 0 − 6/5. If B = 1 it reads ρ 2 ≤ ρ 1 − 11/10. Both contradict 0 ≤ ρ_k ≤ 1 (linarith).

term_bound: for ρ ∈ Policies 3 and every k, 0 ≤ (q k − γ) ρ k ≤ 9/10. This is a case split on k, since q − γ = (9/10, 3/5, 3/10).

u_eq: expanding with Fin.sum_univ_three and the values of p gives u ρ = 1/10·T0 + 2/5·T1 + 1/2·T2, where Ti = (q B(ρ,i) − γ) ρ(B(ρ,i)).

(L2) u_le: for ρ ∈ Policies 3, u ρ ≤ 6/10. By (L1), T2 = (3/10) ρ 2 ≤ 3/10. By term_bound, T0 ≤ 9/10 and T1 ≤ 9/10. So u ρ ≤ 9/100 + 36/100 + 15/100 = 6/10 (linarith).

(L3) Witness π₀ = ![1, 0, 1]:
- It lies in Policies 3 (fin_cases and simp).
- 0 ∈ argmax c π₀ 0: checking each l, the values are 1 ≥ 1, −1/5 and 7/10.
- 0 ∈ argmax c π₀ 1: the values are 7/10 ≥ 7/10, 0 and 3/10.
- So by br_eq_zero, B(π₀,0) = B(π₀,1) = 0, and by (L1), B(π₀,2) = 2.
- Hence u π₀ = 1/10·9/10 + 2/5·9/10 + 1/2·3/10 = 6/10.
- With (L2) and isMaxOn_iff, π₀ is a maximizer of u on Policies 3. This proves the existence half.

Exclusion (not_om): suppose π ∈ Policies 3 is a maximizer and OMPolicy q π.
- Optimality gives 6/10 = u π₀ ≤ u π = 1/10·T0 + 2/5·T1 + 1/2·(3/10)π 2.
- Since T0, T1 ≤ 9/10 and π 2 ≤ 1, linarith gives π 2 ≥ 1 and T1 ≥ 9/10.
- Write b = B(π,1), keep the fact br_argmax π 1 1 (π 1 − c 1 1 ≤ π b − c 1 b), and split on b:
  - b = 1: T1 = (3/5) π 1 ≤ 3/5 < 9/10. Contradiction.
  - b = 2: T1 = (3/10) π 2 ≤ 3/10. Contradiction.
  - b = 0: the argmax fact reads π 1 ≤ π 0 − 3/10 ≤ 7/10 < 1 ≤ π 2, so π 1 < π 2. OMPolicy applied to (1, 2) then gives q 1 < q 2, i.e. 7/10 < 2/5, which is false.

Final theorem `solution`: the existence half uses the witness π₀ with π₀_mem and π₀_isMaxOn; the second half is not_om.