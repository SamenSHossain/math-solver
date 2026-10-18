**Complete proof (no `sorry`, standard axioms only).** Every policy in the printed family attains the universal upper bound $0.6$ on the strategic utility, and individuals starting at $x_2$ move to $x_1$ (including at the tie $\pi(x_2)=0.7$, by the outcome tie-break).

Notation: p = (1/10, 2/5, 1/2), q = (1, 7/10, 2/5), γ = 1/10, c is the given 3x3 cost matrix, and β = MonotoneBinary.br c q ρ. All helper lemmas are in namespace StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_optimal_family.

1. Membership and specification (mb_br_mem, nm_br_mem, mb_br_spec, nm_br_spec). Both br functions are `min'` of a filtered Finset, so `Finset.min'_mem` puts MonotoneBinary.br in bestOutcome and NonMonotone.br in preferredSet. Unfolding bestOutcome/argmax (or preferredSet) and rewriting with `Finset.mem_filter` gives two facts:
   - for every l, ρ l − c i l ≤ ρ β_i − c i β_i;
   - for every l in argmax c ρ i, q l ≤ q β_i.
   For NonMonotone.br the second fact holds for every l in bestSet c ρ i.

2. Constants and eq_zero_of_q. q_vals, p_vals and γ_val record the numeric values (by simp or rfl). eq_zero_of_q: if q 0 ≤ q k then k = 0. Proof by fin_cases on k; the cases k = 1 and k = 2 would need 1 ≤ 7/10 or 1 ≤ 2/5.

3. (L1) mb_br_two: for ρ ∈ Policies 3, β_2 = 2. Take l = 2 in the first fact: ρ 2 ≤ ρ β_2 − c 2 β_2. If β_2 = 0 this gives ρ 2 ≤ ρ 0 − 6/5; if β_2 = 1 it gives ρ 2 ≤ ρ 1 − 11/10. Since 0 ≤ ρ 2 and ρ 0, ρ 1 ≤ 1, both are impossible (fin_cases after generalizing β_2, then linarith).

4. qterm_le: for every k, (q k − γ)·ρ k ≤ 9/10. Here q k − γ ∈ {9/10, 3/5, 3/10} and 0 ≤ ρ k ≤ 1 (fin_cases, then nlinarith).

5. (L2) u_le: u ρ ≤ 6/10 for every ρ ∈ Policies 3.
   - Expand the sum with Fin.sum_univ_three, substitute β_2 = 2, and regroup with ring: u ρ = p0·X0 + p1·X1 + p2·((q 2 − γ)·ρ 2), where X_i = (q β_i − γ)·ρ β_i.
   - Bounds: X0 ≤ 9/10 and X1 ≤ 9/10 (qterm_le), and (q 2 − γ)·ρ 2 = (3/10)·ρ 2 ≤ 3/10.
   - Substituting the p values, linarith gives u ρ ≤ 9/100 + 36/100 + 15/100 = 6/10.

6. (L3) mb_br_eq_zero: assume π ∈ Policies 3, π 0 = 1, π 1 ≤ 7/10, π 2 = 1. Then for i ≠ 2, β_i = 0.
   - First show 0 ∈ argmax c π i, checking all (i, l) by fin_cases, simp [c] and linarith:
     - i = 0: π 0 − c 0 0 = 1, which is at least π 1 − 1/5 and π 2 − 3/10 = 7/10.
     - i = 1: π 0 − c 1 0 = 7/10, which is at least π 1 (by h1) and π 2 − 7/10 = 3/10.
   - The second fact of step 1 then gives q 0 ≤ q β_i, so β_i = 0 by eq_zero_of_q.
   - The tie case π 1 = 7/10 is covered automatically by the outcome tie-break.
   - nm_br_one_eq_zero runs the same argument with bestSet/preferredSet and shows NonMonotone.br c q π 1 = 0.

7. u_eq: under the same hypotheses, u π = 6/10. Expand the sum, substitute β_0 = β_1 = 0 and β_2 = 2, then the values of p, q, γ and π 0 = π 2 = 1: (1/10)(9/10) + (2/5)(9/10) + (1/2)(3/10) = 6/10, closed by norm_num.

8. Main theorem `solution` (top level, under `open StrategicPolicy.NonMonotone in`):
   - The second conjunct is nm_br_one_eq_zero.
   - For IsMaxOn, rewrite with isMaxOn_iff, take any ρ ∈ Policies 3, rewrite u π = 6/10 (u_eq), and conclude with u_le ρ.