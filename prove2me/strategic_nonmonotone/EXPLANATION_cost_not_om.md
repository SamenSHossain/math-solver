**Complete proof (no `sorry`, standard axioms only).** The example's cost is not outcome monotonic because moving from $x_1$ down to the lower-outcome $x_2$ is not free.

Claim: the example's cost c is not outcome monotonic, i.e. ¬ OMCost q c.

Proof. Suppose OMCost q c holds. Its third conjunct says that for all i ≠ j, q j < q i ↔ c i j = 0. Take i = 0 and j = 1 (0 ≠ 1 in Fin 3, shown by `decide`). The forward direction then gives q 1 < q 0 → c 0 1 = 0.

Helper lemma q_one_lt_q_zero: q 1 = 7/10 < 1 = q 0. Proved by `simp [q]` to evaluate the ![...] entries, then `norm_num`.

So c 0 1 = 0. But helper lemma c_zero_one says c 0 1 = 1/5, proved by `simp [c]` on the !![...] matrix entry. Rewriting gives 1/5 = 0, which `norm_num` refutes. Contradiction. ∎

In Lean: `rintro ⟨-, -, h3⟩`, then `have h := (h3 0 1 (by decide)).1 q_one_lt_q_zero`, then `rw [c_zero_one] at h`, then `norm_num at h`. The helper lemmas are in namespace StrategicPolicy.NonMonotone.Sol_StrategicPolicy_NonMonotone_cost_not_om. `theorem solution` is top-level, and its statement uses fully qualified names. The file uses no sorry, axiom or native_decide.