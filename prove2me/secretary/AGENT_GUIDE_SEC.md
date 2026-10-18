# Guide for proof agents (Prove2Me workspace): Secretary problem, the 37% rule (ClassicalSecretary)

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. Run `export PATH="$HOME/.elan/bin:$PATH"` first.
- READ IN FULL FIRST: `Definitions/Def_ClassicalSecretary_Model.lean` (namespace `ClassicalSecretary`).
  - `relRank σ j := #{k | k < j ∧ σ k < σ j}`.
  - `history σ i := ((List.finRange n).take (i+1)).map (relRank σ)`.
  - `StoppingRule := List ℕ → Bool`.
  - `StopsAt s σ i := s (history σ i) = true ∧ ∀ j < i, s (history σ j) = false`.
  - `IsBest σ i := ∀ j, σ j ≤ σ i`, and `Wins s σ := ∃ i, StopsAt s σ i ∧ IsBest σ i`.
  - `successProb n s := #{σ | Wins s σ} / card (Perm (Fin n))` (reals).
  - `optimalProb n := ⨆ s, successProb n s`.
  - `cutoffRule r h := decide (r ≤ h.length) && decide (h.getLast? = some (h.length - 1))`. It accepts at time `i` iff `r ≤ i+1` and the
    current applicant is a candidate, i.e. `relRank σ i = i`.
- Theorem mirrors are in `Theorems/Thm_ClassicalSecretary_<name>.lean` (already built); do NOT edit them. Their preamble is
  `import Mathlib`, `import Definitions.Def_ClassicalSecretary_Model`, `open Finset Filter Topology`.
- Type-check a file with `./check.sh Solutions/<file>.lean`. It prints `CHECK OK` only when there are no errors and no `sorry`.
  Experiment with `lake env lean Solutions/Scratch_SEC_<yourkey>_*.lean`. NEVER run `lake build`. Never edit `Theorems/`, `Definitions/`,
  `.lake/`, or files you did not create; other agents work in parallel.

## Solution file layout (mandatory)
```lean
import Mathlib
import Definitions.Def_ClassicalSecretary_Model
-- optionally: import Theorems.Thm_ClassicalSecretary_<other milestone>   (ONLY other milestones, never the target itself)

set_option autoImplicit false

open Finset Filter Topology

namespace ClassicalSecretary.<HelperNs>
...
end ClassicalSecretary.<HelperNs>

open ClassicalSecretary in
theorem solution <binders exactly as in the target> : <conclusion exactly as in the target> := by ...
```
- `theorem solution` must be TOP-LEVEL. It must copy the target's binders and conclusion exactly; only the name changes. Check this with
  `example : (type_of% @solution) = (type_of% @ClassicalSecretary.<name>) := rfl` in a scratch copy that also imports the target's
  Theorems module.
- No `sorry`, `admit`, `native_decide`, new axioms, `unsafe`, or `implemented_by`. Keep compile time well under 120 s.
- Importing OTHER milestone theorems (`Theorems.Thm_ClassicalSecretary_*`) is allowed and encouraged. They are proved separately on the
  platform. Locally they are `sorry` stubs, so `#print axioms` will then show `sorryAx`. That is expected only when it comes from those
  imports. Do NOT import other solution files.

## Mathematics

### Track A, combinatorics (milestones `successProb_cutoffRule_one`, `successProb_cutoffRule`, `exists_optimal_cutoffRule`)
Shared library in `Solutions/Scratch_SEC_core.lean`, namespace `ClassicalSecretary.SecCore`.

1. **Lehmer code.**
   - Let `code σ : Fin n → ℕ := relRank σ` and `A n : Finset (Fin n → ℕ) := Fintype.piFinset (fun j => range (j.val+1))`.
   - `relRank σ j ≤ j`, so `code σ ∈ A n`, and `#(A n) = n!` (`Fintype.card_piFinset`, `prod_range_add_one_eq_factorial`).
   - `code` is injective. Show `σ j < σ k ↔ τ j < τ k` for all `j, k` by induction on `max j k`:
     - `{l < m | σ l < σ m}` is an initial segment of `{l < m}` in the common order of `σ` and `τ` on positions `< m`;
     - initial segments of equal size coincide;
     - then `σ ∘ τ⁻¹` is a strictly monotone bijection of `Fin n`, so it is `id`.
   - Hence `code` is a bijection onto `A n`, and for every predicate `P`: `#{σ | P (code σ)} = #{a ∈ A n | P a}`.
   - Any other proof of this transfer is fine, e.g. an inductive decomposition removing the last time step.
2. **Translating the definitions.**
   - `history σ i = hist (code σ) i` with `hist a i := ((List.finRange n).take (i+1)).map a`. Its length is `i+1` and its `getLast?` is
     `some (a i)`.
   - Candidate: `relRank σ i = i ↔ ∀ k < i, σ k < σ i`.
   - `IsBest σ i ↔ code σ i = i ∧ ∀ j > i, code σ j < j`. If the best is at `i`, no later applicant is a candidate. Conversely, by
     induction on `m ≥ i`, `σ i` is the maximum of `σ` on `[0, m]`, since a later new maximum would be a candidate.
3. **Counting lemma (independence).** Let `E` be a predicate on `Fin n → ℕ` invariant under `Function.update · j c`. Then for any
   `C ⊆ range (j+1)`, `#{a ∈ A n | E a ∧ a j ∈ C} * (j+1) = #{a ∈ A n | E a} * #C`. Split by the value of `a j`
   (`card_eq_sum_card_fiberwise`); all fibers have the same size, via the bijection `update a j c`.
4. **Facts about an arbitrary rule `s`.** Work with counts over `A n`.
   - `R i := #{a | ∀ j < i, s (hist a j) = false}` (not stopped before `i`).
   - `Q i := #{a | stopsAt s a i ∧ a i = i}`, where `stopsAt` is the `a`-version of `StopsAt`.
   - (P1) `#{wins} * n = ∑_{i<n} Q i * (i+1)`. Wins are the disjoint union over `i` of `stopsAt i ∧ a i = i ∧ ∀ j > i, a j < j`. Apply
     the counting lemma for `j = i+1, …, n-1` successively: `#{F ∧ ∀ j ∈ (i, m), a j < j} * m = #F * (i+1)`, by induction on `m`.
   - (P2) `Q i * (i+1) ≤ R i`. Use the counting lemma with `E = {∀ j < i, s (hist a j) = false}` and `C = {i}`.
   - (P3) `R (i+1) + #{stopsAt i} = R i`, so `R (i+1) + Q i ≤ R i`, and `R 0 = n!`.
   - For the cutoff rule with cutoff `r`: `stopsAt i ↔ r ≤ i+1 ∧ a i = i ∧ ∀ j < i, ¬ (r ≤ j+1 ∧ a j = j)`. So for `i + 1 ≥ r`,
     `Q i * (i+1) = R i` and `R (i+1) = R i - Q i`. For `i + 1 < r`, `Q i = 0` and `R (i+1) = R i`.
5. **Cutoff formula.** For `2 ≤ r ≤ n` and `i ≥ r-1`: `R i * i = n! * (r-1)` and `Q i = n!(r-1)/(i(i+1))`. Hence
   `successProb = ∑_{i=r-1}^{n-1} (r-1)/(i n) = ((r-1)/n) ∑_{i ∈ Icc r n} 1/(i-1)` after reindexing. For `r = 1`, the rule stops at time 0
   (`a 0 = 0`), and `successProb = 1/n`. This one can also be done directly: wins iff `σ 0` is the maximum, which happens for `(n-1)!`
   permutations.
6. **Optimality (backward induction).** Let `p i := Q i / n!` and `ρ i := R i / n!` (reals).
   - Define `V k := if n ≤ k then 0 else (1/(k+1)) * max ((k+1)/n) (V (k+1)) + (k/(k+1)) * V (k+1)`, by recursion on `n - k` or as a
     function `V : ℕ → ℝ` via `Nat.rec` on the distance to `n`.
   - Claim: `∑_{k ≤ i < n} p i (i+1)/n ≤ ρ k * V k`, by backward induction on `k`. The step uses (P2), (P3), `0 ≤ p`, and
     `0 ≤ V`:
     `p_k (k+1)/n + ρ_{k+1} V_{k+1} ≤ p_k((k+1)/n - V_{k+1}) + ρ_k V_{k+1} ≤ (ρ_k/(k+1)) max(0, (k+1)/n - V_{k+1}) + ρ_k V_{k+1} = ρ_k V_k`.
   - So `successProb n s ≤ V 0` for every rule.
   - Threshold:
     - `V (k+1) ≤ V k`.
     - The stop region `{k < n | (k+1)/n ≥ V (k+1)}` is up-closed and contains `n-1`. Let `k*` be its least element.
     - For `k ≥ k*`, `V k = 1/n + (k/(k+1)) V (k+1)`. This is the same recursion as the value from time `k` of the cutoff rule with
       `r = k*+1`, which by (P2)/(P3) equalities stops at every candidate after `k*`. For `k < k*`, `V k = V (k+1)`.
     - So `V 0 = V k* = successProb n (cutoffRule (k*+1))`.
   - Finally, `optimalProb n = ⨆ s, successProb n s ≤ V 0` (`ciSup_le`), and `≥` holds by `le_ciSup`. `BddAbove` holds because
     `successProb ≤ 1`. This gives `exists_optimal_cutoffRule` with `r = k*+1 ∈ [1, n]`.

### Track B, analysis (`neg_mul_log_max`, `tendsto_successProb_cutoffRule`, `exp_neg_one_le_optimalProb`, `tendsto_optimal_cutoff_div`, GOAL `tendsto_optimalProb`)
Import the milestone theorems `successProb_cutoffRule_one`, `successProb_cutoffRule` and `exists_optimal_cutoffRule` as needed, plus
`exp_neg_one_le_optimalProb` once you have it as a separate target. Write `g x := -x * Real.log x`; Mathlib has `Real.negMulLog`,
`Real.continuous_negMulLog`, `Real.strictConcaveOn_negMulLog`.
- `neg_mul_log_max`: use `log y ≤ y - 1` (`Real.log_le_sub_one_of_pos`) with `y = 1/(e x)`; it is strict unless `y = 1`
  (`Real.log_lt_sub_one_of_pos`). The case `x = 0` gives `g 0 = 0`.
- Harmonic bounds for `1 ≤ a ≤ n`:
  - `log(n/a) ≤ ∑_{i=a}^{n-1} 1/i`, since `log(1+1/i) ≤ 1/i`, telescoping;
  - `∑_{i=a}^{n-1} 1/i ≤ 1/a + log(n/a)`, since `1/i ≤ -log(1-1/i)` for `i ≥ 2`.
  - Hence, for `1 ≤ r ≤ n` with `a = r-1`: `g((r-1)/n) ≤ successProb n (cutoffRule r) ≤ g((r-1)/n) + 1/n`. For `r = 1` both bounds read
    `0 ≤ 1/n ≤ 0 + 1/n`.
  - Reindex `∑_{i∈Icc r n} 1/(i-1) = ∑_{i=r-1}^{n-1} 1/i`.
- `tendsto_successProb_cutoffRule`: from the two-sided bound, `(r n - 1)/n → x`, continuity of `g` on `[0,1]`, and squeeze
  (`tendsto_of_tendsto_of_tendsto_of_le_of_le'`).
- `exp_neg_one_le_optimalProb` (`V_n ≥ 1/e` for every `n ≥ 1`):
  - Trapezoid refinement: `∑_{i=a}^{n-1} 1/i ≥ log(n/a) + (1/a - 1/n)/2`, from `log(1+u) ≤ u(2+u)/(2(1+u))` for `u ≥ 0`. The difference
    has derivative `u²/(2(1+u)²) ≥ 0`. This gives `successProb ≥ g(x) + (1-x)/(2n)` with `x = a/n`.
  - Take `a = ⌈n/e⌉`, so `x ∈ [1/e, 1/e + 1/n)` and `2 ≤ a+1 ≤ n` for `n ≥ 2`. Use `g(x) ≥ 1/e - (e/2)(x - 1/e)²` for
    `x ∈ [1/e, 1]` (`g'' = -1/x ≥ -e`).
  - Then `successProb - 1/e ≥ (1/(2n))(1 - 1/e - (1+e)/n) > 0` for `n ≥ 6`.
  - For `1 ≤ n ≤ 5`, use explicit cutoffs. `n = 1`: `r = 1`, `P = 1`. `n = 2`: `r = 1`, `1/2`. `n = 3`: `r = 2`, `1/2`. `n = 4`: `r = 2`,
    `11/24`. `n = 5`: `r = 3`, `13/30`. Each exceeds `1/e`; use `Real.exp_one_gt_d9`.
  - `optimalProb n ≥ successProb n s` by `le_ciSup` with `BddAbove` (`successProb ≤ 1`).
  - Any other correct route is fine.
- `tendsto_optimal_cutoff_div`:
  - Strong concavity: `g x ≤ 1/e - (x - 1/e)²/2` on `[0,1]`, since `g'' = -1/x ≤ -1` on `(0,1]`.
  - With `x_n = (r n - 1)/n`: `1/e ≤ V_n = P_n(r n) ≤ g(x_n) + 1/n ≤ 1/e - (x_n - 1/e)²/2 + 1/n`. So `(x_n - 1/e)² ≤ 2/n → 0`, and
    `r n / n = x_n + 1/n`.
  - The lower bound `1/e ≤ V_n` is milestone `exp_neg_one_le_optimalProb`; import it.
- GOAL `tendsto_optimalProb`:
  - `1/e ≤ V_n` (milestone 8).
  - `V_n = P_n(r)` for some `r ∈ [1,n]` (milestone 3), which is `≤ g((r-1)/n) + 1/n ≤ 1/e + 1/n`.
  - Squeeze for `n ≥ 1`.

### Track C: `optimal_table` (n = 1, …, 10)
- Import `successProb_cutoffRule_one`, `successProb_cutoffRule`, `exists_optimal_cutoffRule`.
- For each `n`: `optimalProb n = P_n(r₀)` for some `r₀ ∈ [1,n]` (milestone 3), and every `P_n(r) ≤ optimalProb n` (`le_ciSup`).
- Compute `P_n(r)` for all `r ∈ [1, n]` exactly with milestones 1 and 2 (`interval_cases r`; `norm_num [Finset.sum_Icc_succ_top]`/`decide`).
  Show `P_n(r*) ≥ P_n(r)` for all `r`. Then `P_n(r*) ≥ P_n(r₀) = optimalProb n ≥ P_n(r*)`.
- The listed values are the maxima: `1, 1/2, 1/2, 11/24, 13/30, 77/180, 29/70, 459/1120, 341/840, 3349/8400`.

## Return
A structured result: per target, status OK / PARTIAL, file path, the exact `check.sh` tail, and a short paper-style proof description.
