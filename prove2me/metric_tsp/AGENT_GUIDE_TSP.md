# Guide for proof agents (Prove2Me workspace): Metric TSP vs the Held–Karp (subtour) LP

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. Run `export PATH="$HOME/.elan/bin:$PATH"` first.
- READ IN FULL FIRST: `Definitions/Def_MetricTSP_model.lean` (namespace `MetricTSP`, 70 lines).
  - `IsMetricCost c`: symmetric, zero diagonal, triangle inequality. Nonnegativity follows from `c u u ≤ c u v + c v u`.
  - `tourCost c π = ∑ i, c (π i) (π (finRotate n i))`, and `tspOpt c = sInf {t | ∃ π, t = tourCost c π}`.
  - `IsHeldKarp x`: symmetric, zero diagonal, `0 ≤ x ≤ 1`, `∑ u, x v u = 2` for every `v`, and
    `2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, x u v` for every nonempty proper `S`.
  - `hkValue c = sInf {t | ∃ x, IsHeldKarp x ∧ t = (1/2) * ∑ u, ∑ v, c u v * x u v}`.
- Statement mirrors live in `Theorems/` and are already built. Do NOT edit them, `Definitions/` or `.lake/`. NEVER run `lake build`.
- Type-check with `./check.sh Solutions/<file>.lean`; it prints `CHECK OK` only with no errors and no `sorry`. Experiment with
  `lake env lean Solutions/Scratch_TSP_<track>_*.lean`. Other agents work in parallel; only touch files you create.

## Generic facts every track needs (prove them yourself)
- `tspOpt c ≤ tourCost c π` for every `π`. Use `csInf_le`; the set is finite, the range of a function on a `Fintype`, so `BddBelow`.
  `tspOpt` is attained: the set is finite and nonempty, so use `Set.Finite.csInf_mem` or similar.
- The LP set is nonempty for `n ≥ 3`. Take the uniform point `x u v = if u = v then 0 else 2/(n-1)`:
  - its degrees are `(n-1)·2/(n-1) = 2`;
  - `x ≤ 1` because `n ≥ 3`;
  - a cut `S` with `|S| = k`, `1 ≤ k ≤ n-1`, gives `k(n-k)·2/(n-1) ≥ 2`, because `k(n-k) ≥ n-1`.
- The LP objective is `≥ 0` (costs and `x` are nonnegative), so the set is bounded below.
- To prove `tspOpt c ≤ K * hkValue c` with `K ≥ 0`: show `tspOpt c ≤ K * t` for every `t` in the LP set. For `K > 0`, `le_csInf` on
  `tspOpt c / K` (nonempty set) gives `tspOpt c / K ≤ hkValue c`.

## Solution file layout (mandatory)
```lean
import Mathlib
import Definitions.Def_MetricTSP_model
-- (track 1 sketch only) import Theorems.Thm_MetricTSP_four_thirds_conjecture_of_five_le

set_option autoImplicit false

namespace MetricTSP.<HelperNs>
open MetricTSP
...
end MetricTSP.<HelperNs>

open MetricTSP in
theorem solution <binders exactly as the target> : <conclusion exactly as the target> := by ...
```
- `theorem solution` is TOP-LEVEL. Verify it with
  `example : (type_of% @solution) = (type_of% @MetricTSP.<target>) := rfl` in a scratch copy that imports `Theorems.Thm_MetricTSP_<target>`.
- No `sorry`, `admit`, `native_decide` or axioms, except the track-1 sketch, which imports the open child theorem.
- Keep the compile time well under 150 s.

## Track 1: small cases
Target A: `Theorems/Thm_MetricTSP_tspOpt_le_hkValue_of_le_four.lean`, i.e. `tspOpt_le_hkValue_of_le_four (n) (hn : 3 ≤ n) (hn4 : n ≤ 4) (c) (hc) : tspOpt c ≤ hkValue c`.
File: `Solutions/Sol_MetricTSP_tspOpt_le_hkValue_of_le_four.lean`.
- n = 3: the degree constraints with `x ≤ 1` force `x u v = 1` for all `u ≠ v`, since each vertex has two other neighbours summing
  to 2. So the objective equals `c 0 1 + c 1 2 + c 2 0`, which is the cost of the tour given by the identity ordering.
- n = 4: from the degree equations at the 4 vertices, opposite edges carry equal weight:
  `x01 = x23 =: a`, `x02 = x13 =: b`, `x03 = x12 =: e`, with `a + b + e = 2` and each `≤ 1`.
  - The three Hamiltonian cycles are `T_ab = M_a ∪ M_b`, `T_ae = M_a ∪ M_e` and `T_be = M_b ∪ M_e`, where `M_a = {01, 23}`,
    `M_b = {02, 13}`, `M_e = {03, 12}`.
  - With `λ_be = 1 - a`, `λ_ae = 1 - b`, `λ_ab = 1 - e` (each `≥ 0`, summing to 1), we have
    `x = λ_ab·χ(T_ab) + λ_ae·χ(T_ae) + λ_be·χ(T_be)`. Hence the objective is `Σ λ·cost(T) ≥ min cost(T) ≥ tspOpt`.
  - Exhibit the three tours as explicit permutations of `Fin 4`; `decide`/`fin_cases` helps with the bookkeeping.
- Reduce `n ∈ {3, 4}` to `Fin 3`/`Fin 4` via `interval_cases n` (`subst`).

Target B, the SKETCH: `Theorems/Thm_MetricTSP_four_thirds_conjecture.lean`, i.e. `four_thirds_conjecture (n) (hn : 3 ≤ n) (c) (hc) : tspOpt c ≤ 4 / 3 * hkValue c`.
File: `Solutions/Sol_MetricTSP_four_thirds_conjecture.lean`.
- Import `Theorems.Thm_MetricTSP_four_thirds_conjecture_of_five_le`, the open child
  `four_thirds_conjecture_of_five_le (n) (hn : 5 ≤ n) (c) (hc) : tspOpt c ≤ 4/3 * hkValue c`.
- Include the target-A development, so this file does NOT import target A's Theorems module; paste the lemmas instead.
- `n ≥ 5` uses the child. `n ∈ {3,4}` uses `tspOpt ≤ hkValue ≤ 4/3 · hkValue`, since `hkValue ≥ 0`.
- `#print axioms` will show `sorryAx`, but only from the child; that is expected.
- Optional stretch: also prove n = 5 (`tspOpt ≤ hkValue`; the subtour polytope of K5 is integral) and make the child `6 ≤ n`, but
  only if you finish everything else first. Then rename consistently, i.e. tell the orchestrator.

## Track 2: `Theorems/Thm_MetricTSP_tspOpt_le_two_mul_hkValue.lean`
Statement: `tspOpt c ≤ 2 * (1 - 1/n) * hkValue c` for `n ≥ 3`. File: `Solutions/Sol_MetricTSP_tspOpt_le_two_mul_hkValue.lean`.
Plan (avoid spanning-tree libraries; use a Prim order and insertion):
1. **Prim order.** Choose an ordering `v_0, …, v_{n-1}` of `Fin n` greedily: `v_k` minimises the distance to `{v_0, …, v_{k-1}}`.
   Let `d_k := min_{j<k} c v_j v_k` for `k ≥ 1`. (Any construction is fine, e.g. by recursion, a list built step by step, or `Finset` arguments.)
2. **Insertion bound.** Represent a cyclic tour as a `List (Fin n)`, with `cost L = ∑ c L_i L_{i+1 mod |L|}`. Inserting `v` right after
   `u ∈ L` (between `u` and its successor `w`) increases the cost by `c u v + c v w - c u w ≤ 2 c u v`, by the triangle inequality.
   - By induction there is a cyclic list of `{v_0..v_k}` with cost `≤ 2 Σ_{1≤j≤k} d_j`, inserting `v_k` after its nearest earlier
     vertex.
   - The final nodup list of length `n` gives a permutation `π` with `tourCost c π = cost L`.
   - So `tspOpt ≤ 2 Σ_{k≥1} d_k`.
3. **Threshold counting.** For `t ≥ 0` let `G_t` be the graph `{uv : c u v ≤ t}`. When `d_k > t`, the set `A_k = {v_0..v_{k-1}}` is a
   union of `G_t`-components. Otherwise some outside vertex would be within `t` of `A_k`, and the greedy choice would give `d_k ≤ t`.
   These sets are nonempty, proper and strictly increasing in `k`, so `#{k ≥ 1 : d_k > t} ≤ comp(G_t) - 1`.
4. **LP side.** Let `z = (1 - 1/n) x`. Then `z(E) = n - 1`, and for every vertex set `S`, `z(E(S)) ≤ |S| - 1`. Indeed
   `x(E(S)) = (2|S| - x(δ(S)))/2 ≤ |S| - 1` for proper nonempty `S`, and `z(E) = n - 1` for `S = V`.
   - Summing over the components `C` of `G_t`: `z(edges with c ≤ t) ≤ Σ_C (|C| - 1) = n - comp(G_t)`.
   - So `z(edges with c > t) ≥ comp(G_t) - 1 ≥ #{k : d_k > t}`.
5. **Layer cake.** `Σ_e c_e z_e = ∫_0^∞ z({e : c_e > t}) dt ≥ ∫_0^∞ #{k : d_k > t} dt = Σ_k d_k`.
   - A DISCRETE version avoids integrals: sort the finitely many values, or prove `Σ_e c_e z_e ≥ Σ_k d_k` by Abel summation over
     the distinct values `0 = a_0 < a_1 < … < a_m` of `c`.
   - Equivalently use `∑ f = ∑_j (a_j - a_{j-1}) · #{f ≥ a_j}`.
   - Choose whatever is easiest in Lean.
6. Combine: for every feasible `x`, `tspOpt ≤ 2 Σ d_k ≤ 2 c·z = 2(1 - 1/n)·(1/2)∑∑ c x`. Then take the infimum.
- Building the edge set as unordered pairs is optional. You may work with ordered pairs `u < v` or with double sums and factor `1/2`.

## Track 3: `Theorems/Thm_MetricTSP_tspOpt_le_three_halves_hkValue.lean` (Wolsey 1980; Shmoys–Williamson 1990)
Statement: `tspOpt c ≤ 3/2 * hkValue c` for `n ≥ 3`. File: `Solutions/Sol_MetricTSP_tspOpt_le_three_halves_hkValue.lean`.
This is Christofides' analysis:
- `tour ≤ MST + min-cost perfect matching M_T` on the odd-degree vertex set `T` of the MST, by Euler tour plus shortcutting;
- `MST ≤ (1 - 1/n) LP ≤ LP`, as in track 2;
- `M_T ≤ LP/2`, because `x/2` lies in the dominant of the `T`-join polytope: `x(δ(S))/2 ≥ 1` for every `T`-odd `S`.

The last step needs Edmonds–Johnson (`T`-join polytope) or Edmonds' perfect matching polytope theorem. Neither is in Mathlib, so it
must be proved, e.g.:
- by induction on the number of edges, using the classical proof that a vertex of
  `{y ≥ 0 : y(δ(S)) ≥ 1 for T-odd S}` is integral (an uncrossing argument);
- or by a direct primal–dual argument (Edmonds' blossom algorithm analysis);
- or via a minimal-counterexample argument.

Search for the shortest rigorous route before coding. Reuse the track-2 approach for the MST part, but write your own file (no imports
of other solutions). This track is LARGE: build it in layers with `sorry`-free lemmas, report honestly if incomplete, and list the
precise remaining lemmas.

## Return
A structured result: per target, status OK / PARTIAL, file path, the exact `check.sh` tail, and a short proof description; for
PARTIAL, the remaining lemmas.
