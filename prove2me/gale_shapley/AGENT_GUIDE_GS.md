# Guide for proof agents (Prove2Me workspace): Gale–Shapley mission (StableMatching)

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. Run `export PATH="$HOME/.elan/bin:$PATH"` first.
- READ IN FULL FIRST: `Definitions/Def_StableMatching_GaleShapley.lean` (namespace `StableMatching`).
  - `Instance n` has `manRank womanRank : Fin n → (Fin n ≃ Fin n)`. Smaller rank means more preferred.
  - `manPrefers m w w' := manRank m w < manRank m w'` and `womanPrefers w m m' := womanRank w m < womanRank w m'`.
  - `Matching n := Fin n ≃ Fin n`, with `μ m` the wife of `m` and `μ.symm w` the husband of `w`.
  - `IsBlockingPair I μ m w := manPrefers m w (μ m) ∧ womanPrefers w m (μ.symm w)`, and `IsStable I μ := ∀ m w, ¬ IsBlockingPair`.
  - `GSState n` has `next : Fin n → ℕ` and `fiance : Fin n → Option (Fin n)`. `init` sets `next = 0` and `fiance = none`.
  - `IsEngaged s m := ∃ w, s.fiance w = some m`.
  - `proposal s m := if h : ¬ s.IsEngaged m ∧ s.next m < n then some ((manRank m).symm ⟨s.next m, h.2⟩) else none`.
  - `favourite w c := if c.Nonempty then some (the member of c of minimal womanRank w) else none`.
  - `gsRound s` has `next m := if (proposal s m).isSome then next m + 1 else next m` and
    `fiance w := favourite w ((univ.filter (proposal s · = some w)) ∪ (s.fiance w).toFinset)`.
  - `gsRun k := gsRound^[k] init`, `galeShapley := gsRun (n^2)`, and `IsGSOutcome μ := ∀ m, galeShapley.fiance (μ m) = some m`.
  - `MenDeviation I I' C := (∀ m ∉ C, I'.manRank m = I.manRank m) ∧ I'.womanRank = I.womanRank`.
  - `WomanDeviation I I' w := I'.manRank = I.manRank ∧ ∀ w' ≠ w, I'.womanRank w' = I.womanRank w'`.
  - `example3 : Instance 3` is defined with `rank3`.
- Theorem mirrors are in `Theorems/Thm_StableMatching_<name>.lean`; do NOT edit them. Their preamble is
  `import Mathlib` + `import Definitions.Def_StableMatching_GaleShapley`.
- Type-check a file with `./check.sh Solutions/<file>.lean`. It prints `CHECK OK` only when there are no errors and no `sorry`.
  For quick experiments use `lake env lean Solutions/Scratch_GS_<yourkey>_*.lean`. NEVER run `lake build`. Never edit `Theorems/`,
  `Definitions/`, `.lake/`, or files you did not create. Other agents run in parallel.
- Concrete computation: `decide` can evaluate `gsRun`/`galeShapley` on 3×3 instances, but it needs
  `set_option maxRecDepth 100000 in` (or larger) in front of the declaration. No `native_decide`.

## Solution file layout (mandatory)
```lean
import Mathlib
import Definitions.Def_StableMatching_GaleShapley

set_option autoImplicit false

open StableMatching

namespace StableMatching.<HelperNs>
... helper lemmas ...
end StableMatching.<HelperNs>

open StableMatching.<HelperNs> in
theorem solution <binders exactly as in the target> : <conclusion exactly as in the target> := by ...
```
- `theorem solution` must be TOP-LEVEL (not inside any namespace). It must copy the target's binders and conclusion exactly; only the
  name changes. Check this with `example : (type_of% @solution) = (type_of% @StableMatching.<name>) := rfl` in a scratch copy that also
  imports `Theorems.Thm_StableMatching_<name>`. Those Theorems modules are already built.
- No `sorry`, `admit`, `native_decide`, new axioms, `unsafe`, or `implemented_by`. Keep each file compiling in well under 120 s.
- A solution may NOT import other solution files. Reuse is by copying text: the shared core library (below) is pasted verbatim into each
  solution that needs it.

## The shared core library: `Solutions/Scratch_GS_core.lean`
It lives in namespace `StableMatching.GSCore`, compiles standalone, and contains no `theorem solution`. It must provide at least the following,
with clean names and statements, for an arbitrary `I : Instance n`. Write `s k := I.gsRun k` and `N := n^2`.
1. Round lemmas: `gsRun_succ : I.gsRun (k+1) = I.gsRound (I.gsRun k)`; field lemmas for `gsRound`.
   - `proposal_eq_some : I.proposal s m = some w ↔ ¬ s.IsEngaged m ∧ s.next m = I.manRank m w` (the clause `next < n` is then automatic).
   - `favourite_spec : I.favourite w c = some m ↔ m ∈ c ∧ ∀ m' ∈ c, I.womanRank w m ≤ I.womanRank w m'`, and `favourite_eq_none ↔ c = ∅`.
2. Invariant `Inv I s`, proved for every `I.gsRun k`:
   - (a) fiancés are injective: `s.fiance w = some m → s.fiance w' = some m → w = w'`;
   - (b) `s.fiance w = some m → s.next m = I.manRank m w + 1`;
   - (c) `s.next m ≤ n`;
   - (d) `(I.manRank m w : ℕ) < s.next m → ∃ m', s.fiance w = some m' ∧ I.womanRank w m' ≤ I.womanRank w m`
     (every woman a man has proposed to holds someone at least as good).
   - Derived (e): `¬ s.IsEngaged m → s.next m < n`. Otherwise he proposed to all `n` women. By (d) they are all engaged, to men
     other than `m`, and by (a) these are `n` distinct men among the `n - 1` others, which is impossible. A counting argument with
     `Finset.card_le_card_of_injOn` or similar.
   - Monotonicity: a woman engaged at `s k` stays engaged at `s (k+1)`, and her fiancé's rank weakly decreases (improves). `next` is
     nondecreasing.
3. Fixpoint: if every man is engaged at `s`, then `I.gsRound s = s`. Nobody proposes, and `favourite w (∅ ∪ {old}) = old`.
4. Termination: `∀ m, (I.gsRun (n^2)).IsEngaged m`. Use the potential `Φ s := ∑ m, s.next m`.
   - If some man is unengaged at `s k`, he is unengaged at every earlier state, because all-engaged is a fixpoint. At each of those
     rounds some unengaged man proposes, by (e). So `Φ (s k) ≥ k`.
   - But `Φ (s k) ≤ n*n - 1`, by (c) and (e) for the unengaged man. Hence `k < n^2`.
5. Outcome: there is `μ` with `I.IsGSOutcome μ`. Build it from the final state with `Equiv.ofBijective`, using injectivity from the
   fiancé function and `Finite.injective_iff_surjective`. Any GS outcome satisfies
   `I.galeShapley.next m = I.manRank m (μ m) + 1`, and `I.galeShapley.fiance w = some (μ.symm w)`, so the outcome is unique.
6. Stability: `I.IsGSOutcome μ → I.IsStable μ`. If `(m, w)` blocked `μ`, then `manRank m w < manRank m (μ m) < next m`, so by (d) `w`
   holds `μ.symm w` with `womanRank w (μ.symm w) ≤ womanRank w m`, which contradicts strict preference.

## Targets and proof plans
Names below are `StableMatching.<name>`, with theorem ids from the platform.

### Core track: `galeShapley_stable` (GOAL), `galeShapley_all_engaged`, `stable_matching_exists`
These are immediate from the core: (4), (5)+(6), and the goal applied to `I`.

### `galeShapley_man_optimal` and `galeShapley_woman_pessimal`
- Man-optimality: fix a stable `μ`. Prove the invariant `J s`, for every `gsRun k`:
  `∀ m, s.next m ≤ manRank m (μ m) + 1 ∧ (s.next m = manRank m (μ m) + 1 → s.fiance (μ m) = some m)`.
- Key step (no man is rejected by his stable partner): suppose `m` is a candidate of `w = μ m` in a round (a proposer, or her current
  fiancé) but her new fiancé is `m' ≠ m`.
  - `m'` is a candidate: he proposed to `w` this round (then `next m' = rank_{m'} w`) or was her fiancé (then `next m' = rank_{m'} w + 1`
    by (b)).
  - Using `J` and (b): `rank_{m'} w ≤ rank_{m'} (μ m')`. In the proposing case, equality `next m' = rank(μ m') + 1` would make `m'`
    engaged, a contradiction.
  - `w ≠ μ m'`, so the inequality is strict. `w` strictly prefers `m'` to `m = μ.symm w`, by `favourite_spec` and injectivity of
    `womanRank w`.
  - So `(m', w)` blocks `μ`, contradicting stability.
- Then `J` is preserved. At the final state, `next m = rank(μ₀ m) + 1 ≤ rank(μ m) + 1`.
- Woman-pessimality follows from man-optimality and stability of `μ`. Let `m₀ = μ₀.symm w` and `m = μ.symm w`. If `w` strictly
  preferred `m₀` to `m`, then `m₀ ≠ m`. So `μ m₀ ≠ w`, and man-optimality gives `rank_{m₀} w < rank_{m₀} (μ m₀)`. Hence `(m₀, w)` blocks
  `μ`.

### `galeShapley_truthful_men` and `galeShapley_group_strategyproof_men` (Dubins–Freedman; Gale–Sotomayor blocking lemma)
- **Blocking lemma.** Let `μ₀` be the GS outcome of `I`, `μ` ANY matching, and `M' := {m | manPrefers m (μ m) (μ₀ m)}` nonempty.
  Then some `(m, w)` blocks `μ` (w.r.t. `I`) with `m ∉ M'`.
- **Group strategy-proofness.** Let `μ` be the GS outcome of `I` and `μ'` that of `I'`. Assume every member of `C` strictly improves.
  Then `C ⊆ M'` (with `μ'` in the role of `μ` and `μ` in the role of `μ₀`), so `M'` is nonempty. The lemma gives `(m, w)` blocking `μ'`
  w.r.t. `I`, with `m ∉ C`. `I'` agrees with `I` on `m`'s list and on all women's lists, so `(m, w)` blocks `μ'` w.r.t. `I'`. That
  contradicts stability of the GS outcome of `I'` (core (6)). Truthfulness is the case `C = {m}`.
- **Proof of the blocking lemma.** Write `P t m w :≡ I.proposal (I.gsRun t) m = some w` ("`m` proposes to `w` in round `t`") and `N = n^2`.
  - Case 1: `μ₀ '' M' ≠ μ '' M'`. Both have size `|M'|`, so pick `w ∈ μ '' M' \ μ₀ '' M'` with `w = μ m'` and `m' ∈ M'`. Then `m'`
    prefers `w` to `μ₀ m'`. Stability of `μ₀` forces `w` to strictly prefer `m := μ₀.symm w` to `m'`. Since `w ∉ μ₀ '' M'`, `m ∉ M'`.
    So `m` weakly prefers `μ₀ m = w` to `μ m`, and `μ m ≠ w`. Hence `(m, w)` blocks `μ`.
  - Case 2: `μ₀ '' M' = μ '' M' =: W'`. Every `m ∈ M'` proposes to `μ m ∈ W'` at some round `< N`: proposals go in rank order and
    `rank(μ m) < rank(μ₀ m) < next_N m`. Let `T` be the LAST round `< N` in which some `m* ∈ M'` proposes to some `w ∈ W'`.
    - Claim A: a man of `M'` is never rejected at a round `t ≥ T`. If he were, he would be unengaged at `t+1`. He ends engaged to
      `μ₀ m ∈ W'`, so he proposes to `μ₀ m` at some round `> t ≥ T`, contradicting the choice of `T`.
      "Rejected at round `t` by `w`" means: he is a candidate of `w` in round `t` and `fiance_{t+1} w ≠ some him`. A man can be a
      candidate of only one woman per round.
    - Hence `m*` is accepted: `fiance_{T+1} w = some m*`.
    - Let `m'' := μ.symm w ∈ M'`. He proposed to `w` (at a round `< N`) and does not end with `w`, since `μ₀ m'' ≠ μ m'' = w`. So he
      is rejected by `w` at some round `t₂`, and by Claim A `t₂ < T`. At that round `w` takes someone strictly better than `m''`. Her
      fiancé only improves, so at the start of round `T` she is engaged to some `m` with
      `womanRank w m < womanRank w m''`.
    - `m ≠ m*`, because `m*` is unengaged at `T` (he proposes). So `m` is rejected at `T`, and by Claim A `m ∉ M'`.
    - `m` was engaged to `w` at `T`, so `next_T m = rank_m w + 1`. He is rejected and ends engaged, so
      `rank_m w < rank_m (μ₀ m) ≤ rank_m (μ m)`. The last inequality is `m ∉ M'`.
    - So `(m, w)` blocks `μ`.
  Useful history facts to prove first:
  - `next_{t+1} m = next_t m + 1` iff `m` proposes at `t`, and otherwise it is unchanged.
  - `m` proposes to `w` at round `t` iff `next_t m = rank_m w` and `m` is unengaged at `t`. Hence for every `w` with
    `rank_m w < next_T m` there is a round `t < T` with `P t m w`.
  - Engaged at `t+1` implies candidate at `t` of the same woman.
  - A man engaged at `N` to `μ₀ m` with an unengaged earlier state `t` proposes to `μ₀ m` at some round in `[t, N)`.
  - Use `Nat.find`/`Finset.max'` for `T`.

### `galeShapley_not_truthful_women` and `galeShapley_coalition_weakly_manipulable` (concrete 3×3 examples)
Both were found by computer search with an exact simulation of `gsRound`. `MR[m][w]` = `manRank m w`, and `WR[w][m]` = `womanRank w m`.
Each row is a permutation; build the `Equiv` with an explicit inverse table, e.g. `⟨![a,b,c], ![..], by decide, by decide⟩`.
- Women manipulate:
  - `MR = [[0,2,1],[1,2,0],[2,1,0]]` and `WR = [[2,0,1],[2,1,0],[0,1,2]]`.
  - Woman `w = 2` deviates to `WR'[2] = [0,2,1]`.
  - GS outcomes: `μ = ![0,2,1]` (man 0→w0, man 1→w2, man 2→w1) and `μ' = ![2,0,1]` (man 0→w2, man 1→w0, man 2→w1).
  - Woman 2: true rank of `μ.symm 2 = 1` is `WR[2][1] = 1`, and of `μ'.symm 2 = 0` is `WR[2][0] = 0`, which is better.
- Weak coalition:
  - `MR = [[2,0,1],[1,0,2],[0,1,2]]` and `WR = [[2,0,1],[1,2,0],[0,2,1]]`.
  - `C = {0,1}`; man 0 changes his list to `[0,2,1]`, and man 1 keeps `[1,0,2]`.
  - GS outcomes: `μ = ![2,0,1]` and `μ' = ![2,1,0]`. Man 0 keeps w2, and man 1 goes from w0 (rank 1) to w1 (rank 0).
- Re-verify the claimed outcomes in Lean with `decide`; if a table is off, recompute it with
  `/tmp/claude-0/-home-user-math-solver/ee9f98fb-9768-5748-b1b3-ebbf1e9b4bc0/scratchpad/gs/sim.py` (function `gs(n, MR, WR)`, returning men→women).
- Prove `IsGSOutcome` by `decide` (with raised `maxRecDepth`), and the deviation and preference facts by `decide`/`rfl`/`funext`+`decide`.

### `example3_stable_iff`
`μ : Matching 3` ranges over the 6 permutations. Try `revert μ; decide` (with raised `maxRecDepth`), or `Fintype`-enumerate `Equiv.Perm (Fin 3)`.
Alternatively, case on the values `μ 0, μ 1, μ 2` and decide each case. Both sides are decidable.

### `stable_matchings_distribLattice` (Conway; Knuth)
Facts for stable `μ, ν`:
- (K1) If `m` strictly prefers `μ m` to `ν m`, then `w := μ m` strictly prefers `ν.symm w` to `m`. Otherwise `(m, w)` blocks `ν`.
- (K2) Decomposition. Let `M_μ := {m | rank_m (μ m) < rank_m (ν m)}` and `W_ν := {w | womanRank w (ν.symm w) < womanRank w (μ.symm w)}`.
  - (K1) gives `μ '' M_μ ⊆ W_ν`.
  - For `w ∈ W_ν`, `ν.symm w ∈ M_μ`: by stability of `μ`, `ν.symm w` cannot strictly prefer `w = ν(ν.symm w)` to his `μ`-partner,
    and the two differ. So `|W_ν| ≤ |M_μ|`.
  - Hence `μ '' M_μ = W_ν = ν '' M_μ`. Symmetric statements hold with `μ, ν` swapped.
- Join and meet for men. `λ m :=` the man-better of `μ m, ν m`, and `ρ m :=` the man-worse.
  - Both are injective, hence bijective, by (K1)/(K2) case analysis.
  - Both are stable: a blocking pair of `λ` blocks `μ` or `ν`, and a blocking pair of `ρ` contradicts (K2) plus injectivity of `ρ`.
  - Pointwise, `manRank m (λ m) = min` of the two ranks and `manRank m (ρ m) = max`.
- Lattice structure.
  - The order `L.le μ ν ↔ ∀ m, manRank m (μ m) ≤ manRank m (ν m)` makes "man-better" smaller. So `inf = λ` (pointwise min of ranks)
    and `sup = ρ` (pointwise max).
  - Let `f : {μ // stable} → (Fin n → Fin n)` be `f μ = fun m => manRank m (μ.1 m)`. It is injective (`manRank m` is injective), and it maps
    `⊔`/`⊓` to pointwise `max`/`min`.
  - Use `Function.Injective.distribLattice f hf map_sup map_inf`. It needs `Max`/`Min` instances (in this Mathlib possibly named
    `Sup`/`Inf` or `Max`/`Min`; check). Its `le` is `f a ≤ f b`, which is `∀ m, …` by `Pi.le_def`.
  - Then `L.le μ ν ↔ ∀ m, ...` holds by `Iff.rfl` or `Pi.le_def`.

## Return
A structured result: per target, status OK / PARTIAL, file path, the exact `check.sh` tail, and a short paper-style proof description.
