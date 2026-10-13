# Seymour's second-neighborhood conjecture (Prove2Me mission)

Target: `OAI.SeymourSecondNeighborhood.exists_goodVertex` — every finite nonempty oriented graph has a vertex
with |N⁺₁(v)| ≤ |N⁺₂(v)|. The mission follows the OpenAI preprint *A proof of Seymour's second-neighborhood
conjecture* (September 23, 2026, `openai/math` at commit `adc7f124`).

## What was done

- The manuscript's argument was read in full and checked: Lemma 2.2 (minimal counterexample ⇒ subset deficit),
  Lemma 2.3 (transitive-tournament blow-up ⇒ strict expansion), Lemma 3.1 (pruning two families of pairs, a
  statement about arbitrary finite relations proved there by a rank argument), Lemma 3.2 (kernels at maximum
  support rank) and Proposition 4.1 (no positive-indegree strict expander). Brute-force checks in `checks/`:
  no strict expander exists on ≤ 6 vertices (exhaustive) or in 700 000 random samples on 7–9 vertices; the
  pruning lemma holds exhaustively on 2 points and in random trials on 3; its matching bound holds on
  150 000 random instances and is tight.
- Published on the platform: the definition block `SeymourSecondNeighborhood_Image`
  (`Def_SeymourSecondNeighborhood_Image.lean`) and the five lemma statements as theorems
  `OAI.SeymourSecondNeighborhood.{lemma_2_2, lemma_2_3, prop_4_1, Pruning.lemma_3_1, Pruning.lemma_3_2}`
  (`Thm_*.lean` mirrors).
- `Sol_OAI_SeymourSecondNeighborhood_exists_goodVertex.lean`: accepted **proof sketch** of the main theorem
  from `lemma_2_2`, `lemma_2_3` and `prop_4_1` (strong induction on the order, a minimal all-bad subrelation
  via `Nat.find`, blow-up with m = n + 1).
- `Sol_OAI_SeymourSecondNeighborhood_lemma_2_2.lean`: **Proved** (minimal counterexample ⇒ positive indegrees
  and subset deficit; the arc-deletion step of the manuscript, with an induction on the adjoined set).
- `Sol_OAI_SeymourSecondNeighborhood_lemma_2_3.lean`: **Proved** (blow-up; per-block bound summed over blocks).
- `Sol_OAI_SeymourSecondNeighborhood_prop_4_1.lean`: accepted **sketch** reducing Proposition 4.1 to the
  pruning lemma `Pruning.lemma_3_1` (the extremal argument of Section 4).
- `Sol_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_1.lean`: accepted **sketch** reducing the pruning lemma to
  two new statements published on the platform: `Pruning.konig` (Kőnig's theorem, vertex-cover form) and
  `Pruning.matching_bound` (every matching of the augmented bipartite graph Γ has at most |Z| + |H| edges).
- `Sol_OAI_SeymourSecondNeighborhood_Pruning_konig.lean`: **Proved** (from Hall's theorem in deficiency form).
- `Sol_OAI_SeymourSecondNeighborhood_Pruning_lemma_3_2.lean`: **Proved** (rank-increase by a single-entry
  perturbation).

## State of the mission

Everything in the manuscript's chain is now machine-checked except `Pruning.matching_bound`, the rank-argument
core of its Section 3 (open). Proving it would close the whole conjecture on the platform:
`matching_bound` ⇒ `lemma_3_1` ⇒ `prop_4_1` ⇒ (with `lemma_2_2`, `lemma_2_3`) `exists_goodVertex`.
`platform_ids.txt` lists the theorem ids.
