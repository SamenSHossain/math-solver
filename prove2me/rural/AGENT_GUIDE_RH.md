# Guide for proof agents (Prove2Me workspace): Rural hospitals theorem

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. `export PATH="$HOME/.elan/bin:$PATH"`.
- Definitions (READ FIRST): `Definitions/Def_RuralHospitals_Market.lean` (Market with docRank/hospRank injective rank functions, smaller = better, `none` = unmatched/empty; `assigned μ h = univ.filter (μ · = some h)`; IsMatching, IsIndividuallyRational, IsBlockingPair, IsStable).
- Target: `Theorems/Thm_RuralHospitals_rural_hospitals_theorem.lean`.
- Type-check: `./check.sh Solutions/<file>.lean` (CHECK OK only with no errors and no sorry). Scratch: `Solutions/Scratch_RH_<key>*.lean` with `lake env lean <file>`. Never `lake build`; never edit Theorems/, Definitions/, .lake/, or other agents' files.
- File layout: `import Mathlib`, `import Definitions.Def_RuralHospitals_Market`, `set_option autoImplicit false`, `open RuralHospitals Finset`, helper lemmas inside `namespace RH_<key> … end RH_<key>` (each taking `{D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]` and whatever DecidableEq D / classical you need — use `classical` inside proofs), then a TOP-LEVEL `theorem solution` copying the target's binders and conclusion EXACTLY (only the name changes). No `Theorems.*` imports.
- No sorry/admit/native_decide/axioms; keep compile time small.

## Mathematics (direct counting proof; no deferred acceptance needed)
Fix a market M and stable matchings μ, ν. For a pair (μ, ν) define
  P(μ,ν) := {d | M.docRank d (μ d) < M.docRank d (ν d)}   (doctors strictly preferring μ),
  Hp(μ,ν) := {h | ∃ d, μ d = some h ∧ d ∈ P(μ,ν)}.
Write ρ_h for M.hospRank h. Facts:
F1. If d ∈ P(μ,ν) then μ d = some h for some h (if μ d = none, docRank d none < docRank d (ν d) contradicts the individual rationality of ν: docRank d (ν d) ≤ docRank d none), and μ d ≠ ν d.
F2. If d ∈ P(μ,ν) and μ d = some h then, because (d, h) does not block ν (d prefers h to ν d; ρ_h (some d) < ρ_h none by individual rationality of μ):
    (assigned ν h).card = M.capacity h (≥ from ¬(card < capacity), ≤ from IsMatching ν), and
    ∀ d' ∈ assigned ν h, ρ_h (some d') < ρ_h (some d) (≤ from the negated disjunct; ≠ by injectivity since d' ≠ d: ν d' = some h = μ d ≠ ν d).
F3. (Key exchange.) If h ∈ Hp(μ,ν), witnessed by d₀ ∈ P(μ,ν) with μ d₀ = some h, then no d' ∈ assigned ν h \ assigned μ h lies in P(ν,μ): otherwise F2 for (ν, μ) and d' gives ρ_h (some d₀) < ρ_h (some d') (d₀ ∈ assigned μ h), while F2 for (μ, ν) and d₀ gives ρ_h (some d') < ρ_h (some d₀) (d' ∈ assigned ν h). Since preferences are strict, a doctor d' with ν d' ≠ μ d' lies in P(μ,ν) or P(ν,μ) (docRank d injective; equal ranks would force μ d' = ν d'). Hence assigned ν h \ assigned μ h ⊆ P(μ,ν) for h ∈ Hp(μ,ν).
F4. (Counting.) Let S = Hp(μ,ν) (as a Finset). Then
    Σ_{h∈S} |assigned μ h| ≤ Σ_{h∈S} |assigned ν h|   (pointwise, by F2 and IsMatching μ),
    Σ_{h∈S} |assigned ν h| − Σ_{h∈S} |assigned μ h| = |A'| − |B'| where A' = {d | ν d ∈ some '' S ∧ μ d ≠ ν d} and B' = {d | μ d ∈ some '' S ∧ μ d ≠ ν d} (both sums count disjoint unions of the fibres; the common part {d | μ d = ν d ∈ some '' S} cancels; `Finset.card_biUnion`, `Finset.sum_card` style lemmas, or `Finset.card_eq_sum_card_fiberwise`),
    A' ⊆ P(μ,ν) (F3) and P(μ,ν) ⊆ B' (F1 and the definition of Hp).
  So |P| ≥ |A'| ≥ |B'| ≥ |P|; all are equal. Consequences:
  C1. every d ∈ P(μ,ν) has ν d = some h with h ∈ Hp(μ,ν) (A' ⊆ P and |A'| = |P| give A' = P);
  C2. for h ∈ Hp(μ,ν): |assigned μ h| = |assigned ν h| (pointwise ≤ with equal sums, `Finset.sum_eq_sum_iff_of_le`), and |assigned ν h| = M.capacity h (F2).
  Prove F1–F4/C1–C2 as ONE core lemma for arbitrary stable (μ, ν); then use it for (μ, ν) and for (ν, μ).
Main theorem with P = P(μ,ν), N = P(ν,μ), Hp = Hp(μ,ν), Hn = Hp(ν,μ):
  (1) doctors: if d ∈ P, μ d and ν d are both some (F1, C1); if d ∈ N, symmetric; otherwise docRank d (μ d) = docRank d (ν d), so μ d = ν d.
  (2) hospitals: if h ∈ Hp use C2; if h ∈ Hn use C2 for (ν, μ); otherwise assigned μ h = assigned ν h: a doctor d ∈ assigned ν h is not in P (C1 would put h in Hp) and not in N (then h ∈ Hn by definition), so μ d = ν d = some h; symmetric for assigned μ h.
  (3) part 2: if |assigned μ h| < capacity h then h ∉ Hp (C2 gives |assigned μ h| = |assigned ν h| = capacity) and h ∉ Hn (C2 for (ν,μ) gives |assigned μ h| = capacity), so assigned ν h = assigned μ h by (2).

## Return
Structured result: status OK/PARTIAL, file, check_tail, proof_description, remaining.
