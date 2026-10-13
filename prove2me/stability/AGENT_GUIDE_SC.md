# Guide for proof agents (Prove2Me workspace, mission "C^r Stability Conjecture")

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. `export PATH="$HOME/.elan/bin:$PATH"`.
- Definitions (READ FIRST): `Definitions/Def_ClosingLemma_DiffeoCrTopology.lean` (Diff n M r = Diffeomorph (𝓡 n) (𝓡 n) M M r, crTopology), `Definitions/Def_PughClosingLemma_nonwandering.lean` (IsNonwandering, nonwanderingSet), `Definitions/Def_StabilityConjecture_Basic.lean` (IsHyperbolicSet, IsHyperbolicPeriodicPt, SatisfiesAxiomA, IsStructurallyStable, IsOmegaStable).
- Type-check: `./check.sh Solutions/<file>.lean` (CHECK OK only with no errors and no sorry). Scratch: `Solutions/Scratch_SC_<key>*.lean` with `lake env lean <file>`. Never `lake build`; never edit Theorems/, Definitions/, .lake/, or other agents' files.
- Submission file layout:
  ```
  import Mathlib
  import Definitions.Def_ClosingLemma_DiffeoCrTopology
  import Definitions.Def_PughClosingLemma_nonwandering
  import Definitions.Def_StabilityConjecture_Basic

  set_option autoImplicit false

  open scoped Manifold ContDiff Topology
  open StabilityConjecture ClosingLemma
  ```
  then private helper lemmas (or `namespace SC_<key> … end`), then a TOP-LEVEL `theorem solution` whose binders and conclusion are copied EXACTLY from the target theorem (only the name changes). No `Theorems.*` imports for these two targets.
- No sorry/admit/native_decide/axioms. Keep compile time small.

## Targets
A. `Theorems/Thm_StabilityConjecture_omegaStable_of_structurallyStable.lean`:
   IsStructurallyStable r f → IsOmegaStable r f.
   Math: keep the same neighbourhood U. For g ∈ U take the conjugacy h : M ≃ₜ M with h (f x) = g (h x).
   (i) Iterates: h (f^[k] x) = g^[k] (h x) (`Function.Semiconj.iterate_right` or induction).
   (ii) Generic topological lemma (state it for any topological space X, maps F G : X → X, homeomorphism h with h ∘ F = G ∘ h): x ∈ nonwanderingSet F → h x ∈ nonwanderingSet G. For V ∈ 𝓝 (h x), U := h ⁻¹' V ∈ 𝓝 x (`h.continuous.continuousAt.preimage_mem_nhds`); nonwandering gives k ≥ 1 and z = F^[k] w with w ∈ U, z ∈ U; then h z = G^[k] (h w) ∈ G^[k] '' V and h z ∈ V.
   (iii) Apply (ii) to h and to h.symm (h.symm ∘ g = f ∘ h.symm) to get x ∈ Ω(f) ↔ h x ∈ Ω(g).
   (iv) The restriction is a homeomorphism Ω(f) ≃ₜ Ω(g): e.g. `Homeomorph.subtype` (grep its exact signature) or build it from `h.toEquiv.subtypeEquiv` with continuity via `Continuous.subtype_mk`/`continuous_subtype_val`. The conjugacy: if (y : M) = f x then (h' y : M) = h y = h (f x) = g (h x) = g (h' x).
B. `Theorems/Thm_StabilityConjecture_periodic_hyperbolic_of_hyperbolic_nonwandering.lean`:
   IsHyperbolicSet f Ω(f) → every periodic point p is an IsHyperbolicPeriodicPt.
   Math: p ∈ periodicPts f gives m > 0 with f^[m] p = p (`Function.mem_periodicPts`, `Function.IsPeriodicPt`). Let O = Set.range (fun k => f^[k] p).
   (i) O is finite (every f^[k] p equals f^[k % m] p: `Function.IsPeriodicPt.iterate_mod_apply`), hence compact (`Set.Finite.isCompact`).
   (ii) f '' O = O: ⊆ since f (f^[k] p) = f^[k+1] p (`Function.iterate_succ_apply'`); ⊇ since f^[k] p = f (f^[k + m - 1] p) using periodicity.
   (iii) O ⊆ Ω(f): every point of O is periodic, and a periodic point q (f^[m] q = q, m ≥ 1) is nonwandering: q ∈ f^[m] '' U ∩ U for every U ∈ 𝓝 q.
   (iv) Take the data (g, Es, Eu, C, lam) of the hyperbolic structure of Ω(f) and restrict the pointwise conditions to x ∈ O ⊆ Ω(f).

## Return
Structured result: status OK/PARTIAL, file, check_tail, proof_description, remaining.
