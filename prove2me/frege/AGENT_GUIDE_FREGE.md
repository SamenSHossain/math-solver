# Guide for proof agents (Prove2Me workspace): soundness / completeness of bounded-depth Frege `F_d`

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. Run `export PATH="$HOME/.elan/bin:$PATH"` first.
- READ IN FULL FIRST: `Definitions/Def_FdVersusFdSucc_defs.lean` (155 lines, namespace `FdVersusFdSucc`). Key objects:
  - `inductive Formula | pos ℕ | neg ℕ | and (List Formula) | or (List Formula)`. This is a NESTED inductive (through `List`).
  - `Formula.eval v`, `Formula.dual`, `Formula.depth`, `Formula.size` are all defined by structural recursion through `As.attach`
    (e.g. `eval v (and As) = As.attach.all fun ⟨A, _⟩ => eval v A`, `depth (and As) = (As.attach.map fun ⟨A,_⟩ => depth A).foldr max 0 + 1`).
  - `Formula.IsTautology A := ∀ v, A.eval v = true`.
  - `Sequent := List Formula`. `Step prev Γ` with constructors `ax Γ i (pos i ∈ Γ) (neg i ∈ Γ)`, `andI Γ As (∀ A ∈ As, (A :: Γ) ∈ prev)` concluding `and As :: Γ`,
    `orI Γ As A (A ∈ As) ((A :: Γ) ∈ prev)` concluding `or As :: Γ`, `weaken Γ Δ (Γ ∈ prev) (Γ ⊆ Δ)` concluding `Δ`,
    `cut Γ A ((A :: Γ) ∈ prev) ((A.dual :: Γ) ∈ prev)` concluding `Γ`.
  - `IsDepthProof d π := (∀ i (h : i < π.length), Step (π.take i) π[i]) ∧ ∀ Γ ∈ π, ∀ A ∈ Γ, A.depth ≤ d`.
  - `IsDepthProofOf d π A := IsDepthProof d π ∧ [A] ∈ π`.
- Targets (mirrors in `Theorems/`, do NOT edit them):
  - `Theorems/Thm_FdVersusFdSucc_depth_frege_sound.lean`:
    `theorem depth_frege_sound (d : ℕ) (π : List Sequent) (A : Formula) (h : IsDepthProofOf d π A) : A.IsTautology`
  - `Theorems/Thm_FdVersusFdSucc_depth_frege_complete.lean`:
    `theorem depth_frege_complete (d : ℕ) (A : Formula) (hd : A.depth ≤ d) (hA : A.IsTautology) : ∃ π : List Sequent, IsDepthProofOf d π A`
- Type-check: `./check.sh Solutions/<file>.lean` (prints `CHECK OK` only with no errors and no `sorry`). Scratch files: `Solutions/Scratch_FR_<key>*.lean`.
  NEVER run `lake build`; never edit `Theorems/`, `Definitions/`, `.lake/`.

## Solution file layout (mandatory)
```lean
import Mathlib
import Definitions.Def_FdVersusFdSucc_defs

set_option autoImplicit false

open Filter

namespace FdVersusFdSucc.<HelperNamespace>   -- e.g. FrSound / FrComplete; all helper lemmas go here
open FdVersusFdSucc Formula
...
end FdVersusFdSucc.<HelperNamespace>

open FdVersusFdSucc in
theorem solution (d : ℕ) (π : List Sequent) (A : Formula)
    (h : IsDepthProofOf d π A) : A.IsTautology := by
  ...
```
The final `theorem solution` must be TOP-LEVEL (not inside a namespace) and copy the target's binders and conclusion exactly; only the name
changes to `solution`. Do not import `Theorems.*`. No `sorry`, `admit`, `native_decide`, new `axiom`s. Keep compile time well under 120 s.

## Working with the nested inductive
- Induction on `Formula`: use `induction A using Formula.rec (motive_2 := fun As => ∀ A ∈ As, P A)` style, or (often easier) strong
  induction on `sizeOf A` / on `A.size`, or write helper lemmas by well-founded recursion with
  `termination_by A` and `decreasing_by` using `List.sizeOf_lt_of_mem`. Check `#check @Formula.rec` first.
- First prove clean equation lemmas, e.g.
  `eval v (and As) = true ↔ ∀ A ∈ As, eval v A = true`, `eval v (or As) = true ↔ ∃ A ∈ As, eval v A = true`,
  `depth A ≤ depth (and As) - 1` / `A ∈ As → depth A < depth (and As)`, `A ∈ As → size A < size (and As)`,
  `size (and As) = (As.map size).sum + 1`. Useful: `List.all_eq_true`, `List.any_eq_true`, `List.attach_map_subtype_val`,
  `List.mem_attach`, `List.foldr_max`-style lemmas (`List.le_foldr_max`?) — search with `exact?`/`#find`-style experiments in scratch files.

## Proof plans
### Soundness
1. `eval_dual : (A.dual).eval v = !(A.eval v)` by induction on `A` (De Morgan).
2. Call a sequent valid if `∀ v, ∃ B ∈ Γ, B.eval v = true`. Show every rule preserves validity: if every sequent of `prev` is valid and
   `Step prev Γ` then `Γ` is valid (cut uses `eval_dual`; weakening uses `⊆`; `andI` with `As = []` is fine since `and []` is true).
3. By strong induction on `i`, every `π[i]` is valid (premises lie in `π.take i`, whose members are `π[j]` with `j < i`;
   `List.mem_take_iff_getElem` or similar).
4. `[A] ∈ π` is valid, so `A.eval v = true` for all `v`.

### Completeness (cut-free proof search; no cut needed)
Let `Derivable d Γ := ∃ π, IsDepthProof d π ∧ Γ ∈ π`. Valid as above.
1. Monotonicity: `Step prev Γ → prev ⊆ prev' → Step prev' Γ`.
2. Concatenation: `IsDepthProof d π₁ → IsDepthProof d π₂ → IsDepthProof d (π₁ ++ π₂)` (for an index `|π₁| + i`, the prefix is
   `π₁ ++ π₂.take i ⊇ π₂.take i`), and `IsDepthProof d π → Step π Γ → (∀ B ∈ Γ, B.depth ≤ d) → IsDepthProof d (π ++ [Γ])`.
   Hence: a rule whose (finitely many) premises are derivable has a derivable conclusion (concatenate the premise proofs — use a fold over a
   list of premises for `andI` — then append the conclusion).
3. Main lemma, by strong induction on `μ Γ := (Γ.map size).sum`: if `Γ` is valid and all its formulas have depth `≤ d`, then `Γ` is derivable.
   - If `Γ` contains `and As`: let `Γ' := Γ.erase (and As)`; each `A :: Γ'` (A ∈ As) is valid and has smaller `μ`; derive them, apply `andI`
     to get `and As :: Γ'`, then `weaken` to `Γ` (`and As :: Γ.erase _ ⊆ Γ`). Depth of `A` is `< depth (and As) ≤ d`.
   - Else if `Γ` contains `or As`: `As ++ Γ'` is valid with smaller `μ`; derive it. Then repeatedly apply weaken + `orI`
     (with `S_j := or As :: (As.drop j ++ Γ')`: weaken `S_j` to `A_{j+1} :: (or As :: As.drop (j+1) ++ Γ')`, `orI` gives
     `or As :: (or As :: …)`, weaken to `S_{j+1}`), ending at `or As :: Γ'`, then weaken to `Γ`. (Lists are compared with `⊆`, so
     duplicates/permutations cost only a weakening.) Alternative: induct on `As` generalizing the context.
   - Else all members are literals: if no `pos i, neg i` pair, the assignment `v i := decide (neg i ∈ Γ)` falsifies every member — contradiction;
     so `Step.ax` applies to `[] ` prefix: `π = [Γ]`.
4. `A` tautology ⇒ `[A]` valid ⇒ derivable ⇒ the theorem.

## Return
A structured result: status OK / PARTIAL, file path, the exact `check.sh` output tail, and a short paper-style description of the proof.
