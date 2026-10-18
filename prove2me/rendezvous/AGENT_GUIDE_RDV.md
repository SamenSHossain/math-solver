# Guide for proof agents (Prove2Me workspace): Alpern–Gal asymmetric rendezvous value 13/4

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. Run `export PATH="$HOME/.elan/bin:$PATH"` first.
- READ IN FULL FIRST: `Definitions/Def_SymmetricRendezvousLine_defs.lean` (namespace `SymmetricRendezvousLine`).
  - `IsFeasiblePath f := f 0 = 0 ∧ ∀ s t, 0 ≤ s → 0 ≤ t → |f s - f t| ≤ |s - t|`.
  - `MixedStrategy` bundles `Ω : Type`, a σ-algebra, a probability measure `P`, `path : Ω → ℝ → ℝ`, `path_feasible`, and
    `path_measurable : ∀ t, Measurable (fun ω => path ω t)`.
  - `meetingTime x y := ⨅ (t : ℝ) (_ : 0 ≤ t ∧ x t = y t), ENNReal.ofReal t`.
  - `orient b := if b then 1 else -1`.
  - `expectedMeetingTime S₁ S₂ := (1/4) * ∑ b₁, ∑ b₂, ∫⁻ p, meetingTime (fun t => orient b₁ * S₁.path p.1 t) (fun t => 2 + orient b₂ * S₂.path p.2 t) ∂(S₁.P.prod S₂.P)`.
  - `asymmetricRendezvousValue := ⨅ S₁ S₂, expectedMeetingTime S₁ S₂`.
- Target: `Theorems/Thm_SymmetricRendezvousLine_asymmetric_rendezvous_value_eq_thirteen_quarters.lean`:
  `theorem asymmetric_rendezvous_value_eq_thirteen_quarters : asymmetricRendezvousValue = 13 / 4` (values in `ENNReal`). It is already built.
- Type-check a file with `./check.sh Solutions/<file>.lean`. It prints `CHECK OK` only when there are no errors and no `sorry`.
  Experiment with `lake env lean Solutions/Scratch_RDV_<yourkey>_*.lean`. NEVER run `lake build`. Never edit `Theorems/`, `Definitions/`,
  `.lake/`, or files you did not create; another agent works in parallel.

## Final solution layout
```lean
import Mathlib
import Definitions.Def_SymmetricRendezvousLine_defs

set_option autoImplicit false

open MeasureTheory

namespace SymmetricRendezvousLine.AG
... all helper lemmas ...
end SymmetricRendezvousLine.AG

open SymmetricRendezvousLine in
theorem solution : asymmetricRendezvousValue = 13 / 4 := by ...
```
- `theorem solution` is TOP-LEVEL. Check it with
  `example : (type_of% @solution) = (type_of% @SymmetricRendezvousLine.asymmetric_rendezvous_value_eq_thirteen_quarters) := rfl`.
- No `sorry`, `admit`, `native_decide`, new axioms. Keep compile time under 120 s.

## Mathematics
Write `T b₁ b₂ f g := meetingTime (fun t => orient b₁ * f t) (fun t => 2 + orient b₂ * g t)`.

### Part U: upper bound `asymmetricRendezvousValue ≤ 13/4`, by explicit deterministic strategies
- `f t := 2 - |t - 2|` moves forward 2 and then back.
- `g t := max (1 - |t - 1|) (2 - |t - 4|)` moves 0→1→0→2→0 on `[0,6]`.
- Both are feasible: `f 0 = 0`, `g 0 = max 0 (-2) = 0`. They are 1-Lipschitz because `||a|-|b|| ≤ |a-b|` and `|max a b - max c d| ≤ max |a-c| |b-d|`.
- With `u = f + g` and `v = f - g` on `t ≥ 0`, the four orientation cases are:
  - `(true,true)`: meet iff `f t = 2 + g t`, iff `v = 2`. `v = 0` on `[0,1]` and `v = 2t-2` on `[1,2]`, so first at **t = 2**.
  - `(true,false)`: meet iff `f t = 2 - g t`, iff `u = 2`. `u = 2t` on `[0,1]`, so first at **t = 1**.
  - `(false,true)`: meet iff `-f t = 2 + g t`, iff `u = -2`. `u = 2t` on `[0,1]`, `= 2` on `[1,4]`, and `= 10 - 2t` on `[4,6]`, so first at
    **t = 6**.
  - `(false,false)`: meet iff `-f t = 2 - g t`, iff `v = -2`. `v = 0` on `[0,1]`, `2t-2` on `[1,2]`, and `6 - 2t` on `[2,4]`, so first at
    **t = 4**.
  - The sum is `13`.
- `meetingTime x y = ENNReal.ofReal τ`: `iInf₂_le` at `τ` gives `≤`. For `≥`, use `le_iInf₂`: every `t ≥ 0` with `x t = y t` has `τ ≤ t`.
  Prove that by contraposition, case-splitting `t` on the intervals and unfolding `|·|`/`max` with `abs_of_nonneg`, `abs_of_nonpos`,
  `max_eq_left`, etc.
- Strategies: `Ω = Unit`, `P = Measure.dirac ()`, and `path _ = f` (resp. `g`). Measurability is trivial (constant in `ω`).
  `Measure.dirac_prod_dirac` and `lintegral_dirac` (`MeasurableSingletonClass`) reduce each integral to the value at the point. Then
  `(1/4) * (2 + 1 + 6 + 4) = 13/4` in `ENNReal`; convert carefully with `ENNReal.ofReal` arithmetic.

### Part L: lower bound `13/4 ≤ asymmetricRendezvousValue`
**L1. Core deterministic lemma (Alpern–Gal).** For feasible `f, g`: `(13 : ENNReal) ≤ ∑ b₁, ∑ b₂, T b₁ b₂ f g`.
- If some term is `⊤`, the claim is trivial. Otherwise take any meeting times `t₀, t₁, t₂, t₃ ≥ 0`, one per orientation case, i.e. points of the
  sets. Taking them within `ε` of each infimum (or attaining the infimum, since the meeting set is closed by continuity) reduces the claim to the
  real inequality below.
- **Real inequality** (checked by LP over all 24 orderings; minimum exactly 13). Let `t₀..t₃ ≥ 0` and `aᵢ = f tᵢ`, `cᵢ = g tᵢ`.
  - Meeting conditions: `a₀ = 2 + c₀`, `a₁ = 2 - c₁`, `-a₂ = 2 + c₂`, `-a₃ = 2 - c₃`.
  - Lipschitz facts: `|aᵢ| ≤ tᵢ`, `|cᵢ| ≤ tᵢ`, `|aᵢ - aⱼ| ≤ |tᵢ - tⱼ|`, `|cᵢ - cⱼ| ≤ |tᵢ - tⱼ|`.
  - Then `t₀ + t₁ + t₂ + t₃ ≥ 13`.
  - Proof: case on the relative order of the `tᵢ` (`le_total` on the 6 pairs), rewrite each `|tᵢ - tⱼ|` accordingly, split the abs
    hypotheses into two linear inequalities each (`abs_le`), and call `linarith`. Every ordering admits a linear certificate.
  - Geometric meaning: `(u,v)/2 = ((f+g)/2, (f-g)/2)` moves with ℓ¹-speed ≤ 1 from the origin and must touch the four sides of `[-1,1]²`.
- Convert to `ENNReal`: `13 ≤ ∑ ofReal tᵢ` from `13 ≤ ∑ tᵢ` (`ENNReal.ofReal_add`, `ENNReal.ofReal_le_ofReal`). Then pass from the chosen
  `tᵢ` to the infima with an `ε`-argument (`ENNReal.le_of_forall_pos_le_add` or similar), or show the infimum is attained.

**L2. Measurability of the meeting time.** For a `MixedStrategy` pair, `p ↦ T b₁ b₂ (S₁.path p.1) (S₂.path p.2)` is measurable on
`S₁.Ω × S₂.Ω` (product σ-algebra).
- Let `X p t := orient b₁ * S₁.path p.1 t - (2 + orient b₂ * S₂.path p.2 t)`. It is continuous in `t ≥ 0` (2-Lipschitz there), and
  measurable in `p` for each `t` (`(path_measurable t).comp measurable_fst`, etc.). Also `X p 0 = -2 ≠ 0`.
- For `s ≥ 0`: `T ≤ ofReal s ↔ ∃ t ∈ [0,s], X p t = 0`. The meeting set is closed and `X` is continuous, so the inf is attained; this needs
  care with `ENNReal.ofReal`, `iInf`. Also `∃ t ∈ [0,s], X p t = 0 ↔ ∀ k : ℕ, ∃ q : ℚ, q ∈ [0,s] ∧ |X p q| < 1/(k+1)`, by Lipschitz
  continuity, density of `ℚ`, and compactness of `[0,s]`.
- The right-hand side is a countable intersection/union of measurable sets, so `{p | T p ≤ ofReal s}` is measurable. Conclude with a
  measurability criterion for `ENNReal`-valued maps from sets `{f ≤ c}` (e.g. `measurable_of_Iic`, or via `ENNReal.ofReal`/rational `c`).
  Alternatively express `T` as an `iInf` over a countable family.
- Any correct approach is fine, e.g. `MeasureTheory.hitting`-style lemmas if they apply.

**L3. Integration.**
- `expectedMeetingTime S₁ S₂ = (1/4) * ∑∑ ∫⁻ T…`. Use `lintegral_finset_sum`, which needs measurability (L2), to get
  `(1/4) * ∫⁻ (∑∑ T…)`.
- By L1 this is `≥ (1/4) * ∫⁻ 13 = (1/4) * 13`. The product of probability measures is a probability measure.
- Hence `13/4 ≤ ⨅ S₁ S₂, …` by `le_iInf₂`. With part U, `le_antisymm` gives the theorem.

## Return
A structured result: status OK / PARTIAL, file paths, the exact `check.sh` tail, and a short paper-style proof description.
