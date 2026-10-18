# Guide for proof agents (Prove2Me workspace): Lindelöf-hypothesis mission milestones

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. Run `export PATH="$HOME/.elan/bin:$PATH"` first.
- Definitions (READ FIRST):
  - `Definitions/Def_LindelofHypothesis_GrowthAndZeroCounts.lean` defines
    `LindelofHypothesis.mu σ : EReal := sInf ((↑) '' {a : ℝ | (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T => T ^ a)})`.
  - `Definitions/Def_RiemannVonMangoldt_ZeroCounts.lean` defines
    `RiemannVonMangoldt.LindelofHypothesis := ∀ ε > 0, (fun t : ℝ => riemannZeta (1/2 + t * I)) =O[atTop] (fun t => t ^ ε)`.
- TARGETS, mirrors in `Theorems/` and already built (do NOT edit). The preamble is `import Mathlib` + both Definitions, then
  `open Complex Filter Asymptotics` and `open scoped ENNReal`.
  1. `LindelofHypothesis.mu_eq_zero_of_one_lt (σ : ℝ) (hσ : 1 < σ) : mu σ = 0`.
  2. `LindelofHypothesis.lindelof_iff_isLittleO : RiemannVonMangoldt.LindelofHypothesis ↔ ∀ ε : ℝ, 0 < ε → (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =o[atTop] (fun t : ℝ => t ^ ε)`.
  3. `LindelofHypothesis.lindelof_iff_mu_half_eq_zero : RiemannVonMangoldt.LindelofHypothesis ↔ mu (1 / 2) = 0`.
  4. `LindelofHypothesis.mu_convex : ∃ f : ℝ → ℝ, ConvexOn ℝ Set.univ f ∧ ∀ σ : ℝ, mu σ = (f σ : EReal)`. Note that this requires
     μ to be FINITE on every vertical line, σ ∈ ℝ.
- A useful Proved platform theorem, importable as `import Theorems.Thm_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip`:
  `PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip (a b α) (hab : a < b) (hα : 0 ≤ α)`.
  - Conclusion: `∃ C > 0, ∀ f M, 0 ≤ M → DiffContOnCl ℂ f (re ⁻¹' Ioo a b) → (∃ c < π/(b-a), ∃ B, ∀ z in the open strip, ‖f z‖ ≤ exp (B * exp (c * |z.im|))) → (‖f‖ ≤ M (1+|im|)^α on re = a) → (same on re = b) → ‖f z‖ ≤ C M (1+|z.im|)^α on the closed strip`.
  - It has the SAME exponent on both lines.
  - Mathlib also has `PhragmenLindelof.vertical_strip`, Hadamard three lines (`Mathlib/Analysis/Complex/Hadamard.lean`),
    `riemannZeta_one_sub` (functional equation), `zeta_eq_tsum_one_div_nat_cpow` (Re s > 1),
    `riemannZeta_eulerProduct*`, `riemannZeta_ne_zero_of_one_le_re`, `Complex.Gamma`, `Complex.Gamma_mul_Gamma_one_sub`, and so on.
    Search Mathlib (`grep -rn` under `.lake/packages/mathlib/Mathlib`) before reproving anything.
- Type-check with `./check.sh Solutions/<file>.lean` (CHECK OK) and experiment with `lake env lean Solutions/Scratch_LH_<key>_*.lean`.
  NEVER run `lake build`. Only touch your own files. You may READ other agents' files and COPY lemma text from them.

## Solution files
`Solutions/Sol_LindelofHypothesis_<name>.lean`, with this layout:
```lean
import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
-- optional: import Theorems.Thm_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip  (Proved platform theorem)

set_option autoImplicit false
open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis.LH<Key>
... helpers ...
end LindelofHypothesis.LH<Key>

open LindelofHypothesis in
theorem solution : <exactly the target's type> := ...
```
- `theorem solution` is TOP-LEVEL. Check it with `example : (type_of% @solution) = (type_of% @LindelofHypothesis.<name>) := rfl` in a
  scratch copy that also imports `Theorems.Thm_LindelofHypothesis_<name>`.
- No `sorry`, `admit` or `native_decide`. `#print axioms solution` must be ⊆ {propext, Classical.choice, Quot.sound}. Importing the Proved
  PL platform theorem is allowed: its local stub shows `sorryAx`, and that is the only acceptable source of `sorryAx`. Say so in your
  report and confirm that every other lemma is clean.
- Keep compile time under 150 s.

## Shared lemmas about `mu` (prove once, then copy)
- (M1) If `ζ(σ+iT) = O(T^a)` then `mu σ ≤ a` (`sInf_le`).
- (M2) If `mu σ < a` (a real), then `ζ(σ+iT) = O(T^a)`: there is `a' < a` in the set, and `T^{a'} ≤ T^a` eventually.
- (M3) If `‖ζ(σ+iT)‖ ≥ c > 0` eventually, then `mu σ ≥ 0`, because `O(T^a)` with `a < 0` would force `ζ → 0`.

## Target 1: μ(σ) = 0 for σ > 1
- Upper bound: `‖ζ(σ+iT)‖ ≤ ∑ n^{-σ}` (`zeta_eq_tsum_one_div_nat_cpow`, norm of a tsum), so `O(T^0)` and μ ≤ 0.
- Lower bound: from the Euler product, `‖ζ(s)‖ ≥ ∏_p (1 + p^{-σ})^{-1} = ζ(2σ)/ζ(σ) > 0`. Alternatively use any positive lower bound,
  e.g. `‖ζ(s)‖ ≥ 1 - ∑_{n≥2} n^{-σ}` for large σ — but that only works for σ > ~1.73, so use the Euler product, or
  `ζ(s)·∑ μ(n) n^{-s} = 1` (Möbius) with `‖∑ μ(n) n^{-s}‖ ≤ ζ(σ)`, giving `‖ζ(s)‖ ≥ 1/ζ(σ)`. Mathlib has Dirichlet-series identities for
  `LSeries` with Möbius; search `LSeries_mu`/`moebius` in `Mathlib/NumberTheory/LSeries`.
- Then (M3) gives μ ≥ 0.

## Target 2: big-O ⇔ little-o
- (⇒) `O(t^{ε/2})` is `o(t^ε)`, since `t^{ε/2} = o(t^ε)` as `t → ∞`.
- (⇐) `o` implies `O`.

## Target 3: LH ⇔ μ(1/2) = 0
- (⇐) Given ε, `mu (1/2) = 0 < ε`, so (M2) gives `O(t^ε)`.
- (⇒) LH gives `mu (1/2) ≤ ε` for all ε, by (M1), so `mu (1/2) ≤ 0`. For `mu (1/2) ≥ 0`, suppose `ζ(1/2+iT) = O(T^{-δ})`.
  - Use Phragmén–Lindelöf on the strip `1/2 ≤ Re s ≤ 5/2` for `F(s) = ζ(s)·(s-1)/(s+1)`. It is holomorphic, the pole is removed,
    and the factor tends to 1.
  - Show the interpolated bound gives `ζ(3/2 + iT) = O(T^{-δ/2})`. This contradicts `‖ζ(3/2+iT)‖ ≥ c > 0` (target-1 lower bound).
  - Different exponents on the two lines need the auxiliary weight trick. Multiply by `G(s) = exp(κ(s) · log(-i(s - c)))` for
    suitable linear `κ` and large `c`, handling `t → +∞` and `t → -∞` separately (or using `(s + K)^{w(s)}` with real-part
    control), so that both boundary exponents become 0. This is the classical proof of convexity of μ (Titchmarsh §5.65, or
    Iwaniec–Kowalski 5.A).
  - The equal-exponent PL platform theorem then applies to `F·G`.
  - The a priori growth condition (`≤ exp(B exp(c|t|))`, `c < π/(b-a)`) follows from a crude polynomial bound for ζ in
    `Re s ≥ 1/2`, `|t| ≥ 1`. That bound needs ζ for `Re s > 0`: `ζ(s) = s/(s-1) - s ∫_1^∞ {x} x^{-s-1} dx`, or
    `ζ(s) = ∑_{n≤N} n^{-s} + N^{1-s}/(s-1) - s ∫_N^∞ {x} x^{-s-1} dx`. Prove it by the identity theorem: both sides are analytic for
    Re s > 0 and agree for Re s > 1, by Abel summation. Check Mathlib first: there may already be a representation or growth bound
    for `riemannZeta` in the critical strip (search `riemannZeta` with `isBigO`, `norm_le`, `HurwitzZeta`).
  - Alternatively prove `mu (1/2) ≥ 0` any other rigorous way.

## Target 4: μ is real-valued and convex (the hardest)
1. **Polynomial bounds on every vertical line, uniformly in strips.**
   - For `Re s ≥ 1/2` and |t| ≥ 1 use the bound from target 3.
   - For `Re s ≤ 1/2` use the functional equation `ζ(1-s) = 2(2π)^{-s} Γ(s) cos(πs/2) ζ(s)` (`riemannZeta_one_sub`). This needs
     `|Γ(σ+it) cos(π(σ+it)/2)| ≤ C (1+|t|)^{K}` on strips.
   - Get it from `|Γ(1/2+it)|² = π/cosh(πt)`, by reflection `Γ(s)Γ(1-s) = π/sin(πs)`, and the recurrence `Γ(s+1) = sΓ(s)`.
   - Strips are handled by PL applied to `h(s) = Γ(s)·exp(∓iπs/2)`, using `|Γ(σ+it)| ≤ Γ(σ)` for σ > 0 as the a priori bound,
     since `π/2 < π/width` for width 1.
2. **Convexity inequality.** For σ₁ < σ₂, if `ζ = O(T^{a₁})` on σ₁ and `O(T^{a₂})` on σ₂, then on σ = λσ₁+(1-λ)σ₂ it is
   `O(T^{λa₁+(1-λ)a₂})`. Use PL with the auxiliary weight. For lines crossing `Re s = 1`, use `F(s) = ζ(s)(s-1)/(s+1)`.
3. Define `f σ :=` the real value of `mu σ`. Show `mu σ ≠ ⊤` from step 1 and `mu σ ≠ ⊥`: if `mu σ₀ = ⊥`, the convexity
   inequality between σ₀ and σ₂ = max(σ₀, 2) + 1 (where μ = 0, target 1) makes μ = ⊥ at a point > 1, a contradiction. Then pass the
   inequality to the infima to get `ConvexOn ℝ univ f`; arbitrary real upper exponents work, so take limits.

Build bottom-up in layered, sorry-free lemmas. Keep `Solutions/Scratch_LH_<key>_progress.md` updated with proved lemmas (names and
statements) and what remains, so a later round can continue.

## Return
Per target: status OK / PARTIAL, file path, the exact `check.sh` tail, a short proof description, and for PARTIAL the precise remaining
lemmas.
