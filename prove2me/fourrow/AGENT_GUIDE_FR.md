# Guide for proof agents (Prove2Me workspace, target OAI.FourRow.robust_permanent)

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. `export PATH="$HOME/.elan/bin:$PATH"`.
- Definitions: `Definitions/Def_FourRowPermanent.lean` (namespace `OAI.FourRow`, inside `noncomputable section`): `Site := Fin 4`, `Perm := Equiv.Perm Site`, `Law := Perm → ℝ`, `Functions := Site → Site → ℝ`, `IsProbability ν := (∀ π, 0 ≤ ν π) ∧ ∑ π, ν π = 1`, `UniformMarginals ν := ∀ i j, ∑ π, (if π i = j then ν π else 0) = 1/4`, `totalVariation ν := (∑ π, |ν π - 1/24|)/2`, `lpNorm p f := ((∑ j, (f j) ^ p) / 4) ^ (1 / p)` (real powers, rpow), `permanentExpectation ν f := ∑ π, ν π * ∏ i, f i (π i)`. READ IT FIRST.
- Target: `Theorems/Thm_OAI_FourRow_robust_permanent.lean`.
- Type-check: `./check.sh Solutions/<file>.lean` (prints CHECK OK only with no errors and no sorry). Scratch: `Solutions/Scratch_FR_<key>*.lean` with `lake env lean <file>`. Never `lake build`; never edit Theorems/, Definitions/, .lake/, or other agents' files.
- Every part file starts with:
  ```
  import Mathlib
  import Definitions.Def_FourRowPermanent

  set_option autoImplicit false

  open OAI.FourRow
  ```
  followed by the VERBATIM contents of `Solutions/FR_common_block.txt` (shared helper definitions `rowSq`, `rowDist`, `totalDist`, `uniformLaw` in namespace `OAI.FourRow.Sol`), followed by `namespace OAI.FourRow.Sol` … your lemmas … `end OAI.FourRow.Sol`. Do not change the common block; other parts depend on it.
- The final merged file will contain the common block once and all parts, so every helper lemma name must be UNIQUE ACROSS PARTS: prefix every helper you add with your part letter (`A_`, `B_`, `C_`, `D_`). The exported lemma names below are fixed.
- No sorry/admit/native_decide/axioms in a finished part. Keep each `nlinarith`/`ring`/`simp` call fast; aim for each part to compile in < 60 s.

## Constants (fixed)
p₀ = 2 − 1/2000, ε = 1/25000. Check: 4/3 < p₀ < 2, 9/5 ≤ p₀, and 6ε + 5(2 − p₀)/8 = 6/25000 + 5/16000 = 0.0005525 ≤ 1/1728 ≈ 0.0005787.

## Exported lemma statements (fixed; all in namespace OAI.FourRow.Sol, with `open OAI.FourRow`)
Part A:
  theorem uniform_stability (f : Functions) (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
      permanentExpectation uniformLaw f ≤ 1 - totalDist f / 1728
Part B:
  theorem perturbation (ν : Law) (hp : IsProbability ν) (hm : UniformMarginals ν)
      (f : Functions) (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
      permanentExpectation ν f ≤ permanentExpectation uniformLaw f + 6 * totalVariation ν * totalDist f
Part C:
  theorem norm_lower (p : ℝ) (hp0 : 9 / 5 ≤ p) (hp2 : p ≤ 2) (f : Functions) (hf : ∀ i j, 0 ≤ f i j)
      (hn : ∀ i, rowSq (f i) = 4) :
      1 - (5 * (2 - p) / 8) * totalDist f ≤ ∏ i, lpNorm p (f i)
Part D: the top-level `theorem solution` (exact statement of the target, outside any namespace, after `open OAI.FourRow OAI.FourRow.Sol`), proved from A, B, C. While A–C are being written, put their exact statements in your file as `theorem … := by sorry` placeholders (clearly marked) so your part type-checks; the assembler will replace them.

## Mathematics (blueprint; source: OpenAI, "A strict four-row permanent inequality and permutation moments", 2026)
Notation: rows a, b : Site → ℝ, nonnegative, normalized rowSq = 4 (i.e. the normalized L² norm is 1). Then each entry satisfies a j ≤ 2 (a j² ≤ rowSq a = 4), and rowDist a = 8 − 2 Σ a j ≤ 8.

Part A (exponent-two inequality with stability, uniform law).
1. Pair entries. For two rows a, b and the six 2-subsets {j<k} of Site in the order {0,1},{0,2},{0,3},{1,2},{1,3},{2,3}, put x_S(a,b) = a j * b k + a k * b j. The complement of the m-th subset is the (5−m)-th subset. Generalized Laplace expansion: Σ_{π} ∏_i f i (π i) = Σ_{m=0}^{5} x_{S_m}(f 0, f 1) · x_{S_{5−m}}(f 2, f 3). Prove by expanding the sum over the 24 permutations of Fin 4: e.g. `Equiv.Perm.decomposeFin : Perm (Fin (n+1)) ≃ Fin (n+1) × Perm (Fin n)` with `Equiv.sum_comp`, `Fintype.sum_prod_type`, `Equiv.Perm.decomposeFin_symm_apply_zero`, `Equiv.Perm.decomposeFin_symm_apply_succ`, `Fin.sum_univ_succ`, `Fin.prod_univ_four`, `Equiv.swap_apply_def`, then `ring`. (Any correct way to enumerate the 24 permutations is fine.)
2. pairSq(a,b) := Σ_m x_{S_m}(a,b)² = rowSq a · rowSq b + ⟨a,b⟩² − 2 Σ_j a j² b j² (ring identity).
3. pairSq(a,b) ≤ 24 for normalized nonneg rows: ⟨a,b⟩² ≤ 4 Σ_j (a j b j)² (Cauchy–Schwarz against the all-ones vector, `Finset.sum_mul_sq_le_sq_mul_sq`) and ⟨a,b⟩² ≤ rowSq a rowSq b = 16, so pairSq ≤ 16 + ⟨a,b⟩² − ⟨a,b⟩²/2 ≤ 24.
4. Stability: rowDist a + rowDist b ≤ 18 (24 − pairSq(a,b)). With t = ⟨a,b⟩ ∈ [0,4], s = Σ (a j b j)², D = 24 − pairSq = 8 − t² + 2s, d = Σ (a j − b j)² = 8 − 2t, e = Σ (a j b j − 1)² = s − 2t + 4: d ≤ D (because 2s ≥ t²/2 and t ≤ 4) and 2e ≤ D (D − 2e = t(4 − t)). Pointwise, for 0 ≤ a j ≤ 2 and b j ≥ 0: (a j − 1)² ≤ (a j² − 1)² ≤ 2(a j² − a j b j)² + 2(a j b j − 1)² ≤ 8(a j − b j)² + 2(a j b j − 1)². Summing, rowDist a ≤ 8d + 2e ≤ 9D, and the same for b.
5. With U = pairSq(f 0, f 1), V = pairSq(f 2, f 3) ∈ [0, 24]: by Cauchy–Schwarz on the expansion of step 1 (the reversed index is a bijection of Fin 6, e.g. `Fin.revPerm`), (Σ_π ∏ f)² ≤ U V, so with P = permanentExpectation uniformLaw f = (Σ_π ∏ f)/24 we get 576 P² ≤ U V ≤ 12(U + V) (as (24−U)V + (24−V)U ≥ 0). Stability gives totalDist f ≤ 18(48 − U − V). Hence P² ≤ 1 − totalDist/864, and since totalDist ≤ 32 < 864, P ≤ 1 − totalDist/1728 (if P ≤ 0 trivially; otherwise (1 − x/2)² ≥ 1 − x ≥ P²).

Part B (perturbation using exactly uniform marginals).
1. For 0 ≤ a i ≤ 2 (i : Fin 4) with g i = a i − 1: ∏ a − 1 − Σ g = g0 g1 + g2 g3 + A B where A = g0(1+g1) + g1, B = g2(1+g3) + g3 (ring). |xy| ≤ (x² + y²)/2, and A² ≤ ((1+g1)² + 1)(g0² + g1²) ≤ 5(g0² + g1²) (likewise B). So |∏ a − 1 − Σ (a i − 1)| ≤ 3 Σ (a i − 1)².
2. Marginal identity: if UniformMarginals ν then for every i and h : Site → ℝ, Σ_π ν π · h (π i) = (Σ_j h j)/4 (rewrite h (π i) = Σ_j [π i = j] h j, swap sums). The uniform law is a probability law with uniform marginals (each fibre {π | π i = j} has 6 elements).
3. Hence Σ_π (ν π − 1/24)(1 + Σ_i (f i (π i) − 1)) = 0, so permanentExpectation ν f − permanentExpectation uniformLaw f = Σ_π (ν π − 1/24) R(π) with R(π) = ∏ f i (π i) − 1 − Σ_i (f i (π i) − 1), |R(π)| ≤ 3 Σ_i (f i (π i) − 1)² ≤ 3 totalDist f. So the difference is ≤ (Σ_π |ν π − 1/24|) · 3 totalDist f = 6 totalVariation ν · totalDist f.

Part C (passing from exponent 2 to p ∈ [9/5, 2]).
1. For x ≥ 0, δ ≥ 0, 2 − δ > 0: x^(2−δ) ≥ x² − δ x² (x − 1). (x = 0: both sides 0, `Real.zero_rpow`. x > 0: x^(2−δ) = x² · exp(−δ log x) ≥ x²(1 − δ log x) ≥ x²(1 − δ(x − 1)) by `Real.add_one_le_exp` and `Real.log_le_sub_one_of_pos`; `Real.rpow_def_of_pos`, `Real.rpow_add`, `Real.rpow_two`/`Real.rpow_natCast`.)
2. For a normalized nonneg row: Σ_j a j²(a j − 1) ≤ (5/2) rowDist a, from the pointwise identity (5/2)(x−1)² + (x² − 1)/2 − x²(x−1) = (x−1)²(2 − x) ≥ 0 for x ≤ 2 and Σ (a j² − 1) = 0.
3. Hence (Σ_j a j ^ p)/4 ≥ 1 − (5(2−p)/8) rowDist a =: L. If L > 0 then L ≤ 1, L ≤ L^(1/p) (`Real.rpow_le_rpow_of_exponent_ge`, 1/p ≤ 1) ≤ ((Σ a^p)/4)^(1/p) (`Real.rpow_le_rpow`); if L ≤ 0 use lpNorm ≥ 0. So lpNorm p a ≥ 1 − (5(2−p)/8) rowDist a.
4. With e_i = (5(2−p)/8) rowDist (f i) ∈ [0, 1] (rowDist ≤ 8 and 2 − p ≤ 1/5): 1 − Σ e_i ≤ ∏ (1 − e_i) (induction over a Finset, or expand the four factors) ≤ ∏ lpNorm p (f i) (`Finset.prod_le_prod`).

Part D (assembly and homogeneity).
1. Normalized case (all rowSq (f i) = 4): permanentExpectation ν f ≤ 1 − D/1728 + 6 ε D ≤ 1 − (5(2−p₀)/8) D ≤ ∏ lpNorm p₀ (f i), with D = totalDist f ≥ 0 and totalVariation ν < ε.
2. General f: if some row has rowSq = 0, that row is identically 0 (a j² ≤ rowSq), so every product ∏ f i (π i) vanishes, permanentExpectation = 0 ≤ ∏ lpNorm (each lpNorm ≥ 0). Otherwise c i := √(rowSq (f i)/4) > 0, g i j := f i j / c i has rowSq = 4, permanentExpectation ν f = (∏ c i) · permanentExpectation ν g (`Finset.prod_mul_distrib`), and lpNorm p (fun j => c * a j) = c * lpNorm p a for c ≥ 0, p ≠ 0 (`Real.mul_rpow`, `Real.rpow_mul`, `Finset.mul_sum`).
3. `theorem solution` : refine ⟨2 - 1/2000, by norm_num, by norm_num, 1/25000, by norm_num, ?_⟩ and conclude.

## Return
Structured result: status OK/PARTIAL, file, check_tail, proof_description, remaining.
