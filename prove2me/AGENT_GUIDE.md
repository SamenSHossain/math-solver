# Guide for proof agents (Prove2Me workspace, Ghadimi–Lan RSG mission)

## Environment
- Workspace: `/root/prove2me_workspace`. Lean 4.33.1, Mathlib commit 0df444a (Oct 2026). Always `export PATH="$HOME/.elan/bin:$PATH"`.
- `Definitions/Def_ConvexOptAlg_SmoothGD_Defs.lean`, `Definitions/Def_GhadimiLan_RSG_Model.lean`: the platform definitions, verbatim. READ THEM FIRST.
- `Theorems/Thm_<slug>.lean`: platform theorem statements (bodies are `sorry`, that is expected). `<slug>` = theorem name with `.` → `_`.
- `Solutions/Sol_<slug>.lean`: the file that will be submitted for theorem `<slug>`.
- Type-check a file: `./check.sh Solutions/Sol_<slug>.lean` (runs `lake env lean`; ~30-60 s because of `import Mathlib`). Prints `CHECK OK` only when there are no errors and no `sorry`.
- Scratch experiments (`#check`, `exact?`, `apply?`, `simp?`): put them in `Solutions/Scratch_<yourname>.lean` and run `lake env lean Solutions/Scratch_<yourname>.lean`. Never run `lake build` (other agents share the build directory). Never edit files under `Theorems/`, `Definitions/` or `.lake/`.

## Hard rules for a submittable file (violations are rejected by the server)
1. The file contains a top-level `theorem solution <binders> : <type>` whose binders and conclusion are EXACTLY those of the target in `Theorems/Thm_<slug>.lean` (copy them; only the name changes). Do not wrap `solution` in a namespace or section with variables. Use `open GhadimiLan.RSG` (and `open ConvexOptAlg.SmoothGD` if needed) so the names resolve.
2. NEVER `import Theorems.Thm_<slug>` for the target itself. Importing OTHER platform theorems is allowed and encouraged (`import Theorems.Thm_ConvexOptAlg_SmoothGD_lemma_3_4` etc.); they are used by their full name (`ConvexOptAlg.SmoothGD.lemma_3_4`).
3. No `sorry`, no `admit`, no `native_decide`, no axioms. Helper lemmas in the same file (before `solution`) are fine; make them `private` or namespace them under `GhadimiLan.RSG.Sol_<slug>` to avoid name clashes with Mathlib.
4. Start the file with the target's preamble (copy from the Thm file: `import Mathlib`, the two `import Definitions.Def_...`, `open MeasureTheory ProbabilityTheory`, `open scoped InnerProductSpace`) and add `set_option autoImplicit false` (the server elaborates with autoImplicit off; `lake env lean` does not apply the lakefile options, so set it explicitly).
5. Keep it robust: avoid fragile `simp` calls on huge goals; prefer explicit lemma names. The server has a 300 s compile limit; keep elaboration reasonable (no `import Mathlib`-wide `exact?` left in the final file).

## Mathlib at this commit — naming cautions (always confirm with grep, never guess)
- Search: `grep -rn "theorem NAME" .lake/packages/mathlib/Mathlib | head` or `grep -rln "condExp_mul" .lake/packages/mathlib/Mathlib`.
- Conditional expectation is `MeasureTheory.condExp` (notation `μ[f|m]`), lemmas are `condExp_*` (not `condexp_*`). Files: `Mathlib/MeasureTheory/Function/ConditionalExpectation/*.lean`, `Mathlib/Probability/ConditionalExpectation.lean` (independence ↔ condExp), `Mathlib/Probability/Independence/Basic.lean` (IndepFun lemmas, `IndepFun.comp`, `IndepFun.integral_mul`).
- `MemLp` (not `Memℒp`), `memLp_two_iff_integrable_sq`, `MemLp.integrable_sq`, `MemLp.add`, `MemLp.const_mul`, `Integrable`, `Integrable.const_mul`, `integral_finset_sum`, `integral_const_mul`, `integral_add`, `integral_sub`, `integral_mono`, `integral_condExp`, `setIntegral_*` (not `set_integral_*`).
- `Measurable.prodMk` (not `prod_mk`), `Measurable.comp`, `Measurable.eval`, `measurable_pi_apply`, `measurable_pi_lambda`, `Measurable.mono` (change σ-algebra), `Filtration.le`, `Filtration.mono`.
- Inner product on `EuclideanSpace ℝ (Fin n)`: notation `⟪a, b⟫_ℝ`; `real_inner_self_eq_norm_sq`, `inner_add_right`, `inner_sub_right`, `inner_smul_right`, `inner_neg_right`, `real_inner_comm`, `norm_sub_sq_real`, `norm_add_sq_real`, `norm_smul`, `abs_real_inner_le_norm`, `real_inner_le_norm`. Coordinates: `EuclideanSpace.inner_eq_star_dotProduct`, `PiLp.inner_apply`.
- `IsGLB (Set.range f) fstar`: `hfstar.1 ⟨x, rfl⟩ : fstar ≤ f x` (lower bound), `hfstar.2` for the greatest part.
- `Finset.sum_Icc_succ_top`, `Finset.sum_Ioc_...`, `Finset.sum_le_sum`, `Finset.sum_congr`, `Finset.mem_Icc`. Induction on `N` with `Finset.Icc 1 (N+1) = insert (N+1) (Finset.Icc 1 N)` via `Finset.sum_Icc_succ_top (by omega)`.
- Lipschitz ⇒ continuous ⇒ measurable: build `LipschitzWith` from `hf.2.2` with `LipschitzWith.of_dist_le_mul` (dist = ‖x - y‖ via `dist_eq_norm`), then `.continuous.measurable`.

## What to return (the last message IS the return value)
Return a JSON-like summary: `status` (OK / PARTIAL), `file`, the exact `check.sh` output tail, `imports_of_platform_theorems` used, a precise mathematical description of the proof (steps, lemmas used) suitable for a paper-style explanation, and for PARTIAL the exact remaining goals and what was tried.
