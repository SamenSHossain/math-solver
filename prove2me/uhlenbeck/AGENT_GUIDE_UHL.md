# Guide for proof agents (Prove2Me workspace, Uhlenbeck gauge-theory mission)

## Environment
- Workspace: `/root/prove2me_workspace`. Lean 4.33.1, Mathlib commit 0df444a. Always `export PATH="$HOME/.elan/bin:$PATH"`.
- `Definitions/Def_uhlenbeck_gauge_box_defs.lean`: the platform definitions (R4, Mat, IsSuN, levi, TwoForm, IsAntisymm, IsSuNValued, hodgeStar, normSq, trWedge, IsSelfDual, IsAntiSelfDual, Connection, IsSUConnection, partialDeriv, curvature, chernSimonsCurrent, boundaryChernSimons, yangMills, OnBoxBoundary). READ IT FIRST, every definition.
- `Theorems/Thm_UhlenbeckGauge_<name>.lean`: platform theorem statements (bodies are `sorry`, expected). Module name = `Theorems.Thm_UhlenbeckGauge_<name>`, Lean name = `UhlenbeckGauge.<name>`. Already PROVED on the platform (safe to import, importing them keeps a proof a direct proof):
  - `norm_add_hodgeStar_sq` (Lemma 3.1.2): for antisymmetric su(n)-valued F, in ℂ: `normSq (F + ⋆F) = 2 normSq F − 2 trWedge F` and `normSq (F − ⋆F) = 2 normSq F + 2 trWedge F`.
  - `trWedge_curvature_eq_div_chernSimons` (Fact 3.1.3 local form).
  - `integral_trWedge_eq_boundaryChernSimons` (Fact 3.1.3 box form): `a ≤ b → IsSUConnection A → ∫ x in Icc a b, trWedge (curvature A x) = boundaryChernSimons a b A`.
- Accepted platform proofs of those three, written by another user, are in `/tmp/claude-0/-home-user-math-solver/ee9f98fb-9768-5748-b1b3-ebbf1e9b4bc0/scratchpad/uhl_ref/` (m0 = Lemma 3.1.2, m1 = local transgression, m2 = box Stokes). They contain WORKING helper lemmas you may copy into your file as `private` lemmas: `levi_repeat01..23` (levi with a repeated index is 0), `levi_eval` (explicit table), `hodge_01..23`, `trace_norm_cast`, `normSq_six`, `smooth_pd` (partial derivative of a smooth matrix function is smooth), `smooth_mul`, `smooth_trace`, `smooth_current`, and the use of `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`.
- `Solutions/<file>.lean`: the file that will be submitted. Type-check with `./check.sh Solutions/<file>.lean` (runs `lake env lean`; prints `CHECK OK` only with no errors and no `sorry`).
- Scratch experiments: `Solutions/Scratch_<yourkey>.lean`, run `lake env lean Solutions/Scratch_<yourkey>.lean`. Never run `lake build`. Never edit `Theorems/`, `Definitions/`, `.lake/`, or other agents' files.

## Hard rules for a submittable file
1. Top-level `theorem solution <binders> : <type>` with binders and conclusion EXACTLY those of the target theorem (copy them; only the name changes). Not inside a namespace or a section with variables.
2. Start with the target's preamble: `import Definitions.Def_uhlenbeck_gauge_box_defs`, then any allowed `import Theorems.Thm_UhlenbeckGauge_...`, then `open UhlenbeckGauge` (add `Matrix MeasureTheory` etc. as needed) and `set_option autoImplicit false`.
3. NEVER import the target's own module. No `sorry`, `admit`, `native_decide`, axioms. `set_option maxHeartbeats` up to 0 is tolerated by the server (the accepted proofs use `maxHeartbeats 0`), but keep total compile time well under 300 s.
4. Helper lemmas go above `solution`, marked `private` (or in a namespace `UhlenbeckGauge.Sol_<key>`) to avoid clashes.

## Mathlib naming cautions (confirm with grep or #check, never guess)
- `grep -rn "theorem NAME" .lake/packages/mathlib/Mathlib | head`.
- Integrals: `MeasureTheory.integral_mono`, `setIntegral_mono_on`, `integral_re` (∫ re f = re ∫ f, needs Integrable), `integral_neg`, `integral_congr_ae`, `setIntegral_congr_fun` / `setIntegral_congr_ae`, `setIntegral_eq_zero_iff_of_nonneg_ae`, `integral_nonneg`, `ContinuousOn.integrableOn_compact` with `isCompact_Icc`, `Real.volume_Icc_pi`, `Measure.restrict_eq_zero`.
- Continuity / a.e. → everywhere: `MeasureTheory.Measure.eqOn_of_ae_eq` (needs `s ⊆ closure (interior s)` and `[IsOpenPosMeasure μ]`), `Set.pi_univ_Icc`, `interior_pi_set`, `closure_pi_set`, `interior_Icc`, `closure_Ioo`.
- Smoothness: `ContDiff.continuous`, `ContDiff.fderiv_right`, `ContDiff.clm_apply`, `ContDiff.differentiable`, `contDiff_const`. Derivatives: `fderiv_const_mul`, `fderiv_sum`, `Filter.EventuallyEq.fderiv_eq`, `HasFDerivAt.comp`, `Complex.conjCLE`, `ContinuousLinearMap.fderiv`, `fderiv_comp`.
- Matrices: `Matrix.conjTranspose_mul`, `Matrix.conjTranspose_sub`, `Matrix.trace_mul_comm`, `Matrix.trace_sub`, `Matrix.ext`, `Matrix.of_apply`, `Matrix.conjTranspose_apply`.

## What to return (your last message IS the return value)
Structured result: status OK/PARTIAL, file, check tail, platform imports used, a precise mathematical description of the proof suitable for a paper-style explanation, and for PARTIAL the exact remaining goals and what was tried.
