# Guide for proof agents (Prove2Me workspace, Onsager reciprocal relations mission)

## Environment
- Workspace: `/root/prove2me_workspace`. Lean 4.33.1, Mathlib commit 0df444a. Always `export PATH="$HOME/.elan/bin:$PATH"`.
- `Definitions/Def_OnsagerReciprocal_basic.lean`: the platform definitions (namespace `OnsagerReciprocal`): `fluctuationWeight β x = Real.exp (-(1/2) * (x ⬝ᵥ (β *ᵥ x)))`, `fluctuationAverage β f = (∫ x, f x * fluctuationWeight β x) / ∫ x, fluctuationWeight β x`, `conjugate β x = β *ᵥ x`, `meanFluctuation lam t x₀ = NormedSpace.exp ((-t) • lam) *ᵥ x₀`, `meanConjugate β lam t x₀ = β *ᵥ meanFluctuation lam t x₀`, `kineticCoeff β lam = lam * β⁻¹`, `timeCorrelation β lam t i k = fluctuationAverage β (fun x => meanFluctuation lam t x i * x k)`. READ THE FILE FIRST.
- `Theorems/Thm_OnsagerReciprocal_<name>.lean`: platform theorem statements (bodies are `sorry`, expected). Module `Theorems.Thm_OnsagerReciprocal_<name>`, Lean name `OnsagerReciprocal.<name>`. Statements available: `integrable_norm_pow_mul_fluctuationWeight` (new: ‖x‖^m * w integrable for PosDef β), `kinetic_coefficients_relation`, `meanFluctuation_dynamics` (ξ(0)=x and HasDerivAt of s ↦ ξ(s) with value −(γ *ᵥ Ξ(t))), `timeCorrelation_hasDerivAt`, `conjugate_fluctuation_average` (⟨(βx)ᵢ xₖ⟩ = δᵢₖ), `reciprocity_at_time_zero`, and the root `onsager_reciprocal_relations`.
- `Solutions/<file>.lean`: the file to be submitted. Type-check with `./check.sh Solutions/<file>.lean` (runs `lake env lean`, ~30-60 s because of `import Mathlib`; prints `CHECK OK` only with no errors and no `sorry`).
- Scratch: `Solutions/Scratch_<key>.lean`, run `lake env lean Solutions/Scratch_<key>.lean`. Never run `lake build`. Never edit `Theorems/`, `Definitions/`, `.lake/`, or other agents' files.

## Hard rules for a submittable file
1. Top-level `theorem solution <binders> : <type>` with binders and conclusion EXACTLY those of the target (copy them; only the name changes). The target statements live inside `namespace OnsagerReciprocal`, so names like `timeCorrelation` are unqualified there: in your file either write `open OnsagerReciprocal` before `solution` or qualify the names; the elaborated type must be identical. Do not put `solution` inside a namespace.
2. Preamble: `import Mathlib`, `import Definitions.Def_OnsagerReciprocal_basic`, then any allowed `import Theorems.Thm_OnsagerReciprocal_...`, then `open Matrix` (plus `MeasureTheory` etc. as needed), `set_option autoImplicit false`.
3. NEVER import the target's own module. No `sorry`, `admit`, `native_decide`, axioms. Keep compile time well under 300 s.
4. Helper lemmas above `solution`, marked `private` or namespaced `OnsagerReciprocal.Sol_<key>`.

## Useful facts / names (confirm with grep or #check, never guess)
- `Matrix.PosDef`: check its definition at this commit (`grep -n "def PosDef" .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean`); for ℝ, `star x = x`. `hβ.1 : β.IsHermitian` gives `βᵀ = β` (`Matrix.IsHermitian`, `conjTranspose_eq_transpose_of_trivial`). Invertibility: `hβ.isUnit`, `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv` (need `IsUnit β.det`: `hβ.det_pos`, `Matrix.isUnit_iff_isUnit_det`).
- Matrix exponential: the norm on matrices is not a global instance. Use `attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra` (see Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean header). `NormedSpace.exp_zero`, `hasDerivAt_exp_smul_const`, `Matrix.mulVec_mulVec`, `Matrix.one_mulVec`, `Matrix.mulVec_single`, `hasDerivAt_pi`.
- Integrals: `integral_finset_sum`, `integral_mul_left`/`integral_const_mul`, `integral_mul_right`, `Integrable.mono'`, `integral_pos_iff_support_of_nonneg`, `norm_le_pi_norm` (|x k| ≤ ‖x‖ in the sup norm on `Fin n → ℝ`).
- Integration by parts on ℝⁿ: `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean; read its exact hypotheses).
- Decay: `integrable_one_add_norm` (Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean: `(1 + ‖x‖)^(-r)` integrable for `finrank < r` and an add-Haar measure), `integrable_rpow_mul_exp_neg_mul_sq` (1D), `Real.pow_div_factorial_le_exp`, `Real.add_one_le_exp`.
- One-sided derivatives: `HasDerivAt.hasDerivWithinAt`, `hasDerivWithinAt_const`, `HasDerivWithinAt.congr`, `uniqueDiffWithinAt_Ici` / `uniqueDiffOn_Ici`, `UniqueDiffWithinAt.eq_deriv`.

## What to return (your last message IS the return value)
Structured result: status OK/PARTIAL, file, check tail, platform imports used, a precise mathematical description of the proof suitable for a paper-style explanation, and for PARTIAL the exact remaining goals and what was tried.
