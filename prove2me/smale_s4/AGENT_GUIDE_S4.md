# Guide for proof agents (Prove2Me workspace): Smale's question mission, provable children

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. `export PATH="$HOME/.elan/bin:$PATH"`.
- Definitions (READ FIRST): `Definitions/Def_SmaleDiffS4_Basic.lean`: `E n = EuclideanSpace ℝ (Fin n)`; `DiffDisk n = {f : Diffeomorph 𝓘(ℝ, E n) 𝓘(ℝ, E n) (E n) (E n) ∞ // ∀ x, 1 ≤ ‖x‖ → f x = x}`; `diskJet n f k = UniformFun.ofFun (iteratedFDeriv ℝ k f.1)`; the topology on `DiffDisk n` is `TopologicalSpace.induced (diskJet n) inferInstance` (product over k of the uniform-convergence topologies); `1 : DiffDisk n` is the identity.
- Targets: `Theorems/Thm_SmaleDiffS4_continuous_of_smoothIsotopy.lean` (B) and `Theorems/Thm_SmaleDiffS4_diffDisk_one_pathConnected.lean` (C).
- Type-check: `./check.sh Solutions/<file>.lean` (CHECK OK only with no errors and no sorry). Scratch: `Solutions/Scratch_S4_<key>*.lean`. Never `lake build`; never edit Theorems/, Definitions/, .lake/, or other agents' files.
- File layout: `import Mathlib`, `import Definitions.Def_SmaleDiffS4_Basic` (C may also `import Theorems.Thm_SmaleDiffS4_continuous_of_smoothIsotopy` and use `SmaleDiffS4.continuous_of_smoothIsotopy`; its local body is sorry, intended — it is a separate platform theorem), `set_option autoImplicit false`, `open SmaleDiffS4`, `open scoped ContDiff Manifold`, helpers in `namespace SmaleDiffS4.S4_<key> … end`, then a TOP-LEVEL `theorem solution` copying the target's binders and conclusion exactly.
- No sorry/admit/native_decide/axioms. Keep compile time small.

## B. continuous_of_smoothIsotopy
Goal: `Continuous g` for `g : Set.Icc 0 1 → DiffDisk n` with `(g t).1 x = F (t, x)`, `F` jointly C^∞.
1. `continuous_induced_rng` reduces to continuity of `diskJet n ∘ g`; `continuous_pi` to each k; for a `UniformFun` target use `UniformFun.tendsto_iff_tendstoUniformly` (or the basis of the uniformity) to reduce continuity at t₀ to: `iteratedFDeriv ℝ k (g t).1 → iteratedFDeriv ℝ k (g t₀).1` uniformly on `E n` as t → t₀.
2. `(g t).1 = fun y => F (t, y)` (funext with hg), so the k-th derivative is Ψ(t,x) := iteratedFDeriv ℝ k (fun y => F (t, y)) x.
3. Continuity of Ψ in (t, x): `fun y => F (t, y)` is F composed with the affine map y ↦ (t,0) + inr y, so Ψ(t,x) = (iteratedFDeriv ℝ k F (t,x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ ℝ (E n)) (`ContinuousLinearMap.iteratedFDeriv_comp_right`, `iteratedFDeriv_comp_add_left`/`_right`); then `hF.continuous_iteratedFDeriv` and continuity of `ContinuousMultilinearMap.compContinuousLinearMapL` (or prove continuity of the composition directly).
4. Outside the closed unit ball nothing moves: for ‖x‖ > 1 and t ∈ [0,1], (g t).1 agrees with id on the open set {‖y‖ > 1}, so Ψ(t,x) = iteratedFDeriv ℝ k id x for all such t (`Filter.EventuallyEq.iteratedFDeriv_eq` or similar; grep). Hence the difference Ψ(t,x) − Ψ(t₀,x) vanishes off the closed ball.
5. On the compact set (closed interval around t₀) × closedBall 0 1, Ψ is uniformly continuous, giving uniform convergence on the ball (`IsCompact.uniformContinuousOn_of_continuous`, `ContinuousOn.tendstoUniformlyOn`, grep `tendstoUniformlyOn` + compact). Combine with step 4.

## C. diffDisk_one_pathConnected
Goal: `PathConnectedSpace (DiffDisk 1)`. Plan: for f ∈ DiffDisk 1 join 1 to f by g t := the diffeomorphism x ↦ (1 − t) • x + t • f x, t ∈ [0,1], and use B for continuity (then PathConnected as in: refine ⟨⟨1⟩, fun f g => (joined_one f).symm.trans (joined_one g)⟩).
1. E 1 is one-dimensional: work with the coordinate x 0 (or the linear isometry `EuclideanSpace` ≃ ℝ for Fin 1). The derivative of f at x is v ↦ a(x) • v with a(x) := (fderiv ℝ f x (EuclideanSpace.single 0 1)) 0; a is continuous, never 0 (f is a diffeomorphism, so its derivative is invertible), and a = 1 where ‖x‖ > 1. Since E 1 is connected, a > 0 everywhere (IVT / `IsPreconnected` argument).
2. For t ∈ [0,1], h_t(x) := (1 − t) • x + t • f x is smooth, has derivative ((1 − t) + t a(x)) • id with (1 − t) + t a(x) > 0, equals x for ‖x‖ ≥ 1, and is a bijection of E 1 (strictly increasing in the coordinate and equal to the identity outside [−1, 1]; or: injective by monotonicity, surjective by continuity/IVT).
3. Build the diffeomorphism: a Homeomorph from the bijection (continuous inverse via strict monotonicity or `Continuous.homeoOfEquivCompactToT2`-style arguments are not available here; use e.g. `Homeomorph` from a continuous open bijection, or `ContinuousLinearEquiv`-free arguments), smoothness of the inverse from the inverse function theorem (`Homeomorph.contDiff_symm` with derivative `ContinuousLinearEquiv` at each point; grep), and package as `Diffeomorph` (`contMDiff_iff_contDiff` for the model `𝓘(ℝ, E 1)`).
4. Continuity of t ↦ g t by B with F(t,x) = (1 − t) • x + t • f x (jointly smooth: `ContDiff.add`, `ContDiff.smul`, `f.1.contDiff` from `Diffeomorph.contMDiff_toFun` + `contMDiff_iff_contDiff`).

## Return
Structured result: status OK/PARTIAL, file, check_tail, proof_description, remaining.
