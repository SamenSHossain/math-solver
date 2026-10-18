# Guide for proof agents (Prove2Me workspace): DISPROOF of TailRiskSharing.RobustVaR.theorem6_robust_var_comonotonic

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. `export PATH="$HOME/.elan/bin:$PATH"`.
- Definitions (READ ALL FIRST): `Definitions/Def_TailRiskSharing_VaRConv_Setting.lean` (IsAtomless, distFn, VaRL, VaRR, Allocations, Side, VaRS), `..._VaRTail_Setting.lean`, `..._TailConv_Setting.lean` (Linf), `..._ComonoConv_Comonotone.lean` (Comonotone, ComonoAllocations, comonoInfConv), `..._RobustVaR_Setting.lean` (IsOptimalComonoAllocation), `..._RobustVaR_Wasserstein.lean` (wassersteinK, robustSet, robust).
- Target: `Theorems/Thm_TailRiskSharing_RobustVaR_theorem6_robust_var_comonotonic.lean`. The exact statement of our `theorem solution` (the negation of the whole quantified target) is in `Solutions/RV_statement.txt`; it has been checked to wrap exactly the target's type. Use it VERBATIM.
- Type-check: `./check.sh Solutions/<file>.lean` (CHECK OK only with no errors and no sorry). Scratch: `Solutions/Scratch_RV_<key>*.lean` with `lake env lean <file>`. Never `lake build`; never edit Theorems/, Definitions/, .lake/, or other agents' files.
- Every part file starts with:
  ```
  import Mathlib
  import Definitions.Def_TailRiskSharing_RobustVaR_Setting
  import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

  set_option autoImplicit false

  open MeasureTheory TailRiskSharing.RobustVaR
  ```
  then `namespace RVDisproof` … lemmas … `end RVDisproof`. A disproof may NOT import any `Theorems.*` module.
- Helper names must be unique across parts: prefix helpers with your part letter (`A_`, `B_`, `C_`). Exported names below are fixed.
- No sorry/admit/native_decide/axioms in a finished part; keep compile time small.

## Why the statement is false (the counterexample)
The formal `ComonoAllocations P dom n X` only asks each component to be comonotone WITH X: `Comonotone P (Xs i) X := ∃ Ω₀, MeasurableSet Ω₀ ∧ P Ω₀ = 1 ∧ ∀ ω ω' ∈ Ω₀, 0 ≤ (Xs i ω - Xs i ω') * (X ω - X ω')`. For the constant X = 0 the product is always 0, so EVERY allocation of 0 into L^∞ is "comonotonic" (the paper requires the components to be comonotone with each other).
Instance: m = 1 (two agents), Λ = Side.L, δs = fun _ => 1, α = 3/4, X = fun _ => 0, on an atomless probability space with an event A of probability 1/2. Let Z := fun ω => if ω ∈ A then -4 else 4 (so P{Z ≤ -4} = 1/2 and P{-Z ≤ -4} = 1/2).
- (Z, -Z) is in ComonoAllocations (both in Linf, they sum to 0 pointwise, each comonotone with the constant 0 with Ω₀ = univ).
- Key bound (Part B): robust P 1 1 (VaRL P (3/4)) Z' ≤ 4 - K whenever Z' ∈ Linf and P{Z' ≤ -K} ≥ 1/2. Applied with K = 4 to Z and -Z: each robust value ≤ 0, so the allocation's value is ≤ 0, hence comonoInfConv ≤ 0 (`iInf₂_le` / `biInf_le`).
- The claimed right-hand side is robust P 1 1 (VaRL P (3/4)) 0 + 1/(3/4) ≥ 0 + 4/3 > 0 (Part C: robust of 0 is ≥ 0, because 0 itself lies in the ball, VaRL P (3/4) 0 = 0, and sSup of a set not bounded above is 0 by `Real.sSup_of_not_bddAbove`). So the first conjunct's equation fails, and the whole statement fails.

## Exported statements (fixed; all inside `namespace RVDisproof`)
Part A (an atomless probability space in every universe):
  theorem A_space : ∃ P : Measure (ULift.{u} ℝ), IsProbabilityMeasure P ∧
      TailRiskSharing.VaRConv.IsAtomless P ∧ ∃ A : Set (ULift.{u} ℝ), MeasurableSet A ∧ P A = 1 / 2
  (declare `universe u` before it). Suggested construction: P = (volume.restrict (Set.Icc (0:ℝ) 1)).map (MeasurableEquiv.ulift.symm) (MeasurableEquiv.ulift : ULift α ≃ᵐ α, Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:360), A = ULift.down ⁻¹' Set.Iic (1/2). Atomless for μ = volume.restrict (Icc 0 1) on ℝ: given measurable s with 0 < μ s, the function g c = (μ (s ∩ Iic c)).toReal is 1-Lipschitz (μ (s ∩ Ioc c c') ≤ volume (Ioc c c') = c' − c), g 0 = 0 (s ∩ Iic 0 ∩ Icc 0 1 ⊆ {0}), g 1 = (μ s).toReal; by the intermediate value theorem (`intermediate_value_Icc`) pick c ∈ [0,1] with g c = (μ s).toReal / 2 and t = s ∩ Iic c. Transfer along the measurable equivalence.
Part B (generic analytic bound):
  theorem B_robust_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : Ω → ℝ) (hZ : Z ∈ TailRiskSharing.TailConv.Linf P) (K : ℝ)
      (hK : (1 / 2 : ℝ) ≤ P.real {ω | Z ω ≤ -K}) :
      robust P 1 1 (TailRiskSharing.VaRConv.VaRL P (3 / 4)) Z ≤ 4 - K
  Proof. robust = sSup of robustSet; the set is nonempty (Z itself: wassersteinK P 1 Z Z = 0 since the integrand is |0|^1 = 0), so it suffices (`csSup_le`) that every Y ∈ Linf with wassersteinK P 1 Y Z ≤ 1 has t := VaRL P (3/4) Y ≤ 4 − K. Write q_W(u) := VaRL P (1 - u) W = sInf {x | u ≤ distFn P W x} (since 1 − (1 − u) = u). Facts:
   (i) For W ∈ Linf with a.e. bound |W| ≤ C (C ≥ 0 WLOG): distFn P W x = 0 for x < −C and = 1 for x ≥ C; hence for u ∈ (0,1] the set {x | u ≤ distFn P W x} is nonempty (contains C) and bounded below (by −C), and q_W is monotone on (0,1] with −C ≤ q_W(u) ≤ C; also q_W(u) = 0 for u ≤ 0 (sInf univ = 0, `Real.sInf_of_not_bddBelow` or `Real.sInf_univ`) and u > 1 (sInf ∅ = 0). So |q_W| ≤ C everywhere.
   (ii) Integrability: u ↦ |q_Y(u) − q_Z(u)| is IntervalIntegrable on [0,1]. E.g. q_W agrees on Ioc 0 1 with the globally monotone function u ↦ if u ≤ 0 then −C else if u ≤ 1 then q_W u else C (`Monotone.measurable` / `Monotone.intervalIntegrable`), and interval integrability only sees Ioc 0 1; or use measurability plus the bound |q_W| ≤ C (`Measure.integrableOn_of_bounded`).
   (iii) For u ∈ [1/4, 1]: q_Y(u) ≥ t, because {x | u ≤ F_Y x} ⊆ {x | 1/4 ≤ F_Y x} (`csInf_le_csInf`; t = sInf {x | 1 − 3/4 ≤ F_Y x}).
   (iv) For u ∈ (0, 1/2]: q_Z(u) ≤ −K, because −K ∈ {x | u ≤ F_Z x} (F_Z(−K) = P.real{Z ≤ −K} ≥ 1/2 ≥ u) and the set is bounded below (`csInf_le`).
   (v) wassersteinK P 1 Y Z = ∫ u in 0..1, |q_Y u − q_Z u| (Real.rpow_one, 1/1 = 1) ≥ ∫ u in (1/4)..(1/2), |q_Y u − q_Z u| (nonnegative integrand; `intervalIntegral.integral_mono_interval` or split with `intervalIntegral.integral_add_adjacent_intervals`) ≥ ∫ u in (1/4)..(1/2), (t + K) = (t + K)/4. With wassersteinK ≤ 1 this gives t ≤ 4 − K.
Part C (assembly): the top-level `theorem solution` with the statement from Solutions/RV_statement.txt VERBATIM (top level, outside any namespace, after `open MeasureTheory TailRiskSharing.RobustVaR`), proved from A_space and B_robust_le. While A and B are being written, put their exact statements in your file inside `namespace RVDisproof` as clearly marked `:= by sorry` placeholders between the comment lines `-- BEGIN PLACEHOLDERS` and `-- END PLACEHOLDERS`. Steps: `intro h`; obtain P, hprob, hatom, A, hA, hPA from A_space.{u_1} (the universe of Ω in the statement; use `haveI := hprob`); specialize `h (P := P) hatom (fun _ => 0) (zero ∈ Linf) Side.L 1`; take the first conjunct at δs = fun _ => 1, α = 3/4 to get the equation E; show comonoInfConv … ≤ ((0:ℝ):EReal) via the allocation ![Z, -Z] (or fun i => if i = 0 then Z else -Z) and B_robust_le with K = 4 (P.real {Z ≤ −4} = P.real A = 1/2, P.real {−Z ≤ −4} = P.real Aᶜ = 1/2 via `prob_compl_eq_one_sub` or `measureReal_compl`); show the right side is ≥ 4/3 (robust of the zero function ≥ 0; ∑ over Fin 1 of 1/(3/4) = 4/3); conclude with EReal coercion lemmas (`EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff`) a contradiction.

## Return
Structured result: status OK/PARTIAL, file, check_tail, proof_description, remaining.
