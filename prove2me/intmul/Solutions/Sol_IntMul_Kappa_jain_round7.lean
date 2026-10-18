import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_IntMul_Kappa_jain_round8

open IntMul
set_option autoImplicit false

/-- `KappaBound` is antitone in `κ`: since `lg n ≥ 1`, `(lg n)^(1-κ)` decreases as `κ` grows, so a
machine meeting the bound for a larger saving also meets it for every smaller one. -/
private lemma kappaBound_antitone {κ κ' : ℝ} (hk : κ' ≤ κ) (h : KappaBound κ) : KappaBound κ' := by
  obtain ⟨M, hcorr, c, hc, n₀, hM⟩ := h
  refine ⟨M, hcorr, c, hc, n₀, fun n hn h1 => ?_⟩
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := hM n hn h1 x y hx hy
  refine ⟨t, ht.trans ?_, hh⟩
  have hlg : (1 : ℝ) ≤ (lg n : ℝ) := by exact_mod_cast le_max_right _ _
  have hpow : (lg n : ℝ) ^ (1 - κ) ≤ (lg n : ℝ) ^ (1 - κ') :=
    Real.rpow_le_rpow_of_exponent_le hlg (by linarith)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)) hc.le

/-- Jain round seven (κ = 0.00006397891967576) follows from Jain round eight (κ = 0.00012612978530233), a strictly larger saving. -/
theorem solution : KappaBound (0.00006397891967576 : ℝ) :=
  kappaBound_antitone (by norm_num) IntMul.Kappa.jain_round8
