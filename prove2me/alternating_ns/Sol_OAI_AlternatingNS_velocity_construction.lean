/-
Portions of this file are adapted from the OpenAI "math" repository
(https://github.com/openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a),
files lean/OAI/MathematicalPhysics/AlternatingFlow/*.lean, which formalize the manuscript
"Computation under Rapidly Vanishing Navier-Stokes Forcing" (OpenAI, September 27, 2026).
Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0). The adapted portions are distributed under the
same license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: the modules were merged into one file in dependency order; the duplicate model
definitions were replaced by the platform definition `Definitions.Def_NavierStokesAlternating`
(only four small helper facts from Model.lean are kept); the modules needed only for the force,
for energy uniqueness and for the final assembly were omitted; local adjustments were made to
compile against Lean 4.33.1 / Mathlib 0df444a; and the final theorem `solution` restates the
platform child `OAI.AlternatingNS.velocity_construction` and derives it from the upstream results.
-/
import Mathlib
import Definitions.Def_NavierStokesAlternating

set_option autoImplicit false

-- Compatibility shims: these core lemmas exist in newer Lean versions used upstream, but not in
-- Lean 4.33.1; they are restatements of `if_pos`, `if_neg` and `dif_pos`.
namespace OAI

theorem ite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

theorem ite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

theorem dite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : c) : dite c t e = t h := dif_pos h

end OAI

-- From Model.lean (only the helper facts; the definitions come from the platform import).
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS

theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩

theorem twoAtLeastTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

theorem threeAtLeastTwo : Nat.AtLeastTwo 3 := ⟨Nat.le_succ 2⟩

theorem eightAtLeastTwo : Nat.AtLeastTwo 8 := ⟨by decide⟩

end AlternatingNS
end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Scales.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Scales

def K (N n : ℕ) : ℕ := N + 2 * n + 2

def s (N n : ℕ) : ℕ := (N + 1) * 2 ^ ((n + 3) ^ 2)

noncomputable def ε (b N n : ℕ) : ℝ := ((b : ℝ) ^ s N n)⁻¹

lemma exponent_succ (n : ℕ) : (n + 1 + 3) ^ 2 = (n + 3) ^ 2 + (2 * n + 7) := by
  ring

lemma s_succ (N n : ℕ) : s N (n + 1) = 2 ^ (2 * n + 7) * s N n := by
  simp only [s, exponent_succ, pow_add]
  ring

lemma pow_lower (n : ℕ) : 8 * (n + 1) ≤ 2 ^ ((n + 3) ^ 2) := by
  have h : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have he : n + 3 ≤ (n + 3) ^ 2 := by nlinarith
  calc
    8 * (n + 1) ≤ 8 * 2 ^ n := Nat.mul_le_mul_left 8 h
    _ = 2 ^ (n + 3) := by simp [pow_add]; ring
    _ ≤ 2 ^ ((n + 3) ^ 2) := Nat.pow_le_pow_right (by decide) he

lemma s_lower (N n : ℕ) : 8 * (N + 1) * (n + 1) ≤ s N n := by
  have h := Nat.mul_le_mul_left (N + 1) (pow_lower n)
  simpa only [s, mul_left_comm, mul_assoc] using h

lemma capacity_lt (N n : ℕ) : 1 + 2 * K N n < s N n := by
  have h := s_lower N n
  dsimp [K]
  nlinarith

lemma K_add_one_lt (N n : ℕ) : K N n + 1 < s N n := by
  have := capacity_lt N n
  omega

lemma s_pos (N n : ℕ) : 0 < s N n := by
  unfold s
  positivity

lemma strictMono_s (N : ℕ) : StrictMono (s N) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [s_succ]
  have hp : 1 < 2 ^ (2 * n + 7) := one_lt_pow₀ (by decide) (by omega)
  nlinarith [s_pos N n]

lemma scale_gap (N n : ℕ) : s N n + 1 + 2 * K N n < s N (n + 1) := by
  rw [s_succ]
  have hc := capacity_lt N n
  have hp : 2 ≤ 2 ^ (2 * n + 7) := by
    exact Nat.le_pow (by omega)
  nlinarith [s_pos N n]

lemma old_scale_gap (N j n : ℕ) (hjn : j < n) :
    s N j + (1 + 2 * K N j) ≤ s N n := by
  have h₁ := scale_gap N j
  have h₂ := (strictMono_s N).monotone (Nat.succ_le_of_lt hjn)
  simp only [Nat.succ_eq_add_one] at h₂
  omega

lemma derivative_gap (N r n : ℕ) (hn : r ≤ n) :
    s N n + (r + 1) * (s N n + 1 + K N n) ≤ s N (n + 1) := by
  have hk := K_add_one_lt N n
  have hp : 2 * r + 3 ≤ 2 ^ (2 * n + 7) := by
    have ht : 2 * n + 7 < 2 ^ (2 * n + 7) := Nat.lt_two_pow_self
    omega
  rw [s_succ]
  nlinarith

lemma s_zero_add (N n : ℕ) : s N 0 + n ≤ s N n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := strictMono_s N (Nat.lt_succ_self n)
    simp only [Nat.succ_eq_add_one] at *
    omega

lemma n_le_s (N n : ℕ) : n ≤ s N n := by
  have := s_zero_add N n
  omega

lemma ε_pos (b N n : ℕ) (hb : 0 < b) : 0 < ε b N n := by
  unfold ε
  positivity

lemma ε_nonneg (b N n : ℕ) (hb : 0 < b) : 0 ≤ ε b N n :=
  (ε_pos b N n hb).le

lemma ε_strictAnti (b N : ℕ) (hb : 1 < b) : StrictAnti (ε b N) := by
  intro n m hnm
  unfold ε
  apply inv_strictAnti₀ _ _
  · positivity
  · exact pow_lt_pow_right₀ (by exact_mod_cast hb) (strictMono_s N hnm)

lemma ε_le_geometric (b N n : ℕ) (hb : 2 ≤ b) :
    ε b N n ≤ (1 / 2 : ℝ) ^ n := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold ε
  rw [one_div, inv_pow]
  apply inv_anti₀ (by positivity)
  calc
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ s N n := pow_le_pow_right₀ (by norm_num) (n_le_s N n)
    _ ≤ (b : ℝ) ^ s N n := pow_le_pow_left₀ (by norm_num) hb' _

lemma ε_le_initial_geometric (b N n : ℕ) (hb : 2 ≤ b) :
    ε b N n ≤ ε b N 0 * (1 / 2 : ℝ) ^ n := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (b : ℝ) ^ s N 0 * 2 ^ n ≤ (b : ℝ) ^ s N n := by
    calc
      (b : ℝ) ^ s N 0 * 2 ^ n ≤ (b : ℝ) ^ s N 0 * (b : ℝ) ^ n := by
        gcongr
      _ = (b : ℝ) ^ (s N 0 + n) := (pow_add _ _ _).symm
      _ ≤ (b : ℝ) ^ s N n := pow_le_pow_right₀ (by linarith) (s_zero_add N n)
  simpa only [ε, one_div, inv_pow, mul_inv_rev, mul_comm] using
    (inv_anti₀ (by positivity : (0 : ℝ) < (b : ℝ) ^ s N 0 * 2 ^ n) hp)

lemma summable_ε (b N : ℕ) (hb : 2 ≤ b) : Summable (ε b N) := by
  exact Summable.of_nonneg_of_le
    (fun n => ε_nonneg b N n (by omega))
    (fun n => ε_le_geometric b N n hb) summable_geometric_two

lemma total_memory_le (b N : ℕ) (hb : 2 ≤ b) :
    (∑' n : ℕ, ε b N n) ≤ 2 * ε b N 0 := by
  have hg := summable_geometric_two.mul_left (ε b N 0)
  have h := (summable_ε b N hb).tsum_le_tsum
    (fun n => ε_le_initial_geometric b N n hb) hg
  calc
    (∑' n : ℕ, ε b N n) ≤ ∑' n : ℕ, ε b N 0 * (1 / 2 : ℝ) ^ n := h
    _ = 2 * ε b N 0 := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      ring

lemma initial_memory_small (b N : ℕ) (hb : 4 ≤ b) : 2 * ε b N 0 < 1 / 4 := by
  have hs : 2 ≤ s N 0 := by have := s_lower N 0; nlinarith
  have hb' : (4 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (16 : ℝ) ≤ (b : ℝ) ^ s N 0 := by
    calc
      (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ (4 : ℝ) ^ s N 0 := pow_le_pow_right₀ (by norm_num) hs
      _ ≤ (b : ℝ) ^ s N 0 := pow_le_pow_left₀ (by norm_num) hb' _
  have hε : ε b N 0 ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpow
  norm_num at hε
  linarith

lemma derivative_cost_bound (b N r n : ℕ) (hb : 2 ≤ b) (hn : r ≤ n) :
    ε b N (n + 1) * (b : ℝ) ^ ((r + 1) * (s N n + 1 + K N n)) ≤ ε b N n := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have h := pow_le_pow_right₀ hb' (derivative_gap N r n hn)
  have hpos : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  dsimp [ε]
  rw [← div_eq_inv_mul, ← one_div]
  apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hpos _)).2
  simpa [pow_add, mul_comm] using h

lemma summable_weighted_ε (b N J : ℕ) (hb : 2 ≤ b) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ J * ε b N n) := by
  have h₀ := summable_pow_mul_geometric_of_norm_lt_one J
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h₁ := ((summable_nat_add_iff 1).2 h₀).mul_left (2 : ℝ)
  have h₂ : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ J * (1 / 2 : ℝ) ^ n) := by
    apply h₁.congr
    intro n
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (ε_nonneg b N n (by omega)))
    (fun n => mul_le_mul_of_nonneg_left (ε_le_geometric b N n hb) (by positivity)) h₂

lemma weighted_ε_tendsto_zero (b N J : ℕ) (hb : 2 ≤ b) :
    Filter.Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ J * ε b N n)
      Filter.atTop (𝓝 0) :=
  (summable_weighted_ε b N J hb).tendsto_atTop_zero

lemma weighted_ε_bounded (b N J : ℕ) (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (1 + (n : ℝ)) ^ J * ε b N n ≤ C := by
  refine ⟨∑' n : ℕ, (1 + (n : ℝ)) ^ J * ε b N n, ?_, ?_⟩
  · apply tsum_nonneg
    intro n
    exact mul_nonneg (by positivity) (ε_nonneg b N n (by omega))
  · intro n
    apply (summable_weighted_ε b N J hb).le_tsum
    intro j _
    exact mul_nonneg (by positivity) (ε_nonneg b N j (by omega))

end Scales
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Detector.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Detector

open Scales

noncomputable def increment (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) : ℝ :=
  ε b N n - ε b N (n + 1) + if halted n then 2 * ε b N (n + 1) else 0

noncomputable def signal (b N : ℕ) (halted : ℕ → Bool) : ℕ → ℝ
  | 0 => -ε b N 0
  | n + 1 => signal b N halted n + increment b N halted n

noncomputable def during (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) (θ : ℝ) : ℝ :=
  signal b N halted n + θ * increment b N halted n

noncomputable def loading (b N : ℕ) (θ : ℝ) : ℝ := -1 + θ * (1 - ε b N 0)

lemma signal_formula (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n = -ε b N n +
      2 * ∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0 := by
  induction n with
  | zero => simp [signal]
  | succ n ih =>
    simp only [signal, increment, ih, Finset.sum_range_succ]
    split_ifs <;> ring

lemma signal_before_halt (b N : ℕ) (halted : ℕ → Bool) (n : ℕ)
    (hn : ∀ j < n, halted j = false) : signal b N halted n = -ε b N n := by
  rw [signal_formula]
  have hsum : (∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hn j (Finset.mem_range.1 hj)]
  rw [hsum]
  ring

lemma signal_first_halt (b N : ℕ) (halted : ℕ → Bool) (n : ℕ)
    (hprev : ∀ j < n, halted j = false) (hn : halted n = true) :
    signal b N halted (n + 1) = ε b N (n + 1) := by
  rw [signal, signal_before_halt b N halted n hprev]
  simp only [increment, hn, ite_true]
  ring

lemma increment_nonneg (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    0 ≤ increment b N halted n := by
  have hε := ε_strictAnti b N (by omega) (Nat.lt_succ_self n)
  have hp := ε_pos b N (n + 1) (by omega)
  simp only [Nat.succ_eq_add_one] at hε
  unfold increment
  split_ifs <;> linarith

lemma increment_le (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    increment b N halted n ≤ ε b N n + ε b N (n + 1) := by
  have hp := ε_pos b N (n + 1) (by omega)
  unfold increment
  split_ifs <;> linarith

lemma signal_monotone (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) :
    Monotone (signal b N halted) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [signal, le_add_iff_nonneg_right] using increment_nonneg b N hb halted n

lemma during_zero (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    during b N halted n 0 = signal b N halted n := by simp [during]

lemma during_one (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    during b N halted n 1 = signal b N halted (n + 1) := by simp [during, signal]

lemma during_before_halt (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ)
    (hn : ∀ j ≤ n, halted j = false) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) :
    during b N halted n θ < 0 := by
  have he := ε_strictAnti b N (by omega) (Nat.lt_succ_self n)
  have hp := ε_pos b N (n + 1) (by omega)
  simp only [Nat.succ_eq_add_one] at he
  have hm := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr he.le)
  rw [during, signal_before_halt b N halted n (fun j hj => hn j hj.le)]
  simp only [increment, hn n le_rfl, Bool.false_eq_true, ↓reduceIte, add_zero]
  nlinarith

lemma loading_negative (b N : ℕ) (hb : 2 ≤ b) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) :
    loading b N θ < 0 := by
  have hp := ε_pos b N 0 (by omega)
  have hle := ε_le_geometric b N 0 hb
  norm_num at hle
  have hm := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hle)
  unfold loading
  nlinarith

lemma scalar_reachability (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) :
    (∃ n : ℕ, ∃ θ ∈ Set.Icc (0 : ℝ) 1, 0 < during b N halted n θ) ↔
      ∃ n : ℕ, halted n = true := by
  constructor
  · rintro ⟨n, θ, hθ, hpos⟩
    by_contra h
    have hfalse : ∀ j, halted j = false := by
      intro j
      exact Bool.eq_false_iff.2 (fun hj => h ⟨j, hj⟩)
    exact (during_before_halt b N hb halted n (fun j _ => hfalse j) θ hθ).not_gt hpos
  · intro h
    let n := Nat.find h
    have hn : halted n = true := Nat.find_spec h
    have hprev : ∀ j < n, halted j = false :=
      fun j hj => Bool.eq_false_iff.2 (Nat.find_min h hj)
    refine ⟨n, 1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [during_one, signal_first_halt b N halted n hprev hn]
    exact ε_pos b N (n + 1) (by omega)

lemma signal_upper_bound (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n ≤ 2 * ∑' j : ℕ, ε b N j := by
  have hsum : (∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0) ≤
      ∑ j ∈ Finset.range n, ε b N j := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact (ε_strictAnti b N (by omega) (Nat.lt_succ_self j)).le
    · exact ε_nonneg b N j (by omega)
  have htotal := (summable_ε b N hb).sum_le_tsum (Finset.range n)
    (fun j _ => ε_nonneg b N j (by omega))
  rw [signal_formula]
  linarith [ε_nonneg b N n (by omega)]

lemma signal_in_plateau (b N : ℕ) (hb : 4 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hl := signal_monotone b N (by omega) halted (Nat.zero_le n)
  have hu := signal_upper_bound b N (by omega) halted n
  have hsum := total_memory_le b N (by omega)
  have hs := initial_memory_small b N hb
  simp only [signal] at hl
  constructor <;> linarith

lemma during_in_plateau (b N : ℕ) (hb : 4 ≤ b) (halted : ℕ → Bool) (n : ℕ)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) : during b N halted n θ ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h₀ := signal_in_plateau b N hb halted n
  have h₁ := signal_in_plateau b N hb halted (n + 1)
  have hi := increment_nonneg b N (by omega) halted n
  have hleft := mul_nonneg hθ.1 hi
  have hright := mul_nonneg (sub_nonneg.mpr hθ.2) hi
  simp only [signal] at h₁
  change -1 < signal b N halted n + θ * increment b N halted n ∧
    signal b N halted n + θ * increment b N halted n < 1
  constructor <;> nlinarith [h₀.1, h₁.2]

lemma machine_scalar_reachability (b : ℕ) (hb : 2 ≤ b) (M : Machine) (w : List ℕ) :
    (∃ n : ℕ, ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      0 < during b w.length (fun j => M.isHalting (M.run w j)) n θ) ↔ M.Halts w :=
  scalar_reachability b w.length hb (fun j => M.isHalting (M.run w j))

end Detector
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Encoding.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Encoding

noncomputable def code (b : ℕ) : List ℕ → ℝ
  | [] => 0
  | d :: ds => ((d : ℝ) + code b ds) / b

noncomputable def tailMax (b : ℕ) : ℝ :=
  letI := twoAtLeastTwo
  ((b : ℝ) - 2) / ((b : ℝ) - 1)

lemma tailMax_nonneg (b : ℕ) (hb : 2 ≤ b) : 0 ≤ tailMax b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tailMax
  exact div_nonneg (by linarith) (by linarith)

lemma tailMax_lt_one (b : ℕ) (hb : 2 ≤ b) : tailMax b < 1 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tailMax
  apply (div_lt_one (by linarith)).2
  linarith

lemma tailMax_identity (b : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * tailMax b = (b : ℝ) - 2 + tailMax b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h : (b : ℝ) - 1 ≠ 0 := by linarith
  unfold tailMax
  field_simp
  ring

lemma code_nonneg (b : ℕ) (L : List ℕ) : 0 ≤ code b L := by
  induction L with
  | nil => simp [code]
  | cons d L ih => simpa only [code] using div_nonneg (by positivity) (Nat.cast_nonneg b)

lemma code_le_tailMax (b : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ d ∈ L, d + 2 ≤ b) : code b L ≤ tailMax b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  induction L with
  | nil => exact tailMax_nonneg b hb
  | cons d L ih =>
    have hd : (d : ℝ) + 2 ≤ b := by exact_mod_cast hL d (by simp)
    have ht : code b L ≤ tailMax b := ih (fun a ha => hL a (List.mem_cons_of_mem d ha))
    rw [code, div_le_iff₀ hb']
    have hi := tailMax_identity b hb
    linarith

lemma digit_interval (b d : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ a ∈ L, a + 2 ≤ b) :
    (d : ℝ) / b ≤ code b (d :: L) ∧ code b (d :: L) ≤ ((d : ℝ) + 1) / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  constructor
  · exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (code_nonneg b L)) hb'.le
  · apply div_le_div_of_nonneg_right _ hb'.le
    linarith [code_le_tailMax b hb L hL, tailMax_lt_one b hb]

lemma code_append (b : ℕ) (hb : 0 < b) (L R : List ℕ) :
    code b (L ++ R) = code b L + ((b : ℝ) ^ L.length)⁻¹ * code b R := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  induction L with
  | nil => simp [code]
  | cons d L ih =>
    simp only [List.cons_append, code, List.length_cons, pow_succ, ih]
    field_simp
    ring

lemma code_denominator (b : ℕ) (hb : 0 < b) (L : List ℕ) :
    ∃ a : ℕ, (b : ℝ) ^ L.length * code b L = a := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  induction L with
  | nil => exact ⟨0, by simp [code]⟩
  | cons d L ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨b ^ L.length * d + a, ?_⟩
    calc
      (b : ℝ) ^ (d :: L).length * code b (d :: L) =
          (b : ℝ) ^ L.length * d + (b : ℝ) ^ L.length * code b L := by
        simp only [List.length_cons, code, pow_succ]
        field_simp
      _ = ((b ^ L.length * d + a : ℕ) : ℝ) := by rw [ha]; push_cast; rfl

lemma configuration_block (b g : ℕ) (hb : 0 < b) (L R : List ℕ) :
    code b (g :: (L ++ R)) =
      ((g : ℝ) + code b L + ((b : ℝ) ^ L.length)⁻¹ * code b R) / b := by
  rw [code, code_append b hb]
  ring

lemma integral_rescale (b k l : ℕ) (hkl : k ≤ l) {x : ℝ}
    (hx : ∃ a : ℤ, (b : ℝ) ^ k * x = a) :
    ∃ a : ℤ, (b : ℝ) ^ l * x = a := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨(b : ℤ) ^ (l - k) * a, ?_⟩
  calc
    (b : ℝ) ^ l * x = (b : ℝ) ^ (l - k) * ((b : ℝ) ^ k * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hkl]
    _ = ((b : ℤ) ^ (l - k) * a : ℤ) := by rw [ha]; push_cast; rfl

lemma sum_integral {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, ∃ a : ℤ, f i = a) : ∃ a : ℤ, ∑ i ∈ S, f i = a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨a, ha⟩ := hf i (by simp)
    obtain ⟨c, hc⟩ := ih (fun j hj => hf j (by simp [hj]))
    exact ⟨a + c, by simp [Finset.sum_insert hi, ha, hc]⟩

noncomputable def donor (b N : ℕ) (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), if j % 2 = n % 2 then Scales.ε b N j * C j else 0

lemma old_record_integral (b N j n : ℕ) (hb : 0 < b) (hjn : j < n) {C : ℝ}
    (hC : ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C = a) :
    ∃ a : ℤ, (b : ℝ) ^ Scales.s N n * (Scales.ε b N j * C) = a := by
  apply integral_rescale b (Scales.s N j + (1 + 2 * Scales.K N j))
    (Scales.s N n) (Scales.old_scale_gap N j n hjn)
  obtain ⟨a, ha⟩ := hC
  refine ⟨a, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  calc
    (b : ℝ) ^ (Scales.s N j + (1 + 2 * Scales.K N j)) * (Scales.ε b N j * C) =
      (b : ℝ) ^ (1 + 2 * Scales.K N j) * C := by
        dsimp [Scales.ε]
        rw [pow_add]
        field_simp
    _ = a := ha

lemma donor_integer_add (b N n : ℕ) (hb : 0 < b) (C : ℕ → ℝ)
    (hC : ∀ j, ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C j = a) :
    ∃ a : ℤ, (b : ℝ) ^ Scales.s N n * donor b N C n = a + C n := by
  have hI : ∀ j ∈ Finset.range n,
      ∃ a : ℤ, (b : ℝ) ^ Scales.s N n *
        (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) = a := by
    intro j hj
    split_ifs
    · exact old_record_integral b N j n hb (Finset.mem_range.1 hj) (hC j)
    · exact ⟨0, by simp⟩
  obtain ⟨a, ha⟩ := sum_integral (Finset.range n) _ hI
  refine ⟨a, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  rw [donor, Finset.sum_range_succ]
  simp only [ite_true, mul_add, Finset.mul_sum]
  rw [ha]
  dsimp [Scales.ε]
  field_simp

def DecoderLaw (b : ℕ) (P : ℝ → ℝ) : Prop :=
  Function.Periodic P 1 ∧ ∀ v ∈ Set.Icc 0 (tailMax b), P v = v

lemma decoder_int_add (b : ℕ) (P : ℝ → ℝ) (hP : DecoderLaw b P)
    (a : ℤ) (v : ℝ) (hv : v ∈ Set.Icc 0 (tailMax b)) : P ((a : ℝ) + v) = v := by
  have h := hP.1.int_mul a v
  simpa only [mul_one, add_comm, hP.2 v hv] using h

lemma read_current (b N n : ℕ) (hb : 2 ≤ b) (C : ℕ → ℝ)
    (hC : ∀ j, ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C j = a)
    (hc : C n ∈ Set.Icc 0 (tailMax b))
    (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ Scales.s N n * donor b N C n) = C n := by
  obtain ⟨a, ha⟩ := donor_integer_add b N n (by omega) C hC
  rw [ha]
  exact decoder_int_add b P hP a (C n) hc

lemma remove_prefix (b s : ℕ) (hb : 0 < b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (L ++ R)) :
    ∃ a : ℤ, (b : ℝ) ^ (s + L.length) * D = a + code b R := by
  obtain ⟨a, ha⟩ := hD
  obtain ⟨c, hc⟩ := code_denominator b hb L
  refine ⟨(b : ℤ) ^ L.length * a + c, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  calc
    (b : ℝ) ^ (s + L.length) * D = (b : ℝ) ^ L.length * ((b : ℝ) ^ s * D) := by
      rw [pow_add]; ring
    _ = (b : ℝ) ^ L.length * a + (b : ℝ) ^ L.length * code b L + code b R := by
      rw [ha, code_append b hb]
      field_simp
      ring
    _ = (((b : ℤ) ^ L.length * a + c : ℤ) : ℝ) + code b R := by rw [hc]; push_cast; rfl

lemma read_after_prefix (b s : ℕ) (hb : 2 ≤ b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (L ++ R))
    (hR : ∀ d ∈ R, d + 2 ≤ b) (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ (s + L.length) * D) = code b R := by
  obtain ⟨a, ha⟩ := remove_prefix b s (by omega) L R D hD
  rw [ha]
  exact decoder_int_add b P hP a _ ⟨code_nonneg b R, code_le_tailMax b hb R hR⟩

lemma read_configuration (b s g : ℕ) (hb : 2 ≤ b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (g :: (L ++ R)))
    (hd : ∀ d ∈ g :: (L ++ R), d + 2 ≤ b)
    (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ s * D) = code b (g :: (L ++ R)) ∧
    P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b R ∧
    P ((b : ℝ) ^ (s + 1) * D) - ((b : ℝ) ^ L.length)⁻¹ *
      P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b L := by
  have hLR : ∀ d ∈ L ++ R, d + 2 ≤ b :=
    fun d h => hd d (List.mem_cons_of_mem g h)
  have hR : ∀ d ∈ R, d + 2 ≤ b := fun d h => hLR d (List.mem_append_right L h)
  have h₁ := read_after_prefix b s hb [g] (L ++ R) D hD hLR P hP
  have h₂ := read_after_prefix b s hb (g :: L) R D (by simpa using hD) hR P hP
  simp only [List.length_cons, List.length_nil] at h₁ h₂
  have h₂' : P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b R := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂
  refine ⟨?_, h₂', ?_⟩
  · obtain ⟨a, ha⟩ := hD
    rw [ha]
    exact decoder_int_add b P hP a _
      ⟨code_nonneg b _, code_le_tailMax b hb _ hd⟩
  · rw [h₁, h₂', code_append b (by omega)]
    ring

end Encoding
end AlternatingNS

namespace AlternatingNS
namespace Encoding

lemma donor_in_plateau (b N n : ℕ) (hb : 4 ≤ b) (C : ℕ → ℝ)
    (hC : ∀ j, C j ∈ Set.Icc (0 : ℝ) 1) :
    donor b N C n ∈ Set.Ico (0 : ℝ) (1 / 4) := by
  have hterm : ∀ j : ℕ,
      0 ≤ (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) ∧
        (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) ≤ Scales.ε b N j := by
    intro j
    have hε := Scales.ε_nonneg b N j (by omega)
    split_ifs
    · exact ⟨mul_nonneg hε (hC j).1, mul_le_of_le_one_right hε (hC j).2⟩
    · exact ⟨le_rfl, hε⟩
  constructor
  · apply Finset.sum_nonneg
    intro j _
    exact (hterm j).1
  · apply lt_of_le_of_lt _ (Scales.initial_memory_small b N hb)
    apply le_trans _ (Scales.total_memory_le b N (by omega))
    calc
      donor b N C n ≤ ∑ j ∈ Finset.range (n + 1), Scales.ε b N j :=
        Finset.sum_le_sum (fun j _ => (hterm j).2)
      _ ≤ ∑' j : ℕ, Scales.ε b N j :=
        (Scales.summable_ε b N (by omega)).sum_le_tsum _
          (fun j _ => Scales.ε_nonneg b N j (by omega))

lemma pop_code (b d : ℕ) (hb : 0 < b) (L : List ℕ) :
    (b : ℝ) * code b (d :: L) - d = code b L := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  dsimp [code]
  field_simp
  ring

lemma tape_step_right (b a w : ℕ) (hb : 0 < b) (L R : List ℕ) :
    (((w : ℝ) + code b L) / b, (b : ℝ) * code b (a :: R) - a) =
      (code b (w :: L), code b R) := by
  rw [pop_code b a hb R]
  rfl

lemma tape_step_stay (b a w : ℕ) (hb : 0 < b) (L R : List ℕ) :
    (code b L, ((w : ℝ) + ((b : ℝ) * code b (a :: R) - a)) / b) =
      (code b L, code b (w :: R)) := by
  rw [pop_code b a hb R]
  rfl

lemma tape_step_left (b a w l : ℕ) (hb : 0 < b) (L R : List ℕ) :
    ((b : ℝ) * code b (l :: L) - l,
      ((l : ℝ) + ((w : ℝ) + ((b : ℝ) * code b (a :: R) - a)) / b) / b) =
      (code b L, code b (l :: w :: R)) := by
  rw [pop_code b l hb L, pop_code b a hb R]
  rfl

end Encoding
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Profiles.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def clock (t : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Real.smoothTransition (2 * t - 1 / 2)

lemma clock_smooth : ContDiff ℝ ∞ clock := by
  unfold clock
  fun_prop

lemma clock_mem (t : ℝ) : clock t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma clock_zero (t : ℝ) (ht : t ≤ 1 / 4) : clock t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

lemma clock_one (t : ℝ) (ht : 3 / 4 ≤ t) : clock t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

lemma clock_monotone : Monotone clock := by
  intro a b hab
  apply Real.smoothTransition.monotone
  linarith

noncomputable def periodizer (a c x : ℝ) : ℝ :=
  Int.fract x - Real.smoothTransition ((Int.fract x - a) / (c - a))

lemma periodizer_periodic (a c : ℝ) : Function.Periodic (periodizer a c) 1 := by
  intro x
  simp only [periodizer, Int.fract_add_one]

lemma periodizer_int_add (a c : ℝ) (k : ℤ) (x : ℝ) :
    periodizer a c ((k : ℝ) + x) = periodizer a c x := by
  simp only [periodizer, Int.fract_intCast_add]

lemma periodizer_self (a c x : ℝ) (hac : a < c) (ha : a < 1)
    (hx : x ∈ Set.Icc 0 a) : periodizer a c x = x := by
  have hf : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1, hx.2.trans_lt ha⟩
  rw [periodizer, hf, Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sub_pos.mpr hac).le

lemma periodizer_near_zero (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1)
    (x : ℝ) (hx : x ∈ Set.Ioo (c - 1) a) : periodizer a c x = x := by
  by_cases hx0 : 0 ≤ x
  · exact periodizer_self a c x hac (hac.trans hc) ⟨hx0, hx.2.le⟩
  · have hn : ⌊x⌋ = (-1 : ℤ) := Int.floor_eq_iff.2 (by norm_num; constructor <;> linarith [hx.1])
    have hf : Int.fract x = x + 1 := by rw [Int.fract, hn]; norm_num
    have hh : 1 ≤ (x + 1 - a) / (c - a) :=
      (le_div_iff₀ (sub_pos.mpr hac)).2 (by linarith [hx.1])
    rw [periodizer, hf, Real.smoothTransition.one_of_one_le hh]
    ring

lemma periodizer_smooth (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1) :
    ContDiff ℝ ∞ (periodizer a c) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have hg : ContDiff ℝ ∞ (fun y : ℝ => y - (⌊x⌋ : ℝ)) := by fun_prop
    apply hg.contDiffAt.congr_of_eventuallyEq
    have hlo : (⌊x⌋ : ℝ) + (c - 1) < x := by linarith
    have hhi : x < (⌊x⌋ : ℝ) + a := by linarith
    filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
    have hy' : y - (⌊x⌋ : ℝ) ∈ Set.Ioo (c - 1) a := by
      constructor <;> linarith [hy.1, hy.2]
    calc
      periodizer a c y = periodizer a c ((⌊x⌋ : ℝ) + (y - (⌊x⌋ : ℝ))) := by congr 1; ring
      _ = periodizer a c (y - (⌊x⌋ : ℝ)) := periodizer_int_add a c _ _
      _ = y - (⌊x⌋ : ℝ) := periodizer_near_zero a c ha hac hc _ hy'
  · have hg : ContDiff ℝ ∞ (fun y : ℝ => (y - (⌊x⌋ : ℝ)) -
        Real.smoothTransition (((y - (⌊x⌋ : ℝ)) - a) / (c - a))) := by fun_prop
    apply hg.contDiffAt.congr_of_eventuallyEq
    have hlo : (⌊x⌋ : ℝ) < x := (Int.floor_le x).lt_of_ne (Ne.symm hx)
    filter_upwards [Ioo_mem_nhds hlo (Int.lt_floor_add_one x)] with y hy
    have hy' : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩
    simp only [periodizer, Int.fract, hy']

noncomputable def decoder (b : ℕ) : ℝ → ℝ :=
  letI := twoAtLeastTwo
  letI := threeAtLeastTwo
  periodizer ((2 * Encoding.tailMax b + 1) / 3) ((Encoding.tailMax b + 2) / 3)

lemma decoder_law (b : ℕ) (hb : 2 ≤ b) : Encoding.DecoderLaw b (decoder b) := by
  have hm := Encoding.tailMax_lt_one b hb
  refine ⟨periodizer_periodic _ _, ?_⟩
  intro x hx
  apply periodizer_self
  · linarith
  · linarith
  · exact ⟨hx.1, by linarith [hx.2]⟩

lemma decoder_smooth (b : ℕ) (hb : 2 ≤ b) : ContDiff ℝ ∞ (decoder b) := by
  have hm0 := Encoding.tailMax_nonneg b hb
  have hm1 := Encoding.tailMax_lt_one b hb
  apply periodizer_smooth <;> linarith

lemma iteratedDeriv_periodic (f : ℝ → ℝ) (hf : Function.Periodic f 1) (r : ℕ) :
    Function.Periodic (iteratedDeriv r f) 1 := by
  have heq : (fun x => f (x + 1)) = f := funext hf
  have h := iteratedDeriv_comp_add_const r f 1
  rw [heq] at h
  exact fun x => (congr_fun h x).symm

lemma periodic_derivatives_bounded (f : ℝ → ℝ) (hf : Function.Periodic f 1)
    (hs : ContDiff ℝ ∞ f) (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv r f x| ≤ C := by
  have hcont : Continuous (fun x => |iteratedDeriv r f x|) :=
    (hs.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)).abs
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hcont.continuousOn (s := Set.Icc 0 1))
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := (iteratedDeriv_periodic f hf r).exists_mem_Ico (by norm_num) x 0
  rw [hxy]
  apply le_trans _ (le_max_right _ _)
  apply hC
  exact ⟨y, ⟨hy.1, by simpa using hy.2.le⟩, rfl⟩

lemma decoder_derivatives_bounded (b : ℕ) (hb : 2 ≤ b) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv r (decoder b) x| ≤ C :=
  periodic_derivatives_bounded (decoder b) (decoder_law b hb).1 (decoder_smooth b hb) r

end Profiles

namespace Encoding

lemma read_donor_configuration (b N n : ℕ) (hb : 2 ≤ b)
    (g : ℕ → ℕ) (L R : ℕ → List ℕ)
    (hL : ∀ j, (L j).length = Scales.K N j)
    (hR : ∀ j, (R j).length = Scales.K N j)
    (hd : ∀ j, ∀ d ∈ g j :: (L j ++ R j), d + 2 ≤ b) :
    let C := fun j => code b (g j :: (L j ++ R j))
    let D := donor b N C n
    Profiles.decoder b ((b : ℝ) ^ Scales.s N n * D) = C n ∧
    Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D) =
      code b (R n) ∧
    Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1) * D) -
      ((b : ℝ) ^ Scales.K N n)⁻¹ *
        Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D) =
      code b (L n) := by
  dsimp only
  have hC : ∀ j, ∃ a : ℤ,
      (b : ℝ) ^ (1 + 2 * Scales.K N j) * code b (g j :: (L j ++ R j)) = a := by
    intro j
    obtain ⟨a, ha⟩ := code_denominator b (by omega) (g j :: (L j ++ R j))
    refine ⟨a, ?_⟩
    simp only [List.length_cons, List.length_append, hL, hR] at ha
    have he : 1 + 2 * Scales.K N j = Scales.K N j + Scales.K N j + 1 := by omega
    simpa only [he, Int.cast_natCast] using ha
  have h := read_configuration b (Scales.s N n) (g n) hb (L n) (R n)
    (donor b N (fun j => code b (g j :: (L j ++ R j))) n)
    (donor_integer_add b N n (by omega) _ hC) (hd n)
    (Profiles.decoder b) (Profiles.decoder_law b hb)
  simpa only [hL] using h

end Encoding
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Machines.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Machine

def Admissible (M : Machine) (c : Configuration) : Prop :=
  c.state ≤ M.states ∧ ∀ i, c.tape i < M.alphabet

def command (M : Machine) (q a : ℕ) : Rule :=
  letI := neZeroThree
  if q = M.states ∨ q ∈ M.haltingStates then (q, a, 1)
  else (M.instruction q a).getD (M.states, a, 1)

lemma step_eq_command (M : Machine) (c : Configuration) :
    M.step c =
      { state := (M.command c.state (c.tape c.head)).1
        head := c.head + (((M.command c.state (c.tape c.head)).2.2.val : ℤ) - 1)
        tape := Function.update c.tape c.head (M.command c.state (c.tape c.head)).2.1 } := by
  unfold step isHalting command
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp [Function.update_eq_self]
  · cases M.instruction c.state (c.tape c.head) <;> simp [Function.update_eq_self]

lemma command_valid (M : Machine) (hM : M.WellFormed) (q a : ℕ)
    (hq : q ≤ M.states) (ha : a < M.alphabet) :
    (M.command q a).1 ≤ M.states ∧ (M.command q a).2.1 < M.alphabet := by
  unfold command
  split_ifs with h
  · exact ⟨hq, ha⟩
  · cases hc : M.instruction q a with
    | none => simp [ha]
    | some r =>
      have hr := hM.2.2 q a r (lt_of_le_of_ne hq (by tauto)) ha hc
      exact ⟨hr.1.le, hr.2⟩

lemma initial_admissible (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) : M.Admissible (M.initial w) := by
  refine ⟨hM.1.le, ?_⟩
  intro i
  dsimp [initial]
  split_ifs
  · cases h : w[i.toNat]? with
    | none => simp [alphabet]
    | some a => exact hw a (List.mem_of_getElem? h)
  · simp [alphabet]

lemma step_admissible (M : Machine) (hM : M.WellFormed) (c : Configuration)
    (hc : M.Admissible c) : M.Admissible (M.step c) := by
  rw [step_eq_command]
  have hr := command_valid M hM c.state (c.tape c.head) hc.1 (hc.2 c.head)
  refine ⟨hr.1, ?_⟩
  intro i
  dsimp
  by_cases hi : i = c.head
  · subst i; simpa using hr.2
  · simpa [Function.update_of_ne hi] using hc.2 i

lemma run_zero (M : Machine) (w : List ℕ) : M.run w 0 = M.initial w := rfl

lemma run_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    M.run w (n + 1) = M.step (M.run w n) :=
  Function.iterate_succ_apply' _ _ _

lemma run_admissible (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) : M.Admissible (M.run w n) := by
  induction n with
  | zero => exact initial_admissible M hM w hw
  | succ n ih => rw [run_succ]; exact step_admissible M hM _ ih

def Window (N n : ℕ) (c : Configuration) : Prop :=
  -(n : ℤ) ≤ c.head ∧ c.head ≤ n ∧
    ∀ i : ℤ, (i < -(n : ℤ) ∨ (N : ℤ) + n ≤ i) → c.tape i = 0

lemma initial_window (M : Machine) (w : List ℕ) : Window w.length 0 (M.initial w) := by
  refine ⟨by simp [initial], by simp [initial], ?_⟩
  intro i hi
  dsimp [initial]
  by_cases h : 0 ≤ i
  · rw [ite_eq_left h, List.getElem?_eq_none (by omega)]
    rfl
  · simp [h]

lemma step_window (M : Machine) (N n : ℕ) (c : Configuration)
    (hc : Window N n c) : Window N (n + 1) (M.step c) := by
  rw [step_eq_command]
  have hd := (M.command c.state (c.tape c.head)).2.2.isLt
  rcases hc with ⟨hl, hu, ht⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp; omega
  · dsimp; omega
  · intro i hi
    have hi' : i ≠ c.head := by omega
    have hblank := ht i (by omega)
    simpa [Function.update_of_ne hi'] using hblank

lemma run_window (M : Machine) (w : List ℕ) (n : ℕ) :
    Window w.length n (M.run w n) := by
  induction n with
  | zero => exact initial_window M w
  | succ n ih => rw [run_succ]; exact step_window M w.length n _ ih

def leftDigits (c : Configuration) (j : ℕ) : ℕ := 2 * c.tape (c.head - (j + 1))
def rightDigits (c : Configuration) (j : ℕ) : ℕ := 2 * c.tape (c.head + j)

lemma leftDigits_padded (N n : ℕ) (c : Configuration) (hc : Window N n c)
    (j : ℕ) (hj : Scales.K N n ≤ j) : leftDigits c j = 0 := by
  unfold leftDigits
  have hh := hc.2.1
  rw [hc.2.2 _ (Or.inl (by dsimp [Scales.K] at hj; omega))]

lemma rightDigits_padded (N n : ℕ) (c : Configuration) (hc : Window N n c)
    (j : ℕ) (hj : Scales.K N n ≤ j) : rightDigits c j = 0 := by
  unfold rightDigits
  have hh := hc.1
  rw [hc.2.2 _ (Or.inr (by dsimp [Scales.K] at hj; omega))]

def base (M : Machine) : ℕ := 2 * (1 + max (M.states + 1) M.alphabet)

lemma base_ge_four (M : Machine) : 4 ≤ M.base := by
  have h := le_max_left (M.states + 1) M.alphabet
  dsimp [base, states] at *
  omega

lemma state_digit_bound (M : Machine) (q : ℕ) (hq : q ≤ M.states) :
    2 * q + 2 ≤ M.base := by
  have h := le_max_left (M.states + 1) M.alphabet
  dsimp [base]
  omega

lemma symbol_digit_bound (M : Machine) (a : ℕ) (ha : a < M.alphabet) :
    2 * a + 2 ≤ M.base := by
  have h := le_max_right (M.states + 1) M.alphabet
  dsimp [base]
  omega

end Machine
end AlternatingNS

namespace AlternatingNS
namespace Encoding

def digits (K : ℕ) (f : ℕ → ℕ) : List ℕ := List.ofFn (fun i : Fin K => f i)

noncomputable def streamCode (b K : ℕ) (f : ℕ → ℕ) : ℝ := code b (digits K f)

lemma digits_length (K : ℕ) (f : ℕ → ℕ) : (digits K f).length = K := by
  simp [digits]

lemma digits_succ (K : ℕ) (f : ℕ → ℕ) :
    digits (K + 1) f = f 0 :: digits K (fun j => f (j + 1)) :=
  List.ofFn_succ

lemma streamCode_succ (b K : ℕ) (f : ℕ → ℕ) :
    streamCode b (K + 1) f = ((f 0 : ℝ) + streamCode b K (fun j => f (j + 1))) / b := by
  simp only [streamCode, digits_succ, code]

lemma streamCode_congr (b K : ℕ) (f g : ℕ → ℕ) (h : ∀ j < K, f j = g j) :
    streamCode b K f = streamCode b K g := by
  have hl : digits K f = digits K g :=
    congrArg List.ofFn (funext (fun j : Fin K => h j j.isLt))
  exact congrArg (code b) hl

lemma streamCode_extend_one (b K : ℕ) (hb : 0 < b) (f : ℕ → ℕ) (hK : f K = 0) :
    streamCode b (K + 1) f = streamCode b K f := by
  unfold streamCode digits
  rw [List.ofFn_succ', List.concat_eq_append]
  change code b (List.ofFn (fun i : Fin K => f i) ++ [f K]) = _
  rw [code_append b hb]
  simp [hK, code]

lemma streamCode_padding (b K L : ℕ) (hb : 0 < b) (hKL : K ≤ L) (f : ℕ → ℕ)
    (hf : ∀ j, K ≤ j → f j = 0) : streamCode b L f = streamCode b K f := by
  induction L, hKL using Nat.le_induction with
  | base => rfl
  | succ L hL ih => rw [streamCode_extend_one b L hb f (hf L hL), ih]

lemma streamCode_pop (b K L : ℕ) (hb : 0 < b) (hKL : K ≤ L + 1)
    (f : ℕ → ℕ) (hf : ∀ j, K ≤ j → f j = 0) :
    streamCode b L (fun j => f (j + 1)) = (b : ℝ) * streamCode b K f - f 0 := by
  have h := streamCode_succ b L f
  rw [streamCode_padding b K (L + 1) hb hKL f hf] at h
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  apply (eq_div_iff hb').1 at h
  linarith

end Encoding

namespace Machine

noncomputable def leftCode (b N n : ℕ) (c : Configuration) : ℝ :=
  Encoding.streamCode b (Scales.K N n) (leftDigits c)

noncomputable def rightCode (b N n : ℕ) (c : Configuration) : ℝ :=
  Encoding.streamCode b (Scales.K N n) (rightDigits c)

def recordedDigits (M : Machine) (w : List ℕ) (n : ℕ) : List ℕ :=
  let c := M.run w n
  2 * c.state :: (Encoding.digits (Scales.K w.length n) (leftDigits c) ++
    Encoding.digits (Scales.K w.length n) (rightDigits c))

noncomputable def recordedBlock (M : Machine) (w : List ℕ) (n : ℕ) : ℝ :=
  Encoding.code M.base (M.recordedDigits w n)

lemma recordedDigits_bound (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) :
    ∀ d ∈ M.recordedDigits w n, d + 2 ≤ M.base := by
  have hc := run_admissible M hM w hw n
  intro d hd
  simp only [recordedDigits, Encoding.digits, List.mem_cons, List.mem_append,
    List.mem_ofFn] at hd
  rcases hd with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact state_digit_bound M _ hc.1
  · exact symbol_digit_bound M _ (hc.2 _)
  · exact symbol_digit_bound M _ (hc.2 _)

lemma recordedBlock_mem (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n : ℕ) :
    M.recordedBlock w n ∈ Set.Icc (0 : ℝ) (Encoding.tailMax M.base) :=
  ⟨Encoding.code_nonneg _ _, Encoding.code_le_tailMax _ (by have := base_ge_four M; omega)
    _ (recordedDigits_bound M hM w hw n)⟩

lemma recordedBlock_formula (M : Machine) (w : List ℕ) (n : ℕ) :
    M.recordedBlock w n =
      ((2 * (M.run w n).state : ℕ) + leftCode M.base w.length n (M.run w n) +
        ((M.base : ℝ) ^ Scales.K w.length n)⁻¹ *
          rightCode M.base w.length n (M.run w n)) / M.base := by
  unfold recordedBlock recordedDigits leftCode rightCode Encoding.streamCode
  rw [Encoding.configuration_block _ _ (by have := base_ge_four M; omega),
    Encoding.digits_length]

lemma recordedBlock_integral (M : Machine) (w : List ℕ) (n : ℕ) :
    ∃ a : ℤ, (M.base : ℝ) ^ (1 + 2 * Scales.K w.length n) * M.recordedBlock w n = a := by
  obtain ⟨a, ha⟩ := Encoding.code_denominator M.base (by have := base_ge_four M; omega)
    (M.recordedDigits w n)
  refine ⟨a, ?_⟩
  have hlen : (M.recordedDigits w n).length = 1 + 2 * Scales.K w.length n := by
    simp only [recordedDigits, List.length_cons, List.length_append, Encoding.digits_length]
    omega
  simpa only [recordedBlock, hlen, Int.cast_natCast] using ha

lemma read_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (n : ℕ) :
    let b := M.base
    let s := Scales.s w.length n
    let K := Scales.K w.length n
    let D := Encoding.donor b w.length (M.recordedBlock w) n
    Profiles.decoder b ((b : ℝ) ^ s * D) = M.recordedBlock w n ∧
    Profiles.decoder b ((b : ℝ) ^ (s + 1 + K) * D) = rightCode b w.length n (M.run w n) ∧
    Profiles.decoder b ((b : ℝ) ^ (s + 1) * D) - ((b : ℝ) ^ K)⁻¹ *
      Profiles.decoder b ((b : ℝ) ^ (s + 1 + K) * D) = leftCode b w.length n (M.run w n) :=
  Encoding.read_donor_configuration M.base w.length n (by have := base_ge_four M; omega)
    (fun j => 2 * (M.run w j).state)
    (fun j => Encoding.digits (Scales.K w.length j) (leftDigits (M.run w j)))
    (fun j => Encoding.digits (Scales.K w.length j) (rightDigits (M.run w j)))
    (fun j => Encoding.digits_length _ _) (fun j => Encoding.digits_length _ _)
    (recordedDigits_bound M hM w hw)

end Machine
end AlternatingNS

namespace AlternatingNS
namespace Machine

def execute (c : Configuration) (r : Rule) : Configuration where
  state := r.1
  head := c.head + ((r.2.2.val : ℤ) - 1)
  tape := Function.update c.tape c.head r.2.1

lemma step_execute (M : Machine) (c : Configuration) :
    M.step c = execute c (M.command c.state (c.tape c.head)) := step_eq_command M c

lemma execute_right (c : Configuration) (r : Rule) (hd : r.2.2 = 2) :
    leftDigits (execute c r) 0 = 2 * r.2.1 ∧
    (∀ j, leftDigits (execute c r) (j + 1) = leftDigits c j) ∧
    (∀ j, rightDigits (execute c r) j = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [leftDigits, execute, hd]
  · intro j
    have hi : c.head - ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + 1 - ((j : ℤ) + 1 + 1) = c.head - ((j : ℤ) + 1) := by omega
    simp [leftDigits, execute, hd, he, Function.update_of_ne hi]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + 1 + (j : ℤ) = c.head + ((j : ℤ) + 1) := by omega
    simp [rightDigits, execute, hd, he, Function.update_of_ne hi]

lemma execute_stay (c : Configuration) (r : Rule) (hd : r.2.2 = 1) :
    (∀ j, leftDigits (execute c r) j = leftDigits c j) ∧
    rightDigits (execute c r) 0 = 2 * r.2.1 ∧
    (∀ j, rightDigits (execute c r) (j + 1) = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hi : c.head - ((j : ℤ) + 1) ≠ c.head := by omega
    simp [leftDigits, execute, hd, Function.update_of_ne hi]
  · simp [rightDigits, execute, hd]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    simp [rightDigits, execute, hd, Function.update_of_ne hi]

lemma execute_left (c : Configuration) (r : Rule) (hd : r.2.2 = 0) :
    (∀ j, leftDigits (execute c r) j = leftDigits c (j + 1)) ∧
    rightDigits (execute c r) 0 = leftDigits c 0 ∧
    rightDigits (execute c r) 1 = 2 * r.2.1 ∧
    (∀ j, rightDigits (execute c r) (j + 1 + 1) = rightDigits c (j + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hi : c.head - ((j : ℤ) + 1 + 1) ≠ c.head := by omega
    have he : c.head + (-1) - ((j : ℤ) + 1) = c.head - ((j : ℤ) + 1 + 1) := by omega
    simp [leftDigits, execute, hd, he, Function.update_of_ne hi]
  · simp [leftDigits, rightDigits, execute, hd, sub_eq_add_neg]
  · simp [rightDigits, execute, hd]
  · intro j
    have hi : c.head + ((j : ℤ) + 1) ≠ c.head := by omega
    have he : c.head + (-1) + ((j : ℤ) + 1 + 1) = c.head + ((j : ℤ) + 1) := by omega
    simp [rightDigits, execute, hd, he, Function.update_of_ne hi]

lemma code_execute_right (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 2) :
    leftCode b N (n + 1) (execute c r) = ((2 * r.2.1 : ℕ) + leftCode b N n c) / b ∧
    rightCode b N (n + 1) (execute c r) =
      (b : ℝ) * rightCode b N n c - rightDigits c 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := execute_right c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [hK, Encoding.streamCode_succ, h₀]
    have he : (fun j => leftDigits (execute c r) (j + 1)) = leftDigits c := funext h₁
    rw [he, Encoding.streamCode_padding b (Scales.K N n) (Scales.K N n + 1) hb
      (by omega) _ (leftDigits_padded N n c hc)]
  · unfold rightCode
    rw [show rightDigits (execute c r) = (fun j => rightDigits c (j + 1)) from funext h₂]
    exact Encoding.streamCode_pop b (Scales.K N n) _ hb (by omega) _
      (rightDigits_padded N n c hc)

lemma code_execute_stay (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 1) :
    leftCode b N (n + 1) (execute c r) = leftCode b N n c ∧
    rightCode b N (n + 1) (execute c r) =
      ((2 * r.2.1 : ℕ) + ((b : ℝ) * rightCode b N n c - rightDigits c 0)) / b := by
  obtain ⟨h₀, h₁, h₂⟩ := execute_stay c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [show leftDigits (execute c r) = leftDigits c from funext h₀]
    exact Encoding.streamCode_padding b (Scales.K N n) _ hb (by omega) _
      (leftDigits_padded N n c hc)
  · unfold rightCode
    rw [hK, Encoding.streamCode_succ, h₁, funext h₂]
    rw [Encoding.streamCode_pop b (Scales.K N n) (Scales.K N n + 1) hb (by omega) _
      (rightDigits_padded N n c hc)]

lemma code_execute_left (b N n : ℕ) (hb : 0 < b) (c : Configuration)
    (hc : Window N n c) (r : Rule) (hd : r.2.2 = 0) :
    leftCode b N (n + 1) (execute c r) =
      (b : ℝ) * leftCode b N n c - leftDigits c 0 ∧
    rightCode b N (n + 1) (execute c r) =
      ((leftDigits c 0 : ℝ) + ((2 * r.2.1 : ℕ) +
        ((b : ℝ) * rightCode b N n c - rightDigits c 0)) / b) / b := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := execute_left c r hd
  have hK : Scales.K N (n + 1) = (Scales.K N n + 1) + 1 := by dsimp [Scales.K]; omega
  constructor
  · unfold leftCode
    rw [funext h₀]
    exact Encoding.streamCode_pop b (Scales.K N n) _ hb (by omega) _
      (leftDigits_padded N n c hc)
  · unfold rightCode
    rw [hK, Encoding.streamCode_succ, Encoding.streamCode_succ]
    simp only [h₁, zero_add, h₂]
    rw [funext h₃, Encoding.streamCode_pop b (Scales.K N n) (Scales.K N n) hb (by omega) _
      (rightDigits_padded N n c hc)]

end Machine
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/MachineProfiles.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def selector (b a : ℕ) (v : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  letI := eightAtLeastTwo
  Real.smoothTransition (8 * ((b : ℝ) * v - 2 * a) + 2) *
    Real.smoothTransition (8 * (2 * a + 1 - (b : ℝ) * v) + 2)

lemma selector_smooth (b a : ℕ) : ContDiff ℝ ∞ (selector b a) := by
  unfold selector
  fun_prop

lemma selector_nonneg (b a : ℕ) (v : ℝ) : 0 ≤ selector b a v :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma selector_le_one (b a : ℕ) (v : ℝ) : selector b a v ≤ 1 := by
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

lemma selector_one (b a : ℕ) (v : ℝ)
    (h₀ : 2 * (a : ℝ) - 1 / 8 ≤ b * v) (h₁ : (b : ℝ) * v ≤ 2 * a + 9 / 8) :
    selector b a v = 1 := by
  rw [selector, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

lemma selector_zero_left (b a : ℕ) (v : ℝ) (h : (b : ℝ) * v ≤ 2 * a - 1 / 4) :
    selector b a v = 0 := by
  rw [selector, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma selector_zero_right (b a : ℕ) (v : ℝ) (h : 2 * (a : ℝ) + 5 / 4 ≤ b * v) :
    selector b a v = 0 := by
  rw [selector, Real.smoothTransition.zero_of_nonpos (by linarith :
    8 * (2 * (a : ℝ) + 1 - b * v) + 2 ≤ 0), mul_zero]

lemma selector_support_bound (b a : ℕ) (v : ℝ) (h : selector b a v ≠ 0) :
    2 * (a : ℝ) - 1 / 4 < b * v ∧ (b : ℝ) * v < 2 * a + 5 / 4 := by
  constructor
  · by_contra hn
    exact h (selector_zero_left b a v (le_of_not_gt hn))
  · by_contra hn
    exact h (selector_zero_right b a v (le_of_not_gt hn))

lemma selector_support_disjoint (b a q : ℕ) (haq : a ≠ q) :
    Disjoint (Function.support (selector b a)) (Function.support (selector b q)) := by
  rw [Set.disjoint_left]
  intro v ha hq
  obtain ⟨ha₀, ha₁⟩ := selector_support_bound b a v ha
  obtain ⟨hq₀, hq₁⟩ := selector_support_bound b q v hq
  rcases lt_or_gt_of_ne haq with h | h
  · have h' : (a : ℝ) + 1 ≤ q := by exact_mod_cast h
    linarith
  · have h' : (q : ℝ) + 1 ≤ a := by exact_mod_cast h
    linarith

lemma selector_on_cell (b a q : ℕ) (v : ℝ)
    (h₀ : 2 * (q : ℝ) ≤ b * v) (h₁ : (b : ℝ) * v ≤ 2 * q + 1) :
    selector b a v = if a = q then 1 else 0 := by
  split_ifs with h
  · subst a
    apply selector_one <;> linarith
  · rcases lt_or_gt_of_ne h with ha | ha
    · have h' : (a : ℝ) + 1 ≤ q := by exact_mod_cast ha
      apply selector_zero_right
      linarith
    · have h' : (q : ℝ) + 1 ≤ a := by exact_mod_cast ha
      apply selector_zero_left
      linarith

lemma selector_code (b a q : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ d ∈ L, d + 2 ≤ b) :
    selector b a (Encoding.code b (2 * q :: L)) = if a = q then 1 else 0 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have h := Encoding.digit_interval b (2 * q) hb L hL
  have h₀ := (div_le_iff₀ hb').1 h.1
  have h₁ := (le_div_iff₀ hb').1 h.2
  push_cast at h₀ h₁
  apply selector_on_cell <;> nlinarith

lemma selector_streamCode (b a q K : ℕ) (hb : 2 ≤ b) (hK : 0 < K) (f : ℕ → ℕ)
    (hf : ∀ j, f j + 2 ≤ b) (h₀ : f 0 = 2 * q) :
    selector b a (Encoding.streamCode b K f) = if a = q then 1 else 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  rw [Encoding.streamCode, Encoding.digits_succ, h₀]
  apply selector_code b a q hb
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
  exact hf _

end Profiles

namespace Machine

lemma selector_recordedBlock (M : Machine) (hM : M.WellFormed) (w : List ℕ)
    (hw : M.ValidInput w) (n q : ℕ) :
    Profiles.selector M.base q (M.recordedBlock w n) =
      if q = (M.run w n).state then 1 else 0 := by
  apply Profiles.selector_code _ _ _ (by have := base_ge_four M; omega)
  intro d hd
  exact recordedDigits_bound M hM w hw n d (List.mem_cons_of_mem _ hd)

lemma selector_leftCode (M : Machine) (c : Configuration) (hc : M.Admissible c) (N n a : ℕ) :
    Profiles.selector M.base a (leftCode M.base N n c) =
      if a = c.tape (c.head - 1) then 1 else 0 := by
  apply Profiles.selector_streamCode _ _ _ _ (by have := base_ge_four M; omega)
    (by dsimp [Scales.K]; omega)
  · intro j
    exact symbol_digit_bound M _ (hc.2 _)
  · simp [leftDigits]

lemma selector_rightCode (M : Machine) (c : Configuration) (hc : M.Admissible c) (N n a : ℕ) :
    Profiles.selector M.base a (rightCode M.base N n c) =
      if a = c.tape c.head then 1 else 0 := by
  apply Profiles.selector_streamCode _ _ _ _ (by have := base_ge_four M; omega)
    (by dsimp [Scales.K]; omega)
  · intro j
    exact symbol_digit_bound M _ (hc.2 _)
  · simp [rightDigits]

end Machine
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/LocalRules.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace LocalRule

noncomputable def readC (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ Scales.s N n * D)
noncomputable def readB (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D)
noncomputable def readA (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ (Scales.s N n + 1) * D) -
    ((M.base : ℝ) ^ Scales.K N n)⁻¹ * readB M N n D

noncomputable def updateLeft (b _a l : ℕ) (r : Rule) (A _B : ℝ) : ℝ :=
  letI := neZeroThree
  letI := twoAtLeastTwo
  if r.2.2 = 0 then (b : ℝ) * A - 2 * l
  else if r.2.2 = 1 then A else ((2 * r.2.1 : ℕ) + A) / b

noncomputable def updateRight (b a l : ℕ) (r : Rule) (_A B : ℝ) : ℝ :=
  letI := neZeroThree
  letI := twoAtLeastTwo
  let R := (b : ℝ) * B - 2 * a
  if r.2.2 = 0 then ((2 * l : ℕ) + ((2 * r.2.1 : ℕ) + R) / b) / b
  else if r.2.2 = 1 then ((2 * r.2.1 : ℕ) + R) / b else R

noncomputable def branchNumerator (b K a l : ℕ) (r : Rule) (A B : ℝ) : ℝ :=
  (2 * r.1 : ℕ) + updateLeft b a l r A B +
    ((b : ℝ) ^ K)⁻¹ * updateRight b a l r A B

noncomputable def branch (M : Machine) (N n q a : ℕ) (A B : ℝ) : ℝ :=
  letI := neZeroThree
  let r := M.command q a
  if r.2.2 = 0 then ∑ l ∈ Finset.range M.alphabet,
    Profiles.selector M.base l A * branchNumerator M.base (Scales.K N (n + 1)) a l r A B
  else branchNumerator M.base (Scales.K N (n + 1)) a 0 r A B

noncomputable def write (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Scales.ε M.base N (n + 1) / M.base *
    ∑ q ∈ Finset.range (M.states + 1), ∑ a ∈ Finset.range M.alphabet,
      Profiles.selector M.base q (readC M N n D) *
        Profiles.selector M.base a (readB M N n D) *
          branch M N n q a (readA M N n D) (readB M N n D)

noncomputable def haltWeight (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (M.states + 1),
    if q = M.states ∨ q ∈ M.haltingStates then Profiles.selector M.base q (readC M N n D) else 0

noncomputable def signal (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Scales.ε M.base N n - Scales.ε M.base N (n + 1) +
    2 * Scales.ε M.base N (n + 1) * haltWeight M N n D

lemma readC_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readC M N n) := by
  exact (Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)

lemma readB_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readB M N n) := by
  exact (Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)

lemma readA_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readA M N n) := by
  exact ((Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)).sub (contDiff_const.mul (readB_smooth M N n))

lemma branchNumerator_smooth (b K a l : ℕ) (r : Rule) (A B : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun D => branchNumerator b K a l r (A D) (B D)) := by
  unfold branchNumerator updateLeft updateRight
  split_ifs <;> fun_prop

lemma branch_smooth (M : Machine) (N n q a : ℕ) (A B : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun D => branch M N n q a (A D) (B D)) := by
  unfold branch
  dsimp only
  split_ifs
  · apply ContDiff.sum
    intro l _
    exact ((Profiles.selector_smooth M.base l).comp hA).mul
      (branchNumerator_smooth _ _ _ _ _ _ _ hA hB)
  · exact branchNumerator_smooth _ _ _ _ _ _ _ hA hB

lemma write_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (write M N n) := by
  unfold write
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro q _
  apply ContDiff.sum
  intro a _
  exact (((Profiles.selector_smooth M.base q).comp (readC_smooth M N n)).mul
    ((Profiles.selector_smooth M.base a).comp (readB_smooth M N n))).mul
    (branch_smooth M N n q a _ _ (readA_smooth M N n) (readB_smooth M N n))

lemma haltWeight_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (haltWeight M N n) := by
  unfold haltWeight
  apply ContDiff.sum
  intro q _
  split_ifs
  · exact (Profiles.selector_smooth M.base q).comp (readC_smooth M N n)
  · exact contDiff_const

lemma signal_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (signal M N n) := by
  exact contDiff_const.add (contDiff_const.mul (haltWeight_smooth M N n))

lemma readC_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readC M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      M.recordedBlock w n := (M.read_run hM w hw n).1

lemma readB_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readB M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Machine.rightCode M.base w.length n (M.run w n) := (M.read_run hM w hw n).2.1

lemma readA_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readA M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Machine.leftCode M.base w.length n (M.run w n) := (M.read_run hM w hw n).2.2

end LocalRule
end AlternatingNS

namespace AlternatingNS
namespace LocalRule

lemma branchNumerator_execute (b N n : ℕ) (hb : 0 < b) (c : Machine.Configuration)
    (hc : Machine.Window N n c) (r : Rule) :
    branchNumerator b (Scales.K N (n + 1)) (c.tape c.head) (c.tape (c.head - 1)) r
      (Machine.leftCode b N n c) (Machine.rightCode b N n c) =
    (2 * r.1 : ℕ) + Machine.leftCode b N (n + 1) (Machine.execute c r) +
      ((b : ℝ) ^ Scales.K N (n + 1))⁻¹ * Machine.rightCode b N (n + 1) (Machine.execute c r) := by
  by_cases h₀ : r.2.2 = 0
  · obtain ⟨hL, hR⟩ := Machine.code_execute_left b N n hb c hc r h₀
    rw [hL, hR]
    simp [branchNumerator, updateLeft, updateRight, h₀, Machine.leftDigits, Machine.rightDigits]
  · by_cases h₁ : r.2.2 = 1
    · obtain ⟨hL, hR⟩ := Machine.code_execute_stay b N n hb c hc r h₁
      rw [hL, hR]
      simp [branchNumerator, updateLeft, updateRight, h₁, Machine.rightDigits]
    · have h₂ : r.2.2 = 2 := by omega
      obtain ⟨hL, hR⟩ := Machine.code_execute_right b N n hb c hc r h₂
      rw [hL, hR]
      simp [branchNumerator, updateLeft, updateRight, h₀, h₁, Machine.rightDigits]

lemma branch_on_configuration (M : Machine) (N n : ℕ) (c : Machine.Configuration)
    (ha : M.Admissible c) (hw : Machine.Window N n c) :
    branch M N n c.state (c.tape c.head)
      (Machine.leftCode M.base N n c) (Machine.rightCode M.base N n c) =
    (2 * (M.step c).state : ℕ) + Machine.leftCode M.base N (n + 1) (M.step c) +
      ((M.base : ℝ) ^ Scales.K N (n + 1))⁻¹ * Machine.rightCode M.base N (n + 1) (M.step c) := by
  have hb : 0 < M.base := by have := M.base_ge_four; omega
  have hnum := branchNumerator_execute M.base N n hb c hw (M.command c.state (c.tape c.head))
  rw [Machine.step_execute]
  unfold branch
  dsimp only
  split_ifs with h₀
  · rw [Finset.sum_eq_single_of_mem (c.tape (c.head - 1)) (Finset.mem_range.2 (ha.2 _))]
    · rw [Machine.selector_leftCode M c ha N n, ite_eq_left rfl, one_mul]
      exact hnum
    · intro l _ hl
      simp [Machine.selector_leftCode M c ha N n l, hl]
  · simpa only [branchNumerator, updateLeft, updateRight, h₀, ite_false, Machine.execute] using hnum

lemma write_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    write M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1) := by
  have hc := M.run_admissible hM w hw n
  have hq : (M.run w n).state ∈ Finset.range (M.states + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_of_le hc.1)
  have ha : (M.run w n).tape (M.run w n).head ∈ Finset.range M.alphabet :=
    Finset.mem_range.2 (hc.2 _)
  unfold write
  rw [readC_run M hM w hw n, readB_run M hM w hw n, readA_run M hM w hw n]
  simp only [Machine.selector_recordedBlock M hM w hw n,
    Machine.selector_rightCode M (M.run w n) hc w.length n,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', ite_eq_left hq, ite_eq_left ha]
  rw [branch_on_configuration M w.length n (M.run w n) hc (M.run_window w n)]
  rw [Machine.recordedBlock_formula, Machine.run_succ]
  ring

lemma haltWeight_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    haltWeight M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      if M.isHalting (M.run w n) then 1 else 0 := by
  have hc := (M.run_admissible hM w hw n).1
  unfold haltWeight
  rw [readC_run M hM w hw n,
    Finset.sum_eq_single_of_mem (M.run w n).state (Finset.mem_range.2 (by omega))]
  · simp [Machine.selector_recordedBlock M hM w hw n, Machine.isHalting]
  · intro q _ hq
    simp [Machine.selector_recordedBlock M hM w hw n q, hq]

lemma signal_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    signal M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Detector.increment M.base w.length (fun j => M.isHalting (M.run w j)) n := by
  rw [signal, haltWeight_run M hM w hw n]
  simp only [Detector.increment, mul_ite, mul_one, mul_zero]

end LocalRule
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/SpatialCurls.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Spatial

noncomputable def d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) (x : Space) : E := fderiv ℝ F x (e i)

lemma coord_smooth (i : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x i) :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff

lemma coord_hasFDeriv (i : Fin 3) (x : Space) :
    HasFDerivAt (fun x : Space => x i) (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i) x :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt

lemma e_apply (i j : Fin 3) : e i j = if j = i then 1 else 0 := by
  simp [e, EuclideanSpace.single, PiLp.single_apply]

lemma d_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (d i F) := by
  exact (hF.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).clm_apply contDiff_const

lemma d_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) : tsupport (d i F) ⊆ tsupport F :=
  tsupport_fderiv_apply_subset ℝ (e i)

lemma d_comm (i j : Fin 3) (F : Space → ℝ) (hF : ContDiff ℝ ∞ F) :
    d i (d j F) = d j (d i F) := by
  ext x
  have hd := (hF.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).differentiable (by simp)
  have heq (a b : Fin 3) : d a (d b F) x = fderiv ℝ (fderiv ℝ F) x (e a) (e b) := by
    unfold d
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [heq, heq]
  exact hF.contDiffAt.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) _ _

noncomputable def curl (i j : Fin 3) (φ : Space → ℝ) (x : Space) : Space :=
  d j φ x • e i - d i φ x • e j

lemma curl_smooth (i j : Fin 3) (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (curl i j φ) :=
  ((d_smooth j φ hφ).smul contDiff_const).sub ((d_smooth i φ hφ).smul contDiff_const)

lemma curl_tsupport (i j : Fin 3) (φ : Space → ℝ) : tsupport (curl i j φ) ⊆ tsupport φ := by
  apply (tsupport_sub _ _).trans
  apply Set.union_subset
  · exact (tsupport_smul_subset_left _ _).trans (d_tsupport j φ)
  · exact (tsupport_smul_subset_left _ _).trans (d_tsupport i φ)

lemma curl_div (i j : Fin 3) (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : Space) :
    (∑ k : Fin 3, d k (curl i j φ) x k) = 0 := by
  have hd (k : Fin 3) := (d_smooth k φ hφ).differentiable (by simp)
  have hc (k : Fin 3) : d k (curl i j φ) x k =
      d k (d j φ) x * (if k = i then 1 else 0) -
        d k (d i φ) x * (if k = j then 1 else 0) := by
    change (fderiv ℝ ((fun y => d j φ y • e i) - (fun y => d i φ y • e j)) x (e k)) k = _
    rw [fderiv_sub ((hd j x).smul_const _) ((hd i x).smul_const _),
      fderiv_smul_const (hd j x), fderiv_smul_const (hd i x)]
    simp [e_apply, d]
  simp_rw [hc]
  rw [Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [d_comm i j φ hφ, sub_self]

def box : Set Space := {x | ∀ i : Fin 3, |x i| ≤ 3}

def plateau : Set Space := {x | ∀ i : Fin 3, |x i| < 2}

noncomputable def cutoff (x : Space) : ℝ :=
  letI := threeAtLeastTwo
  ∏ i : Fin 3, Real.smoothTransition (3 - x i) * Real.smoothTransition (3 + x i)

lemma cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  unfold cutoff
  apply contDiff_prod
  intro i _
  have hi := coord_smooth i
  fun_prop

lemma isClosed_box : IsClosed box := by
  have heq : box = ⋂ i : Fin 3, {x : Space | |x i| ≤ 3} := by ext; simp [box]
  rw [heq]
  exact isClosed_iInter (fun i => isClosed_le (coord_smooth i).continuous.abs continuous_const)

lemma box_compact : IsCompact box := by
  apply (isCompact_closedBall (0 : Space) 9).of_isClosed_subset isClosed_box
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  calc
    ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ ∑ _i : Fin 3, (3 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
    _ ≤ 9 ^ 2 := by norm_num

lemma plateau_open : IsOpen plateau := by
  have heq : plateau = ⋂ i : Fin 3, {x : Space | |x i| < 2} := by ext; simp [plateau]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (coord_smooth i).continuous.abs continuous_const)

lemma cutoff_one (x : Space) (hx : x ∈ plateau) : cutoff x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  have hi := abs_lt.1 (hx i)
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 - x i),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 + x i), one_mul]

lemma cutoff_one_near (x : Space) (hx : x ∈ plateau) :
    cutoff =ᶠ[𝓝 x] (fun _ => 1) :=
  Filter.eventually_of_mem (plateau_open.mem_nhds hx) (fun y hy => cutoff_one y hy)

lemma cutoff_support : tsupport cutoff ⊆ box := by
  apply closure_minimal _ isClosed_box
  intro x hx i
  by_contra hi
  have hn : 3 < |x i| := lt_of_not_ge hi
  have hz : Real.smoothTransition (3 - x i) * Real.smoothTransition (3 + x i) = 0 := by
    rcases (lt_abs.1 hn) with hn | hn
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - x i ≤ 0), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 + x i ≤ 0), mul_zero]
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

noncomputable def shearPotential (d i j : Fin 3) (L E : ℝ → ℝ) (x : Space) : ℝ :=
  x j * L (x d) - x i * E (x d)

noncomputable def localizedShear (d i j : Fin 3) (L E : ℝ → ℝ) : Space → Space :=
  curl i j (fun x => cutoff x * shearPotential d i j L E x)

lemma shearPotential_smooth (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (shearPotential d i j L E) :=
  ((coord_smooth j).mul (hL.comp (coord_smooth d))).sub
    ((coord_smooth i).mul (hE.comp (coord_smooth d)))

lemma localizedShear_smooth (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (localizedShear d i j L E) :=
  curl_smooth i j _ (cutoff_smooth.mul (shearPotential_smooth d i j L E hL hE))

lemma localizedShear_support (d i j : Fin 3) (L E : ℝ → ℝ) :
    tsupport (localizedShear d i j L E) ⊆ box :=
  (curl_tsupport _ _ _).trans (tsupport_mul_subset_left.trans cutoff_support)

lemma localizedShear_div (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) (x : Space) :
    (∑ k : Fin 3, Spatial.d k (localizedShear d i j L E) x k) = 0 :=
  curl_div i j _ (cutoff_smooth.mul (shearPotential_smooth d i j L E hL hE)) x

lemma localizedShear_plateau (d i j : Fin 3) (hij : i ≠ j) (hdi : d ≠ i) (hdj : d ≠ j)
    (L E : ℝ → ℝ) (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E)
    (x : Space) (hx : x ∈ plateau) :
    localizedShear d i j L E x = L (x d) • e i + E (x d) • e j := by
  have heq : (fun y => cutoff y * shearPotential d i j L E y) =ᶠ[𝓝 x]
      shearPotential d i j L E := by
    filter_upwards [cutoff_one_near x hx] with y hy
    rw [hy, one_mul]
  have hL' := ((hL.differentiable (by simp)) (x d)).hasFDerivAt.comp x (coord_hasFDeriv d x)
  have hE' := ((hE.differentiable (by simp)) (x d)).hasFDerivAt.comp x (coord_hasFDeriv d x)
  have hφ := ((coord_hasFDeriv j x).mul hL').sub ((coord_hasFDeriv i x).mul hE')
  have hφeq := hφ.fderiv
  change fderiv ℝ (shearPotential d i j L E) x = _ at hφeq
  simp only [localizedShear, curl, Spatial.d, heq.fderiv_eq, hφeq]
  simp [ContinuousLinearMap.comp_apply, PiLp.proj_apply, e_apply, hij, hij.symm, hdi,
    hdj, sub_eq_add_neg]

end Spatial
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/TimeGlue.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def pulse (t : ℝ) : ℝ := deriv clock t

lemma pulse_smooth : ContDiff ℝ ∞ pulse := by
  exact ContDiff.deriv' (by simpa using clock_smooth)

lemma clock_hasDeriv (t : ℝ) : HasDerivAt clock (pulse t) t :=
  (clock_smooth.differentiable (by simp) t).hasDerivAt

lemma pulse_zero_left (t : ℝ) (ht : t ≤ 0) : pulse t = 0 := by
  have heq : clock =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds (by linarith : t < (1 : ℝ) / 4)] with u hu
    exact clock_zero u hu.le
  simpa [pulse] using heq.deriv_eq

lemma pulse_zero_right (t : ℝ) (ht : 1 ≤ t) : pulse t = 0 := by
  have heq : clock =ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds (by linarith : (3 : ℝ) / 4 < t)] with u hu
    exact clock_one u hu.le
  simpa [pulse] using heq.deriv_eq

end Profiles

namespace TimeGlue

noncomputable def glue {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (W : ℕ → A → E) (t : ℝ) (x : A) : E :=
  ∑' k : ℕ, g (t - k) • W k x

lemma eq_sum {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (W : ℕ → A → E)
    (t : ℝ) (x : A) (a : ℕ) (ht : t ≤ a) :
    glue g W t x = ∑ k ∈ Finset.range a, g (t - k) • W k x := by
  apply tsum_eq_sum
  intro k hk
  have hk' : a ≤ k := by simpa using hk
  have hka : (a : ℝ) ≤ k := by exact_mod_cast hk'
  rw [hg _ (by linarith), zero_smul]

lemma locally_eq_sum {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace A] (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (W : ℕ → A → E)
    (z : ℝ × A) : ∃ a : ℕ,
      Function.uncurry (glue g W) =ᶠ[𝓝 z]
        (fun z : ℝ × A => ∑ k ∈ Finset.range a, g (z.1 - k) • W k z.2) := by
  obtain ⟨a, ha⟩ := exists_nat_gt z.1
  refine ⟨a, ?_⟩
  have hn : ∀ᶠ z' : ℝ × A in 𝓝 z, z'.1 < (a : ℝ) :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds ha
  filter_upwards [hn] with z' hz'
  exact eq_sum g hg W z'.1 z'.2 a hz'.le

lemma smooth {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (hs : ContDiff ℝ ∞ g)
    (W : ℕ → A → E) (hW : ∀ k, ContDiff ℝ ∞ (W k)) :
    ContDiff ℝ ∞ (Function.uncurry (glue g W)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨a, ha⟩ := locally_eq_sum g hg W z
  have hf : ContDiff ℝ ∞
      (fun z : ℝ × A => ∑ k ∈ Finset.range a, g (z.1 - k) • W k z.2) := by
    apply ContDiff.sum
    intro k _
    exact (hs.comp (contDiff_fst.sub contDiff_const)).smul ((hW k).comp contDiff_snd)
  exact hf.contDiffAt.congr_of_eventuallyEq ha

lemma hasDerivAt {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g g' : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (hg' : ∀ t, t ≤ 0 → g' t = 0)
    (hd : ∀ t, HasDerivAt g (g' t) t) (W : ℕ → A → E) (t : ℝ) (x : A) :
    HasDerivAt (fun u => glue g W u x) (glue g' W t x) t := by
  obtain ⟨a, ha⟩ := exists_nat_gt t
  rw [eq_sum g' hg' W t x a ha.le]
  have hf : HasDerivAt (fun u => ∑ k ∈ Finset.range a, g (u - k) • W k x)
      (∑ k ∈ Finset.range a, g' (t - k) • W k x) t := by
    apply HasDerivAt.fun_sum
    intro k _
    have hk := ((hd (t - k)).comp t ((hasDerivAt_id t).sub_const (k : ℝ))).smul_const (W k x)
    simpa using hk
  apply hf.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ha] with u hu
  exact eq_sum g hg W u x a hu.le

lemma pulse_slot {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ℕ → A → E) (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) (x : A) :
    glue Profiles.pulse W t x = Profiles.pulse (t - k) • W k x := by
  apply tsum_eq_single k
  intro j hj
  rcases lt_or_gt_of_ne hj with hj | hj
  · have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    rw [Profiles.pulse_zero_right _ (by linarith [ht.1]), zero_smul]
  · have hj' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hj
    rw [Profiles.pulse_zero_left _ (by linarith [ht.2]), zero_smul]

lemma clock_slot {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ℕ → A → E) (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) (x : A) :
    glue Profiles.clock W t x = (∑ j ∈ Finset.range k, W j x) +
      Profiles.clock (t - k) • W k x := by
  rw [eq_sum Profiles.clock (fun u hu => Profiles.clock_zero u (by linarith)) W t x
    (k + 1) (by simpa using ht.2), Finset.sum_range_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast (Finset.mem_range.1 hj)
  rw [Profiles.clock_one _ (by linarith [ht.1]), one_smul]

end TimeGlue
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Construction.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Construction

def donorIndex (n : ℕ) : Fin 3 :=
  letI := neZeroThree
  if n % 2 = 0 then 1 else 2

def receiverIndex (n : ℕ) : Fin 3 :=
  letI := neZeroThree
  if n % 2 = 0 then 2 else 1

lemma indices_distinct (n : ℕ) : receiverIndex n ≠ 0 ∧ donorIndex n ≠ receiverIndex n ∧
    donorIndex n ≠ 0 := by
  unfold donorIndex receiverIndex
  split_ifs <;> decide

noncomputable def slot (M : Machine) (N n : ℕ) : Space → Space :=
  letI := neZeroThree
  Spatial.localizedShear (donorIndex n) (receiverIndex n) 0
    (LocalRule.write M N n) (LocalRule.signal M N n)

noncomputable def loading (M : Machine) (w : List ℕ) : Space → Space :=
  letI := neZeroThree
  Spatial.localizedShear 2 1 0
    (fun _ => Scales.ε M.base w.length 0 * M.recordedBlock w 0)
    (fun _ => 1 - Scales.ε M.base w.length 0)

noncomputable def piece (M : Machine) (w : List ℕ) : ℕ → Space → Space :=
  fun n => Nat.casesOn n (loading M w) (fun k => slot M w.length k)

noncomputable def velocity (M : Machine) (w : List ℕ) : Velocity :=
  TimeGlue.glue Profiles.pulse (piece M w)

lemma slot_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (slot M N n) :=
  Spatial.localizedShear_smooth _ _ _ _ _ (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n)

lemma loading_smooth (M : Machine) (w : List ℕ) : ContDiff ℝ ∞ (loading M w) :=
  Spatial.localizedShear_smooth _ _ _ _ _ contDiff_const contDiff_const

lemma piece_smooth (M : Machine) (w : List ℕ) (n : ℕ) : ContDiff ℝ ∞ (piece M w n) := by
  cases n with
  | zero => exact loading_smooth M w
  | succ n => exact slot_smooth M w.length n

lemma piece_support (M : Machine) (w : List ℕ) (n : ℕ) :
    tsupport (piece M w n) ⊆ Spatial.box := by
  cases n <;> exact Spatial.localizedShear_support _ _ _ _ _

lemma piece_div (M : Machine) (w : List ℕ) (n : ℕ) (x : Space) :
    (∑ i : Fin 3, Spatial.d i (piece M w n) x i) = 0 := by
  cases n with
  | zero => exact Spatial.localizedShear_div _ _ _ _ _ contDiff_const contDiff_const x
  | succ n =>
    exact Spatial.localizedShear_div _ _ _ _ _ (LocalRule.write_smooth M w.length n)
      (LocalRule.signal_smooth M w.length n) x

lemma velocity_smooth (M : Machine) (w : List ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (velocity M w)) :=
  TimeGlue.smooth Profiles.pulse Profiles.pulse_zero_left Profiles.pulse_smooth
    (piece M w) (piece_smooth M w)

lemma velocity_supported (M : Machine) (w : List ℕ) (t : ℝ) :
    Function.support (velocity M w t) ⊆ Spatial.box := by
  intro x hx
  by_contra hn
  have hz (k : ℕ) : piece M w k x = 0 := by
    by_contra hk
    exact hn (piece_support M w k (subset_closure hk))
  exact hx (by simp [velocity, TimeGlue.glue, hz])

lemma velocity_rest (M : Machine) (w : List ℕ) (x : Space) : velocity M w 0 x = 0 := by
  rw [velocity, TimeGlue.pulse_slot _ 0 0 (by norm_num) x]
  simp [Profiles.pulse_zero_left]

lemma velocity_div (M : Machine) (w : List ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    div (velocity M w) t x = 0 := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  have heq : velocity M w t = (fun x => Profiles.pulse (t - k) • piece M w k x) :=
    funext (TimeGlue.pulse_slot _ k t hk)
  unfold div dx
  rw [heq]
  have hd := (piece_smooth M w k).differentiable (by simp) x
  change (∑ i : Fin 3, (fderiv ℝ (Profiles.pulse (t - k) • piece M w k) x (e i)) i) = 0
  simp only [fderiv_const_smul hd, smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  change Profiles.pulse (t - k) * (∑ i : Fin 3, Spatial.d i (piece M w k) x i) = 0
  rw [piece_div, mul_zero]

lemma slot_plateau (M : Machine) (N n : ℕ) (x : Space) (hx : x ∈ Spatial.plateau) :
    slot M N n x = LocalRule.write M N n (x (donorIndex n)) • e (receiverIndex n) +
      LocalRule.signal M N n (x (donorIndex n)) • e 0 :=
  Spatial.localizedShear_plateau _ _ _ (indices_distinct n).1 (indices_distinct n).2.1
    (indices_distinct n).2.2 _ _ (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n) x hx

lemma loading_plateau (M : Machine) (w : List ℕ) (x : Space) (hx : x ∈ Spatial.plateau) :
    loading M w x = (Scales.ε M.base w.length 0 * M.recordedBlock w 0) • e 1 +
      (1 - Scales.ε M.base w.length 0) • e 0 :=
  Spatial.localizedShear_plateau 2 1 0 (by decide) (by decide) (by decide)
    _ _ contDiff_const contDiff_const x hx

end Construction
end AlternatingNS

namespace AlternatingNS
namespace Construction

lemma donorIndex_succ (n : ℕ) : donorIndex (n + 1) = receiverIndex n := by
  unfold donorIndex receiverIndex
  split_ifs <;> omega

lemma donorIndex_eq (j n : ℕ) : donorIndex j = donorIndex n ↔ j % 2 = n % 2 := by
  unfold donorIndex
  split_ifs <;> norm_num <;> omega

noncomputable def memory (M : Machine) (w : List ℕ) (n : ℕ) : Space :=
  ∑ j ∈ Finset.range (n + 1),
    (Scales.ε M.base w.length j * M.recordedBlock w j) • e (donorIndex j)

noncomputable def history (M : Machine) (w : List ℕ) (n : ℕ) : Space :=
  memory M w n + Detector.signal M.base w.length (fun j => M.isHalting (M.run w j)) n • e 0

noncomputable def displacement (M : Machine) (w : List ℕ) : ℕ → Space
  | 0 => (Scales.ε M.base w.length 0 * M.recordedBlock w 0) • e 1 +
      (1 - Scales.ε M.base w.length 0) • e 0
  | n + 1 => (Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1)) •
      e (receiverIndex n) +
      Detector.increment M.base w.length (fun j => M.isHalting (M.run w j)) n • e 0

noncomputable def node (M : Machine) (w : List ℕ) : ℕ → Space
  | 0 => observedParticle
  | n + 1 => history M w n

noncomputable def path (M : Machine) (w : List ℕ) (t : ℝ) : Space :=
  observedParticle + TimeGlue.glue Profiles.clock (fun k (_ : Unit) => displacement M w k) t ()

lemma memory_zero_coord (M : Machine) (w : List ℕ) (n : ℕ) : memory M w n 0 = 0 := by
  have h0 (j : ℕ) : (0 : Fin 3) ≠ donorIndex j := (indices_distinct j).2.2.symm
  simp [memory, WithLp.ofLp_sum, Finset.sum_apply, Spatial.e_apply, h0]

lemma memory_donor (M : Machine) (w : List ℕ) (n : ℕ) :
    memory M w n (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  simp only [memory, Encoding.donor, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Spatial.e_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [donorIndex_eq, eq_comm (a := n % 2) (b := j % 2), mul_ite, mul_one, mul_zero]

lemma memory_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    memory M w (n + 1) = memory M w n +
      (Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1)) • e (receiverIndex n) := by
  simp only [memory, Finset.sum_range_succ (n := n + 1), donorIndex_succ]

lemma history_zero_coord (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w n 0 = Detector.signal M.base w.length (fun j => M.isHalting (M.run w j)) n := by
  simp [history, PiLp.add_apply, memory_zero_coord, PiLp.smul_apply, Spatial.e_apply]

lemma history_donor (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w n (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  simp [history, PiLp.add_apply, memory_donor, PiLp.smul_apply, Spatial.e_apply, (indices_distinct n).2.2]

lemma history_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w (n + 1) = history M w n + displacement M w (n + 1) := by
  simp only [history, memory_succ, Detector.signal, displacement, add_smul]
  abel

lemma observedParticle_eq : observedParticle = -e 0 := by
  ext i
  fin_cases i <;> norm_num [observedParticle, e, PiLp.single_apply, PiLp.neg_apply,
    EuclideanSpace.single, EuclideanSpace.equiv]

lemma node_succ (M : Machine) (w : List ℕ) (k : ℕ) :
    node M w (k + 1) = node M w k + displacement M w k := by
  cases k with
  | zero =>
    simp only [node, history, memory, Nat.zero_add, Finset.sum_range_one, donorIndex, Nat.zero_mod,
      ite_true, Detector.signal, displacement, observedParticle_eq, sub_smul, one_smul, neg_smul]
    abel
  | succ n => exact history_succ M w n

lemma node_sum (M : Machine) (w : List ℕ) (k : ℕ) :
    node M w k = observedParticle + ∑ j ∈ Finset.range k, displacement M w j := by
  induction k with
  | zero => simp [node]
  | succ k ih => rw [node_succ, ih, Finset.sum_range_succ, add_assoc]

lemma path_slot (M : Machine) (w : List ℕ) (k : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) :
    path M w t = node M w k + Profiles.clock (t - k) • displacement M w k := by
  rw [path, TimeGlue.clock_slot _ k t ht (), ← add_assoc, ← node_sum]

lemma path_node (M : Machine) (w : List ℕ) (k : ℕ) : path M w k = node M w k := by
  rw [path_slot M w k k (by constructor <;> linarith)]
  simp [Profiles.clock_zero]

lemma memory_bound (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (n : ℕ) (i : Fin 3) : 0 ≤ memory M w n i ∧ memory M w n i < 1 / 4 := by
  have hb := M.base_ge_four
  have he (j : ℕ) := Scales.ε_nonneg M.base w.length j (by omega)
  have hC (j : ℕ) := M.recordedBlock_mem hM w hw j
  have hm := Encoding.tailMax_lt_one M.base (by omega)
  have hterm (j : ℕ) : 0 ≤ ((Scales.ε M.base w.length j * M.recordedBlock w j) •
      e (donorIndex j)) i ∧
      ((Scales.ε M.base w.length j * M.recordedBlock w j) • e (donorIndex j)) i ≤
        Scales.ε M.base w.length j := by
    simp only [PiLp.smul_apply, Spatial.e_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]
      exact ⟨mul_nonneg (he j) (hC j).1, mul_le_of_le_one_right (he j) ((hC j).2.trans hm.le)⟩
    · simp only [mul_zero]
      exact ⟨le_rfl, he j⟩
  simp only [memory, WithLp.ofLp_sum, Finset.sum_apply]
  refine ⟨Finset.sum_nonneg (fun j _ => (hterm j).1), ?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), Scales.ε M.base w.length j :=
      Finset.sum_le_sum (fun j _ => (hterm j).2)
    _ ≤ ∑' j, Scales.ε M.base w.length j :=
      (Scales.summable_ε M.base w.length (by omega)).sum_le_tsum _ (fun j _ => he j)
    _ ≤ 2 * Scales.ε M.base w.length 0 := Scales.total_memory_le _ _ (by omega)
    _ < 1 / 4 := Scales.initial_memory_small _ _ hb

lemma node_plateau (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (k : ℕ) : node M w k ∈ Spatial.plateau := by
  have hb := M.base_ge_four
  intro i
  cases k with
  | zero =>
    simp only [node, observedParticle_eq, PiLp.neg_apply, Spatial.e_apply]
    split_ifs <;> norm_num
  | succ n =>
    change |history M w n i| < 2
    by_cases hi : i = 0
    · rw [hi, history_zero_coord]
      have hp := Detector.signal_in_plateau M.base w.length hb
        (fun j => M.isHalting (M.run w j)) n
      exact (abs_lt.2 hp).trans (by norm_num)
    · simp only [history, PiLp.add_apply, PiLp.smul_apply, Spatial.e_apply,
        ite_eq_right hi, smul_eq_mul, mul_zero, add_zero]
      rw [abs_of_nonneg (memory_bound M hM w hw n i).1]
      exact (memory_bound M hM w hw n i).2.trans (by norm_num)

lemma segment_plateau (a b : Space) (ha : a ∈ Spatial.plateau) (hb : b ∈ Spatial.plateau)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) : (1 - θ) • a + θ • b ∈ Spatial.plateau := by
  intro i
  have hai := abs_lt.mp (ha i)
  have hbi := abs_lt.mp (hb i)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  apply abs_lt.mpr
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (le_of_lt (sub_pos.mpr hai.2)),
    mul_nonneg hθ.1 (le_of_lt (sub_pos.mpr hbi.2)),
    mul_nonneg (sub_nonneg.mpr hθ.2) (le_of_lt (sub_pos.mpr hai.1)),
    mul_nonneg hθ.1 (le_of_lt (sub_pos.mpr hbi.1))]

lemma path_plateau (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (t : ℝ) (ht : 0 ≤ t) : path M w t ∈ Spatial.plateau := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  rw [path_slot M w k t hk]
  have heq : node M w k + Profiles.clock (t - k) • displacement M w k =
      (1 - Profiles.clock (t - k)) • node M w k + Profiles.clock (t - k) • node M w (k + 1) := by
    rw [node_succ, smul_add, sub_smul, one_smul]
    abel
  rw [heq]
  exact segment_plateau _ _ (node_plateau M hM w hw k) (node_plateau M hM w hw (k + 1))
    _ (Profiles.clock_mem _)

end Construction
end AlternatingNS

namespace AlternatingNS
namespace Construction

lemma path_donor (M : Machine) (w : List ℕ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc ((n : ℝ) + 1) (n + 1 + 1)) :
    path M w t (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  have ht' : t ∈ Set.Icc ((n + 1 : ℕ) : ℝ) ((n + 1 : ℕ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  rw [path_slot M w (n + 1) t ht']
  simp only [node, PiLp.add_apply, PiLp.smul_apply, history_donor, displacement,
    Spatial.e_apply, (indices_distinct n).2.1, (indices_distinct n).2.2,
    ite_false, smul_eq_mul, mul_zero, add_zero]

lemma piece_path (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) :
    piece M w k (path M w t) = displacement M w k := by
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg k) ht.1
  have hp := path_plateau M hM w hw t ht0
  cases k with
  | zero => exact loading_plateau M w _ hp
  | succ n =>
    change slot M w.length n (path M w t) = _
    rw [slot_plateau M w.length n _ hp,
      path_donor M w n t (by simpa only [Nat.cast_add, Nat.cast_one] using ht),
      LocalRule.write_run M hM w hw, LocalRule.signal_run M hM w hw]
    rfl

lemma velocity_path (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (t : ℝ) (ht : 0 ≤ t) :
    velocity M w t (path M w t) =
      TimeGlue.glue Profiles.pulse (fun k (_ : Unit) => displacement M w k) t () := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  rw [velocity, TimeGlue.pulse_slot _ k t hk, TimeGlue.pulse_slot _ k t hk,
    piece_path M hM w hw k t hk]

theorem path_isTrajectory (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) :
    IsTrajectory (velocity M w) observedParticle (path M w) := by
  refine ⟨by simpa only [Nat.cast_zero, node] using path_node M w 0, ?_⟩
  intro t ht
  rw [velocity_path M hM w hw t ht]
  exact ((TimeGlue.hasDerivAt Profiles.clock Profiles.pulse
    (fun s hs => Profiles.clock_zero s (by linarith)) Profiles.pulse_zero_left
    Profiles.clock_hasDeriv (fun k (_ : Unit) => displacement M w k) t ()).const_add
      observedParticle).hasDerivWithinAt

lemma path_loading_coord (M : Machine) (w : List ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    path M w t 0 = Detector.loading M.base w.length (Profiles.clock t) := by
  rw [path_slot M w 0 t (by simpa using ht)]
  simp [node, observedParticle_eq, displacement, PiLp.add_apply, PiLp.smul_apply,
    PiLp.neg_apply, Spatial.e_apply, Detector.loading]

lemma path_slot_coord (M : Machine) (w : List ℕ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc ((n : ℝ) + 1) (n + 1 + 1)) :
    path M w t 0 = Detector.during M.base w.length (fun j => M.isHalting (M.run w j)) n
      (Profiles.clock (t - (n + 1))) := by
  rw [path_slot M w (n + 1) t (by simpa only [Nat.cast_add, Nat.cast_one] using ht)]
  simp [node, displacement, PiLp.add_apply, PiLp.smul_apply, Spatial.e_apply,
    (indices_distinct n).1.symm, Detector.during, history_zero_coord]

theorem path_reachability (M : Machine) (w : List ℕ) :
    (∃ t : ℝ, 0 ≤ t ∧ 0 < path M w t 0) ↔ M.Halts w := by
  have hb := M.base_ge_four
  constructor
  · rintro ⟨t, ht, hp⟩
    have hk : t ∈ Set.Icc (⌊t⌋₊ : ℝ) (⌊t⌋₊ + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
    generalize hfloor : ⌊t⌋₊ = k at hk
    cases k with
    | zero =>
      have ht' : t ∈ Set.Icc 0 1 := by simpa using hk
      rw [path_loading_coord M w t ht'] at hp
      exact False.elim ((Detector.loading_negative M.base w.length (by omega) _
        (Profiles.clock_mem t)).not_gt hp)
    | succ n =>
      rw [path_slot_coord M w n t (by simpa only [Nat.cast_add, Nat.cast_one] using hk)] at hp
      exact (Detector.machine_scalar_reachability M.base (by omega) M w).mp
        ⟨n, _, Profiles.clock_mem _, hp⟩
  · intro h
    let n := Nat.find h
    have hn : M.isHalting (M.run w n) = true := Nat.find_spec h
    have hprev : ∀ j < n, M.isHalting (M.run w j) = false :=
      fun j hj => Bool.eq_false_iff.2 (Nat.find_min h hj)
    refine ⟨((n + 1 + 1 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [path_node]
    change 0 < history M w (n + 1) 0
    rw [history_zero_coord, Detector.signal_first_halt M.base w.length _ n hprev hn]
    exact Scales.ε_pos M.base w.length (n + 1) (by omega)

end Construction
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Analytic.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Analytic

lemma spatial_fderiv_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) := by
  exact (hF.comp ((contDiff_fst.fst).prodMk contDiff_snd)).fderiv contDiff_snd (by simp)

lemma dx_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (i : Fin 3) :
    ContDiff ℝ ∞ (Function.uncurry (dx i F)) :=
  (spatial_fderiv_smooth F hF).clm_apply contDiff_const

noncomputable def fullDt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) : Field E := fun t x => fderiv ℝ (fun s => F s x) t 1

lemma fullDt_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (Function.uncurry (fullDt F)) := by
  exact ((hF.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv contDiff_fst (by simp)).clm_apply
    contDiff_const

lemma dt_eq_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    dt F t x = fullDt F t x := by
  unfold dt fullDt
  have hd : DifferentiableAt ℝ (fun s => F s x) t :=
    ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
  rw [fderivWithin_eq_fderiv (uniqueDiffOn_Ici _ _ ht) hd]

lemma smooth_classical (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ClassicalRegularity U (fun _ _ => 0) := by
  refine ⟨fun x => ?_, fun t _ => ?_, fun t _ i => ?_, fun t _ => differentiable_const _, ?_⟩
  · exact ((hU.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableOn
  · exact (hU.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  · exact ((dx_smooth U hU i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  · intro T _
    refine ⟨hU.continuous.continuousOn, ?_, fun i => (dx_smooth U hU i).continuous.continuousOn,
      fun i j => (dx_smooth (dx j U) (dx_smooth U hU j) i).continuous.continuousOn,
      continuousOn_const, ?_⟩
    · apply (fullDt_smooth U hU).continuous.continuousOn.congr
      intro z hz
      exact dt_eq_full U hU z.1 hz.1.1 z.2
    · intro i
      change ContinuousOn (fun z : ℝ × Space => fderiv ℝ (fun _ : Space => (0 : ℝ)) z.2 (e i)) _
      simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × Space => (0 : ℝ))
        (timeCylinder T))

lemma residual_navierStokes (ν : ℝ) (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (h0 : ∀ x, U 0 x = 0) (hd : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    NavierStokes ν (residual ν U) U (fun _ _ => 0) := by
  refine ⟨smooth_classical U hU, h0, fun t ht x => ⟨hd t ht x, ?_⟩⟩
  have hp : grad (fun _ _ => 0) t x = 0 := by
    ext i
    simp [grad, dx, EuclideanSpace.equiv]
  rw [hp, residual]
  abel

lemma advection_smooth (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ContDiff ℝ ∞ (Function.uncurry (advection U)) :=
  (spatial_fderiv_smooth U hU).clm_apply hU

lemma laplacian_smooth (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ContDiff ℝ ∞ (Function.uncurry (laplacian U)) := by
  change ContDiff ℝ ∞ (fun z : ℝ × Space => ∑ i : Fin 3, dx i (dx i U) z.1 z.2)
  apply ContDiff.sum
  intro i _
  exact dx_smooth (dx i U) (dx_smooth U hU i) i

lemma residual_smooth (ν : ℝ) (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    Smooth (residual ν U) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × Space =>
      fullDt U z.1 z.2 + advection U z.1 z.2 - ν • laplacian U z.1 z.2) :=
    ((fullDt_smooth U hU).add (advection_smooth U hU)).sub
      ((laplacian_smooth U hU).const_smul ν)
  apply hf.contDiffOn.congr
  intro z hz
  simp only [Function.uncurry, residual, dt_eq_full U hU z.1 hz.1]

lemma dx_supported {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hF : ∀ t, Function.support (F t) ⊆ K) (i : Fin 3) :
    ∀ t, Function.support (dx i F t) ⊆ K := by
  intro t x hx
  exact (closure_minimal (hF t) hK) ((Spatial.d_tsupport i (F t)) (subset_closure hx))

lemma outside_dt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (K : Set Space) (hF : ∀ t, Function.support (F t) ⊆ K)
    (t : ℝ) (x : Space) (hx : x ∉ K) : dt F t x = 0 := by
  have he : (fun s => F s x) = fun _ => 0 := by
    funext s
    exact Function.notMem_support.1 (fun hx' => hx (hF s hx'))
  simp [dt, he]

lemma residual_supported (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsClosed K)
    (hU : ∀ t, Function.support (U t) ⊆ K) :
    ∀ t, Function.support (residual ν U t) ⊆ K := by
  intro t x hx
  by_contra hn
  have hUx : U t x = 0 := Function.notMem_support.1 (fun hx' => hn (hU t hx'))
  have hΔ : laplacian U t x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact Function.notMem_support.1 (fun hx' => hn (dx_supported (dx i U) K hK
      (dx_supported U K hK hU i) i t hx'))
  exact hx (by simp [residual, outside_dt U K hU t x hn, advection, hUx, hΔ])

lemma finite_bound {E : Type*} [NormedAddCommGroup E]
    (F : Field E) (hF : Continuous (Function.uncurry F)) (K : Set Space) (hK : IsCompact K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (T : ℝ) :
    ∃ C : ℝ≥0, ∀ t ∈ Set.Icc 0 T, ∀ x, ‖F t x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨⟨max 0 C, le_max_left _ _⟩, fun t ht x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_right _ _)
  · have hz : F t x = 0 := Function.notMem_support.1 (fun hx' => hx (hs t hx'))
    simp only [hz, norm_zero]
    exact le_max_left _ _

lemma finite_lipschitz (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) (T : ℝ) :
    ∃ C : ℝ≥0, ∀ t ∈ Set.Icc 0 T, LipschitzWith C (U t) := by
  have hder : ∀ t, Function.support (fderiv ℝ (U t)) ⊆ K :=
    fun t => (support_fderiv_subset ℝ).trans (closure_minimal (hs t) hK.isClosed)
  obtain ⟨C, hC⟩ := finite_bound (fun t x => fderiv ℝ (U t) x)
    (spatial_fderiv_smooth U hU).continuous K hK hder T
  refine ⟨C, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
    ((hU.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast hC t ht x

end Analytic
end AlternatingNS

namespace AlternatingNS
namespace Analytic

lemma trajectory_unique (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) (γ δ : ℝ → Space) (hγ : IsTrajectory U a γ) (hδ : IsTrajectory U a δ)
    (T : ℝ) (hT : 0 ≤ T) : γ T = δ T := by
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  have hc (β : ℝ → Space) (hβ : IsTrajectory U a β) : ContinuousOn β (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn (fun t ht => (hβ.2 t ht.1).mono Set.Icc_subset_Ici_self)
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hC t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (hc γ hγ) (fun t ht => (hγ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun _ _ => Set.mem_univ _) (hc δ hδ)
    (fun t ht => (hδ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun _ _ => Set.mem_univ _) (hγ.1.trans hδ.1.symm) ⟨hT, le_rfl⟩

lemma finite_trajectory (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) (T : ℝ) (hT : 0 ≤ T) :
    ∃ γ : ℝ → Space, γ 0 = a ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ (U t (γ t)) (Set.Icc 0 T) t := by
  obtain ⟨L, hL⟩ := finite_bound U hU.continuous K hK hs T
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hpl : IsPicardLindelof U t₀ a (L * ⟨T, hT⟩) 0 L C := by
    refine ⟨fun t ht => (hC t ht).lipschitzOnWith, fun x _ => ?_,
      fun t ht x _ => hL t ht x, ?_⟩
    · exact (hU.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    · change (L : ℝ) * max (T - 0) (0 - 0) ≤ (L : ℝ) * T - 0
      simp [max_eq_left hT]
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma finite_trajectory_unique (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (γ δ : ℝ → Space) (T : ℝ) (h0 : γ 0 = δ 0)
    (hγ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ (U t (γ t)) (Set.Icc 0 T) t)
    (hδ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt δ (U t (δ t)) (Set.Icc 0 T) t) :
    Set.EqOn γ δ (Set.Icc 0 T) := by
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  have hd (β : ℝ → Space)
      (hβ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt β (U t (β t)) (Set.Icc 0 T) t) :
      ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt β (U t (β t)) (Set.Ici t) t := by
    intro t ht
    apply (hβ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (fun y hy => ⟨ht.1.trans hy.1, hy.2⟩)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hC t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hγ) (hd γ hγ) (fun _ _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hδ) (hd δ hδ) (fun _ _ => Set.mem_univ _) h0

lemma global_trajectory (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) : ∃ γ, IsTrajectory U a γ := by
  classical
  have hex (n : ℕ) := finite_trajectory U hU K hK hs a ((n : ℝ) + 1) (by positivity)
  choose α hα₀ hα using hex
  have coherent (n m : ℕ) (t : ℝ) (ht : 0 ≤ t) (hn : t ≤ (n : ℝ) + 1)
      (hm : t ≤ (m : ℝ) + 1) : α n t = α m t := by
    apply finite_trajectory_unique U hU K hK hs (α n) (α m) t
      ((hα₀ n).trans (hα₀ m).symm)
      (fun s hs => (hα n s ⟨hs.1, hs.2.trans hn⟩).mono
        (Set.Icc_subset_Icc le_rfl hn))
      (fun s hs => (hα m s ⟨hs.1, hs.2.trans hm⟩).mono
        (Set.Icc_subset_Icc le_rfl hm)) ⟨ht, le_rfl⟩
  let γ : ℝ → Space := fun t => α ⌈t⌉₊ t
  have agrees (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 ((n : ℝ) + 1)) : γ t = α n t :=
    coherent _ _ t ht.1 (by linarith [Nat.le_ceil t]) ht.2
  refine ⟨γ, ?_, fun t ht => ?_⟩
  · exact hα₀ _
  · obtain ⟨n, hn⟩ := exists_nat_gt t
    have htn : t < (n : ℝ) + 1 := by linarith
    have hmem : Set.Icc 0 ((n : ℝ) + 1) ∈ 𝓝[Set.Ici 0] t := by
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds (Iio_mem_nhds htn))] with s hs hs'
      exact ⟨hs, hs'.le⟩
    have he := agrees n t ⟨ht, htn.le⟩
    rw [he]
    apply ((hα n t ⟨ht, htn.le⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
    · filter_upwards [hmem] with s hs
      exact agrees n s hs
    · exact he

theorem global_material_flow (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) :
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory U a (X a)) ∧
      (∀ a γ, IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) := by
  classical
  choose X hX using global_trajectory U hU K hK hs
  exact ⟨X, hX, fun a γ hγ t ht => trajectory_unique U hU K hK hs a γ (X a) hγ (hX a) t ht⟩

end Analytic
end AlternatingNS

namespace AlternatingNS
namespace Construction

noncomputable def force (ν : ℝ) (M : Machine) (w : List ℕ) : Velocity :=
  residual ν (velocity M w)

theorem smooth_forced_simulation (ν : ℝ) (M : Machine) (hM : M.WellFormed)
    (w : List ℕ) (hw : M.ValidInput w) :
    Smooth (force ν M w) ∧ Smooth (velocity M w) ∧
    SupportedIn (force ν M w) Spatial.box ∧ SupportedIn (velocity M w) Spatial.box ∧
    NavierStokes ν (force ν M w) (velocity M w) (fun _ _ => 0) ∧
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory (velocity M w) a (X a)) ∧
      (∀ a γ, IsTrajectory (velocity M w) a γ → ∀ t, 0 ≤ t → γ t = X a t) ∧
      ((∃ t : ℝ, 0 ≤ t ∧ 0 < X observedParticle t 0) ↔ M.Halts w) := by
  have hU := velocity_smooth M w
  have hK := Spatial.box_compact
  have hs := velocity_supported M w
  refine ⟨Analytic.residual_smooth ν _ hU, hU.contDiffOn,
    fun t _ => Analytic.residual_supported ν _ _ hK.isClosed hs t,
    fun t _ => hs t,
    Analytic.residual_navierStokes ν _ hU (velocity_rest M w) (velocity_div M w), ?_⟩
  obtain ⟨X, hX, hu⟩ := Analytic.global_material_flow _ hU _ hK hs
  refine ⟨X, hX, hu, ?_⟩
  have he : ∀ t, 0 ≤ t → path M w t = X observedParticle t :=
    hu _ _ (path_isTrajectory M hM w hw)
  rw [← path_reachability M w]
  exact ⟨fun ⟨t, ht, hp⟩ => ⟨t, ht, by rw [he t ht]; exact hp⟩,
    fun ⟨t, ht, hp⟩ => ⟨t, ht, by rw [← he t ht]; exact hp⟩⟩

end Construction
end AlternatingNS
namespace AlternatingNS
namespace Analytic

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def zeroExtend (K : Set Space) (g : C(K, E)) (x : Space) : E := by
  classical
  exact if hx : x ∈ K then g ⟨x, hx⟩ else 0

omit [NormedSpace ℝ E] in
lemma zeroExtend_memLp (K : Set Space) (hK : IsCompact K) (g : C(K, E)) :
    MemLp (zeroExtend K g) 2 (volume : Measure Space) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hm : StronglyMeasurable (zeroExtend K g) :=
    g.continuous.stronglyMeasurable.dite stronglyMeasurable_const hK.measurableSet
  have hs : HasCompactSupport (zeroExtend K g) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hx'
    exact hx (by simp [zeroExtend, hx'])
  apply hs.memLp_of_bound hm.aestronglyMeasurable ‖g‖
  filter_upwards [] with x
  by_cases hx : x ∈ K
  · simpa [zeroExtend, hx] using g.norm_coe_le_norm ⟨x, hx⟩
  · simp [zeroExtend, hx]

def compactToL2 (K : Set Space) (hK : IsCompact K) [CompactSpace K] :
    C(K, E) →L[ℝ] Lp E 2 (volume : Measure Space) := by
  classical
  let A : C(K, E) →ₗ[ℝ] Lp E 2 (volume : Measure Space) :=
    { toFun := fun g => (zeroExtend_memLp K hK g).toLp (zeroExtend K g)
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [(zeroExtend_memLp K hK (g + h)).coeFn_toLp,
          Lp.coeFn_add ((zeroExtend_memLp K hK g).toLp _) ((zeroExtend_memLp K hK h).toLp _),
          (zeroExtend_memLp K hK g).coeFn_toLp, (zeroExtend_memLp K hK h).coeFn_toLp]
          with x hx hx' hg hh
        simp only [hx, hx', Pi.add_apply, hg, hh]
        by_cases hk : x ∈ K <;> simp [zeroExtend, hk]
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [(zeroExtend_memLp K hK (c • g)).coeFn_toLp,
          Lp.coeFn_smul c ((zeroExtend_memLp K hK g).toLp _),
          (zeroExtend_memLp K hK g).coeFn_toLp] with x hx hx' hg
        simp only [RingHom.id_apply, hx, hx', Pi.smul_apply, hg]
        by_cases hk : x ∈ K <;> simp [zeroExtend, hk] }
  let B : Lp ℝ 2 (volume : Measure Space) :=
    indicatorConstLp 2 hK.measurableSet hK.measure_ne_top 1
  apply A.mkContinuous ‖B‖
  intro g
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul (g := B)
  filter_upwards [(zeroExtend_memLp K hK g).coeFn_toLp, indicatorConstLp_coeFn
    (p := 2) (hs := hK.measurableSet) (hμs := hK.measure_ne_top) (c := (1 : ℝ))] with x hx hb
  change ‖((zeroExtend_memLp K hK g).toLp _) x‖ ≤ _
  rw [hx, hb]
  by_cases hk : x ∈ K
  · simpa [zeroExtend, hk] using g.norm_coe_le_norm ⟨x, hk⟩
  · simp [zeroExtend, hk]

lemma compactToL2_coe (K : Set Space) (hK : IsCompact K) [CompactSpace K] (g : C(K, E)) :
    ∀ᵐ x ∂(volume : Measure Space), compactToL2 K hK g x = zeroExtend K g x :=
  (zeroExtend_memLp K hK g).coeFn_toLp

def onCompact (F : Field E) (hF : Continuous (Function.uncurry F)) (K : Set Space)
    (t : ℝ) : C(K, E) :=
  ⟨fun x => F t x, hF.comp (continuous_const.prodMk continuous_subtype_val)⟩

omit [NormedSpace ℝ E] in
lemma onCompact_continuous (F : Field E) (hF : Continuous (Function.uncurry F))
    (K : Set Space) : Continuous (onCompact F hF K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

lemma compactToL2_onCompact (F : Field E) (hF : Continuous (Function.uncurry F))
    (K : Set Space) (hK : IsCompact K) [CompactSpace K]
    (hs : ∀ t, Function.support (F t) ⊆ K) (t : ℝ) :
    ∀ᵐ x ∂(volume : Measure Space), compactToL2 K hK (onCompact F hF K t) x = F t x := by
  classical
  filter_upwards [compactToL2_coe K hK (onCompact F hF K t)] with x hx
  rw [hx]
  by_cases hk : x ∈ K
  · simp only [zeroExtend, dite_eq_left hk]
    rfl
  · have hz : F t x = 0 := Function.notMem_support.1 (fun hx => hk (hs t hx))
    simp [zeroExtend, hk, hz]

lemma onCompact_hasDerivAt [CompleteSpace E] (F : Field E)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set Space) [CompactSpace K] (t : ℝ) :
    HasDerivAt (onCompact F hF.continuous K)
      (onCompact (fullDt F) (fullDt_smooth F hF).continuous K t) t := by
  let H := onCompact F hF.continuous K
  let G := onCompact (fullDt F) (fullDt_smooth F hF).continuous K
  have hG : Continuous G := onCompact_continuous _ _ _
  have he (s : ℝ) : H s = H 0 + ∫ r in (0 : ℝ)..s, G r := by
    ext x
    change F s x = F 0 x + (ContinuousMap.evalCLM ℝ x) (∫ r in (0 : ℝ)..s, G r)
    rw [← (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm (hG.intervalIntegrable 0 s)]
    have hd (r : ℝ) : HasDerivAt (fun t => F t x) (fullDt F r x) r :=
      ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp) r).hasFDerivAt.hasDerivAt
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r ∈ Set.uIcc 0 s) => hd r)
      (((fullDt_smooth F hF).continuous.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable 0 s)
    change F s x = F 0 x + ∫ r in (0 : ℝ)..s, fullDt F r x
    rw [hi]
    abel
  have h : HasDerivAt (fun s => H 0 + ∫ r in (0 : ℝ)..s, G r) (G t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 t)
      (hG.stronglyMeasurableAtFilter volume (𝓝 t)) hG.continuousAt).const_add (H 0)
  rwa [← funext he] at h

lemma iterate_dx_smooth (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (i : Fin 3) (n : ℕ) : ContDiff ℝ ∞ (Function.uncurry ((dx i)^[n] F)) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dx_smooth _ ih i

lemma spatial_smooth (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (α : MultiIndex) : ContDiff ℝ ∞ (Function.uncurry (spatial α F)) :=
  iterate_dx_smooth _ (iterate_dx_smooth _ (iterate_dx_smooth F hF 2 _) 1 _) 0 _

lemma iterate_dx_supported (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (i : Fin 3) (n : ℕ) :
    ∀ t, Function.support ((dx i)^[n] F t) ⊆ K := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dx_supported _ K hK ih i

lemma spatial_supported (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (α : MultiIndex) :
    ∀ t, Function.support (spatial α F t) ⊆ K :=
  iterate_dx_supported _ K hK
    (iterate_dx_supported _ K hK (iterate_dx_supported F K hK hs 2 _) 1 _) 0 _

lemma fullDt_supported (F : Field E) (K : Set Space)
    (hs : ∀ t, Function.support (F t) ⊆ K) :
    ∀ t, Function.support (fullDt F t) ⊆ K := by
  intro t x hx
  by_contra hk
  have he : (fun s => F s x) = fun _ => 0 := by
    funext s
    exact Function.notMem_support.1 (fun hx' => hk (hs s hx'))
  exact hx (by simp [fullDt, he])

lemma smooth_continuousInH (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (F t) ⊆ K)
    (k : ℕ) (T : ℝ) : ContinuousInH k F T := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro α _
  let hα := (spatial_smooth F hF α).continuous
  refine ⟨fun t => compactToL2 K hK (onCompact (spatial α F) hα K t), ?_, ?_⟩
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · intro t _
    exact compactToL2_onCompact _ hα K hK (spatial_supported F K hK.isClosed hs α) t

lemma smooth_C1InL2 (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (T : ℝ) : C1InL2 U T := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let H := onCompact U hU.continuous K
  let G := onCompact (fullDt U) (fullDt_smooth U hU).continuous K
  refine ⟨fun t => compactToL2 K hK (H t), fun t => compactToL2 K hK (G t), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · intro t _
    exact ((compactToL2 K hK).hasFDerivAt.comp_hasDerivAt t
      (onCompact_hasDerivAt U hU K t)).hasDerivWithinAt
  · intro t _
    exact compactToL2_onCompact U hU.continuous K hK hs t
  · intro t ht
    filter_upwards [compactToL2_onCompact (fullDt U) (fullDt_smooth U hU).continuous
      K hK (fullDt_supported U K hs) t] with x hx
    rw [hx, dt_eq_full U hU t ht.1]

theorem smooth_energyClass (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) :
    EnergyClass U (fun _ _ => 0) := by
  refine ⟨?_, ?_⟩
  · intro T _
    obtain ⟨C, hC⟩ := finite_bound U hU.continuous K hK hs T
    exact ⟨smooth_continuousInH U hU K hK hs 2 T, smooth_C1InL2 U hU K hK hs T,
      smooth_continuousInH (fun _ _ => (0 : ℝ)) contDiff_const K hK
        (fun _ => by simp) 1 T, C, hC⟩
  · intro T _
    obtain ⟨C, hC⟩ := finite_bound U hU.continuous K hK hs T
    obtain ⟨D, hD⟩ := finite_bound (fun t x => fderiv ℝ (U t) x)
      (spatial_fderiv_smooth U hU).continuous K hK
      (fun t => (support_fderiv_subset ℝ).trans (closure_minimal (hs t) hK.isClosed)) T
    exact ⟨C + D, fun t ht x => add_le_add (hC t ht x) (hD t ht x)⟩

end
end Analytic

namespace Construction

theorem velocity_energyClass (M : Machine) (w : List ℕ) :
    EnergyClass (velocity M w) (fun _ _ => 0) :=
  Analytic.smooth_energyClass _ (velocity_smooth M w) _ Spatial.box_compact (velocity_supported M w)

end Construction
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/DerivativeBounds.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Bounds
noncomputable section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def BoundedJets (f : E → F) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ r f x‖ ≤ C

def ScaledJets (s : ℕ → ℝ) (f : ℕ → E → F) : Prop :=
  (∀ n, ContDiff ℝ ∞ (f n)) ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ n x, ‖iteratedFDeriv ℝ r (f n) x‖ ≤ C * s n ^ r

lemma compact_bounded (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    BoundedJets f := by
  refine ⟨hf, fun r => ?_⟩
  obtain ⟨B, hB⟩ := ((hc.iteratedFDeriv r).isCompact_range
    (hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top))).exists_bound_of_continuousOn
      continuous_id.continuousOn
  exact ⟨max 0 B, le_max_left _ _, fun x => (hB _ ⟨x, rfl⟩).trans (le_max_right _ _)⟩

lemma ScaledJets.congr {s : ℕ → ℝ} {f g : ℕ → E → F} (hf : ScaledJets s f)
    (he : ∀ n x, f n x = g n x) : ScaledJets s g := by
  have h : f = g := funext (fun n => funext (he n))
  rwa [← h]

lemma ScaledJets.const {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (a : ℕ → F)
    (B : ℝ) (hB : 0 ≤ B) (ha : ∀ n, ‖a n‖ ≤ B) :
    ScaledJets s (fun n (_ : E) => a n) := by
  refine ⟨fun _ => contDiff_const, fun r => ⟨B, hB, fun n x => ?_⟩⟩
  rcases r with _ | r
  · simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using ha n
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply, norm_zero]
    exact mul_nonneg hB (pow_nonneg (hs n) _)

lemma ScaledJets.fixed {s : ℕ → ℝ} (hs : ∀ n, 1 ≤ s n) {f : E → F}
    (hf : BoundedJets f) : ScaledJets s (fun _ => f) := by
  refine ⟨fun _ => hf.1, fun r => ?_⟩
  obtain ⟨C, hC, h⟩ := hf.2 r
  exact ⟨C, hC, fun n x => (h x).trans (le_mul_of_one_le_right hC (one_le_pow₀ (hs n)))⟩

lemma ScaledJets.add {s : ℕ → ℝ} {f g : ℕ → E → F}
    (hf : ScaledJets s f) (hg : ScaledJets s g) :
    ScaledJets s (fun n x => f n x + g n x) := by
  refine ⟨fun n => (hf.1 n).add (hg.1 n), fun r => ?_⟩
  obtain ⟨A, hA, hfa⟩ := hf.2 r
  obtain ⟨B, hB, hgb⟩ := hg.2 r
  refine ⟨A + B, add_nonneg hA hB, fun n x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply (hf.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)
    (hg.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  exact (norm_add_le _ _).trans (by linarith [hfa n x, hgb n x])

lemma ScaledJets.sub {s : ℕ → ℝ} {f g : ℕ → E → F}
    (hf : ScaledJets s f) (hg : ScaledJets s g) :
    ScaledJets s (fun n x => f n x - g n x) := by
  refine ⟨fun n => (hf.1 n).sub (hg.1 n), fun r => ?_⟩
  obtain ⟨A, hA, hfa⟩ := hf.2 r
  obtain ⟨B, hB, hgb⟩ := hg.2 r
  refine ⟨A + B, add_nonneg hA hB, fun n x => ?_⟩
  rw [fun_iteratedFDeriv_sub_apply (hf.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)
    (hg.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  exact (norm_sub_le _ _).trans (by linarith [hfa n x, hgb n x])

lemma ScaledJets.smul {s : ℕ → ℝ} (_hs : ∀ n, 0 ≤ s n) {f : ℕ → E → F}
    (hf : ScaledJets s f) (a : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (ha : ∀ n, |a n| ≤ B) :
    ScaledJets s (fun n x => a n • f n x) := by
  refine ⟨fun n => contDiff_const.smul (hf.1 n), fun r => ?_⟩
  obtain ⟨C, hC, hc⟩ := hf.2 r
  refine ⟨B * C, mul_nonneg hB hC, fun n x => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' (hf.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt), norm_smul,
    Real.norm_eq_abs]
  calc
    |a n| * ‖iteratedFDeriv ℝ r (f n) x‖ ≤ B * (C * s n ^ r) := by
      gcongr
      exact ha n
      exact hc n x
    _ = _ := by ring

lemma ScaledJets.mul {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f g : ℕ → E → ℝ}
    (hf : ScaledJets s f) (hg : ScaledJets s g) :
    ScaledJets s (fun n x => f n x * g n x) := by
  classical
  refine ⟨fun n => (hf.1 n).mul (hg.1 n), fun r => ?_⟩
  choose A hA hfa using hf.2
  choose B hB hgb using hg.2
  let C := ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * B (r - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _)), fun n x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le (hf.1 n) (hg.1 n) x (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω))).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (A i * s n ^ i) * (B (r - i) * s n ^ (r - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (pow_nonneg (hs n) _))
      · exact hfa i n x
      · exact hgb (r - i) n x
    _ = C * s n ^ r := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by simpa using Finset.mem_range.mp hi
      rw [show (r.choose i : ℝ) * (A i * s n ^ i) * (B (r - i) * s n ^ (r - i)) =
        ((r.choose i : ℝ) * A i * B (r - i)) * (s n ^ i * s n ^ (r - i)) by ring,
        ← pow_add, Nat.add_sub_of_le hir]

lemma ScaledJets.sum {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {ι : Type*}
    (I : Finset ι) (f : ι → ℕ → E → F) (hf : ∀ i ∈ I, ScaledJets s (f i)) :
    ScaledJets s (fun n x => ∑ i ∈ I, f i n x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using ScaledJets.const hs (fun _ => (0 : F)) 0 le_rfl (by simp)
  | @insert a I ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma ScaledJets.ite {s : ℕ → ℝ} {f g : ℕ → E → F} (hs : ∀ n, 0 ≤ s n)
    (hf : ScaledJets s f) (hg : ScaledJets s g) (p : ℕ → Prop) [DecidablePred p] :
    ScaledJets s (fun n => if p n then f n else g n) := by
  refine ⟨fun n => by dsimp only; split_ifs <;> [exact hf.1 n; exact hg.1 n], fun r => ?_⟩
  obtain ⟨A, hA, hfa⟩ := hf.2 r
  obtain ⟨B, hB, hgb⟩ := hg.2 r
  refine ⟨max A B, le_trans hA (le_max_left _ _), fun n x => ?_⟩
  dsimp only
  split_ifs
  · exact (hfa n x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hs n) _))
  · exact (hgb n x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hs n) _))

lemma ScaledJets.comp {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → F}
    (hf : ScaledJets s f) {g : F → G} (hg : BoundedJets g) :
    ScaledJets s (fun n => g ∘ f n) := by
  classical
  refine ⟨fun n => hg.1.comp (hf.1 n), fun r => ?_⟩
  choose A hA hfa using hf.2
  choose B hB hgb using hg.2
  let D : ℝ := 1 + ∑ i ∈ Finset.range (r + 1), A i
  let C : ℝ := ∑ i ∈ Finset.range (r + 1), B i
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hA i))
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hB i)
  refine ⟨r.factorial * C * D ^ r, by positivity, fun n x => ?_⟩
  have h := norm_iteratedFDeriv_comp_le hg.1 (hf.1 n) (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω)) x
    (C := C) (D := D * s n) ?_ ?_
  · simpa only [mul_pow, mul_assoc] using h
  · intro i hi
    exact (hgb i (f n x)).trans (Finset.single_le_sum (fun i _ => hB i)
      (Finset.mem_range.mpr (by omega)))
  · intro i hi hir
    have hai : A i ≤ D := by
      have := Finset.single_le_sum (s := Finset.range (r + 1)) (f := A)
        (fun i _ => hA i) (Finset.mem_range.mpr (by omega : i < r + 1))
      dsimp [D]; linarith
    have hai' : A i ≤ D ^ i := hai.trans (le_self_pow₀ hD (by omega))
    calc
      ‖iteratedFDeriv ℝ i (f n) x‖ ≤ A i * s n ^ i := hfa i n x
      _ ≤ D ^ i * s n ^ i := mul_le_mul_of_nonneg_right hai' (pow_nonneg (hs n) _)
      _ = (D * s n) ^ i := (mul_pow _ _ _).symm

lemma norm_comp_linear (f : E → F) (hf : ContDiff ℝ ∞ f) (L : G →L[ℝ] E)
    (r : ℕ) (x : G) :
    ‖iteratedFDeriv ℝ r (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ r f (L x)‖ * ‖L‖ ^ r := by
  rw [L.iteratedFDeriv_comp_right hf x (WithTop.coe_le_coe.mpr le_top)]
  simpa using (iteratedFDeriv ℝ r f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

lemma ScaledJets.comp_linear {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → F}
    (hf : ScaledJets s f) (L : ℕ → G →L[ℝ] E) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ n, ‖L n‖ ≤ B) : ScaledJets s (fun n => f n ∘ L n) := by
  refine ⟨fun n => (hf.1 n).comp (L n).contDiff, fun r => ?_⟩
  obtain ⟨C, hC, hc⟩ := hf.2 r
  refine ⟨C * B ^ r, by positivity, fun n x => ?_⟩
  apply (norm_comp_linear (f n) (hf.1 n) (L n) r x).trans
  calc
    _ ≤ (C * s n ^ r) * B ^ r := by
      gcongr
      · exact mul_nonneg hC (pow_nonneg (hs n) _)
      · exact hc n _
      · exact hL n
    _ = _ := by ring

lemma BoundedJets.comp_scaled_linear {s : ℕ → ℝ} (_hs : ∀ n, 0 ≤ s n) {f : E → F}
    (hf : BoundedJets f) (L : ℕ → G →L[ℝ] E) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ n, ‖L n‖ ≤ B * s n) : ScaledJets s (fun n => f ∘ L n) := by
  refine ⟨fun n => hf.1.comp (L n).contDiff, fun r => ?_⟩
  obtain ⟨C, hC, hc⟩ := hf.2 r
  refine ⟨C * B ^ r, by positivity, fun n x => ?_⟩
  apply (norm_comp_linear f hf.1 (L n) r x).trans
  calc
    _ ≤ C * (B * s n) ^ r := by gcongr; exact hc _; exact hL n
    _ = _ := by ring

lemma ScaledJets.constant {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (a : F) :
    ScaledJets s (fun _ (_ : E) => a) :=
  ScaledJets.const hs (fun _ => a) ‖a‖ (norm_nonneg _) (fun _ => le_rfl)

lemma ScaledJets.cmul {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → ℝ}
    (hf : ScaledJets s f) (a : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (ha : ∀ n, |a n| ≤ B) :
    ScaledJets s (fun n x => a n * f n x) := hf.smul hs a B hB ha

lemma ScaledJets.const_mul {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → ℝ}
    (hf : ScaledJets s f) (a : ℝ) : ScaledJets s (fun n x => a * f n x) :=
  hf.cmul hs (fun _ => a) |a| (abs_nonneg _) (fun _ => le_rfl)

lemma ScaledJets.div_const {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → ℝ}
    (hf : ScaledJets s f) (a : ℝ) : ScaledJets s (fun n x => f n x / a) :=
  (hf.const_mul hs a⁻¹).congr (fun _ _ => by simp [div_eq_mul_inv, mul_comm])

lemma decoder_bounded (b : ℕ) (hb : 2 ≤ b) : BoundedJets (Profiles.decoder b) := by
  refine ⟨Profiles.decoder_smooth b hb, fun r => ?_⟩
  obtain ⟨C, hC, hc⟩ := Profiles.decoder_derivatives_bounded b hb r
  exact ⟨C, hC, fun x => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs] using hc x⟩

lemma selector_bounded (b a : ℕ) (hb : 0 < b) : BoundedJets (Profiles.selector b a) := by
  apply compact_bounded _ (Profiles.selector_smooth b a)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (2 * (a : ℝ) - 1 / 4) / b) (b := (2 * (a : ℝ) + 5 / 4) / b))
    isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  obtain ⟨h₁, h₂⟩ := Profiles.selector_support_bound b a x hx
  exact ⟨(div_le_iff₀ hb').mpr (by nlinarith), (le_div_iff₀ hb').mpr (by nlinarith)⟩

def readScale (M : Machine) (N n : ℕ) : ℝ :=
  (M.base : ℝ) ^ (Scales.s N n + 1 + Scales.K N n)

lemma readScale_ge_one (M : Machine) (N n : ℕ) : 1 ≤ readScale M N n :=
  one_le_pow₀ (by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base))

lemma readScale_nonneg (M : Machine) (N n : ℕ) : 0 ≤ readScale M N n :=
  le_trans zero_le_one (readScale_ge_one M N n)

lemma inverse_power_bound (M : Machine) (k : ℕ) : |((M.base : ℝ) ^ k)⁻¹| ≤ 1 := by
  have hb : (1 : ℝ) ≤ M.base := by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base)
  rw [abs_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hb)

lemma scaled_decoder (M : Machine) (N : ℕ) (k : ℕ → ℕ)
    (hk : ∀ n, k n ≤ Scales.s N n + 1 + Scales.K N n) :
    ScaledJets (readScale M N) (fun n D => Profiles.decoder M.base ((M.base : ℝ) ^ k n * D)) := by
  have hb : (1 : ℝ) ≤ M.base := by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base)
  refine (decoder_bounded M.base (by have := M.base_ge_four; omega)).comp_scaled_linear
    (readScale_nonneg M N) (fun n => (M.base : ℝ) ^ k n • ContinuousLinearMap.id ℝ ℝ)
    1 zero_le_one ?_
  intro n
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hb) _),
    ContinuousLinearMap.norm_id, mul_one, one_mul, readScale] using pow_le_pow_right₀ hb (hk n)

lemma readC_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (LocalRule.readC M N) := by
  exact scaled_decoder M N (Scales.s N) (fun _ => by omega)

lemma readB_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (LocalRule.readB M N) := by
  exact scaled_decoder M N (fun n => Scales.s N n + 1 + Scales.K N n) (fun _ => le_rfl)

lemma readA_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (LocalRule.readA M N) := by
  exact (scaled_decoder M N (fun n => Scales.s N n + 1) (fun _ => by omega)).sub
    ((readB_scaled M N).cmul (readScale_nonneg M N) _ 1 zero_le_one
      (fun n => inverse_power_bound M _))

lemma updateLeft_scaled (M : Machine) (N a l : ℕ) (r : Rule) :
    ScaledJets (readScale M N) (fun n D =>
      LocalRule.updateLeft M.base a l r (LocalRule.readA M N n D) (LocalRule.readB M N n D)) := by
  unfold LocalRule.updateLeft
  split_ifs
  · exact ((readA_scaled M N).const_mul (readScale_nonneg M N) _).sub
      (ScaledJets.constant (readScale_nonneg M N) _)
  · exact readA_scaled M N
  · exact ((ScaledJets.constant (readScale_nonneg M N) _).add (readA_scaled M N)).div_const
      (readScale_nonneg M N) _

lemma updateRight_scaled (M : Machine) (N a l : ℕ) (r : Rule) :
    ScaledJets (readScale M N) (fun n D =>
      LocalRule.updateRight M.base a l r (LocalRule.readA M N n D) (LocalRule.readB M N n D)) := by
  have hR := ((readB_scaled M N).const_mul (readScale_nonneg M N) (M.base : ℝ)).sub
    (ScaledJets.constant (readScale_nonneg M N) (2 * (a : ℝ)))
  unfold LocalRule.updateRight
  dsimp only
  split_ifs
  · exact ((ScaledJets.constant (readScale_nonneg M N) _).add
      (((ScaledJets.constant (readScale_nonneg M N) _).add hR).div_const
        (readScale_nonneg M N) _)).div_const (readScale_nonneg M N) _
  · exact ((ScaledJets.constant (readScale_nonneg M N) _).add hR).div_const
      (readScale_nonneg M N) _
  · exact hR

lemma branchNumerator_scaled (M : Machine) (N a l : ℕ) (r : Rule) :
    ScaledJets (readScale M N) (fun n D => LocalRule.branchNumerator M.base
      (Scales.K N (n + 1)) a l r (LocalRule.readA M N n D) (LocalRule.readB M N n D)) := by
  exact ((ScaledJets.constant (readScale_nonneg M N) _).add (updateLeft_scaled M N a l r)).add
    ((updateRight_scaled M N a l r).cmul (readScale_nonneg M N) _ 1 zero_le_one
      (fun n => inverse_power_bound M _))

lemma branch_scaled (M : Machine) (N q a : ℕ) :
    ScaledJets (readScale M N) (fun n D =>
      LocalRule.branch M N n q a (LocalRule.readA M N n D) (LocalRule.readB M N n D)) := by
  classical
  unfold LocalRule.branch
  dsimp only
  split_ifs
  · exact ScaledJets.sum (readScale_nonneg M N) _ _ (fun l _ =>
      ((readA_scaled M N).comp (readScale_nonneg M N)
        (selector_bounded M.base l (by have := M.base_ge_four; omega))).mul
        (readScale_nonneg M N) (branchNumerator_scaled M N a l _))
  · exact branchNumerator_scaled M N a 0 _

def writeCore (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  (1 / (M.base : ℝ)) *
    ∑ q ∈ Finset.range (M.states + 1), ∑ a ∈ Finset.range M.alphabet,
      Profiles.selector M.base q (LocalRule.readC M N n D) *
        Profiles.selector M.base a (LocalRule.readB M N n D) *
          LocalRule.branch M N n q a (LocalRule.readA M N n D) (LocalRule.readB M N n D)

lemma writeCore_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (writeCore M N) := by
  classical
  apply ScaledJets.const_mul (readScale_nonneg M N)
  apply ScaledJets.sum (readScale_nonneg M N)
  intro q _
  apply ScaledJets.sum (readScale_nonneg M N)
  intro a _
  exact (((readC_scaled M N).comp (readScale_nonneg M N)
    (selector_bounded M.base q (by have := M.base_ge_four; omega))).mul (readScale_nonneg M N)
    ((readB_scaled M N).comp (readScale_nonneg M N)
      (selector_bounded M.base a (by have := M.base_ge_four; omega)))).mul (readScale_nonneg M N)
        (branch_scaled M N q a)

lemma write_factor (M : Machine) (N n : ℕ) (D : ℝ) :
    LocalRule.write M N n D = Scales.ε M.base N (n + 1) * writeCore M N n D := by
  unfold LocalRule.write writeCore
  ring

lemma haltWeight_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (LocalRule.haltWeight M N) := by
  classical
  apply ScaledJets.sum (readScale_nonneg M N)
  intro q _
  split_ifs
  · exact (readC_scaled M N).comp (readScale_nonneg M N)
      (selector_bounded M.base q (by have := M.base_ge_four; omega))
  · exact ScaledJets.constant (readScale_nonneg M N) _

lemma ScaledJets.finite_family {s : ℕ → ℝ} (hs : ∀ n, 1 ≤ s n) {ι : Type*} [Fintype ι]
    (f : ι → E → F) (hf : ∀ i, BoundedJets (f i)) (idx : ℕ → ι) :
    ScaledJets s (fun n => f (idx n)) := by
  classical
  refine ⟨fun n => (hf (idx n)).1, fun r => ?_⟩
  choose C hC hc using fun i => (hf i).2 r
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun n x => ?_⟩
  exact ((hc (idx n) x).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))).trans
    (le_mul_of_one_le_right (Finset.sum_nonneg (fun i _ => hC i)) (one_le_pow₀ (hs n)))

lemma norm_postcomp_linear (f : E → F) (hf : ContDiff ℝ ∞ f) (L : F →L[ℝ] G)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (L ∘ f) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ r f x‖ := by
  rw [L.iteratedFDeriv_comp_left hf.contDiffAt (WithTop.coe_le_coe.mpr le_top)]
  exact L.norm_compContinuousMultilinearMap_le _

lemma norm_directional_iterated (f : E → F) (hf : ContDiff ℝ ∞ f) (v : E)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (fun x => fderiv ℝ f x v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (r + 1) f x‖ := by
  apply (norm_postcomp_linear _ (hf.fderiv_right (by simp))
    (ContinuousLinearMap.apply ℝ F v) r x).trans
  rw [norm_iteratedFDeriv_fderiv]
  gcongr
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun L => by
    simpa only [ContinuousLinearMap.apply_apply, mul_comm] using L.le_opNorm v)

lemma norm_e (i : Fin 3) : ‖e i‖ = 1 := by simp [e]

lemma norm_iterated_curl (i j : Fin 3) (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (r : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ r (Spatial.curl i j f) x‖ ≤ 2 * ‖iteratedFDeriv ℝ (r + 1) f x‖ := by
  have h (i j : Fin 3) :
      ‖iteratedFDeriv ℝ r (fun x => Spatial.d j f x • e i) x‖ ≤
        ‖iteratedFDeriv ℝ (r + 1) f x‖ := by
    apply (norm_postcomp_linear _ (Spatial.d_smooth j f hf)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)) r x).trans
    have hn : ‖(ContinuousLinearMap.id ℝ ℝ).smulRight (e i)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun a => by simp [norm_smul, norm_e])
    calc
      _ ≤ 1 * (1 * ‖iteratedFDeriv ℝ (r + 1) f x‖) := by
        gcongr
        change ‖iteratedFDeriv ℝ r (fun x : Space => fderiv ℝ f x (e j)) x‖ ≤ _
        simpa only [norm_e] using norm_directional_iterated f hf (e j) r x
      _ = _ := by ring
  have hi (i j : Fin 3) : ContDiff ℝ ∞ (fun x => Spatial.d j f x • e i) :=
    (Spatial.d_smooth j f hf).smul contDiff_const
  unfold Spatial.curl
  rw [fun_iteratedFDeriv_sub_apply
    ((hi i j).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((hi j i).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  exact (norm_sub_le _ _).trans (by linarith [h i j, h j i])

lemma cutoff_coordinate_bounded (i : Fin 3) :
    BoundedJets (fun x : Space => Spatial.cutoff x * x i) := by
  apply compact_bounded _ (Spatial.cutoff_smooth.mul (Spatial.coord_smooth i))
  exact Spatial.box_compact.of_isClosed_subset isClosed_closure
    (tsupport_mul_subset_left.trans Spatial.cutoff_support)

lemma scaled_coord_comp (M : Machine) (N : ℕ) {f : ℕ → ℝ → ℝ}
    (hf : ScaledJets (readScale M N) f) (idx : ℕ → Fin 3) :
    ScaledJets (readScale M N) (fun n (x : Space) => f n (x (idx n))) := by
  apply hf.comp_linear (readScale_nonneg M N)
    (fun n => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (idx n)) 1 zero_le_one
  intro n
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, PiLp.proj_apply] using PiLp.norm_apply_le x (idx n)

def fixedPotential (n : ℕ) (x : Space) : ℝ :=
  -(Spatial.cutoff x * x (Construction.receiverIndex n))

def corePotential (M : Machine) (N n : ℕ) (x : Space) : ℝ :=
  (Spatial.cutoff x * x 0) * writeCore M N n (x (Construction.donorIndex n)) -
    (Spatial.cutoff x * x (Construction.receiverIndex n)) *
      (2 * LocalRule.haltWeight M N n (x (Construction.donorIndex n)))

lemma fixedPotential_scaled : ScaledJets (fun _ => 1) fixedPotential := by
  have h := ScaledJets.finite_family (fun _ => le_rfl : ∀ _ : ℕ, (1 : ℝ) ≤ 1)
    (fun i (x : Space) => Spatial.cutoff x * x i) cutoff_coordinate_bounded
    Construction.receiverIndex
  exact (h.const_mul (fun _ => zero_le_one) (-1)).congr (fun _ _ => by simp [fixedPotential])

lemma corePotential_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (corePotential M N) := by
  have h (idx : ℕ → Fin 3) := ScaledJets.finite_family (readScale_ge_one M N)
    (fun i (x : Space) => Spatial.cutoff x * x i) cutoff_coordinate_bounded idx
  exact ((h (fun _ => 0)).mul (readScale_nonneg M N)
    (scaled_coord_comp M N (writeCore_scaled M N) Construction.donorIndex)).sub
      ((h Construction.receiverIndex).mul (readScale_nonneg M N)
        ((scaled_coord_comp M N (haltWeight_scaled M N) Construction.donorIndex).const_mul
          (readScale_nonneg M N) 2))

lemma potential_decomposition (M : Machine) (N n : ℕ) (x : Space) :
    Spatial.cutoff x * Spatial.shearPotential (Construction.donorIndex n)
      (Construction.receiverIndex n) 0 (LocalRule.write M N n) (LocalRule.signal M N n) x =
    (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) * fixedPotential n x +
      Scales.ε M.base N (n + 1) * corePotential M N n x := by
  unfold Spatial.shearPotential LocalRule.signal fixedPotential corePotential
  rw [write_factor]
  ring

lemma potential_bound (M : Machine) (N r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖iteratedFDeriv ℝ r (fun x => Spatial.cutoff x *
      Spatial.shearPotential (Construction.donorIndex n) (Construction.receiverIndex n) 0
        (LocalRule.write M N n) (LocalRule.signal M N n) x) x‖ ≤
        C * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ r) := by
  obtain ⟨A, hA, ha⟩ := fixedPotential_scaled.2 r
  obtain ⟨B, hB, hb⟩ := (corePotential_scaled M N).2 r
  refine ⟨A + B, add_nonneg hA hB, fun n x => ?_⟩
  have hε : 0 ≤ Scales.ε M.base N (n + 1) := Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)
  have hε' : Scales.ε M.base N (n + 1) ≤ Scales.ε M.base N n :=
    (Scales.ε_strictAnti M.base N (by have := M.base_ge_four; omega)).antitone (by omega)
  have h₁ := fixedPotential_scaled.1 n
  have h₂ := (corePotential_scaled M N).1 n
  simp_rw [potential_decomposition]
  change ‖iteratedFDeriv ℝ r (fun x =>
    (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • fixedPotential n x +
      Scales.ε M.base N (n + 1) • corePotential M N n x) x‖ ≤ _
  have hs₁ : ContDiff ℝ ∞ (fun x =>
      (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • fixedPotential n x) := h₁.const_smul _
  have hs₂ : ContDiff ℝ ∞ (fun x =>
      Scales.ε M.base N (n + 1) • corePotential M N n x) := h₂.const_smul _
  rw [fun_iteratedFDeriv_add_apply
    (hs₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hs₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  apply (norm_add_le _ _).trans
  rw [iteratedFDeriv_const_smul_apply' (h₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    iteratedFDeriv_const_smul_apply' (h₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hε'), abs_of_nonneg hε]
  have haa : ‖iteratedFDeriv ℝ r (fixedPotential n) x‖ ≤ A := by simpa using ha n x
  have hbb := hb n x
  have hscale := pow_nonneg (readScale_nonneg M N n) r
  calc
    _ ≤ Scales.ε M.base N n * A +
      Scales.ε M.base N (n + 1) * (B * readScale M N n ^ r) := by
      exact add_le_add
        (mul_le_mul (by linarith) haa (norm_nonneg _) (by linarith))
        (mul_le_mul_of_nonneg_left hbb hε)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ Scales.ε M.base N n by linarith) hB,
      mul_nonneg hA (mul_nonneg hε hscale)]

theorem slot_estimate (M : Machine) (N r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤
      C * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1)) := by
  obtain ⟨C, hC, hc⟩ := potential_bound M N (r + 1)
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, fun n x => ?_⟩
  have h := norm_iterated_curl (Construction.receiverIndex n) 0 _
    (Spatial.cutoff_smooth.mul (Spatial.shearPotential_smooth (Construction.donorIndex n)
      (Construction.receiverIndex n) 0 _ _
      (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n))) r x
  exact h.trans (by nlinarith [hc n x])

lemma uniform_read_cost (M : Machine) (N r : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
    Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1) ≤ D * Scales.ε M.base N n := by
  classical
  let q (n : ℕ) := Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1) / Scales.ε M.base N n
  have hε (n : ℕ) : 0 < Scales.ε M.base N n :=
    Scales.ε_pos _ _ _ (by have := M.base_ge_four; omega)
  have hq (n : ℕ) : 0 ≤ q n := div_nonneg
    (mul_nonneg (hε _).le (pow_nonneg (readScale_nonneg M N n) _)) (hε _).le
  let D := 1 + ∑ n ∈ Finset.range r, q n
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => hq n))
  refine ⟨D, zero_le_one.trans hD, fun n => ?_⟩
  by_cases hn : n < r
  · apply (div_le_iff₀ (hε n)).mp
    exact (Finset.single_le_sum (fun n _ => hq n) (Finset.mem_range.mpr hn)).trans
      (by dsimp [D]; linarith)
  · have h := Scales.derivative_cost_bound M.base N r n (by have := M.base_ge_four; omega)
      (by omega)
    have he : readScale M N n ^ (r + 1) =
        (M.base : ℝ) ^ ((r + 1) * (Scales.s N n + 1 + Scales.K N n)) := by
      rw [readScale, ← pow_mul, Nat.mul_comm]
    rw [he]
    exact h.trans (le_mul_of_one_le_left (hε n).le hD)

theorem slot_decay (M : Machine) (N r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤ C * Scales.ε M.base N n := by
  obtain ⟨C, hC, hc⟩ := slot_estimate M N r
  obtain ⟨D, hD, hd⟩ := uniform_read_cost M N r
  refine ⟨C * (1 + D), by positivity, fun n x => (hc n x).trans ?_⟩
  have := mul_le_mul_of_nonneg_left (hd n) hC
  nlinarith

def amplitude (M : Machine) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Scales.ε M.base N n

lemma amplitude_nonneg (M : Machine) (N n : ℕ) : 0 ≤ amplitude M N n := by
  cases n with
  | zero => exact zero_le_one
  | succ n => exact Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)

lemma weighted_amplitude_summable (M : Machine) (N J : ℕ) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ J * amplitude M N n) := by
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (amplitude_nonneg M N _)) _
    ((Scales.summable_weighted_ε M.base N J (by have := M.base_ge_four; omega)).mul_left ((2 : ℝ) ^ J))
  intro n
  simp only [amplitude, Nat.cast_add, Nat.cast_one]
  calc
    (1 + ((n : ℝ) + 1)) ^ J * Scales.ε M.base N n ≤
        (2 * (1 + (n : ℝ))) ^ J * Scales.ε M.base N n := by
      apply mul_le_mul_of_nonneg_right _ (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega))
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = _ := by rw [mul_pow]; ring

lemma piece_decay (M : Machine) (w : List ℕ) (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖iteratedFDeriv ℝ r (Construction.piece M w n) x‖ ≤ C * amplitude M w.length n := by
  have hload := compact_bounded (Construction.loading M w) (Construction.loading_smooth M w)
    (Spatial.box_compact.of_isClosed_subset isClosed_closure (Construction.piece_support M w 0))
  obtain ⟨A, hA, ha⟩ := hload.2 r
  obtain ⟨B, hB, hb⟩ := slot_decay M w.length r
  refine ⟨max A B, hA.trans (le_max_left _ _), fun n x => ?_⟩
  cases n with
  | zero =>
    change ‖iteratedFDeriv ℝ r (Construction.loading M w) x‖ ≤ max A B * 1
    simpa only [mul_one] using (ha x).trans (le_max_left A B)
  | succ n => exact (hb n x).trans (mul_le_mul_of_nonneg_right (le_max_right A B)
      (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)))

lemma pulse_bounded : BoundedJets Profiles.pulse := by
  apply compact_bounded _ Profiles.pulse_smooth
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ℝ)) (b := 1)) isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro t ht
  exact ⟨le_of_not_gt (fun h => ht (Profiles.pulse_zero_left t h.le)),
    le_of_not_gt (fun h => ht (Profiles.pulse_zero_right t h.le))⟩

def pulsePiece (M : Machine) (w : List ℕ) (n : ℕ) (z : ℝ × Space) : Space :=
  Profiles.pulse (z.1 - n) • Construction.piece M w n z.2

lemma pulsePiece_smooth (M : Machine) (w : List ℕ) (n : ℕ) :
    ContDiff ℝ ∞ (pulsePiece M w n) :=
  (Profiles.pulse_smooth.comp (contDiff_fst.sub contDiff_const)).fun_smul
    ((Construction.piece_smooth M w n).comp contDiff_snd)

lemma pulsePiece_decay (M : Machine) (w : List ℕ) (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n z,
    ‖iteratedFDeriv ℝ r (pulsePiece M w n) z‖ ≤ C * amplitude M w.length n := by
  classical
  choose A hA ha using pulse_bounded.2
  choose B hB hb using piece_decay M w
  let C := ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * B (r - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _)),
    fun n z => ?_⟩
  have hp (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Profiles.pulse (z.1 - n)) z‖ ≤ A i := by
    apply (norm_comp_linear (fun t => Profiles.pulse (t - n))
      (Profiles.pulse_smooth.comp (contDiff_id.sub contDiff_const)) (ContinuousLinearMap.fst ℝ ℝ Space)
      i z).trans
    rw [iteratedFDeriv_comp_sub]
    have h₁ := ha i (z.1 - n)
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _) (hA i)
  have hw (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Construction.piece M w n z.2) z‖ ≤
        B i * amplitude M w.length n := by
    apply (norm_comp_linear (Construction.piece M w n) (Construction.piece_smooth M w n)
      (ContinuousLinearMap.snd ℝ ℝ Space) i z).trans
    have h₁ := hb i n z.2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (hB i) (amplitude_nonneg M w.length n))
  apply (norm_iteratedFDeriv_smul_le
    (Profiles.pulse_smooth.comp (contDiff_fst.sub contDiff_const))
    ((Construction.piece_smooth M w n).comp contDiff_snd) z (WithTop.coe_le_coe.mpr le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * (B (r - i) * amplitude M w.length n) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul _ (hw (r - i)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
      exact mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg _)
    _ = C * amplitude M w.length n := by simp only [C, Finset.sum_mul, mul_assoc]

def RapidJets (f : ℝ × Space → F) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ J r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z, 0 ≤ z.1 → (1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ r f z‖ ≤ C

lemma box_norm (x : Space) (hx : x ∈ Spatial.box) : ‖x‖ ≤ 9 := by
  have hi (i : Fin 3) : ‖x.ofLp i‖ ^ 2 ≤ 9 := by
    have := hx i
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (x i)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [← PiLp.norm_sq_eq_of_L2] at hsum
  norm_num at hsum
  nlinarith [norm_nonneg x]

lemma pulsePiece_support (M : Machine) (w : List ℕ) (n : ℕ) :
    tsupport (pulsePiece M w n) ⊆ Set.Icc (n : ℝ) (n + 1) ×ˢ Spatial.box := by
  apply closure_minimal _ (isClosed_Icc.prod Spatial.isClosed_box)
  intro z hz
  have h₁ : Profiles.pulse (z.1 - n) ≠ 0 := fun h => hz (by simp [pulsePiece, h])
  have h₂ : Construction.piece M w n z.2 ≠ 0 := fun h => hz (by simp [pulsePiece, h])
  refine ⟨⟨?_, ?_⟩, Construction.piece_support M w n (subset_closure h₂)⟩
  · exact le_of_not_gt (fun h => h₁ (Profiles.pulse_zero_left _ (by linarith)))
  · exact le_of_not_gt (fun h => h₁ (Profiles.pulse_zero_right _ (by linarith)))

lemma pulsePiece_weighted (M : Machine) (w : List ℕ) (J r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, 0 ≤ z.1 →
      (1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ r (pulsePiece M w n) z‖ ≤
        C * (1 + (n : ℝ)) ^ J * amplitude M w.length n := by
  obtain ⟨C, hC, hc⟩ := pulsePiece_decay M w r
  refine ⟨11 ^ J * C, by positivity, fun n z ht => ?_⟩
  by_cases hz : z ∈ tsupport (iteratedFDeriv ℝ r (pulsePiece M w n))
  · have hsupport := pulsePiece_support M w n (tsupport_iteratedFDeriv_subset r hz)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hw : (1 + z.1 + ‖z.2‖) ^ J ≤ (11 * (1 + (n : ℝ))) ^ J :=
      pow_le_pow_left₀ (by positivity) (by linarith [hsupport.1.2, box_norm z.2 hsupport.2]) _
    calc
      _ ≤ (11 * (1 + (n : ℝ))) ^ J * (C * amplitude M w.length n) :=
        mul_le_mul hw (hc n z) (norm_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC) (by positivity))
      (amplitude_nonneg M w.length n)

theorem velocity_rapidJets (M : Machine) (w : List ℕ) :
    RapidJets (Function.uncurry (Construction.velocity M w)) := by
  classical
  refine ⟨Construction.velocity_smooth M w, fun J r => ?_⟩
  obtain ⟨C, hC, hc⟩ := pulsePiece_weighted M w J r
  let a : ℕ → ℝ := fun n => C * ((1 + (n : ℝ)) ^ J * amplitude M w.length n)
  have has : Summable a := (weighted_amplitude_summable M w.length J).mul_left C
  have ha : ∀ n, 0 ≤ a n := fun n => mul_nonneg hC
    (mul_nonneg (by positivity) (amplitude_nonneg M w.length n))
  refine ⟨∑' n, a n, tsum_nonneg ha, fun z ht => ?_⟩
  obtain ⟨N, hN⟩ := TimeGlue.locally_eq_sum Profiles.pulse Profiles.pulse_zero_left
    (Construction.piece M w) z
  change Function.uncurry (Construction.velocity M w) =ᶠ[𝓝 z]
    (fun z => ∑ n ∈ Finset.range N, pulsePiece M w n z) at hN
  rw [(hN.iteratedFDeriv ℝ r).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun n _ => (pulsePiece_smooth M w n).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  calc
    _ ≤ (1 + z.1 + ‖z.2‖) ^ J * ∑ n ∈ Finset.range N,
        ‖iteratedFDeriv ℝ r (pulsePiece M w n) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ∑ n ∈ Finset.range N, a n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      simpa only [a, mul_assoc] using hc n z ht
    _ ≤ _ := has.sum_le_tsum _ (fun n _ => ha n)

lemma RapidJets.congr {f g : ℝ × Space → F} (hf : RapidJets f) (he : ∀ z, f z = g z) :
    RapidJets g := by rwa [← funext he]

lemma RapidJets.add {f g : ℝ × Space → F} (hf : RapidJets f) (hg : RapidJets g) :
    RapidJets (fun z => f z + g z) := by
  refine ⟨hf.1.add hg.1, fun J r => ?_⟩
  obtain ⟨A, hA, ha⟩ := hf.2 J r
  obtain ⟨B, hB, hb⟩ := hg.2 J r
  refine ⟨A + B, add_nonneg hA hB, fun z hz => ?_⟩
  rw [fun_iteratedFDeriv_add_apply (hf.1.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hg.1.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  calc
    _ ≤ (1 + z.1 + ‖z.2‖) ^ J *
        (‖iteratedFDeriv ℝ r f z‖ + ‖iteratedFDeriv ℝ r g z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ A + B := by rw [mul_add]; exact add_le_add (ha z hz) (hb z hz)

lemma RapidJets.linear {f : ℝ × Space → F} (hf : RapidJets f) (L : F →L[ℝ] G) :
    RapidJets (L ∘ f) := by
  refine ⟨L.contDiff.comp hf.1, fun J r => ?_⟩
  obtain ⟨A, hA, ha⟩ := hf.2 J r
  refine ⟨‖L‖ * A, by positivity, fun z hz => ?_⟩
  calc
    _ ≤ (1 + z.1 + ‖z.2‖) ^ J * (‖L‖ * ‖iteratedFDeriv ℝ r f z‖) :=
      mul_le_mul_of_nonneg_left (norm_postcomp_linear f hf.1 L r z) (by positivity)
    _ = ‖L‖ * ((1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ r f z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ha z hz) (norm_nonneg _)

lemma RapidJets.const_smul {f : ℝ × Space → F} (hf : RapidJets f) (a : ℝ) :
    RapidJets (fun z => a • f z) := hf.linear (a • ContinuousLinearMap.id ℝ F)

lemma RapidJets.sub {f g : ℝ × Space → F} (hf : RapidJets f) (hg : RapidJets g) :
    RapidJets (fun z => f z - g z) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hf.add (hg.const_smul (-1))

lemma RapidJets.zero : RapidJets (fun _ : ℝ × Space => (0 : F)) := by
  refine ⟨contDiff_const, fun J r => ⟨0, le_rfl, fun z _ => ?_⟩⟩
  simp

lemma RapidJets.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × Space → F)
    (hf : ∀ i ∈ s, RapidJets (f i)) : RapidJets (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (RapidJets.zero : RapidJets (fun _ => (0 : F)))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma RapidJets.directional {f : ℝ × Space → F} (hf : RapidJets f) (v : ℝ × Space) :
    RapidJets (fun z => fderiv ℝ f z v) := by
  refine ⟨(hf.1.fderiv_right (by simp)).clm_apply contDiff_const, fun J r => ?_⟩
  obtain ⟨A, hA, ha⟩ := hf.2 J (r + 1)
  refine ⟨‖v‖ * A, by positivity, fun z hz => ?_⟩
  calc
    _ ≤ (1 + z.1 + ‖z.2‖) ^ J * (‖v‖ * ‖iteratedFDeriv ℝ (r + 1) f z‖) :=
      mul_le_mul_of_nonneg_left (norm_directional_iterated f hf.1 v r z) (by positivity)
    _ = ‖v‖ * ((1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ (r + 1) f z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ha z hz) (norm_nonneg _)

lemma dx_eq_full_directional (F : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry F))
    (i : Fin 3) (z : ℝ × Space) :
    dx i F z.1 z.2 = fderiv ℝ (Function.uncurry F) z (0, e i) := by
  have h₁ : HasFDerivAt (fun x : Space => (z.1, x))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hh := (hf.differentiable (by simp) (z.1,z.2)).hasFDerivAt.comp z.2 h₁
  have he := hh.fderiv
  change fderiv ℝ (F z.1) z.2 = _ at he
  rw [dx, he]
  simp

lemma fullDt_eq_full_directional (F : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry F))
    (z : ℝ × Space) :
    Analytic.fullDt F z.1 z.2 = fderiv ℝ (Function.uncurry F) z (1, 0) := by
  have h₁ : HasFDerivAt (fun t : ℝ => (t, z.2))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Space)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hh := (hf.differentiable (by simp) (z.1,z.2)).hasFDerivAt.comp z.1 h₁
  have he := hh.fderiv
  change fderiv ℝ (fun t => F t z.2) z.1 = _ at he
  rw [Analytic.fullDt, he]
  simp

lemma RapidJets.dx {f : Field F} (hf : RapidJets (Function.uncurry f)) (i : Fin 3) :
    RapidJets (Function.uncurry (dx i f)) :=
  (hf.directional (0, e i)).congr (fun z => (dx_eq_full_directional f hf.1 i z).symm)

lemma RapidJets.fullDt {f : Field F} (hf : RapidJets (Function.uncurry f)) :
    RapidJets (Function.uncurry (Analytic.fullDt f)) :=
  (hf.directional (1, 0)).congr (fun z => (fullDt_eq_full_directional f hf.1 z).symm)

lemma RapidJets.smul {f : ℝ × Space → ℝ} {g : ℝ × Space → F}
    (hf : RapidJets f) (hg : RapidJets g) : RapidJets (fun z => f z • g z) := by
  classical
  refine ⟨hf.1.fun_smul hg.1, fun J r => ?_⟩
  choose A hA ha using hf.2 J
  choose B hB hb using hg.2 0
  let C := ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * B (r - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _)),
    fun z hz => ?_⟩
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hf.1 hg.1 z
    (WithTop.coe_le_coe.mpr le_top)) (pow_nonneg (by positivity) J)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = (r.choose i : ℝ) * ((1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ i f z‖) *
        ‖iteratedFDeriv ℝ (r - i) g z‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (ha i z hz) (Nat.cast_nonneg _))
      (by simpa using hb (r - i) z hz) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hA i))

lemma advection_eq_sum (u : Velocity) (t : ℝ) (x : Space) :
    advection u t x = ∑ i : Fin 3, (u t x i) • dx i u t x := by
  have he (v : Space) : v = ∑ i : Fin 3, v i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply]
  conv_lhs => unfold advection; rw [he (u t x)]
  simp only [map_sum, map_smul, dx]

lemma RapidJets.advection {f : Velocity} (hf : RapidJets (Function.uncurry f)) :
    RapidJets (Function.uncurry (advection f)) := by
  have h : ∀ i : Fin 3, RapidJets (fun z : ℝ × Space => f z.1 z.2 i • AlternatingNS.dx i f z.1 z.2) :=
    fun i => (hf.linear (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i)).smul (hf.dx i)
  exact (RapidJets.sum Finset.univ _ (fun i _ => h i)).congr
    (fun z => (advection_eq_sum f z.1 z.2).symm)

lemma RapidJets.laplacian {f : Velocity} (hf : RapidJets (Function.uncurry f)) :
    RapidJets (Function.uncurry (laplacian f)) :=
  RapidJets.sum Finset.univ _ (fun i _ => (hf.dx i).dx i)

lemma RapidJets.fullResidual {f : Velocity} (hf : RapidJets (Function.uncurry f)) (ν : ℝ) :
    RapidJets (fun z : ℝ × Space => Analytic.fullDt f z.1 z.2 + AlternatingNS.advection f z.1 z.2 -
      ν • AlternatingNS.laplacian f z.1 z.2) :=
  (hf.fullDt.add hf.advection).sub (hf.laplacian.const_smul ν)

def HalfEq (f g : Field F) : Prop := ∀ t, 0 ≤ t → ∀ x, f t x = g t x

lemma HalfEq.dx {f g : Field F} (h : HalfEq f g) (i : Fin 3) : HalfEq (dx i f) (dx i g) := by
  intro t ht x
  have he : f t = g t := funext (h t ht)
  simp only [AlternatingNS.dx, he]

lemma HalfEq.dt {f g : Field F} (h : HalfEq f g) : HalfEq (dt f) (dt g) := by
  intro t ht x
  exact congrArg (fun L : ℝ →L[ℝ] F => L 1)
    (fderivWithin_congr (fun u hu => h u hu x) (h t ht x))

lemma HalfEq.spatial {f g : Field F} (h : HalfEq f g) (α : MultiIndex) :
    HalfEq (spatial α f) (spatial α g) := by
  have hi (i : Fin 3) (n : ℕ) {u v : Field F} (hv : HalfEq u v) :
      HalfEq ((AlternatingNS.dx i)^[n] u) ((AlternatingNS.dx i)^[n] v) := by
    induction n with
    | zero => exact hv
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using ih.dx i
  exact hi 0 (α 0) (hi 1 (α 1) (hi 2 (α 2) h))

lemma HalfEq.mixed {f g : Field F} (h : HalfEq f g) (l : ℕ) (α : MultiIndex) :
    HalfEq (mixed l α f) (mixed l α g) := by
  induction l with
  | zero => exact h.spatial α
  | succ l ih => simpa only [AlternatingNS.mixed, Function.iterate_succ_apply'] using ih.dt

lemma RapidJets.spatial {f : Field F} (hf : RapidJets (Function.uncurry f)) (α : MultiIndex) :
    RapidJets (Function.uncurry (spatial α f)) := by
  have hi (i : Fin 3) (n : ℕ) {u : Field F} (hu : RapidJets (Function.uncurry u)) :
      RapidJets (Function.uncurry ((AlternatingNS.dx i)^[n] u)) := by
    induction n with
    | zero => exact hu
    | succ n ih => simpa only [Function.iterate_succ_apply'] using ih.dx i
  exact hi 0 (α 0) (hi 1 (α 1) (hi 2 (α 2) hf))

lemma fullDt_iterate {f : Field F} (hf : RapidJets (Function.uncurry f)) (l : ℕ) :
    RapidJets (Function.uncurry (Analytic.fullDt^[l] f)) ∧
      HalfEq (dt^[l] f) (Analytic.fullDt^[l] f) := by
  induction l with
  | zero => exact ⟨hf, fun _ _ _ => rfl⟩
  | succ l ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨ih.1.fullDt, fun t ht x => ?_⟩
    exact (ih.2.dt t ht x).trans (Analytic.dt_eq_full _ ih.1.1 t ht x)

lemma RapidJets.rapid {f : Velocity} (hf : RapidJets (Function.uncurry f)) : Rapid f := by
  intro J l α
  obtain ⟨hG, he⟩ := fullDt_iterate (hf.spatial α) l
  obtain ⟨C, hC, hc⟩ := hG.2 J 0
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [show mixed l α f t x = (Analytic.fullDt^[l] (AlternatingNS.spatial α f)) t x from he t ht x]
  simpa only [norm_iteratedFDeriv_zero, Function.uncurry] using hc (t, x) ht

lemma Rapid.congr_half {f g : Velocity} (hf : Rapid f) (h : HalfEq f g) : Rapid g := by
  intro J l α
  obtain ⟨C, hC, hc⟩ := hf J l α
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [← h.mixed l α t ht x]
  exact hc t ht x

theorem velocity_rapid (M : Machine) (w : List ℕ) : Rapid (Construction.velocity M w) :=
  (velocity_rapidJets M w).rapid

theorem force_rapid (ν : ℝ) (M : Machine) (w : List ℕ) : Rapid (Construction.force ν M w) := by
  have hf := velocity_rapidJets M w
  have hR : Rapid (fun t x => Analytic.fullDt (Construction.velocity M w) t x +
      advection (Construction.velocity M w) t x - ν • laplacian (Construction.velocity M w) t x) :=
    RapidJets.rapid (f := fun t x => Analytic.fullDt (Construction.velocity M w) t x +
      advection (Construction.velocity M w) t x - ν • laplacian (Construction.velocity M w) t x)
      (hf.fullResidual ν)
  apply Rapid.congr_half hR
  intro t ht x
  simp only [Construction.force, residual]
  rw [Analytic.dt_eq_full _ hf.1 t ht x]

end
end Bounds
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Effective.lean =====
namespace OAI

section EffectiveDevelopment

open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory

namespace AlternatingNS
namespace Effective

lemma nat_pow : Primrec₂ (fun b n : ℕ => b ^ n) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

lemma capacity : Primrec₂ Scales.K :=
  Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 2)

lemma exponent : Primrec₂ Scales.s :=
  Primrec.nat_mul.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))
    (nat_pow.comp (Primrec.const 2) (nat_pow.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 3)) (Primrec.const 2)))

lemma states : Primrec Machine.states :=
  Primrec.nat_add.comp Primrec.fst (Primrec.const 1)

lemma alphabet : Primrec Machine.alphabet :=
  Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)

lemma initialState : Primrec Machine.initialState :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

lemma haltingStates : Primrec Machine.haltingStates :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

lemma table : Primrec Machine.table :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

lemma base : Primrec Machine.base :=
  Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.const 1)
      (Primrec.nat_max.comp (Primrec.nat_add.comp states (Primrec.const 1)) alphabet))

lemma instruction : Primrec (fun z : Machine × ℕ × ℕ => z.1.instruction z.2.1 z.2.2) := by
  have h := Primrec.list_getElem?.comp (table.comp Primrec.fst)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (alphabet.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.option_getD.comp h (Primrec.const none)).of_eq (by
    intro z; dsimp only [Machine.instruction];
    cases (z.1.table[z.2.1 * z.1.alphabet + z.2.2]?) <;> rfl)

lemma member {α : Type*} [Primcodable α] : PrimrecRel (fun l : List α => fun a => a ∈ l) :=
  (Primrec.eq.exists_mem_list).of_eq (by simp)

lemma command : Primrec (fun z : Machine × ℕ × ℕ => z.1.command z.2.1 z.2.2) := by
  apply Primrec.ite
  · exact (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (states.comp Primrec.fst)).or
      (member.comp (haltingStates.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  · exact (Primrec.fst.comp Primrec.snd).pair
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (1 : Fin 3)))
  · exact Primrec.option_getD.comp instruction ((states.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (1 : Fin 3))))

lemma program_of_computable {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Computable f) : ∃ c : Program, ∀ a, Returns c a (f a) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨c, fun a => ?_⟩
  simp [Returns, hc, Encodable.encodek]

lemma compiler_of_computable {A B C : Type*} [Primcodable A] [Primcodable B] [Primcodable C]
    (f : A → B → C) (hf : Computable₂ f) :
    ∃ compile : A → Program, Computable compile ∧
      ∀ a b, Returns (compile a) b (f a b) := by
  obtain ⟨c, hc⟩ := program_of_computable (fun z : A × B => f z.1 z.2) hf
  refine ⟨fun a => c.curry (Encodable.encode a),
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const c) Primrec.encode).to_comp, ?_⟩
  intro a b
  simpa only [Returns, Nat.Partrec.Code.eval_curry, Encodable.encode_prod_val] using hc (a, b)

theorem command_program : ∃ compile : Machine → Program, Computable compile ∧
    ∀ M q a, Returns (compile M) (q, a) (M.command q a) := by
  obtain ⟨c, hC, h⟩ := compiler_of_computable
    (fun M : Machine => fun z : ℕ × ℕ => M.command z.1 z.2) command.to_comp
  exact ⟨c, hC, fun M q a => h M (q, a)⟩

end Effective
end AlternatingNS

end EffectiveDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Quantitative.lean =====
namespace OAI

section QuantitativeDevelopment

open scoped BigOperators ContDiff

namespace AlternatingNS
namespace Quantitative

noncomputable def rhoTerm (m : ℕ) (x : ℝ) : ℝ := x⁻¹ ^ m * expNegInvGlue x

lemma rhoTerm_smooth (m : ℕ) : ContDiff ℝ ∞ (rhoTerm m) := by
  change ContDiff ℝ ∞ (fun x => x⁻¹ ^ m * expNegInvGlue x)
  simpa only [Polynomial.eval_X_pow] using
    (expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (Polynomial.X ^ m : Polynomial ℝ))

lemma rhoTerm_deriv (m : ℕ) :
    deriv (rhoTerm m) = fun x => rhoTerm (m + 2) x - m * rhoTerm (m + 1) x := by
  funext x
  have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    (Polynomial.X ^ m : Polynomial ℝ) x).deriv
  simp only [Polynomial.eval_X_pow] at h
  change deriv (rhoTerm m) x = _ at h
  rw [h]
  simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X_pow, rhoTerm]
  cases m with
  | zero => norm_num
  | succ m => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]; ring

lemma exp_monomial_bound (y : ℝ) (hy : 0 ≤ y) (m : ℕ) :
    y ^ m * Real.exp (-y) ≤ m.factorial := by
  have h := Real.pow_div_factorial_le_exp y hy m
  have hp : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h' := (div_le_iff₀ hp).mp h
  calc
    _ ≤ (Real.exp y * m.factorial) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
    _ = _ := by rw [mul_right_comm, ← Real.exp_add]; simp

lemma rhoTerm_bound (m : ℕ) (x : ℝ) : |rhoTerm m x| ≤ m.factorial := by
  by_cases hx : x ≤ 0
  · simp [rhoTerm, expNegInvGlue.zero_of_nonpos hx]
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [rhoTerm, expNegInvGlue, ite_eq_right hx,
      abs_of_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr hx').le _) (Real.exp_pos _).le)]
    exact exp_monomial_bound x⁻¹ (inv_pos.mpr hx').le m

lemma rhoTerm_derivative_bound (r m : ℕ) (x : ℝ) :
    |iteratedDeriv r (rhoTerm m) x| ≤
      ((m + 2 * r).factorial : ℝ) * (m + 2 * r + 1 : ℕ) ^ r := by
  induction r generalizing m with
  | zero => simpa using rhoTerm_bound m x
  | succ r ih =>
    rw [iteratedDeriv_succ', rhoTerm_deriv]
    have hs (j : ℕ) : ContDiffAt ℝ (r : ℕ∞ω) (rhoTerm j) x :=
      ((rhoTerm_smooth j).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    change |iteratedDeriv r (rhoTerm (m + 2) - fun x => (m : ℝ) * rhoTerm (m + 1) x) x| ≤ _
    rw [iteratedDeriv_sub (hs _) (contDiffAt_const.mul (hs _)), iteratedDeriv_const_mul _ (hs _)]
    have ht : m + 2 + 2 * r = m + 2 * (r + 1) := by omega
    have hf : ((m + 1 + 2 * r).factorial : ℝ) ≤ (m + 2 * (r + 1)).factorial := by
      exact_mod_cast Nat.factorial_le (by omega : m + 1 + 2 * r ≤ m + 2 * (r + 1))
    have hp : ((m + 1 + 2 * r + 1 : ℕ) : ℝ) ^ r ≤ (m + 2 * (r + 1) + 1 : ℕ) ^ r := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (by omega : m + 1 + 2 * r + 1 ≤ m + 2 * (r + 1) + 1)
    have hsmall := (ih (m + 1)).trans (mul_le_mul hf hp (by positivity) (by positivity))
    have hbig := ih (m + 2)
    rw [ht] at hbig
    calc
      _ ≤ |iteratedDeriv r (rhoTerm (m + 2)) x| + (m : ℝ) * |iteratedDeriv r (rhoTerm (m + 1)) x| := by
        simpa only [Real.norm_eq_abs, abs_mul, Nat.abs_cast] using
          norm_sub_le (iteratedDeriv r (rhoTerm (m + 2)) x) ((m : ℝ) * iteratedDeriv r (rhoTerm (m + 1)) x)
      _ ≤ ((m + 2 * (r + 1)).factorial : ℝ) * (m + 2 * (r + 1) + 1 : ℕ) ^ r +
          m * (((m + 2 * (r + 1)).factorial : ℝ) * (m + 2 * (r + 1) + 1 : ℕ) ^ r) :=
        add_le_add hbig (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _))
      _ ≤ _ := by
        rw [pow_succ]
        have hm : (m : ℝ) + 1 ≤ (m + 2 * (r + 1) + 1 : ℕ) := by
          push_cast; nlinarith
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ (m + 2 * (r + 1)).factorial by positivity)
          (show (0 : ℝ) ≤ (m + 2 * (r + 1) + 1 : ℕ) ^ r by positivity)]

lemma rho_derivative_bound (r : ℕ) (x : ℝ) :
    |iteratedDeriv r expNegInvGlue x| ≤ ((2 * r).factorial : ℝ) * (2 * r + 1 : ℕ) ^ r := by
  have he : rhoTerm 0 = expNegInvGlue := by funext x; simp [rhoTerm]
  simpa only [he, zero_add] using rhoTerm_derivative_bound r 0 x

def rhoBound (r : ℕ) : ℕ := (2 * r).factorial * (2 * r + 1) ^ r

lemma rho_jet_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r expNegInvGlue x‖ ≤ rhoBound r := by
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    rhoBound, Nat.cast_mul, Nat.cast_pow] using rho_derivative_bound r x

lemma transition_denom_lower (x : ℝ) :
    (1 / 9 : ℝ) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have he : (1 / 9 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg]
    apply (le_inv_comm₀ (by norm_num) (Real.exp_pos _)).mpr
    have h : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by
      simp
    rw [h]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hhalf : (1 / 9 : ℝ) ≤ expNegInvGlue (1 / 2) := by
    norm_num [expNegInvGlue] at *
    exact he
  by_cases hx : (1 / 2 : ℝ) ≤ x
  · exact le_trans (hhalf.trans (expNegInvGlue.monotone hx))
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _))
  · exact le_trans (hhalf.trans (expNegInvGlue.monotone (by linarith : 1 / 2 ≤ 1 - x)))
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _))

lemma inverse_jet_bound (q r : ℕ) {x : ℝ} (hx : 0 < x) (hq : x⁻¹ ≤ q) :
    ‖iteratedFDeriv ℝ r (fun x : ℝ => x⁻¹) x‖ ≤ (r.factorial * q ^ (r + 1) : ℕ) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hexp : (-1 - (r : ℤ)) = -((r + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, ← inv_pow, norm_mul, norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
    Nat.abs_cast, Nat.cast_mul, Nat.cast_pow,
    abs_of_nonneg (pow_nonneg (inv_pos.mpr hx).le _)]
  gcongr

def reciprocalBound (q : ℕ) (B : ℕ → ℕ) (r : ℕ) : ℕ :=
  r.factorial * (r.factorial * q ^ (r + 1)) *
    (1 + ∑ i ∈ Finset.range (r + 1), B i) ^ r

lemma reciprocal_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (B : ℕ → ℕ)
    (hB : ∀ r x, ‖iteratedFDeriv ℝ r f x‖ ≤ B r)
    (q : ℕ) (hq : 1 ≤ q) (hpos : ∀ x, 0 < f x) (hrecip : ∀ x, (f x)⁻¹ ≤ q)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (fun x => (f x)⁻¹) x‖ ≤ reciprocalBound q B r := by
  classical
  let D : ℝ := 1 + ∑ i ∈ Finset.range (r + 1), (B i : ℝ)
  let C : ℝ := r.factorial * (q : ℝ) ^ (r + 1)
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
  have hd (i : ℕ) (hi : i ≤ r) : (B i : ℝ) ≤ D := by
    have h := Finset.single_le_sum (s := Finset.range (r + 1))
      (f := fun i => (B i : ℝ)) (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (by omega : i < r + 1))
    dsimp [D]; linarith
  have hu : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hinv : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Set.Ioi 0) :=
    (contDiffOn_inv ℝ).mono (by intro y hy; simpa using ne_of_gt hy)
  have h := norm_iteratedFDeriv_comp_le' (g := fun y : ℝ => y⁻¹) (f := f)
    (t := Set.Ioi 0) (fun y hy => by rcases hy with ⟨z, rfl⟩; exact hpos z)
    hu hinv hf (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) x (C := C) (D := D) ?_ ?_
  · simpa only [reciprocalBound, C, D, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.cast_sum, Function.comp_def] using h
  · intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hu (contDiffAt_inv ℝ (hpos x).ne') (hpos x)]
    apply (inverse_jet_bound q i (hpos x) (hrecip x)).trans
    dsimp [C]
    push_cast
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hi
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (by omega)
    · positivity
    · positivity
  · intro i hi hir
    exact (hB i x).trans ((hd i hir).trans (le_self_pow₀ hD (by omega)))

noncomputable def transitionDenom (x : ℝ) : ℝ := expNegInvGlue x + expNegInvGlue (1 - x)

lemma transitionDenom_smooth : ContDiff ℝ ∞ transitionDenom :=
  expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

lemma transitionDenom_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r transitionDenom x‖ ≤ (2 * rhoBound r : ℕ) := by
  have hs : ContDiff ℝ ∞ (fun x => expNegInvGlue (1 - x)) :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  unfold transitionDenom
  rw [fun_iteratedFDeriv_add_apply (expNegInvGlue.contDiff (n := ⊤) |>.of_le
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) |>.contDiffAt)
      (hs.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  apply (norm_add_le _ _).trans
  have h₂ : ‖iteratedFDeriv ℝ r (fun x => expNegInvGlue (1 - x)) x‖ ≤ rhoBound r := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_comp_const_sub]
    simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using rho_jet_bound r (1 - x)
  have h₁ := rho_jet_bound r x
  push_cast
  linarith

def transitionInvBound (r : ℕ) : ℕ := reciprocalBound 9 (fun i => 2 * rhoBound i) r

lemma transitionInv_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (fun x => (transitionDenom x)⁻¹) x‖ ≤ transitionInvBound r := by
  apply reciprocal_jet_bound transitionDenom transitionDenom_smooth
    (fun i => 2 * rhoBound i) transitionDenom_bound 9 (by norm_num)
    (fun x => Real.smoothTransition.pos_denom x) _ r x
  intro x
  exact (inv_le_comm₀ (Real.smoothTransition.pos_denom x) (by norm_num : (0 : ℝ) < 9)).mpr
    (by simpa only [one_div] using transition_denom_lower x)

def transitionBound (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), r.choose i * rhoBound i * transitionInvBound (r - i)

lemma transition_jet_bound (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r Real.smoothTransition x‖ ≤ transitionBound r := by
  have he : Real.smoothTransition = fun x => expNegInvGlue x * (transitionDenom x)⁻¹ := by
    funext x; simp only [Real.smoothTransition, transitionDenom, div_eq_mul_inv]
  rw [he]
  apply (norm_iteratedFDeriv_mul_le (expNegInvGlue.contDiff (n := ⊤))
    (transitionDenom_smooth.inv (fun x => (Real.smoothTransition.pos_denom x).ne')) x
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
  simp only [transitionBound, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul _ (transitionInv_bound (r - i) x) (norm_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left (rho_jet_bound i x) (Nat.cast_nonneg _)

end Quantitative
end AlternatingNS

end QuantitativeDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/EffectiveProfiles.lean =====
namespace OAI

section EffectiveProfilesDevelopment

open scoped BigOperators ContDiff

namespace AlternatingNS
namespace Effective

lemma factorial : Primrec Nat.factorial := by
  have hs : Primrec₂ (fun n a : ℕ => (n + 1) * a) :=
    Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd
  have h := Primrec.nat_rec₁ 1 hs
  refine h.of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one, ih] using (Nat.factorial_succ n).symm

lemma sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℕ} (hf : Primrec₂ f) :
    Primrec₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Primrec₂ (fun a : A => fun z : ℕ × ℕ => z.2 + f a z.1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
  have h := Primrec.nat_rec (Primrec.const (0 : ℕ) : Primrec (fun _ : A => (0 : ℕ))) hs
  refine h.of_eq ?_
  intro a n
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

lemma choose : Primrec₂ Nat.choose := by
  apply Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (Primrec.nat_div.comp (factorial.comp Primrec.fst)
      (Primrec.nat_mul.comp (factorial.comp Primrec.snd)
        (factorial.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd)))) (Primrec.const 0) |>.of_eq
  rintro ⟨n,k⟩
  dsimp only
  split_ifs with h
  · exact (Nat.choose_eq_factorial_div_factorial h).symm
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

lemma rhoBound : Primrec Quantitative.rhoBound := by
  exact Primrec.nat_mul.comp (factorial.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    (nat_pow.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1)) Primrec.id)

lemma reciprocalBound {A : Type*} [Primcodable A] {q : A → ℕ} {B : A → ℕ → ℕ}
    (hq : Primrec q) (hB : Primrec₂ B) :
    Primrec₂ (fun a r => Quantitative.reciprocalBound (q a) (B a) r) := by
  let hr : Primrec (fun z : A × ℕ => z.2) := Primrec.snd
  let hfac := factorial.comp hr
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp hfac
      (Primrec.nat_mul.comp hfac (nat_pow.comp (hq.comp Primrec.fst) (Primrec.succ.comp hr))))
    (nat_pow.comp (Primrec.nat_add.comp (Primrec.const 1)
      ((sum_range hB).comp Primrec.fst (Primrec.succ.comp hr))) hr)

lemma transitionInvBound : Primrec Quantitative.transitionInvBound := by
  have hs : Primrec₂ (fun _ : ℕ => fun r : ℕ => 2 * Quantitative.rhoBound r) :=
    Primrec.nat_mul.comp (Primrec.const 2) (rhoBound.comp Primrec.snd)
  exact (reciprocalBound (Primrec.const 9 : Primrec (fun _ : ℕ => (9 : ℕ))) hs).comp
    Primrec.id Primrec.id

lemma transitionBound : Primrec Quantitative.transitionBound := by
  have hs : Primrec₂ (fun r i : ℕ => r.choose i * Quantitative.rhoBound i *
      Quantitative.transitionInvBound (r - i)) :=
    Primrec.nat_mul.comp (Primrec.nat_mul.comp choose (rhoBound.comp Primrec.snd))
      (transitionInvBound.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
  exact (sum_range hs).comp Primrec.id Primrec.succ

theorem profile_bound_programs :
    ∃ cρ cH : Program,
      (∀ r : ℕ, Returns cρ r (Quantitative.rhoBound r) ∧
        ∀ x : ℝ, ‖iteratedFDeriv ℝ r expNegInvGlue x‖ ≤ Quantitative.rhoBound r) ∧
      (∀ r : ℕ, Returns cH r (Quantitative.transitionBound r) ∧
        ∀ x : ℝ, ‖iteratedFDeriv ℝ r Real.smoothTransition x‖ ≤ Quantitative.transitionBound r) := by
  obtain ⟨cρ, hρ⟩ := program_of_computable Quantitative.rhoBound rhoBound.to_comp
  obtain ⟨cH, hH⟩ := program_of_computable Quantitative.transitionBound transitionBound.to_comp
  exact ⟨cρ, cH, fun r => ⟨hρ r, Quantitative.rho_jet_bound r⟩,
    fun r => ⟨hH r, Quantitative.transition_jet_bound r⟩⟩

end Effective
end AlternatingNS

end EffectiveProfilesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Arithmetic.lean =====
namespace OAI

section ArithmeticDevelopment

namespace AlternatingNS
namespace Arithmetic

lemma int_natCast : Primrec (fun n : ℕ => (n : ℤ)) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq (fun n => rfl)

lemma int_negSucc : Primrec Int.negSucc := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq (fun n => rfl)

lemma int_cases {A B : Type*} [Primcodable A] [Primcodable B]
    {f g : A → ℕ → B} (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec (fun z : A × ℤ => (Int.casesOn z.2 (f z.1) (g z.1) : B)) := by
  have hi : Primrec (fun z : A × ℤ => Encodable.encode z.2) := Primrec.encode.comp Primrec.snd
  refine (Primrec.cond (Primrec.nat_bodd.comp hi)
    (hg.comp Primrec.fst (Primrec.nat_div2.comp hi))
    (hf.comp Primrec.fst (Primrec.nat_div2.comp hi))).of_eq ?_
  rintro ⟨a,z⟩
  cases z with
  | ofNat n =>
    change (bif (Nat.bit false n).bodd then g a (Nat.bit false n).div2
      else f a (Nat.bit false n).div2) = f a n
    simp
  | negSucc n =>
    change (bif (Nat.bit true n).bodd then g a (Nat.bit true n).div2
      else f a (Nat.bit true n).div2) = g a n
    simp

lemma int_toNat : Primrec Int.toNat := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => n) (g := fun _ _ => (0 : ℕ))
    Primrec.snd (Primrec.const (0 : ℕ))
  exact (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq (fun z => by cases z <;> rfl)

lemma int_abs : Primrec Int.natAbs := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => n) (g := fun _ n => n + 1)
    Primrec.snd (Primrec.succ.comp Primrec.snd)
  exact (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq (fun z => by cases z <;> rfl)

lemma int_diff : Primrec₂ (fun a b : ℕ => (a : ℤ) - b) := by
  refine (Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (int_natCast.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (int_negSucc.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)))).of_eq ?_
  rintro ⟨a,b⟩
  dsimp only
  split_ifs <;> omega

lemma int_neg : Primrec (fun z : ℤ => -z) := by
  have h := int_cases (f := fun _ : ℕ => fun n : ℕ => (0 : ℤ) - n)
    (g := fun _ n => (n + 1 : ℕ))
    (int_diff.comp (Primrec.const 0 : Primrec (fun _ : ℕ × ℕ => (0 : ℕ))) Primrec.snd)
    (int_natCast.comp (Primrec.succ.comp Primrec.snd))
  refine (h.comp ((Primrec.const (0 : ℕ)).pair Primrec.id)).of_eq ?_
  intro z
  cases z with
  | ofNat n => change (0 : ℤ) - n = -(n : ℤ); simp
  | negSucc n => change ((n + 1 : ℕ) : ℤ) = -Int.negSucc n; simp

lemma int_add : Primrec₂ (fun a b : ℤ => a + b) := by
  have h := int_diff.comp
    (Primrec.nat_add.comp (int_toNat.comp Primrec.fst) (int_toNat.comp Primrec.snd))
    (Primrec.nat_add.comp (int_toNat.comp (int_neg.comp Primrec.fst))
      (int_toNat.comp (int_neg.comp Primrec.snd)))
  exact h.of_eq (fun z => by push_cast; omega)

lemma int_sub : Primrec₂ (fun a b : ℤ => a - b) :=
  (int_add.comp Primrec.fst (int_neg.comp Primrec.snd)).of_eq (fun _ => (sub_eq_add_neg _ _).symm)

lemma int_mul : Primrec₂ (fun a b : ℤ => a * b) := by
  have hn : Primrec (fun z : ℤ × ℤ => (Int.natAbs z.1 * Int.natAbs z.2 : ℕ)) :=
    Primrec.nat_mul.comp (int_abs.comp Primrec.fst) (int_abs.comp Primrec.snd)
  have hh := Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.fst))
    (Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd))
      (int_natCast.comp hn) (int_neg.comp (int_natCast.comp hn)))
    (Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd))
      (int_neg.comp (int_natCast.comp hn)) (int_natCast.comp hn))
  refine hh.of_eq ?_
  rintro ⟨a,b⟩
  change (bif (Encodable.encode a).bodd then
    (bif (Encodable.encode b).bodd then ((a.natAbs * b.natAbs : ℕ) : ℤ) else
      -((a.natAbs * b.natAbs : ℕ) : ℤ)) else
    (bif (Encodable.encode b).bodd then -((a.natAbs * b.natAbs : ℕ) : ℤ) else
      ((a.natAbs * b.natAbs : ℕ) : ℤ))) = a * b
  have hsign (z : ℤ) : (Encodable.encode z).bodd = decide (z < 0) := by
    cases z with
    | ofNat n =>
      change (Nat.bit false n).bodd = decide ((n : ℤ) < 0)
      simp
    | negSucc n =>
      change (Nat.bit true n).bodd = decide (Int.negSucc n < 0)
      simp

  rw [hsign a, hsign b]
  simp only [Bool.cond_decide, Nat.cast_mul, Int.natCast_natAbs]
  split_ifs with ha hb hb <;> simp_all [abs_of_neg, abs_of_nonneg, not_lt]

end Arithmetic
end AlternatingNS

namespace AlternatingNS.Arithmetic
lemma nat_dvd : PrimrecRel (fun a b : ℕ => a ∣ b) :=
  (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
    (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

lemma nat_gcd : Primrec₂ Nat.gcd := by
  have h := Primrec.nat_findGreatest (p := fun z : ℕ × ℕ => fun d => d ∣ z.1 ∧ d ∣ z.2)
    (Primrec.nat_add.comp Primrec.fst Primrec.snd)
    ((nat_dvd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (nat_dvd.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
  refine h.of_eq ?_
  rintro ⟨a,b⟩
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨?_, fun _ => ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩, ?_⟩
  · by_cases ha : a = 0
    · simp [ha]
    · exact (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)).trans (Nat.le_add_right a b)
  · intro d hd _ hab
    have hpos : 0 < a.gcd b := by
      by_contra hn
      have hz := Nat.gcd_eq_zero_iff.mp (by omega : a.gcd b = 0)
      omega
    exact (not_lt_of_ge (Nat.le_of_dvd hpos (Nat.dvd_gcd hab.1 hab.2))) hd

lemma rat_valid : PrimrecPred (fun z : ℤ × ℕ => 0 < z.2 ∧ z.1.natAbs.Coprime z.2) :=
  (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    (Primrec.eq.comp (nat_gcd.comp (int_abs.comp Primrec.fst) Primrec.snd) (Primrec.const 1))

def ratEquiv : ℚ ≃ {z : ℤ × ℕ // 0 < z.2 ∧ z.1.natAbs.Coprime z.2} where
  toFun q := ⟨(q.num,q.den), q.den_pos, q.reduced⟩
  invFun q := ⟨q.1.1,q.1.2, Nat.ne_of_gt q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def rationalCoding : Primcodable ℚ := by
  letI := Primcodable.subtype rat_valid
  exact Primcodable.ofEquiv _ ratEquiv

lemma rationalCoding_encode (q : ℚ) :
    @Encodable.encode ℚ rationalCoding.toEncodable q = Encodable.encode q := rfl

attribute [local instance] rationalCoding

lemma rat_num : Primrec Rat.num := by
  let := Primcodable.subtype rat_valid
  have := Primrec.fst.comp (Primrec.subtype_val (hp := rat_valid))
  exact this.comp (Primrec.of_equiv (e := ratEquiv))

lemma rat_den : Primrec Rat.den := by
  let := Primcodable.subtype rat_valid
  exact (Primrec.snd.comp (Primrec.subtype_val (hp := rat_valid))).comp
    (Primrec.of_equiv (e := ratEquiv))

lemma int_ediv_nat : Primrec₂ (fun z : ℤ => fun d : ℕ => z / (d : ℤ)) := by
  have h := int_cases
    (f := fun d n : ℕ => ((n / d : ℕ) : ℤ))
    (g := fun d n => if d = 0 then 0 else Int.negSucc (n / d))
    (int_natCast.comp (Primrec.nat_div.comp Primrec.snd Primrec.fst))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
      (int_negSucc.comp (Primrec.nat_div.comp Primrec.snd Primrec.fst)))
  refine (h.comp (Primrec.snd.pair Primrec.fst)).of_eq ?_
  rintro ⟨z,d⟩
  cases z with
  | ofNat n => exact Int.natCast_ediv n d
  | negSucc n => cases d <;> rfl

lemma rat_mk : Primrec₂ mkRat := by
  have hz : PrimrecPred (fun z : ℤ × ℕ => z.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hg : Primrec (fun z : ℤ × ℕ => z.2.gcd z.1.natAbs) :=
    nat_gcd.comp Primrec.snd (int_abs.comp Primrec.fst)
  have hn := Primrec.ite hz (Primrec.const (0 : ℤ)) (int_ediv_nat.comp Primrec.fst hg)
  have hd := Primrec.ite hz (Primrec.const (1 : ℕ)) (Primrec.nat_div.comp Primrec.snd hg)
  apply Primrec.encode_iff.mp
  refine (Primrec₂.natPair.comp (Primrec.encode.comp hn) hd).of_eq ?_
  rintro ⟨n,d⟩
  change Nat.pair (Encodable.encode (if d = 0 then (0 : ℤ) else n / ↑(d.gcd n.natAbs)))
    (if d = 0 then 1 else d / d.gcd n.natAbs) =
    Nat.pair (Encodable.encode (mkRat n d).num) (mkRat n d).den
  rw [Rat.num_mkRat, Rat.den_mkRat]

lemma rat_intCast : Primrec (fun n : ℤ => (n : ℚ)) := by
  exact (rat_mk.comp Primrec.id (Primrec.const 1)).of_eq (fun n => by simp [Rat.mkRat_eq_div])

lemma rat_natCast : Primrec (fun n : ℕ => (n : ℚ)) :=
  (rat_intCast.comp int_natCast).of_eq (fun n => by simp)

lemma rat_add : Primrec₂ (fun a b : ℚ => a + b) := by
  have hn := int_add.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (int_natCast.comp (rat_den.comp Primrec.snd)))
    (int_mul.comp (rat_num.comp Primrec.snd) (int_natCast.comp (rat_den.comp Primrec.fst)))
  have hd := Primrec.nat_mul.comp (rat_den.comp Primrec.fst) (rat_den.comp Primrec.snd)
  exact (rat_mk.comp hn hd).of_eq (fun z => by
    dsimp only
    rw [Rat.add_def, Rat.normalize_eq_mkRat])

lemma rat_mul : Primrec₂ (fun a b : ℚ => a * b) := by
  exact (rat_mk.comp (int_mul.comp (rat_num.comp Primrec.fst) (rat_num.comp Primrec.snd))
    (Primrec.nat_mul.comp (rat_den.comp Primrec.fst) (rat_den.comp Primrec.snd))).of_eq
    (fun z => (Rat.mul_eq_mkRat z.1 z.2).symm)

lemma rat_neg : Primrec (fun a : ℚ => -a) := by
  refine (rat_mk.comp (int_neg.comp rat_num) rat_den).of_eq ?_
  intro q
  rw [Rat.mkRat_eq_div, Int.cast_neg, neg_div, Rat.num_div_den]

lemma rat_sub : Primrec₂ (fun a b : ℚ => a - b) :=
  (rat_add.comp Primrec.fst (rat_neg.comp Primrec.snd)).of_eq (fun _ => (sub_eq_add_neg _ _).symm)

lemma int_le : PrimrecRel (fun a b : ℤ => a ≤ b) :=
  (Primrec.eq.comp (int_toNat.comp int_sub) (Primrec.const 0)).of_eq (fun z => by
    dsimp only; omega)

lemma int_lt : PrimrecRel (fun a b : ℤ => a < b) :=
  (int_le.comp Primrec.snd Primrec.fst).not.of_eq (fun z => by simp)

lemma rat_divInt : Primrec₂ Rat.divInt := by
  have h := int_cases (f := fun a : ℤ => fun d : ℕ => mkRat a d)
    (g := fun a d => mkRat (-a) (d + 1)) rat_mk
    (rat_mk.comp (int_neg.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))
  refine h.of_eq ?_
  rintro ⟨n,d⟩
  cases d with
  | ofNat d => rfl
  | negSucc d => exact (Rat.normalize_eq_mkRat (Nat.succ_ne_zero d)).symm

lemma rat_inv : Primrec (fun q : ℚ => q⁻¹) :=
  (rat_divInt.comp (int_natCast.comp rat_den) rat_num).of_eq (fun q => (Rat.inv_def q).symm)

lemma rat_div : Primrec₂ (fun a b : ℚ => a / b) :=
  (rat_mul.comp Primrec.fst (rat_inv.comp Primrec.snd)).of_eq
    (fun _ => (div_eq_mul_inv _ _).symm)

lemma rat_le : PrimrecRel (fun a b : ℚ => a ≤ b) :=
  (int_le.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (int_natCast.comp (rat_den.comp Primrec.snd)))
    (int_mul.comp (rat_num.comp Primrec.snd) (int_natCast.comp (rat_den.comp Primrec.fst)))).of_eq
    (fun z => (Rat.le_iff z.1 z.2).symm)

lemma rat_lt : PrimrecRel (fun a b : ℚ => a < b) :=
  (rat_le.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => by simp)

lemma rat_abs : Primrec (fun a : ℚ => |a|) :=
  (Primrec.ite (rat_le.comp (Primrec.const 0) Primrec.id) Primrec.id rat_neg).of_eq
    (fun a => by
      change (if 0 ≤ a then a else -a) = |a|
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · exact (abs_of_neg (lt_of_not_ge h)).symm)

lemma rat_floor : Primrec (fun q : ℚ => ⌊q⌋) := by
  change Primrec Rat.floor
  exact (int_ediv_nat.comp rat_num rat_den).of_eq (fun q => (Rat.floor_def q).symm)

lemma rat_pow : Primrec₂ (fun q : ℚ => fun n : ℕ => q ^ n) := by
  have hs : Primrec₂ (fun q : ℚ => fun z : ℕ × ℚ => z.2 * q) :=
    rat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  refine (Primrec.nat_rec (Primrec.const (1 : ℚ)) hs).of_eq ?_
  intro q n
  induction n with
  | zero => simp
  | succ n ih => simpa only [ih] using (pow_succ q n).symm

end AlternatingNS.Arithmetic

end ArithmeticDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Names.lean =====
namespace OAI

section NamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective

attribute [local instance] Arithmetic.rationalCoding

def tolerance (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ n

lemma tolerance_cast (n : ℕ) : (tolerance n : ℝ) = dyadicError n := by
  simp [tolerance, dyadicError]

lemma tolerance_primrec : Primrec tolerance :=
  Arithmetic.rat_pow.comp (Primrec.const (1 / 2)) Primrec.id

lemma tolerance_pos (n : ℕ) : (0 : ℝ) < tolerance n := by
  rw [tolerance_cast]; exact pow_pos (by norm_num) _

lemma tolerance_tendsto : Tendsto (fun n => (tolerance n : ℝ)) atTop (𝓝 0) := by
  simp only [tolerance_cast, dyadicError]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def Named {A : Type*} [Primcodable A] (f : A → ℝ) : Prop :=
  ∃ a : A × ℕ → ℚ, Computable a ∧
    ∀ x n, |f x - (a (x,n) : ℝ)| ≤ tolerance n

lemma computable_find {A : Type*} [Primcodable A] (p : A → ℕ → Prop)
    [DecidableRel p] (hp : Computable (fun z : A × ℕ => decide (p z.1 z.2)))
    (h : ∀ a, ∃ n, p a n) : Computable (fun a => @Nat.find (p a) (fun _ => inferInstance) (h a)) := by
  have hr : Partrec (fun a => Nat.rfind (fun n => Part.some (decide (p a n)))) :=
    Partrec.rfind hp.to₂.partrec₂
  apply hr.of_eq_tot
  intro a
  apply Nat.mem_rfind.mpr
  refine ⟨?_, fun {m} hm => ?_⟩
  · simp [Nat.find_spec (h a)]
  · simp [Nat.find_min (h a) hm]

lemma Named.of_certificate {A : Type*} [Primcodable A] (f : A → ℝ)
    (a e : A × ℕ → ℚ) (ha : Computable a) (he : Computable e)
    (hbound : ∀ x n, |f x - (a (x,n) : ℝ)| ≤ (e (x,n) : ℝ))
    (hlim : ∀ x, Tendsto (fun n => (e (x,n) : ℝ)) atTop (𝓝 0)) : Named f := by
  classical
  let p (z : A × ℕ) (n : ℕ) : Prop := e (z.1,n) ≤ tolerance z.2
  have hp : Computable (fun z : (A × ℕ) × ℕ => decide (p z.1 z.2)) :=
    Arithmetic.rat_le.decide.to_comp.comp
      (he.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (tolerance_primrec.to_comp.comp (Computable.snd.comp Computable.fst))
  have hex (z : A × ℕ) : ∃ n, p z n := by
    have hE := (hlim z.1).eventually (gt_mem_nhds (tolerance_pos z.2))
    obtain ⟨n,hn⟩ := hE.exists
    exact ⟨n, by exact_mod_cast hn.le⟩
  let N (z : A × ℕ) : ℕ := Nat.find (hex z)
  have hN : Computable N := computable_find p hp hex
  refine ⟨fun z => a (z.1,N z), ha.comp (Computable.fst.pair hN), fun x k => ?_⟩
  exact (hbound x (N (x,k))).trans (by exact_mod_cast Nat.find_spec (hex (x,k)))

lemma Named.congr {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (h : ∀ a, f a = g a) : Named g := by
  simpa only [show f = g from funext h] using hf

lemma Named.comp {A B : Type*} [Primcodable A] [Primcodable B] {f : A → ℝ}
    (hf : Named f) {g : B → A} (hg : Computable g) : Named (f ∘ g) := by
  obtain ⟨a, ha, hb⟩ := hf
  exact ⟨fun z => a (g z.1,z.2),
    ha.comp ((hg.comp Computable.fst).pair Computable.snd), fun z n => hb (g z) n⟩

lemma Named.rational {A : Type*} [Primcodable A] {f : A → ℚ} (hf : Computable f) :
    Named (fun a => (f a : ℝ)) :=
  ⟨fun z => f z.1, hf.comp Computable.fst, fun _ n => by
    simp only [sub_self, abs_zero]; exact (tolerance_pos n).le⟩

lemma Named.const {A : Type*} [Primcodable A] (q : ℚ) : Named (fun _ : A => (q : ℝ)) :=
  Named.rational (Computable.const q)

lemma approximation_tendsto {x : ℝ} {a : ℕ → ℚ}
    (h : ∀ n, |x - (a n : ℝ)| ≤ tolerance n) :
    Tendsto (fun n => (a n : ℝ)) atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => x - (tolerance n : ℝ))
    (h := fun n => x + (tolerance n : ℝ))
  · simpa using tendsto_const_nhds.sub tolerance_tendsto
  · simpa using tendsto_const_nhds.add tolerance_tendsto
  · intro n; have := (abs_le.mp (h n)).2; linarith
  · intro n; have := (abs_le.mp (h n)).1; linarith

lemma Named.add {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x + g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  apply Named.of_certificate _ (fun z => a z + b z) (fun z => 2 * tolerance z.2)
    (Arithmetic.rat_add.to_comp.comp ha hb)
    (Arithmetic.rat_mul.to_comp.comp (Computable.const 2)
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    push_cast
    calc
      _ = |(f x - (a (x,n) : ℝ)) + (g x - (b (x,n) : ℝ))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (by linarith [hae x n, hbe x n])
  · intro x; simpa using (tolerance_tendsto.const_mul 2)

lemma Named.neg {A : Type*} [Primcodable A] {f : A → ℝ} (hf : Named f) :
    Named (fun x => -f x) := by
  obtain ⟨a,ha,h⟩ := hf
  refine ⟨fun z => -a z, Arithmetic.rat_neg.to_comp.comp ha, fun x n => ?_⟩
  simpa only [Rat.cast_neg, neg_sub_neg, abs_sub_comm] using h x n

lemma Named.sub {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x - g x) :=
  (hf.add hg.neg).congr (fun _ => (sub_eq_add_neg _ _).symm)

lemma Named.mul {A : Type*} [Primcodable A] {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => f x * g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  let e : A × ℕ → ℚ := fun z => (|a z| + |b z| + tolerance z.2) * tolerance z.2
  have he : Computable e := Arithmetic.rat_mul.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp
      (Arithmetic.rat_add.to_comp.comp (Arithmetic.rat_abs.to_comp.comp ha)
        (Arithmetic.rat_abs.to_comp.comp hb))
      (tolerance_primrec.to_comp.comp Computable.snd))
    (tolerance_primrec.to_comp.comp Computable.snd)
  apply Named.of_certificate _ (fun z => a z * b z) e
    (Arithmetic.rat_mul.to_comp.comp ha hb) he
  · intro x n
    dsimp [e]; push_cast
    have hf : |f x| ≤ |(a (x,n) : ℝ)| + (tolerance n : ℝ) := by
      have h := abs_add_le (f x - (a (x,n) : ℝ)) (a (x,n))
      ring_nf at h
      linarith [hae x n]
    calc
      _ = |f x * (g x - (b (x,n) : ℝ)) + (f x - (a (x,n) : ℝ)) * (b (x,n) : ℝ)| := by congr 1; ring
      _ ≤ |f x| * |g x - (b (x,n) : ℝ)| + |f x - (a (x,n) : ℝ)| * |(b (x,n) : ℝ)| := by
        simpa only [abs_mul] using abs_add_le (f x * (g x - (b (x,n) : ℝ))) ((f x - (a (x,n) : ℝ)) * (b (x,n) : ℝ))
      _ ≤ (|(a (x,n) : ℝ)| + (tolerance n : ℝ)) * (tolerance n : ℝ) +
          (tolerance n : ℝ) * |(b (x,n) : ℝ)| :=
        add_le_add (mul_le_mul hf (hbe x n) (abs_nonneg _) (add_nonneg (abs_nonneg _) (tolerance_pos n).le))
          (mul_le_mul_of_nonneg_right (hae x n) (abs_nonneg _))
      _ = _ := by ring
  · intro x
    dsimp [e]
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
    simpa using (((approximation_tendsto (hae x)).abs.add
      (approximation_tendsto (hbe x)).abs).add tolerance_tendsto).mul tolerance_tendsto

lemma Named.ite {A : Type*} [Primcodable A] (p : A → Prop) [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) {f g : A → ℝ}
    (hf : Named f) (hg : Named g) : Named (fun x => if p x then f x else g x) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  refine ⟨fun z => if p z.1 then a z else b z,
    (Computable.cond (hp.comp Computable.fst) ha hb).of_eq (by simp), ?_⟩
  intro x n; dsimp only; split_ifs <;> simp_all

lemma Named.apply_lipschitz {A : Type*} [Primcodable A] (g : A → ℝ → ℝ)
    (L : A → ℚ) (hL : Computable L) (hpos : ∀ a, 0 ≤ L a)
    (hLip : ∀ a x y, |g a x - g a y| ≤ (L a : ℝ) * |x - y|)
    (hg : Named (fun z : A × ℚ => g z.1 z.2))
    {f : A → ℝ} (hf : Named f) : Named (fun a => g a (f a)) := by
  obtain ⟨a,ha,hae⟩ := hf
  obtain ⟨b,hb,hbe⟩ := hg
  apply Named.of_certificate _ (fun z => b ((z.1,a z),z.2))
    (fun z => (L z.1 + 1) * tolerance z.2)
    (hb.comp ((Computable.fst.pair ha).pair Computable.snd))
    (Arithmetic.rat_mul.to_comp.comp
      (Arithmetic.rat_add.to_comp.comp (hL.comp Computable.fst) (Computable.const 1))
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    push_cast
    calc
      _ ≤ |g x (f x) - g x (a (x,n))| + |g x (a (x,n)) - (b ((x,a (x,n)),n) : ℝ)| := abs_sub_le _ _ _
      _ ≤ (L x : ℝ) * (tolerance n : ℝ) + (tolerance n : ℝ) :=
        add_le_add ((hLip x _ _).trans (mul_le_mul_of_nonneg_left (hae x n) (by exact_mod_cast hpos x)))
          (hbe (x,a (x,n)) n)
      _ = _ := by ring
  · intro x; simpa using tolerance_tendsto.const_mul ((L x : ℝ) + 1)

end AlternatingNS.Effective

end NamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/ExpNames.lean =====
namespace OAI

section ExpNamesDevelopment

open scoped BigOperators ContDiff Topology
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma rat_sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℚ}
    (hf : Computable₂ f) : Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Computable₂ (fun a : A => fun z : ℕ × ℚ => z.2 + f a z.1) :=
    Arithmetic.rat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
  have h := Computable.nat_rec (Computable.snd : Computable (fun z : A × ℕ => z.2))
    (Computable.const (0 : ℚ))
    (hs.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  refine h.to₂.of_eq ?_
  rintro ⟨a,n⟩
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

lemma abs_rat_cast_le_num (q : ℚ) : |(q : ℝ)| ≤ q.num.natAbs := by
  have h : (q.den : ℝ) ≥ 1 := by exact_mod_cast q.den_pos
  rw [Rat.cast_def, abs_div, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_self (Nat.cast_nonneg _) h

lemma exp_named : Named (fun q : ℚ => Real.exp (q : ℝ)) := by
  let N (z : ℚ × ℕ) : ℕ := 2 * z.1.num.natAbs + z.2 + 1
  have hN : Computable N := (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Arithmetic.int_abs.comp (Arithmetic.rat_num.comp Primrec.fst))) Primrec.snd)
    (Primrec.const 1)).to_comp
  let a (z : ℚ × ℕ) : ℚ := ∑ i ∈ Finset.range (N z), z.1 ^ i / i.factorial
  let err (z : ℚ × ℕ) : ℚ := |z.1| ^ N z / (N z).factorial * 2
  have ht : Computable₂ (fun q : ℚ => fun i : ℕ => q ^ i / i.factorial) :=
    Arithmetic.rat_div.to_comp.comp Arithmetic.rat_pow.to_comp
      (Arithmetic.rat_natCast.to_comp.comp (factorial.to_comp.comp Computable.snd))
  have ha : Computable a := (rat_sum_range ht).comp Computable.fst hN
  have he : Computable err := Arithmetic.rat_mul.to_comp.comp
    (Arithmetic.rat_div.to_comp.comp
      (Arithmetic.rat_pow.to_comp.comp (Arithmetic.rat_abs.to_comp.comp Computable.fst) hN)
      (Arithmetic.rat_natCast.to_comp.comp (factorial.to_comp.comp hN))) (Computable.const 2)
  apply Named.of_certificate _ a err ha he
  · intro q n
    have hl : ‖(q : ℂ)‖ / (N (q,n)).succ ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N (q,n)).succ)]
      rw [show (q : ℂ) = ((q : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_eq_abs]
      have hh := abs_rat_cast_le_num q
      dsimp [N]; push_cast; linarith
    have h := Complex.exp_bound' hl
    have hc : (∑ i ∈ Finset.range (N (q,n)), (q : ℂ) ^ i / i.factorial) = (a (q,n) : ℂ) := by
      simp [a]
    rw [hc, show (q : ℂ) = ((q : ℝ) : ℂ) by simp, ← Complex.ofReal_exp,
      show (a (q,n) : ℂ) = ((a (q,n) : ℝ) : ℂ) by simp,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs] at h
    simpa only [err, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_abs,
      Rat.cast_natCast, Rat.cast_ofNat] using h
  · intro q
    have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop |(q : ℝ)|).mul_const 2
    have hshift : Tendsto (fun n => N (q,n)) atTop atTop := by
      apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
      intro n; dsimp [N]; omega
    simpa only [err, Function.comp_def, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_abs, Rat.cast_natCast, Rat.cast_ofNat, zero_mul] using hlim.comp hshift

end AlternatingNS.Effective

end ExpNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/ProfileNames.lean =====
namespace OAI

section ProfileNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma rat_max : Primrec₂ (fun x y : ℚ => max x y) :=
  (Primrec.ite Arithmetic.rat_le Primrec.snd Primrec.fst).of_eq (by intro z; simp [max_def])

lemma Named.inv_of_lower {A : Type*} [Primcodable A] {f : A → ℝ}
    (hf : Named f) (b : A → ℚ) (hb : Computable b) (hpos : ∀ x, 0 < b x)
    (hlower : ∀ x, (b x : ℝ) ≤ f x) : Named (fun x => (f x)⁻¹) := by
  obtain ⟨a,ha,he⟩ := hf
  let c : A × ℕ → ℚ := fun z => max (b z.1) (a z)
  have hc : Computable c := rat_max.to_comp.comp (hb.comp Computable.fst) ha
  apply Named.of_certificate _ (fun z => (c z)⁻¹)
    (fun z => (b z.1)⁻¹ ^ 2 * tolerance z.2)
    (Arithmetic.rat_inv.to_comp.comp hc)
    (Arithmetic.rat_mul.to_comp.comp
      (Arithmetic.rat_pow.to_comp.comp (Arithmetic.rat_inv.to_comp.comp (hb.comp Computable.fst))
        (Computable.const 2)) (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n
    have hb₀ : (0 : ℝ) < b x := by exact_mod_cast hpos x
    have hc₀ : (b x : ℝ) ≤ c (x,n) := by exact_mod_cast (le_max_left (b x) (a (x,n)))
    have ha₀ : (a (x,n) : ℝ) ≤ c (x,n) := by exact_mod_cast (le_max_right (b x) (a (x,n)))
    have hce : |f x - (c (x,n) : ℝ)| ≤ tolerance n := by
      rw [abs_le]
      have h := abs_le.mp (he x n)
      refine ⟨?_, by linarith⟩
      have hmax : (c (x,n) : ℝ) ≤ f x + (tolerance n : ℝ) := by
        dsimp only [c]; push_cast
        apply max_le
        · exact (hlower x).trans (le_add_of_nonneg_right (tolerance_pos n).le)
        · linarith
      linarith
    have hfx : 0 < f x := hb₀.trans_le (hlower x)
    have hcx : 0 < (c (x,n) : ℝ) := hb₀.trans_le hc₀
    push_cast
    rw [inv_sub_inv hfx.ne' hcx.ne', abs_div, abs_mul,
      abs_of_pos hfx, abs_of_pos hcx, abs_sub_comm]
    calc
      _ ≤ (tolerance n : ℝ) / ((b x : ℝ) * (b x : ℝ)) :=
        div_le_div₀ (tolerance_pos n).le hce (mul_pos hb₀ hb₀)
          (mul_le_mul (hlower x) hc₀ hb₀.le hfx.le)
      _ = _ := by ring
  · intro x
    convert tolerance_tendsto.const_mul ((b x : ℝ)⁻¹ ^ 2) using 1 <;>
      simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, inv_pow, mul_zero]

lemma Named.sum_range {A : Type*} [Primcodable A] {f : A × ℕ → ℝ}
    (hf : Named f) (N : A → ℕ) (hN : Computable N) :
    Named (fun x => ∑ i ∈ Finset.range (N x), f (x,i)) := by
  obtain ⟨a,ha,he⟩ := hf
  have hs : Computable₂ (fun z : A × ℕ => fun i : ℕ => a ((z.1,i),z.2)) :=
    ha.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))
  apply Named.of_certificate _ (fun z => ∑ i ∈ Finset.range (N z.1), a ((z.1,i),z.2))
    (fun z => (N z.1 : ℚ) * tolerance z.2)
    ((rat_sum_range hs).comp Computable.id (hN.comp Computable.fst))
    (Arithmetic.rat_mul.to_comp.comp (Arithmetic.rat_natCast.to_comp.comp (hN.comp Computable.fst))
      (tolerance_primrec.to_comp.comp Computable.snd))
  · intro x n; push_cast; rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (N x), (tolerance n : ℝ) := Finset.sum_le_sum (fun i _ => he (x,i) n)
      _ = _ := by simp
  · intro x; push_cast
    simpa only [inv_pow, mul_zero] using tolerance_tendsto.const_mul (N x : ℝ)

lemma rho_named : Named (fun q : ℚ => expNegInvGlue (q : ℝ)) := by
  have hn := exp_named.comp (Arithmetic.rat_neg.comp Arithmetic.rat_inv |>.to_comp)
  exact (Named.ite (fun q : ℚ => q ≤ 0)
    (Arithmetic.rat_le.decide.to_comp.comp Computable.id (Computable.const 0))
    (Named.const 0) hn).congr (by intro q; simp [expNegInvGlue])

lemma transition_named : Named (fun q : ℚ => Real.smoothTransition (q : ℝ)) := by
  have h₂ := rho_named.comp (Arithmetic.rat_sub.to_comp.comp (Computable.const 1) Computable.id)
  have hd := rho_named.add h₂
  have hi := hd.inv_of_lower (fun _ => 1/9) (Computable.const _) (by intro; norm_num)
    (by intro q; simpa [Function.comp_def] using Quantitative.transition_denom_lower (q : ℝ))
  exact (rho_named.mul hi).congr (by intro q; simp [Real.smoothTransition, div_eq_mul_inv])

lemma jet_one_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (B : ℕ)
    (hB : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ B) (x y : ℝ) :
    |f x - f y| ≤ (B : ℝ) * |x-y| := by
  have h : ∀ x, ‖deriv f x‖ ≤ (B : ℝ) := by
    intro z
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] using hB z
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Set.univ) => hf.differentiable (by simp) z) (fun z _ => h z)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)

lemma Named.transition {A : Type*} [Primcodable A] {f : A → ℝ} (hf : Named f) :
    Named (fun a => Real.smoothTransition (f a)) := by
  apply Named.apply_lipschitz (fun _ => Real.smoothTransition)
    (fun _ => (Quantitative.transitionBound 1 : ℚ)) (Computable.const _) (fun _ => by positivity)
    (fun _ x y => ?_) (transition_named.comp Computable.snd) hf
  simpa only [Rat.cast_natCast] using jet_one_lipschitz Real.smoothTransition.contDiff
    (Quantitative.transitionBound 1) (Quantitative.transition_jet_bound 1) x y

end AlternatingNS.Effective

end ProfileNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/DecoderBounds.lean =====
namespace OAI

section DecoderBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Quantitative

lemma linear_id_jet (r : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |iteratedDeriv r id x| ≤ 1 := by
  rw [iteratedDeriv_id]; split_ifs <;> simp_all

lemma transition_affine (r : ℕ) (a d : ℝ) :
    iteratedDeriv r (fun x => Real.smoothTransition ((x-a)/d)) =
      fun x => d⁻¹ ^ r * iteratedDeriv r Real.smoothTransition ((x-a)/d) := by
  have h : (fun x => Real.smoothTransition ((x-a)/d)) =
      (fun x => Real.smoothTransition (d⁻¹ * (x-a))) := by funext x; congr 1; ring
  rw [h, iteratedDeriv_comp_sub_const r (fun z => Real.smoothTransition (d⁻¹ * z)) a,
    iteratedDeriv_comp_const_mul
    (Real.smoothTransition.contDiff.of_le (WithTop.coe_le_coe.mpr le_top))]
  simp only [div_eq_mul_inv, mul_comm]

lemma periodizer_jet_bound (r : ℕ) (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1)
    (x : ℝ) :
    ‖iteratedFDeriv ℝ r (Profiles.periodizer a c) x‖ ≤
      1 + (c-a)⁻¹ ^ r * transitionBound r := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  have hnon : 0 ≤ (c-a)⁻¹ ^ r * (transitionBound r : ℝ) := by positivity
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have he : Profiles.periodizer a c =ᶠ[𝓝 x] (fun y => y - (⌊x⌋ : ℝ)) := by
      have hlo : (⌊x⌋ : ℝ) + (c - 1) < x := by linarith
      have hhi : x < (⌊x⌋ : ℝ) + a := by linarith
      filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
      have hy' : y - (⌊x⌋ : ℝ) ∈ Set.Ioo (c - 1) a := by
        constructor <;> linarith [hy.1, hy.2]
      calc
        Profiles.periodizer a c y = Profiles.periodizer a c ((⌊x⌋ : ℝ) + (y - (⌊x⌋ : ℝ))) := by congr 1; ring
        _ = Profiles.periodizer a c (y - (⌊x⌋ : ℝ)) := Profiles.periodizer_int_add a c _ _
        _ = y - (⌊x⌋ : ℝ) := Profiles.periodizer_near_zero a c ha hac hc _ hy'
    rw [he.iteratedDeriv_eq r]
    change |iteratedDeriv r (fun y => id (y - (⌊x⌋ : ℝ))) x| ≤ _
    rw [iteratedDeriv_comp_sub_const]
    exact (linear_id_jet r (by rw [hx]; simp)).trans (le_add_of_nonneg_right hnon)
  · have he : Profiles.periodizer a c =ᶠ[𝓝 x]
        (fun y => (y - (⌊x⌋ : ℝ)) - Real.smoothTransition ((y - (⌊x⌋ : ℝ)-a)/(c-a))) := by
      have hlo : (⌊x⌋ : ℝ) < x := (Int.floor_le x).lt_of_ne (Ne.symm hx)
      filter_upwards [Ioo_mem_nhds hlo (Int.lt_floor_add_one x)] with y hy
      have hy' : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩
      simp only [Profiles.periodizer, Int.fract, hy']
    rw [he.iteratedDeriv_eq r]
    change |iteratedDeriv r (fun y => ((id : ℝ → ℝ) - fun z => Real.smoothTransition ((z-a)/(c-a)))
      (y - (⌊x⌋ : ℝ))) x| ≤ _
    rw [iteratedDeriv_comp_sub_const]
    dsimp only
    rw [iteratedDeriv_sub contDiffAt_id
      (show ContDiffAt ℝ (r : ℕ∞ω) (fun z => Real.smoothTransition ((z-a)/(c-a))) (x - (⌊x⌋ : ℝ)) from by fun_prop),
      transition_affine]
    calc
      _ ≤ |iteratedDeriv r id (x - (⌊x⌋ : ℝ))| +
          (c-a)⁻¹ ^ r * |iteratedDeriv r Real.smoothTransition ((x - (⌊x⌋:ℝ)-a)/(c-a))| := by
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hac).le) r)] using
          norm_sub_le (iteratedDeriv r id (x - (⌊x⌋ : ℝ)))
            ((c-a)⁻¹ ^ r * iteratedDeriv r Real.smoothTransition ((x - (⌊x⌋:ℝ)-a)/(c-a)))
      _ ≤ _ := add_le_add (linear_id_jet r (by
          rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
          linarith [Int.lt_floor_add_one x]))
        (mul_le_mul_of_nonneg_left
          (by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
            transition_jet_bound r ((x - (⌊x⌋:ℝ)-a)/(c-a)))
          (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hac).le) r))

def decoderBound (b r : ℕ) : ℕ := 1 + (3 * (b - 1)) ^ r * transitionBound r

lemma decoder_jet_bound (b : ℕ) (hb : 2 ≤ b) (r : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (Profiles.decoder b) x‖ ≤ decoderBound b r := by
  have hm0 := Encoding.tailMax_nonneg b hb
  have hm1 := Encoding.tailMax_lt_one b hb
  have hgap : (((Encoding.tailMax b + 2) / 3) - ((2 * Encoding.tailMax b + 1) / 3))⁻¹ =
      (3 * (b - 1) : ℕ) := by
    have hbn : (b - 1 : ℕ) = (b : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ b)
    rw [Nat.cast_mul, hbn]
    have h : (b : ℝ) - 1 ≠ 0 := by
      have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    unfold Encoding.tailMax
    field_simp
    ring
  have h := periodizer_jet_bound r ((2 * Encoding.tailMax b + 1) / 3)
    ((Encoding.tailMax b + 2) / 3) (by linarith) (by linarith) (by linarith) x
  rw [hgap] at h
  simpa only [Profiles.decoder, decoderBound, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow] using h

end AlternatingNS.Quantitative

end DecoderBoundsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/DecoderNames.lean =====
namespace OAI

section DecoderNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma decoderBound : Primrec₂ Quantitative.decoderBound :=
  Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_mul.comp
      (nat_pow.comp (Primrec.nat_mul.comp (Primrec.const 3)
        (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))) Primrec.snd)
      (transitionBound.comp Primrec.snd))

lemma rat_fract : Primrec (fun q : ℚ => Int.fract q) :=
  Arithmetic.rat_sub.comp Primrec.id (Arithmetic.rat_intCast.comp Arithmetic.rat_floor)

lemma frac_cast (q : ℚ) : ((Int.fract q : ℚ) : ℝ) = Int.fract (q : ℝ) := by
  simp only [Int.fract, Rat.cast_sub, Rat.cast_intCast, Rat.floor_cast]

lemma periodizer_named : Named (fun z : (ℚ × ℚ) × ℚ => Profiles.periodizer z.1.1 z.1.2 z.2) := by
  have hv : Computable (fun z : (ℚ × ℚ) × ℚ => Int.fract z.2) := rat_fract.to_comp.comp Computable.snd
  have hA : Computable (fun z : (ℚ × ℚ) × ℚ => (Int.fract z.2 - z.1.1)/(z.1.2-z.1.1)) :=
    Arithmetic.rat_div.to_comp.comp
      (Arithmetic.rat_sub.to_comp.comp hv (Computable.fst.comp Computable.fst))
      (Arithmetic.rat_sub.to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.fst.comp Computable.fst))
  exact ((Named.rational hv).sub (transition_named.comp hA)).congr (by
    intro z
    simp only [Function.comp_def, Profiles.periodizer, Rat.cast_div, Rat.cast_sub]
    rw [frac_cast])

lemma decoder_named : Named (fun z : ℕ × ℚ => Profiles.decoder z.1 (z.2 : ℝ)) := by
  let m (b : ℕ) : ℚ := ((b : ℚ)-2)/((b : ℚ)-1)
  have hm : Computable m := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_sub.to_comp.comp Arithmetic.rat_natCast.to_comp (Computable.const 2))
    (Arithmetic.rat_sub.to_comp.comp Arithmetic.rat_natCast.to_comp (Computable.const 1))
  have ha : Computable (fun z : ℕ × ℚ => (2*m z.1+1)/3) := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp
      (Arithmetic.rat_mul.to_comp.comp (Computable.const 2) (hm.comp Computable.fst))
      (Computable.const 1)) (Computable.const 3)
  have hc : Computable (fun z : ℕ × ℚ => (m z.1+2)/3) := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp (hm.comp Computable.fst) (Computable.const 2)) (Computable.const 3)
  exact (periodizer_named.comp ((ha.pair hc).pair Computable.snd)).congr (by
    intro z; simp [Profiles.decoder, Encoding.tailMax, m])

lemma Named.decoder {A : Type*} [Primcodable A] (b : A → ℕ) (hb : Computable b)
    (hbase : ∀ x, 2 ≤ b x) {f : A → ℝ} (hf : Named f) :
    Named (fun x => Profiles.decoder (b x) (f x)) := by
  let L (x : A) : ℚ := Quantitative.decoderBound (b x) 1
  have hL : Computable L := Arithmetic.rat_natCast.to_comp.comp
    (decoderBound.to_comp.comp hb (Computable.const 1))
  have hg : Named (fun z : A × ℚ => Profiles.decoder (b z.1) (z.2 : ℝ)) :=
    Named.comp (g := fun z : A × ℚ => (b z.1, z.2)) decoder_named
      ((hb.comp Computable.fst).pair Computable.snd)
  have hlip (a : A) (x y : ℝ) : |Profiles.decoder (b a) x - Profiles.decoder (b a) y| ≤
      (L a : ℝ) * |x-y| := by
    simpa only [L, Rat.cast_natCast] using jet_one_lipschitz (Profiles.decoder_smooth _ (hbase a))
      (Quantitative.decoderBound (b a) 1) (Quantitative.decoder_jet_bound (b a) (hbase a) 1) x y
  exact Named.apply_lipschitz (fun x => Profiles.decoder (b x)) L hL
    (fun _ => Nat.cast_nonneg _) hlip hg hf

end AlternatingNS.Effective

end DecoderNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/RecursiveBounds.lean =====
namespace OAI

section RecursiveBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma nat_sum_range {A : Type*} [Primcodable A] {f : A → ℕ → ℕ} (hf : Computable₂ f) :
    Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hs : Computable₂ (fun a : A => fun z : ℕ × ℕ => z.2 + f a z.1) :=
    Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
  have h := Computable.nat_rec (Computable.snd : Computable (fun z : A × ℕ => z.2))
    (Computable.const (0 : ℕ))
    (hs.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  refine h.to₂.of_eq ?_
  rintro ⟨a,n⟩
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]

def Scaled {A E F : Type*} [Primcodable A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : A → ℕ → ℝ) (f : A → ℕ → E → F) : Prop :=
  (∀ a n, ContDiff ℝ ∞ (f a n)) ∧ ∃ B : A × ℕ → ℕ, Computable B ∧
    ∀ a r n x, ‖iteratedFDeriv ℝ r (f a n) x‖ ≤ (B (a,r) : ℝ) * s a n ^ r

variable {A A' E F G : Type*} [Primcodable A] [Primcodable A']
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma Scaled.congr {s : A → ℕ → ℝ} {f g : A → ℕ → E → F} (hf : Scaled s f)
    (he : ∀ a n x, f a n x = g a n x) : Scaled s g := by
  rwa [← show f = g from funext (fun a => funext (fun n => funext (he a n)))]

lemma Scaled.param {s : A → ℕ → ℝ} {f : A → ℕ → E → F} (hf : Scaled s f)
    (g : A' → A) (hg : Computable g) : Scaled (fun a => s (g a)) (fun a => f (g a)) := by
  obtain ⟨hf,B,hB,h⟩ := hf
  exact ⟨fun a n => hf (g a) n, fun z => B (g z.1,z.2),
    hB.comp ((hg.comp Computable.fst).pair Computable.snd), fun a => h (g a)⟩

lemma Scaled.const {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) (f : A → ℕ → F)
    (B : A → ℕ) (hB : Computable B) (h : ∀ a n, ‖f a n‖ ≤ B a) :
    Scaled s (fun a n (_ : E) => f a n) := by
  refine ⟨fun _ _ => contDiff_const, fun z => B z.1, hB.comp Computable.fst, ?_⟩
  intro a r n x
  cases r with
  | zero => simpa using h a n
  | succ r =>
    rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _)

lemma Scaled.add {s : A → ℕ → ℝ} {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x + g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => (sf a n).add (sg a n), fun z => Bf z + B z,
    Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  push_cast
  exact (norm_add_le _ _).trans (by linarith [hfa a r n x, hgb a r n x])

lemma Scaled.sub {s : A → ℕ → ℝ} {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x - g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => (sf a n).sub (sg a n), fun z => Bf z + B z,
    Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  rw [fun_iteratedFDeriv_sub_apply ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  push_cast
  exact (norm_sub_le _ _).trans (by linarith [hfa a r n x, hgb a r n x])

lemma Scaled.smul {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) (c : A → ℕ → ℝ) (B : A → ℕ) (hB : Computable B)
    (hc : ∀ a n, |c a n| ≤ B a) : Scaled s (fun a n x => c a n • f a n x) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => contDiff_const.smul (sf a n), fun z => B z.1 * C z,
    Primrec.nat_mul.to_comp.comp (hB.comp Computable.fst) hC, fun a r n x => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' ((sf a n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul, Real.norm_eq_abs]
  push_cast
  calc
    _ ≤ (B a : ℝ) * ((C (a,r) : ℝ) * s a n ^ r) := by gcongr; exact hc a n; exact hfC a r n x
    _ = _ := by ring

lemma Scaled.mul {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f g : A → ℕ → E → ℝ}
    (hf : Scaled s f) (hg : Scaled s g) : Scaled s (fun a n x => f a n x * g a n x) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  let C (z : A × ℕ) := ∑ i ∈ Finset.range (z.2+1), z.2.choose i * Bf (z.1,i) * B (z.1,z.2-i)
  have hi : Computable₂ (fun z : A × ℕ => fun i : ℕ => z.2.choose i * Bf (z.1,i) * B (z.1,z.2-i)) :=
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp
        (choose.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
        (hA.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)))
      (hB.comp ((Computable.fst.comp Computable.fst).pair
        (Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  have hC : Computable C := (nat_sum_range hi).comp Computable.id
    (Computable.succ.comp Computable.snd)
  refine ⟨fun a n => (sf a n).mul (sg a n), C, hC, fun a r n x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le (sf a n) (sg a n) x
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r+1),
          (r.choose i : ℝ) * (Bf (a,i) * s a n ^ i) * (B (a,r-i) * s a n ^ (r-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _))
      · exact hfa a i n x
      · exact hgb a (r-i) n x
    _ = _ := by
      simp only [C, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by simpa using Finset.mem_range.mp hi
      rw [show (r.choose i : ℝ) * (Bf (a,i) * s a n ^ i) * (B (a,r-i) * s a n ^ (r-i)) =
        (r.choose i * Bf (a,i) * B (a,r-i)) * (s a n ^ i * s a n ^ (r-i)) by ring,
        ← pow_add, Nat.add_sub_of_le hir]

lemma Scaled.ite {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f g : A → ℕ → E → F}
    (hf : Scaled s f) (hg : Scaled s g) (p : A → ℕ → Prop) [DecidableRel p] :
    Scaled s (fun a n => if p a n then f a n else g a n) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  refine ⟨fun a n => by dsimp only; split_ifs <;> [exact sf a n; exact sg a n],
    fun z => Bf z + B z, Primrec.nat_add.to_comp.comp hA hB, fun a r n x => ?_⟩
  dsimp only
  split_ifs
  · exact (hfa a r n x).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) (pow_nonneg (hs a n) _))
  · exact (hgb a r n x).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) (pow_nonneg (hs a n) _))

lemma Scaled.sum_range {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n)
    {f : (A × ℕ) → ℕ → E → F} (hf : Scaled (fun a => s a.1) f)
    (N : A → ℕ) (hN : Computable N) : Scaled s (fun a n x => ∑ i ∈ Finset.range (N a), f (a,i) n x) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  have hi : Computable₂ (fun z : A × ℕ => fun i : ℕ => B ((z.1,i),z.2)) :=
    hB.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))
  refine ⟨fun a n => ContDiff.sum fun i _ => sf (a,i) n,
    fun z => ∑ i ∈ Finset.range (N z.1), B ((z.1,i),z.2),
    (nat_sum_range hi).comp Computable.id (hN.comp Computable.fst), fun a r n x => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((sf (a,i) n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
  apply (norm_sum_le _ _).trans
  simp only [Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => hfB (a,i) r n x)

lemma Scaled.comp {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) {g : A → F → G} (hg : Scaled (fun _ _ => 1) (fun a _ => g a)) :
    Scaled s (fun a n => g a ∘ f a n) := by
  obtain ⟨sf,Bf,hA,hfa⟩ := hf
  obtain ⟨sg,B,hB,hgb⟩ := hg
  let C (z : A × ℕ) := ∑ i ∈ Finset.range (z.2+1), B (z.1,i)
  let D (z : A × ℕ) := 1 + ∑ i ∈ Finset.range (z.2+1), Bf (z.1,i)
  have hC : Computable C := (nat_sum_range hB.to₂).comp Computable.fst
    (Computable.succ.comp Computable.snd)
  have hD : Computable D := Primrec.nat_add.to_comp.comp (Computable.const 1)
    ((nat_sum_range hA.to₂).comp Computable.fst (Computable.succ.comp Computable.snd))
  refine ⟨fun a n => (sg a 0).comp (sf a n), fun z => z.2.factorial * C z * D z ^ z.2,
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (factorial.to_comp.comp Computable.snd) hC)
      (nat_pow.to_comp.comp hD Computable.snd), fun a r n x => ?_⟩
  have hDone : (1 : ℝ) ≤ D (a,r) := by dsimp [D]; exact_mod_cast Nat.le_add_right 1 _
  have h := norm_iteratedFDeriv_comp_le (sg a 0) (sf a n)
    (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞) x
    (C := (C (a,r) : ℝ)) (D := (D (a,r) : ℝ) * s a n) ?_ ?_
  · simpa only [Nat.cast_mul, Nat.cast_pow, mul_pow, mul_assoc] using h
  · intro i hi
    have hle : B (a,i) ≤ C (a,r) := Finset.single_le_sum (s := Finset.range (r+1)) (f := fun i => B (a,i)) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
    have ht : ‖iteratedFDeriv ℝ i (g a) (f a n x)‖ ≤ (B (a,i) : ℝ) := by simpa using hgb a i 0 (f a n x)
    exact ht.trans (by exact_mod_cast hle)
  · intro i hi hir
    have hai : (Bf (a,i) : ℝ) ≤ D (a,r) := by
      have h := Finset.single_le_sum (s := Finset.range (r+1)) (f := fun i => Bf (a,i))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : i < r+1))
      exact_mod_cast (by dsimp [D]; omega : Bf (a,i) ≤ D (a,r))
    have hai' := hai.trans (le_self_pow₀ hDone (by omega : i ≠ 0))
    calc
      _ ≤ (Bf (a,i) : ℝ) * s a n ^ i := hfa a i n x
      _ ≤ (D (a,r) : ℝ) ^ i * s a n ^ i := mul_le_mul_of_nonneg_right hai' (pow_nonneg (hs a n) _)
      _ = _ := (mul_pow _ _ _).symm

lemma Scaled.comp_linear {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled s f) (L : A → ℕ → G →L[ℝ] E) (B : A → ℕ) (hB : Computable B)
    (hL : ∀ a n, ‖L a n‖ ≤ B a) : Scaled s (fun a n => f a n ∘ L a n) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => (sf a n).comp (L a n).contDiff, fun z => C z * B z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp hC (nat_pow.to_comp.comp (hB.comp Computable.fst) Computable.snd),
    fun a r n x => ?_⟩
  apply (Bounds.norm_comp_linear (f a n) (sf a n) (L a n) r x).trans
  push_cast
  calc
    _ ≤ ((C (a,r) : ℝ) * s a n ^ r) * (B a : ℝ) ^ r := by
      gcongr
      · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hs a n) _)
      · exact hfC a r n _
      · exact hL a n
    _ = _ := by ring

lemma Scaled.comp_scaled_linear {s : A → ℕ → ℝ} (_ : ∀ a n, 0 ≤ s a n) {f : A → E → F}
    (hf : Scaled (fun _ _ => 1) (fun a _ => f a))
    (L : A → ℕ → G →L[ℝ] E) (hL : ∀ a n, ‖L a n‖ ≤ s a n) :
    Scaled s (fun a n => f a ∘ L a n) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨fun a n => (sf a 0).comp (L a n).contDiff, B,hB, fun a r n x => ?_⟩
  apply (Bounds.norm_comp_linear (f a) (sf a 0) (L a n) r x).trans
  apply mul_le_mul (by simpa using hfB a r 0 (L a n x)) (pow_le_pow_left₀ (norm_nonneg _) (hL a n) _)
    (by positivity) (by positivity)

lemma Scaled.fixed {s : A → ℕ → ℝ} (hs : ∀ a n, 1 ≤ s a n) {f : A → E → F}
    (hf : Scaled (fun _ _ => 1) (fun a _ => f a)) : Scaled s (fun a _ => f a) := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨sf,B,hB,fun a r n x => ?_⟩
  have h : ‖iteratedFDeriv ℝ r (f a) x‖ ≤ (B (a,r) : ℝ) := by simpa using hfB a r n x
  exact h.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (hs a n)))

end AlternatingNS.Effective

end RecursiveBoundsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/ConstructiveBounds.lean =====
namespace OAI

section ConstructiveBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma Scaled.nat {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    (c : A → ℕ) (hc : Computable c) : Scaled s (fun a _ (_ : ℝ) => (c a : ℝ)) :=
  Scaled.const hs _ c hc (by intro a n; simp)

lemma Scaled.cmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → ℝ}
    (hf : Scaled s f) (c : ℝ) (B : ℕ) (hc : |c| ≤ B) :
    Scaled s (fun a n x => c * f a n x) :=
  hf.smul hs (fun _ _ => c) (fun _ => B) (Computable.const B) (fun _ _ => hc)

lemma Scaled.affine {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    {f : A → ℝ → ℝ} (hf : Scaled (fun _ _ => 1) (fun a _ => f a))
    (c d : A → ℕ → ℝ) (B : A → ℕ) (hB : Computable B)
    (hc : ∀ a n, |c a n| ≤ (B a : ℝ) * s a n) :
    Scaled s (fun a n x => f a (c a n * x + d a n)) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => (sf a 0).comp (contDiff_const.mul contDiff_id |>.add contDiff_const),
    fun z => C z * B z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp hC (nat_pow.to_comp.comp (hB.comp Computable.fst) Computable.snd),
    fun a r n x => ?_⟩
  change ‖iteratedFDeriv ℝ r ((fun y => f a (y + d a n)) ∘
    (c a n • ContinuousLinearMap.id ℝ ℝ)) x‖ ≤ _
  apply (Bounds.norm_comp_linear _ ((sf a 0).comp (contDiff_id.add contDiff_const)) _ r x).trans
  change ‖iteratedFDeriv ℝ r (fun y => f a (y + d a n)) (c a n * x)‖ *
    ‖c a n • ContinuousLinearMap.id ℝ ℝ‖ ^ r ≤ _
  rw [iteratedFDeriv_comp_add_right]
  simp only [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
  push_cast
  calc
    _ ≤ (C (a,r) : ℝ) * ((B a : ℝ) * s a n) ^ r := by
      rw [mul_comm, mul_comm (C (a,r) : ℝ)]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hc a n) r)
        (by simpa using hfC a r 0 (c a n * x + d a n)) (norm_nonneg _)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (hs a n)) r)
    _ = _ := by ring

lemma transition_scaled : Scaled (fun _ : Unit => fun _ => 1)
    (fun _ _ => Real.smoothTransition) :=
  ⟨fun _ _ => Real.smoothTransition.contDiff, fun z => Quantitative.transitionBound z.2,
    transitionBound.to_comp.comp Computable.snd, by intro _ r n x; simpa using Quantitative.transition_jet_bound r x⟩

lemma selector_scaled (b a : A → ℕ) (hB : Computable b) :
    Scaled (fun _ _ => 1) (fun p _ => Profiles.selector (b p) (a p)) := by
  have hT := transition_scaled.param (fun _ : A => ()) (Computable.const ())
  have h₁ := hT.affine (fun _ _ => zero_le_one) (fun p _ => 8 * (b p : ℝ))
    (fun p _ => 2 - 16 * (a p : ℝ)) (fun p => 8 * b p)
    (Primrec.nat_mul.to_comp.comp (Computable.const 8) hB) (by intro p n; simp)
  have h₂ := hT.affine (fun _ _ => zero_le_one) (fun p _ => -(8 * (b p : ℝ)))
    (fun p _ => 16 * (a p : ℝ) + 10) (fun p => 8 * b p)
    (Primrec.nat_mul.to_comp.comp (Computable.const 8) hB) (by intro p n; simp)
  exact (h₁.mul (fun _ _ => zero_le_one) h₂).congr (by intros; dsimp [Profiles.selector]; congr 2 <;> ring)

lemma decoder_scaled : Scaled (fun _ : Machine => fun _ => 1)
    (fun M _ => Profiles.decoder M.base) := by
  refine ⟨fun M _ => Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega),
    fun z => Quantitative.decoderBound z.1.base z.2,
    decoderBound.to_comp.comp (base.to_comp.comp Computable.fst) Computable.snd, ?_⟩
  intro M r n x
  simp only [one_pow, mul_one]
  exact Quantitative.decoder_jet_bound M.base (by have := M.base_ge_four; omega) r x

lemma read_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M)
    (k : A → ℕ → ℕ) (hk : ∀ a n, k a n ≤ Scales.s (N a) n + 1 + Scales.K (N a) n) :
    Scaled (fun a => Bounds.readScale (M a) (N a))
      (fun a n D => Profiles.decoder (M a).base (((M a).base : ℝ) ^ k a n * D)) := by
  apply (decoder_scaled.param M hM).comp_scaled_linear (fun a => Bounds.readScale_nonneg _ _)
    (fun a n => ((M a).base : ℝ) ^ k a n • ContinuousLinearMap.id ℝ ℝ)
  intro a n
  have hb : (1 : ℝ) ≤ (M a).base := by have := (M a).base_ge_four; exact_mod_cast (by omega : 1 ≤ (M a).base)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hb) _),
    ContinuousLinearMap.norm_id, mul_one, Bounds.readScale] using pow_le_pow_right₀ hb (hk a n)

lemma readC_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readC (M a) (N a)) :=
  read_scaled M N hM (fun a => Scales.s (N a)) (by intros; omega)

lemma readB_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readB (M a) (N a)) :=
  read_scaled M N hM _ (by intros; rfl)

lemma readA_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readA (M a) (N a)) :=
  (read_scaled M N hM (fun a n => Scales.s (N a) n + 1) (by intros; omega)).sub
    ((readB_scaled M N hM).smul (fun a => Bounds.readScale_nonneg _ _) _
      (fun _ => 1) (Computable.const 1) (fun a n => by simpa using Bounds.inverse_power_bound (M a) (Scales.K (N a) n)))

lemma updates_scaled (M : A → Machine) (N a l : A → ℕ) (r : A → Rule)
    (hM : Computable M) (ha : Computable a) (hl : Computable l) (hr : Computable r) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.updateLeft (M p).base (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) ∧
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.updateRight (M p).base (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  let s := fun p => Bounds.readScale (M p) (N p)
  have hs : ∀ p n, 0 ≤ s p n := fun p => Bounds.readScale_nonneg _ _
  have hhA := readA_scaled M N hM
  have hhB := readB_scaled M N hM
  have cb := base.to_comp.comp hM
  have hrw := Computable.fst.comp (Computable.snd.comp hr)
  have hb (p : A) (n : ℕ) : |((M p).base : ℝ)| ≤ ((M p).base : ℝ) := by simp
  have hdiv {f : A → ℕ → ℝ → ℝ} (hf : Scaled s f) :
      Scaled s (fun p n D => f p n D / (M p).base) := by
    have h := hf.smul hs (fun p _ => ((M p).base : ℝ)⁻¹) (fun _ => 1) (Computable.const 1)
      (fun p _ => by simpa using Bounds.inverse_power_bound (M p) 1)
    exact h.congr (by intros; simp [div_eq_mul_inv, mul_comm])
  have h2l := Scaled.nat hs (fun p => 2 * l p) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hl)
  have h2a := Scaled.nat hs (fun p => 2 * a p) (Primrec.nat_mul.to_comp.comp (Computable.const 2) ha)
  have h2w := Scaled.nat hs (fun p => 2 * (r p).2.1) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hrw)
  have hLeft := ((hhA.smul hs (fun p _ => ((M p).base : ℝ)) (fun p => (M p).base) cb hb).sub h2l).ite hs
    (hhA.ite hs (hdiv (h2w.add hhA)) (fun p _ => (r p).2.2 = 1)) (fun p _ => (r p).2.2 = 0)
  have hR := (hhB.smul hs (fun p _ => ((M p).base : ℝ)) (fun p => (M p).base) cb hb).sub h2a
  have hRight := (hdiv (h2l.add (hdiv (h2w.add hR)))).ite hs
    ((hdiv (h2w.add hR)).ite hs hR (fun p _ => (r p).2.2 = 1)) (fun p _ => (r p).2.2 = 0)
  constructor
  · exact hLeft.congr (by intro p n x; dsimp [LocalRule.updateLeft]; push_cast; split_ifs <;> rfl)
  · exact hRight.congr (by intro p n x; dsimp [LocalRule.updateRight]; push_cast; split_ifs <;> rfl)

lemma branchNumerator_scaled (M : A → Machine) (N a l : A → ℕ) (r : A → Rule)
    (hM : Computable M) (ha : Computable a) (hl : Computable l) (hr : Computable r) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.branchNumerator (M p).base (Scales.K (N p) (n+1)) (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  obtain ⟨hl',hr'⟩ := updates_scaled M N a l r hM ha hl hr
  exact ((Scaled.nat hs (fun p => 2 * (r p).1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp hr))).add hl').add
    (hr'.smul hs (fun p n => (((M p).base : ℝ) ^ Scales.K (N p) (n+1))⁻¹)
      (fun _ => 1) (Computable.const 1) (fun p n => by simpa using Bounds.inverse_power_bound (M p) (Scales.K (N p) (n+1))))

attribute [local irreducible] LocalRule.readA LocalRule.readB LocalRule.readC
  Profiles.selector LocalRule.branchNumerator

lemma branch_scaled (M : A → Machine) (N q a : A → ℕ)
    (hM : Computable M) (hq : Computable q) (ha : Computable a) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.branch (M p) (N p) n (q p) (a p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  let r := fun p => (M p).command (q p) (a p)
  have hr : Computable r := command.to_comp.comp (hM.pair (hq.pair ha))
  have hb := base.to_comp.comp hM
  have hread := (readA_scaled M N hM).param
    (Prod.fst : A × ℕ → A) Computable.fst
  have hout : Scaled (fun _ : A × ℕ => fun _ => (1:ℝ)) (fun p _ => Profiles.selector (M p.1).base p.2) := selector_scaled (fun p : A × ℕ => (M p.1).base) Prod.snd (hb.comp Computable.fst)
  have hsel : Scaled (fun p : A × ℕ => Bounds.readScale (M p.1) (N p.1))
      (fun p n => Profiles.selector (M p.1).base p.2 ∘ LocalRule.readA (M p.1) (N p.1) n) :=
    Scaled.comp (A := A × ℕ) (E := ℝ) (F := ℝ) (G := ℝ)
      (s := fun p => Bounds.readScale (M p.1) (N p.1))
      (f := fun p => LocalRule.readA (M p.1) (N p.1))
      (g := fun p => Profiles.selector (M p.1).base p.2) (fun p => hs p.1) hread hout
  have hnum := branchNumerator_scaled (fun p : A × ℕ => M p.1) (fun p => N p.1)
    (fun p => a p.1) Prod.snd (fun p => r p.1) (hM.comp Computable.fst)
    (ha.comp Computable.fst) Computable.snd (hr.comp Computable.fst)
  let S := fun (p : A × ℕ) n => Profiles.selector (M p.1).base p.2 ∘ LocalRule.readA (M p.1) (N p.1) n
  let V := fun (p : A × ℕ) n D => LocalRule.branchNumerator (M p.1).base (Scales.K (N p.1) (n+1)) (a p.1) p.2 (r p.1)
    (LocalRule.readA (M p.1) (N p.1) n D) (LocalRule.readB (M p.1) (N p.1) n D)
  have hprod : Scaled (fun p : A × ℕ => Bounds.readScale (M p.1) (N p.1)) (fun p n D => S p n D * V p n D) :=
    Scaled.mul (A := A × ℕ) (E := ℝ) (s := fun p => Bounds.readScale (M p.1) (N p.1)) (f := S) (g := V) (fun p => hs p.1) hsel hnum
  have hsum := hprod.sum_range hs
    (fun p => (M p).alphabet) (alphabet.to_comp.comp hM)
  exact (hsum.ite hs (branchNumerator_scaled M N a (fun _ => 0) r hM ha (Computable.const 0) hr)
    (fun p _ => (r p).2.2 = 0)).congr (by intros; simp only [LocalRule.branch, S, V, r, Function.comp_apply, ite_apply])

attribute [local irreducible] LocalRule.branch

lemma writeCore_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => Bounds.writeCore p.1 p.2) := by
  let A := ((Machine × ℕ) × ℕ) × ℕ
  let M := fun p : A => p.1.1.1
  let N := fun p : A => p.1.1.2
  let q := fun p : A => p.1.2
  let a := fun p : A => p.2
  have hM : Computable M := Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hq : Computable q := Computable.snd.comp Computable.fst
  have ha : Computable a := Computable.snd
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  have hC := (readC_scaled M N hM).comp (A := A) (E := ℝ) (F := ℝ) (G := ℝ) (s := fun p => Bounds.readScale (M p) (N p)) (g := fun p => Profiles.selector (M p).base (q p)) hs (selector_scaled (fun p => (M p).base) q (base.to_comp.comp hM))
  have hB := (readB_scaled M N hM).comp (A := A) (E := ℝ) (F := ℝ) (G := ℝ) (s := fun p => Bounds.readScale (M p) (N p)) (g := fun p => Profiles.selector (M p).base (a p)) hs (selector_scaled (fun p => (M p).base) a (base.to_comp.comp hM))
  have hsum := ((hC.mul (E := ℝ) hs hB).mul (E := ℝ) hs (branch_scaled M N q a hM hq ha)).sum_range
    (fun p : (Machine × ℕ) × ℕ => Bounds.readScale_nonneg p.1.1 p.1.2)
    (fun p => p.1.1.alphabet) (alphabet.to_comp.comp (Computable.fst.comp Computable.fst))
  have hsum' := hsum.sum_range (fun p : Machine × ℕ => Bounds.readScale_nonneg p.1 p.2)
    (fun p => p.1.states + 1) (Computable.succ.comp (states.to_comp.comp Computable.fst))
  exact (hsum'.smul (A := Machine × ℕ) (E := ℝ) (F := ℝ) (fun p => Bounds.readScale_nonneg p.1 p.2) (fun p _ => 1 / (p.1.base : ℝ))
    (fun _ => 1) (Computable.const 1) (fun p _ => by simpa using Bounds.inverse_power_bound p.1 1)).congr
    (by intros; rfl)

lemma haltWeight_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => LocalRule.haltWeight p.1 p.2) := by
  have hs := fun p : (Machine × ℕ) × ℕ => Bounds.readScale_nonneg p.1.1 p.1.2
  have h := (readC_scaled (fun p : (Machine × ℕ) × ℕ => p.1.1) (fun p => p.1.2)
    (Computable.fst.comp Computable.fst)).comp (A := (Machine × ℕ) × ℕ) (s := fun p => Bounds.readScale p.1.1 p.1.2) (E := ℝ) (F := ℝ) (G := ℝ) (g := fun p : (Machine × ℕ) × ℕ => Profiles.selector p.1.1.base p.2) hs
    (selector_scaled (fun p : (Machine × ℕ) × ℕ => p.1.1.base) Prod.snd (base.to_comp.comp (Computable.fst.comp Computable.fst)))
  have hzero : Scaled (fun p : (Machine × ℕ) × ℕ => Bounds.readScale p.1.1 p.1.2)
      (fun _ _ (_ : ℝ) => (0 : ℝ)) := Scaled.const hs _ (fun _ => 0) (Computable.const 0) (by intros; simp)
  have hi := (h.ite (A := (Machine × ℕ) × ℕ) (E := ℝ) (F := ℝ) hs hzero (fun p _ => p.2 = p.1.1.states ∨ p.2 ∈ p.1.1.haltingStates)).sum_range (A := Machine × ℕ) (E := ℝ) (F := ℝ)
    (fun p => Bounds.readScale_nonneg p.1 p.2) (fun p => p.1.states + 1)
    (Computable.succ.comp (states.to_comp.comp Computable.fst))

  exact hi.congr (by intros; simp only [LocalRule.haltWeight, Function.comp_apply, ite_apply])

lemma Scaled.coord {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    {f : A → ℕ → ℝ → ℝ} (hf : Scaled s f) (idx : A → ℕ → Fin 3) :
    Scaled s (fun a n (x : Space) => f a n (x (idx a n))) := by
  apply hf.comp_linear (E := ℝ) (F := ℝ) (G := Space) hs
    (fun a n => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (idx a n))
    (fun _ => 1) (Computable.const 1)
  intro a n
  simp only [Nat.cast_one]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, PiLp.proj_apply] using PiLp.norm_apply_le x (idx a n)

lemma cutoff_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ _ => Spatial.cutoff) := by
  have h₁ := transition_scaled.affine (fun _ _ => zero_le_one)
    (fun _ _ => -1) (fun _ _ => 3) (fun _ => 1) (Computable.const 1) (by intros; norm_num)
  have h₂ := transition_scaled.affine (fun _ _ => zero_le_one)
    (fun _ _ => 1) (fun _ _ => 3) (fun _ => 1) (Computable.const 1) (by intros; norm_num)
  have h := h₁.mul (E := ℝ) (fun _ _ => zero_le_one) h₂
  have hi (i : Fin 3) := h.coord (fun _ _ => zero_le_one) (fun _ _ => i)
  exact (((hi 0).mul (E := Space) (fun _ _ => zero_le_one) (hi 1)).mul
    (E := Space) (fun _ _ => zero_le_one) (hi 2)).congr
    (by intro p n x; simp [Spatial.cutoff, Fin.prod_univ_succ, mul_assoc, sub_eq_add_neg,
      add_comm])

lemma coord_jet_on_box (i : Fin 3) (r : ℕ) (x : Space) (hx : x ∈ Spatial.box) :
    ‖iteratedFDeriv ℝ r (fun x : Space => x i) x‖ ≤ 3 := by
  cases r with
  | zero => simpa using hx i
  | succ r =>
    let L := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i
    have hd : fderiv ℝ (fun x : Space => x i) = fun _ => L := by
      funext x; exact (Spatial.coord_hasFDeriv i x).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hd]
    cases r with
    | zero =>
      simp only [norm_iteratedFDeriv_zero]
      have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        (fun y => by simpa only [L, PiLp.proj_apply, one_mul] using PiLp.norm_apply_le y i)
      linarith
    | succ r => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply, norm_zero]; norm_num

lemma cutoff_coordinate_scaled (idx : A → ℕ → Fin 3) :
    Scaled (fun _ _ => 1) (fun a n (x : Space) => Spatial.cutoff x * x (idx a n)) := by
  obtain ⟨_,B,hB,hcut⟩ := cutoff_scaled
  have hc : Computable (fun r => B ((),r)) := hB.comp ((Computable.const ()).pair Computable.id)
  let C := fun r => ∑ i ∈ Finset.range (r+1), r.choose i * B ((),i) * 3
  have hi : Computable₂ (fun r i : ℕ => r.choose i * B ((),i) * 3) :=
    Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp Computable.fst Computable.snd) (hc.comp Computable.snd)) (Computable.const 3)
  have hC : Computable C := (nat_sum_range hi).comp Computable.id Computable.succ
  refine ⟨fun a n => Spatial.cutoff_smooth.mul (Spatial.coord_smooth (idx a n)),
    fun z => C z.2, hC.comp Computable.snd, fun a r n x => ?_⟩
  simp only [one_pow, mul_one]
  by_cases hx : x ∈ Spatial.box
  · apply (norm_iteratedFDeriv_mul_le Spatial.cutoff_smooth (Spatial.coord_smooth (idx a n)) x
      (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
    simp only [C, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by simpa using hcut () i 0 x) (Nat.cast_nonneg _))
      (coord_jet_on_box _ _ _ hx) (norm_nonneg _) (by positivity)
  · have hn : x ∉ tsupport (fun x : Space => Spatial.cutoff x * x (idx a n)) :=
      fun h => hx (Spatial.cutoff_support (tsupport_mul_subset_left h))
    rw [image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_iteratedFDeriv_subset r h)), norm_zero]
    positivity

lemma fixedPotential_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ => Bounds.fixedPotential) :=
  ((cutoff_coordinate_scaled (fun _ : Unit => Construction.receiverIndex)).cmul
    (fun _ _ => zero_le_one) (-1) 1 (by norm_num)).congr (by intros; simp [Bounds.fixedPotential])

lemma Scaled.grow {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : A → ℕ → ℝ} (hs : ∀ a n, 1 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled (fun _ _ => 1) f) : Scaled s f := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨sf,B,hB,fun a r n x => ?_⟩
  have h : ‖iteratedFDeriv ℝ r (f a n) x‖ ≤ (B (a,r) : ℝ) := by simpa using hfB a r n x
  exact h.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (hs a n)))

lemma corePotential_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => Bounds.corePotential p.1 p.2) := by
  have hs := fun p : Machine × ℕ => Bounds.readScale_nonneg p.1 p.2
  have h (idx : (Machine × ℕ) → ℕ → Fin 3) :=
    (cutoff_coordinate_scaled idx).grow (A := Machine × ℕ) (E := Space) (F := ℝ) (s := fun p => Bounds.readScale p.1 p.2) (fun p => Bounds.readScale_ge_one p.1 p.2)
  have hw := writeCore_scaled.coord hs (fun _ => Construction.donorIndex)
  have hh := (haltWeight_scaled.coord hs (fun _ => Construction.donorIndex)).cmul hs 2 2 (by norm_num)
  exact ((h (fun _ _ => 0)).mul (E := Space) hs hw).sub
    ((h (fun _ => Construction.receiverIndex)).mul (E := Space) hs hh)

end AlternatingNS.Effective

end ConstructiveBoundsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/InitialNames.lean =====
namespace OAI

section InitialNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

def ratCode (b : ℕ) (ds : List ℕ) : ℚ :=
  ds.foldr (fun (d : ℕ) (q : ℚ) => ((d : ℚ) + q) / b) 0

lemma ratCode_cast (b : ℕ) (ds : List ℕ) :
    (ratCode b ds : ℝ) = Encoding.code b ds := by
  induction ds with
  | nil => simp [ratCode, Encoding.code]
  | cons d ds ih => simp only [ratCode, List.foldr_cons, Rat.cast_div, Rat.cast_add,
      Rat.cast_natCast, Encoding.code] at *; rw [ih]

lemma ratCode_primrec : Primrec₂ ratCode :=
  Primrec.list_foldr Primrec.snd (Primrec.const 0)
    ((Arithmetic.rat_div.comp (Arithmetic.rat_add.comp
      (Arithmetic.rat_natCast.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
      (Arithmetic.rat_natCast.comp (Primrec.fst.comp Primrec.fst)))).to₂

lemma digits_eq_map (K : ℕ) (f : ℕ → ℕ) :
    Encoding.digits K f = (List.range K).map f := by
  induction K generalizing f with
  | zero => simp [Encoding.digits]
  | succ K ih => rw [Encoding.digits_succ, ih, List.range_succ_eq_map]; simp only [List.map_cons,
      List.map_map, Function.comp_def, Nat.succ_eq_add_one]

lemma initial_digits_primrec : Primrec (fun z : Machine × List ℕ => z.1.recordedDigits z.2 0) := by
  have hK : Primrec (fun z : Machine × List ℕ => Scales.K z.2.length 0) :=
    capacity.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)
  have hL : Primrec (fun z : Machine × List ℕ => (List.range (Scales.K z.2.length 0)).map (fun _ : ℕ => 0)) := Primrec.list_map (Primrec.list_range.comp hK) (Primrec.const (0 : ℕ)).to₂
  have hR : Primrec (fun z : Machine × List ℕ => (List.range (Scales.K z.2.length 0)).map (fun j : ℕ => 2 * z.2[j]?.getD 0)) := Primrec.list_map (Primrec.list_range.comp hK)
    ((Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
        Primrec.snd) (Primrec.const 0)))).to₂
  refine (Primrec.list_cons.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (initialState.comp Primrec.fst))
    (Primrec.list_append.comp hL hR)).of_eq ?_
  intro z
  simp only [Machine.recordedDigits, Machine.run, Function.iterate_zero, id_eq, Machine.initial,
    digits_eq_map]
  congr 1
  apply congrArg₂ List.append
  · apply List.map_congr_left; intro j hj
    have h : ¬ (0 : ℤ) ≤ 0 - ((j : ℤ) + 1) := by omega
    simp [Machine.leftDigits]; omega
  · apply List.map_congr_left; intro j hj
    simp [Machine.rightDigits]

def initialBlock (M : Machine) (w : List ℕ) : ℚ := ratCode M.base (M.recordedDigits w 0)

lemma initialBlock_primrec : Primrec₂ initialBlock :=
  ratCode_primrec.comp (base.comp Primrec.fst) initial_digits_primrec

lemma initialBlock_cast (M : Machine) (w : List ℕ) :
    (initialBlock M w : ℝ) = M.recordedBlock w 0 := ratCode_cast _ _

lemma epsilon_named : Named (fun z : (Machine × ℕ) × ℕ => Scales.ε z.1.1.base z.1.2 z.2) := by
  have h := Named.rational (Arithmetic.rat_inv.to_comp.comp
    (Arithmetic.rat_pow.to_comp.comp
      (Arithmetic.rat_natCast.to_comp.comp (base.to_comp.comp (Computable.fst.comp Computable.fst)))
      (exponent.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  exact h.congr (by intros; simp only [Scales.ε, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast])

lemma loadingPotential_scaled : Scaled (fun _ : Machine × List ℕ => fun _ => 1)
    (fun z _ (x : Space) => Spatial.cutoff x *
      Spatial.shearPotential 2 1 0 (fun _ => Scales.ε z.1.base z.2.length 0 * z.1.recordedBlock z.2 0)
        (fun _ => 1 - Scales.ε z.1.base z.2.length 0) x) := by
  let B := fun z : Machine × List ℕ => (initialBlock z.1 z.2).num.natAbs
  have hB : Computable B := Arithmetic.int_abs.to_comp.comp
    (Arithmetic.rat_num.to_comp.comp initialBlock_primrec.to_comp)
  have he (z : Machine × List ℕ) : 0 ≤ Scales.ε z.1.base z.2.length 0 ∧
      Scales.ε z.1.base z.2.length 0 ≤ 1 := by
    refine ⟨Scales.ε_nonneg _ _ _ (by have := z.1.base_ge_four; omega), ?_⟩
    simpa [Scales.ε] using (Bounds.inverse_power_bound z.1 (Scales.s z.2.length 0))
  have h₁ := (cutoff_coordinate_scaled (fun _ : Machine × List ℕ => fun _ => (0 : Fin 3))).smul
    (fun _ _ => zero_le_one)
    (fun z _ => Scales.ε z.1.base z.2.length 0 * z.1.recordedBlock z.2 0) B hB (by
      intro z n
      rw [abs_mul, abs_of_nonneg (he z).1, ← initialBlock_cast]
      exact (mul_le_mul_of_nonneg_right (he z).2 (abs_nonneg _)).trans (by
        simpa [B] using abs_rat_cast_le_num (initialBlock z.1 z.2)))
  have h₂ := (cutoff_coordinate_scaled (fun _ : Machine × List ℕ => fun _ => (1 : Fin 3))).smul
    (fun _ _ => zero_le_one) (fun z _ => 1 - Scales.ε z.1.base z.2.length 0)
    (fun _ => 1) (Computable.const 1) (by
      intro z n
      rw [abs_of_nonneg (sub_nonneg.mpr (he z).2)]
      simpa using sub_le_self (1 : ℝ) (he z).1)
  exact (h₁.sub h₂).congr (by intros; dsimp [Spatial.shearPotential]; ring)
end AlternatingNS.Effective

end InitialNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/DecayBounds.lean =====
namespace OAI

section DecayBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding
open Bounds (readScale readScale_nonneg potential_decomposition norm_iterated_curl amplitude norm_comp_linear)

lemma potential_bound : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (fun x => Spatial.cutoff x *
      Spatial.shearPotential (Construction.donorIndex n) (Construction.receiverIndex n) 0
        (LocalRule.write M N n) (LocalRule.signal M N n) x) x‖ ≤
        (C ((M,N),r) : ℝ) * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ r) := by
  obtain ⟨sA, A, cA, ha⟩ := fixedPotential_scaled
  obtain ⟨sB, B, cB, hb⟩ := corePotential_scaled
  refine ⟨fun z => A ((), z.2) + B z,
    Primrec.nat_add.to_comp.comp
      (cA.comp ((Computable.const ()).pair Computable.snd)) cB, fun M N r n x => ?_⟩
  have hA : 0 ≤ (A ((),r) : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ (B ((M,N),r) : ℝ) := Nat.cast_nonneg _
  simp only [Nat.cast_add]
  have hε : 0 ≤ Scales.ε M.base N (n + 1) := Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)
  have hε' : Scales.ε M.base N (n + 1) ≤ Scales.ε M.base N n :=
    (Scales.ε_strictAnti M.base N (by have := M.base_ge_four; omega)).antitone (by omega)
  have h₁ := sA () n
  have h₂ := sB (M,N) n
  simp_rw [potential_decomposition]
  change ‖iteratedFDeriv ℝ r (fun x =>
    (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • Bounds.fixedPotential n x +
      Scales.ε M.base N (n + 1) • Bounds.corePotential M N n x) x‖ ≤ _
  have hs₁ : ContDiff ℝ ∞ (fun x =>
      (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • Bounds.fixedPotential n x) := h₁.const_smul _
  have hs₂ : ContDiff ℝ ∞ (fun x =>
      Scales.ε M.base N (n + 1) • Bounds.corePotential M N n x) := h₂.const_smul _
  rw [fun_iteratedFDeriv_add_apply
    (hs₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hs₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  apply (norm_add_le _ _).trans
  rw [iteratedFDeriv_const_smul_apply' (h₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    iteratedFDeriv_const_smul_apply' (h₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hε'), abs_of_nonneg hε]
  have haa : ‖iteratedFDeriv ℝ r (Bounds.fixedPotential n) x‖ ≤ (A ((),r) : ℝ) := by simpa using ha () r n x
  have hbb := hb (M,N) r n x
  have hscale := pow_nonneg (readScale_nonneg M N n) r
  calc
    _ ≤ Scales.ε M.base N n * (A ((),r) : ℝ) +
      Scales.ε M.base N (n + 1) * ((B ((M,N),r) : ℝ) * readScale M N n ^ r) := by
      exact add_le_add
        (mul_le_mul (by linarith) haa (norm_nonneg _) (by linarith))
        (mul_le_mul_of_nonneg_left hbb hε)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ Scales.ε M.base N n by linarith) hB,
      mul_nonneg hA (mul_nonneg hε hscale)]

lemma slot_estimate : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤
      (C ((M,N),r) : ℝ) * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1)) := by
  obtain ⟨C, hC, hc⟩ := potential_bound
  refine ⟨fun z => 2 * C (z.1,z.2+1),
    Primrec.nat_mul.to_comp.comp (Computable.const 2)
      (hC.comp (Computable.fst.pair (Computable.succ.comp Computable.snd))), fun M N r n x => ?_⟩
  have h := norm_iterated_curl (Construction.receiverIndex n) 0 _
    (Spatial.cutoff_smooth.mul (Spatial.shearPotential_smooth (Construction.donorIndex n)
      (Construction.receiverIndex n) 0 _ _
      (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n))) r x
  apply h.trans
  push_cast
  nlinarith [hc M N (r+1) n x]

def readCost (z : (Machine × ℕ) × ℕ) : ℕ :=
  1 + ∑ n ∈ Finset.range z.2, z.1.1.base ^
    (Scales.s z.1.2 n + (z.2+1) * (Scales.s z.1.2 n + 1 + Scales.K z.1.2 n))

lemma readCost_computable : Computable readCost := by
  have hM : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => z.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hN : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => z.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hs : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => Scales.s z.1.1.2 z.2) := exponent.to_comp.comp hN Computable.snd
  have hK : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => Scales.K z.1.1.2 z.2) := capacity.to_comp.comp hN Computable.snd
  have hp : Computable₂ (fun z : (Machine × ℕ) × ℕ => fun n : ℕ => z.1.1.base ^ (Scales.s z.1.2 n + (z.2+1) * (Scales.s z.1.2 n + 1 + Scales.K z.1.2 n))) := nat_pow.to_comp.comp (base.to_comp.comp hM)
    (Primrec.nat_add.to_comp.comp hs (Primrec.nat_mul.to_comp.comp
      (Computable.succ.comp (Computable.snd.comp Computable.fst))
      (Primrec.nat_add.to_comp.comp (Computable.succ.comp hs) hK)))
  unfold readCost
  exact Primrec.nat_add.to_comp.comp (Computable.const 1)
    ((nat_sum_range hp).comp Computable.id Computable.snd)

lemma uniform_read_cost (M : Machine) (N r n : ℕ) :
    Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1) ≤
      (readCost ((M,N),r) : ℝ) * Scales.ε M.base N n := by
  have hb : (1 : ℝ) ≤ M.base := by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base)
  have hε (n : ℕ) : 0 < Scales.ε M.base N n :=
    Scales.ε_pos _ _ _ (by have := M.base_ge_four; omega)
  have hD : (1 : ℝ) ≤ readCost ((M,N),r) := by
    dsimp [readCost]; push_cast
    exact le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have he : readScale M N n ^ (r + 1) =
      (M.base : ℝ) ^ ((r+1) * (Scales.s N n + 1 + Scales.K N n)) := by
    rw [readScale, ← pow_mul, Nat.mul_comm]
  by_cases hn : n < r
  · have hle : M.base ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)) ≤ readCost ((M,N),r) :=
      (Finset.single_le_sum (f := fun n => M.base ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)).trans (Nat.le_add_left _ _)
    have hpow : ((M.base : ℝ) ^ Scales.s N n) ≠ 0 := ne_of_gt (pow_pos (zero_lt_one.trans_le hb) _)
    calc
      _ ≤ readScale M N n ^ (r+1) := by
        apply mul_le_of_le_one_left (pow_nonneg (readScale_nonneg M N n) _)
        simpa [Scales.ε, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hb) _))] using
          Bounds.inverse_power_bound M (Scales.s N (n+1))
      _ = (M.base : ℝ) ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)) * Scales.ε M.base N n := by
        rw [he, pow_add, Scales.ε]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (hε n).le
  · rw [he]
    exact (Scales.derivative_cost_bound M.base N r n (by have := M.base_ge_four; omega)
      (by omega)).trans (le_mul_of_one_le_left (hε n).le hD)

lemma slot_decay : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤ (C ((M,N),r) : ℝ) * Scales.ε M.base N n := by
  obtain ⟨C,hC,hc⟩ := slot_estimate
  refine ⟨fun z => C z * (1 + readCost z), Primrec.nat_mul.to_comp.comp hC
    (Primrec.nat_add.to_comp.comp (Computable.const 1) readCost_computable), fun M N r n x => ?_⟩
  apply (hc M N r n x).trans
  push_cast
  have h := mul_le_mul_of_nonneg_left (uniform_read_cost M N r n) (Nat.cast_nonneg (C ((M,N),r)) : (0 : ℝ) ≤ _)
  nlinarith

lemma loading_bound : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r x,
    ‖iteratedFDeriv ℝ r (Construction.loading M w) x‖ ≤ C ((M,w),r) := by
  obtain ⟨hs,C,hC,hc⟩ := loadingPotential_scaled
  refine ⟨fun z => 2 * C (z.1,z.2+1), Primrec.nat_mul.to_comp.comp (Computable.const 2)
    (hC.comp (Computable.fst.pair (Computable.succ.comp Computable.snd))), fun M w r x => ?_⟩
  apply (norm_iterated_curl 1 0 _ (hs (M,w) 0) r x).trans
  have h := hc (M,w) (r+1) 0 x
  simp only [one_pow, mul_one] at h
  push_cast
  linarith

lemma piece_decay : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r n x,
    ‖iteratedFDeriv ℝ r (Construction.piece M w n) x‖ ≤ (C ((M,w),r) : ℝ) * amplitude M w.length n := by
  obtain ⟨A,hA,ha⟩ := loading_bound
  obtain ⟨B,hB,hb⟩ := slot_decay
  refine ⟨fun z => A z + B ((z.1.1,z.1.2.length),z.2), Primrec.nat_add.to_comp.comp hA
    (hB.comp (((Computable.fst.comp Computable.fst).pair
      (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.fst))).pair Computable.snd)), fun M w r n x => ?_⟩
  cases n with
  | zero =>
    simp only [Construction.piece, amplitude, mul_one, Nat.cast_add]
    exact (ha M w r x).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  | succ n =>
    simp only [Construction.piece, amplitude, Nat.cast_add]
    exact (hb M w.length r n x).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (Nat.cast_nonneg _)) (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)))

lemma pulse_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ _ => Profiles.pulse) := by
  have hclock := transition_scaled.affine (fun _ _ => zero_le_one) (fun _ _ => 2)
    (fun _ _ => -1/2) (fun _ => 2) (Computable.const 2) (by intros; norm_num)
  have he : (fun t => Real.smoothTransition (2 * t + -1/2)) = Profiles.clock := by
    funext t; unfold Profiles.clock; congr 1; ring
  obtain ⟨hs,C,hC,hc⟩ := hclock
  refine ⟨fun _ _ => Profiles.pulse_smooth, fun z => C ((),z.2+1),
    hC.comp ((Computable.const ()).pair (Computable.succ.comp Computable.snd)), fun a r n x => ?_⟩
  rw [he] at hc
  change ‖iteratedFDeriv ℝ r (deriv Profiles.clock) x‖ ≤ _
  simpa [one_pow, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ'] using hc () (r+1) 0 x

lemma pulsePiece_decay : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r n z,
    ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ ≤ (C ((M,w),r) : ℝ) * amplitude M w.length n := by
  obtain ⟨_,A,hA,ha⟩ := pulse_scaled
  obtain ⟨B,hB,hb⟩ := piece_decay
  let C := fun z : (Machine × List ℕ) × ℕ => ∑ i ∈ Finset.range (z.2+1), z.2.choose i * A ((),i) * B (z.1,z.2-i)
  have hi : Computable₂ (fun z : (Machine × List ℕ) × ℕ => fun i : ℕ => z.2.choose i * A ((),i) * B (z.1,z.2-i)) :=
    Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
      (hA.comp ((Computable.const ()).pair Computable.snd)))
      (hB.comp ((Computable.fst.comp Computable.fst).pair
        (Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  refine ⟨C, (nat_sum_range hi).comp Computable.id (Computable.succ.comp Computable.snd), fun M w r n z => ?_⟩
  have hp (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Profiles.pulse (z.1 - n)) z‖ ≤ (A ((),i) : ℝ) := by
    apply (norm_comp_linear (fun t => Profiles.pulse (t - n))
      (Profiles.pulse_smooth.comp (contDiff_id.sub contDiff_const)) (ContinuousLinearMap.fst ℝ ℝ Space)
      i z).trans
    rw [iteratedFDeriv_comp_sub]
    have h₁ : ‖iteratedFDeriv ℝ i Profiles.pulse (z.1 - n)‖ ≤ (A ((),i) : ℝ) := by simpa using ha () i 0 (z.1 - n)
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg (A ((),i)))
  have hw (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Construction.piece M w n z.2) z‖ ≤
        (B ((M,w),i) : ℝ) * amplitude M w.length n := by
    apply (norm_comp_linear (Construction.piece M w n) (Construction.piece_smooth M w n)
      (ContinuousLinearMap.snd ℝ ℝ Space) i z).trans
    have h₁ := hb M w i n z.2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (Nat.cast_nonneg (B ((M,w),i))) (Bounds.amplitude_nonneg M w.length n))
  apply (norm_iteratedFDeriv_smul_le
    (Profiles.pulse_smooth.comp (contDiff_fst.sub contDiff_const))
    ((Construction.piece_smooth M w n).comp contDiff_snd) z (WithTop.coe_le_coe.mpr le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * (A ((),i) : ℝ) * ((B ((M,w),r-i) : ℝ) * amplitude M w.length n) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul _ (hw (r - i)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg (A ((),i))))
      exact mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg _)
    _ = (C ((M,w),r) : ℝ) * amplitude M w.length n := by
      simp only [C, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_assoc]

lemma epsilon_small (M : Machine) (N n : ℕ) : Scales.ε M.base N n ≤ (1/8:ℝ)^n := by
  have hb : (2 : ℝ) ≤ M.base := by exact_mod_cast (le_trans (by decide : 2 ≤ 4) M.base_ge_four)
  have hs : 3*n ≤ Scales.s N n := by have := Scales.s_lower N n; nlinarith
  unfold Scales.ε
  have hp : (8:ℝ)^n ≤ (M.base:ℝ)^Scales.s N n := by
    calc
      _ = (2:ℝ)^(3*n) := by rw [pow_mul]; norm_num
      _ ≤ (2:ℝ)^Scales.s N n := pow_le_pow_right₀ (by norm_num) hs
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hb _
  simpa only [one_div, inv_pow] using inv_anti₀ (by positivity : (0:ℝ) < 8^n) hp

lemma weighted_epsilon (M : Machine) (N J n : ℕ) :
    (1+(n:ℝ))^J * Scales.ε M.base N n ≤ 4 * J.factorial * (1/2:ℝ)^n := by
  have hpoly : (1+(n:ℝ))^J ≤ (J.factorial:ℝ) * (4 * 4^n) := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < J.factorial)).mp
      (Real.pow_div_factorial_le_exp (1+(n:ℝ)) (by positivity) J)
    have he : Real.exp (1+(n:ℝ)) ≤ 4 * 4^n := by
      rw [Real.exp_add, show (n:ℝ) = n*1 by ring, Real.exp_nat_mul]
      exact mul_le_mul (Real.exp_one_lt_three.le.trans (by norm_num))
        (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_three.le.trans (by norm_num)) n)
        (by positivity) (by norm_num)
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg J.factorial : (0:ℝ) ≤ _)])
  calc
    _ ≤ ((J.factorial:ℝ) * (4 * 4^n)) * (1/8:ℝ)^n :=
      mul_le_mul hpoly (epsilon_small M N n) (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)) (by positivity)
    _ = _ := by rw [mul_assoc _ (4*4^n), mul_assoc 4, ← mul_pow]; norm_num; ring

lemma weighted_amplitude_sum (M : Machine) (N J : ℕ) :
    (∑' n : ℕ, (1+(n:ℝ))^J * amplitude M N n) ≤ (1 + 8 * 2^J * J.factorial : ℕ) := by
  have hs := Bounds.weighted_amplitude_summable M N J
  rw [hs.tsum_eq_zero_add]
  simp only [amplitude, Nat.cast_zero, add_zero, one_pow, mul_one]
  have hc : ∀ n : ℕ, (1+(n+1:ℕ))^J * amplitude M N (n+1) ≤
      (2:ℝ)^J * (4 * J.factorial * (1/2:ℝ)^n) := by
    intro n
    simp only [amplitude, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (2*(1+(n:ℝ)))^J * Scales.ε M.base N n := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by nlinarith) J)
        (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega))
      _ ≤ _ := by rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left (weighted_epsilon M N J n) (by positivity)
  have h := (hs.comp_injective Nat.succ_injective).tsum_le_tsum hc
    ((summable_geometric_two.mul_left (4*(J.factorial:ℝ))).mul_left ((2:ℝ)^J))
  simp only [tsum_mul_left, tsum_geometric_two, amplitude, Nat.cast_add, Nat.cast_one] at h
  push_cast
  nlinarith

end AlternatingNS.Effective

end DecayBoundsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/CertifiedBounds.lean =====
namespace OAI

section CertifiedBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective

variable {A E F : Type*} [Primcodable A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def weight (z : ℝ × Space) : ℝ := 1 + |z.1| + ‖z.2‖

lemma weight_pos (z : ℝ × Space) : 0 < weight z := by unfold weight; positivity

def Certified (f : A → ℝ × Space → F) : Prop :=
  (∀ a, ContDiff ℝ ∞ (f a)) ∧ ∃ B : A × ℕ × ℕ → ℕ, Computable B ∧
    ∀ a J r z, weight z ^ J * ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,J,r)

lemma velocity_certified : Certified (fun z : Machine × List ℕ => Function.uncurry (Construction.velocity z.1 z.2)) := by
  obtain ⟨C,hC,hc⟩ := pulsePiece_decay
  let B := fun z : (Machine × List ℕ) × ℕ × ℕ =>
    11^z.2.1 * C (z.1,z.2.2) * (1 + 8 * 2^z.2.1 * z.2.1.factorial)
  have cb : Computable B := by
    have hJ : Computable (fun z : (Machine × List ℕ) × ℕ × ℕ => z.2.1) := Computable.fst.comp Computable.snd
    exact Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (nat_pow.to_comp.comp (Computable.const 11) hJ)
        (hC.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))))
      (Primrec.nat_add.to_comp.comp (Computable.const 1)
        (Primrec.nat_mul.to_comp.comp
          (Primrec.nat_mul.to_comp.comp (Computable.const 8) (nat_pow.to_comp.comp (Computable.const 2) hJ))
          (factorial.to_comp.comp hJ)))
  refine ⟨fun z => Construction.velocity_smooth z.1 z.2, B, cb, ?_⟩
  rintro ⟨M,w⟩ J r z
  have hc' (n : ℕ) : weight z ^ J * ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ ≤
      11^J * (C ((M,w),r) : ℝ) * ((1+(n:ℝ))^J * Bounds.amplitude M w.length n) := by
    by_cases hz : z ∈ tsupport (iteratedFDeriv ℝ r (Bounds.pulsePiece M w n))
    · have hsupport := Bounds.pulsePiece_support M w n (tsupport_iteratedFDeriv_subset r hz)
      have ht : 0 ≤ z.1 := (Nat.cast_nonneg n).trans hsupport.1.1
      have hw : weight z ^ J ≤ (11 * (1+(n:ℝ)))^J := by
        apply pow_le_pow_left₀ (weight_pos z).le
        dsimp [weight]; rw [abs_of_nonneg ht]
        linarith [hsupport.1.2, Bounds.box_norm z.2 hsupport.2, Nat.cast_nonneg (α := ℝ) n]
      calc
        _ ≤ (11*(1+(n:ℝ)))^J * ((C ((M,w),r) : ℝ) * Bounds.amplitude M w.length n) :=
          mul_le_mul hw (hc M w r n z) (norm_nonneg _) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (Bounds.amplitude_nonneg M w.length n))
  obtain ⟨N,hN⟩ := TimeGlue.locally_eq_sum Profiles.pulse Profiles.pulse_zero_left (Construction.piece M w) z
  change Function.uncurry (Construction.velocity M w) =ᶠ[𝓝 z]
    (fun z => ∑ n ∈ Finset.range N, Bounds.pulsePiece M w n z) at hN
  rw [(hN.iteratedFDeriv ℝ r).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun n _ => (Bounds.pulsePiece_smooth M w n).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  have ha := Bounds.weighted_amplitude_summable M w.length J
  calc
    _ ≤ weight z ^ J * ∑ n ∈ Finset.range N, ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (weight_pos z).le J)
    _ ≤ ∑ n ∈ Finset.range N, 11^J * (C ((M,w),r):ℝ) * ((1+(n:ℝ))^J * Bounds.amplitude M w.length n) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun n _ => hc' n)
    _ ≤ (11^J * (C ((M,w),r):ℝ)) * ∑' n : ℕ, (1+(n:ℝ))^J * Bounds.amplitude M w.length n := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (ha.sum_le_tsum _ (fun n _ => mul_nonneg (by positivity) (Bounds.amplitude_nonneg M w.length n))) (by positivity)
    _ ≤ B ((M,w),J,r) := by
      have h := mul_le_mul_of_nonneg_left (weighted_amplitude_sum M w.length J)
        (show (0:ℝ) ≤ 11^J * C ((M,w),r) by positivity)
      simpa only [B, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

lemma Certified.congr {f g : A → ℝ × Space → F} (hf : Certified f) (h : ∀ a z, f a z = g a z) : Certified g := by
  rwa [← funext (fun a => funext (h a))]

lemma Certified.param {B : Type*} [Primcodable B] {f : A → ℝ × Space → F}
    (hf : Certified f) (g : B → A) (hg : Computable g) : Certified (fun b => f (g b)) := by
  obtain ⟨hs,C,hC,h⟩ := hf
  exact ⟨fun b => hs (g b), fun z => C (g z.1,z.2), hC.comp ((hg.comp Computable.fst).pair Computable.snd), fun b => h (g b)⟩

lemma Certified.add {f g : A → ℝ × Space → F} (hf : Certified f) (hg : Certified g) :
    Certified (fun a z => f a z + g a z) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  obtain ⟨sg,C,hC,hg⟩ := hg
  refine ⟨fun a => (sf a).add (sg a), fun z => B z + C z,
    Primrec.nat_add.to_comp.comp hB hC, fun a J r z => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((sf a).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt, Nat.cast_add]
  calc
    _ ≤ weight z ^ J * (‖iteratedFDeriv ℝ r (f a) z‖ + ‖iteratedFDeriv ℝ r (g a) z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg (weight_pos z).le _)
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hf a J r z) (hg a J r z)

lemma Certified.linear {f : A → ℝ × Space → F} (hf : Certified f)
    (L : A → F →L[ℝ] E) (D : A → ℕ) (hD : Computable D) (hL : ∀ a, ‖L a‖ ≤ D a) :
    Certified (fun a => L a ∘ f a) := by
  obtain ⟨hs,B,hB,hf⟩ := hf
  refine ⟨fun a => (L a).contDiff.comp (hs a), fun z => D z.1 * B z,
    Primrec.nat_mul.to_comp.comp (hD.comp Computable.fst) hB, fun a J r z => ?_⟩
  calc
    _ ≤ weight z ^ J * ((D a : ℝ) * ‖iteratedFDeriv ℝ r (f a) z‖) :=
      mul_le_mul_of_nonneg_left ((Bounds.norm_postcomp_linear (f a) (hs a) (L a) r z).trans
        (mul_le_mul_of_nonneg_right (hL a) (norm_nonneg _))) (pow_nonneg (weight_pos z).le _)
    _ ≤ _ := by rw [mul_left_comm, Nat.cast_mul]; exact mul_le_mul_of_nonneg_left (hf a J r z) (Nat.cast_nonneg _)

lemma Certified.csmul {f : A → ℝ × Space → F} (hf : Certified f) (c : ℝ) (D : ℕ) (hc : |c| ≤ D) :
    Certified (fun a z => c • f a z) := by
  apply hf.linear (fun _ => c • ContinuousLinearMap.id ℝ F) (fun _ => D) (Computable.const D)
  intro _
  simpa only [norm_smul, Real.norm_eq_abs, mul_one] using
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F)) (abs_nonneg c)).trans (by simpa using hc)

lemma Certified.sub {f g : A → ℝ × Space → F} (hf : Certified f) (hg : Certified g) :
    Certified (fun a z => f a z - g a z) := by
  exact (hf.add (hg.csmul (-1) 1 (by norm_num))).congr (by intros; simp [sub_eq_add_neg])

lemma Certified.directional {f : A → ℝ × Space → F} (hf : Certified f)
    (v : A → ℝ × Space) (hv : ∀ a, ‖v a‖ ≤ 1) :
    Certified (fun a z => fderiv ℝ (f a) z (v a)) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  refine ⟨fun a => ((sf a).fderiv_right (by simp)).clm_apply contDiff_const,
    fun z => B (z.1,z.2.1,z.2.2+1), hB.comp (Computable.fst.pair
      ((Computable.fst.comp Computable.snd).pair (Computable.succ.comp (Computable.snd.comp Computable.snd)))), fun a J r z => ?_⟩
  apply le_trans _ (hf a J (r+1) z)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (weight_pos z).le _)
  exact (Bounds.norm_directional_iterated (f a) (sf a) (v a) r z).trans
    (mul_le_of_le_one_left (norm_nonneg _) (hv a))

lemma Certified.smul {f : A → ℝ × Space → ℝ} {g : A → ℝ × Space → F}
    (hf : Certified f) (hg : Certified g) : Certified (fun a z => f a z • g a z) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  obtain ⟨sg,C,hC,hg⟩ := hg
  let D := fun z : A × ℕ × ℕ => ∑ i ∈ Finset.range (z.2.2+1), z.2.2.choose i * B (z.1,z.2.1,i) * C (z.1,0,z.2.2-i)
  have hi : Computable₂ (fun z : A × ℕ × ℕ => fun i : ℕ => z.2.2.choose i * B (z.1,z.2.1,i) * C (z.1,0,z.2.2-i)) := by
    have ha : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.1) := Computable.fst.comp Computable.fst
    have hJ : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hr : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.2.2) := Computable.snd.comp (Computable.snd.comp Computable.fst)
    exact Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp hr Computable.snd) (hB.comp (ha.pair (hJ.pair Computable.snd))))
      (hC.comp (ha.pair ((Computable.const 0).pair (Primrec.nat_sub.to_comp.comp hr Computable.snd))))
  refine ⟨fun a => (sf a).fun_smul (sg a), D,
    (nat_sum_range hi).comp Computable.id (Computable.succ.comp (Computable.snd.comp Computable.snd)), fun a J r z => ?_⟩
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le (sf a) (sg a) z
    (WithTop.coe_le_coe.mpr le_top)) (pow_nonneg (weight_pos z).le J)).trans
  simp only [D, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = (r.choose i : ℝ) * (weight z^J * ‖iteratedFDeriv ℝ i (f a) z‖) * ‖iteratedFDeriv ℝ (r-i) (g a) z‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hf a J i z) (Nat.cast_nonneg _))
      (by simpa using hg a 0 (r-i) z) (norm_nonneg _) (by positivity)

end AlternatingNS.Effective

end CertifiedBoundsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/TypedPrograms.lean =====
namespace OAI

section TypedProgramsDevelopment

namespace AlternatingNS.Effective

open Encodable

def execute {A B : Type*} [Encodable A] [Encodable B] (c : Program) (a : A) : Part B :=
  (c.eval (encode a)).bind (fun n => Part.ofOption (decode n))

lemma execute_partrec {A B : Type*} [Primcodable A] [Primcodable B] :
    Partrec₂ (@execute A B _ _) := by
  exact (Nat.Partrec.Code.eval_part.comp Computable.fst
    (Computable.encode.comp Computable.snd)).bind
    (Computable.ofOption (Computable.decode.comp Computable.snd))

lemma typed_fixedpoint {A B : Type*} [Primcodable A] [Primcodable B]
    (F : Program → A → Part B) (hF : Partrec₂ F) :
    ∃ c : Program, ∀ a, execute c a = F c a := by
  let G (c : Program) (n : ℕ) : Part ℕ :=
    (Part.ofOption (decode n)).bind (fun a : A => (F c a).map encode)
  have hG : Partrec₂ G := (Computable.ofOption (Computable.decode.comp Computable.snd)).bind
    ((hF.comp (Computable.fst.comp Computable.fst) Computable.snd).map
      (Computable.encode.comp Computable.snd))
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hG
  refine ⟨c, fun a => ?_⟩
  simp [execute, hc, G, Part.bind_map]

lemma computable_of_execute {A B : Type*} [Primcodable A] [Primcodable B]
    (c : Program) (f : A → B) (h : ∀ a, f a ∈ execute c a) : Computable f :=
  (execute_partrec.comp (Computable.const c) Computable.id).of_eq_tot h

lemma partrec_ite {A B : Type*} [Primcodable A] [Primcodable B]
    (p : A → Prop) [DecidablePred p] (hp : Computable (fun a => decide (p a)))
    (f g : A → Part B) (hf : Partrec f) (hg : Partrec g) :
    Partrec (fun a => if p a then f a else g a) := by
  
  obtain ⟨cf,hcf⟩ := Nat.Partrec.Code.exists_code.mp hf
  obtain ⟨cg,hcg⟩ := Nat.Partrec.Code.exists_code.mp hg
  have hr : Partrec (fun a => execute (B := B) (if p a then cf else cg) a) :=
    execute_partrec.comp ((Computable.cond hp (Computable.const cf) (Computable.const cg)).of_eq
      (by simp)) Computable.id
  apply hr.of_eq
  intro a
  split_ifs <;> simp [execute, hcf, hcg, encodek, Part.bind_map]

lemma binary_recursive_program {A B : Type*} [Primcodable A] [Primcodable B]
    (p : A → Prop) [DecidablePred p] (hp : Computable (fun a => decide (p a)))
    (base : A → B) (hb : Computable base) (left right : A → A)
    (hl : Computable left) (hr : Computable right)
    (op : A × B × B → B) (ho : Computable op) :
    ∃ c : Program, ∀ a, execute c a =
      if p a then Part.some (base a) else
        (execute c (left a)).bind (fun u => (execute c (right a)).map (fun v => op (a,u,v))) := by
  let F (c : Program) (a : A) : Part B := if p a then Part.some (base a) else
    (execute c (left a)).bind (fun u => (execute c (right a)).map (fun v => op (a,u,v)))
  apply typed_fixedpoint F
  apply partrec_ite (p := fun z : Program × A => p z.2) (hp.comp Computable.snd)
  · exact hb.comp Computable.snd
  · have hrec₁ : Partrec (fun z : Program × A => execute (B := B) z.1 (left z.2)) :=
      execute_partrec.comp Computable.fst (hl.comp Computable.snd)
    have hrec₂ : Partrec (fun z : (Program × A) × B => execute (B := B) z.1.1 (right z.1.2)) :=
      execute_partrec.comp (Computable.fst.comp Computable.fst) (hr.comp (Computable.snd.comp Computable.fst))
    exact hrec₁.bind (hrec₂.map (ho.comp
      ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))))

end AlternatingNS.Effective

end TypedProgramsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/JetNames.lean =====
namespace OAI

section JetNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

noncomputable def direction (i : Fin 4) : ℝ × Space :=
  ![(1,0), (0,e 0), (0,e 1), (0,e 2)] i

lemma direction_norm (i : Fin 4) : ‖direction i‖ ≤ 1 := by
  fin_cases i <;> simp [direction, Prod.norm_def, Bounds.norm_e]

def shift (i : Fin 4) (h : ℚ) (q : RationalPoint) : RationalPoint :=
  if i = 0 then (q.1+h,q.2) else
  if i = 1 then (q.1,q.2.1+h,q.2.2) else
  if i = 2 then (q.1,q.2.1,q.2.2.1+h,q.2.2.2) else
  (q.1,q.2.1,q.2.2.1,q.2.2.2+h)

lemma shift_computable : Computable (fun z : Fin 4 × ℚ × RationalPoint => shift z.1 z.2.1 z.2.2) := by
  have h0 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have h1 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have h2 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have h3 : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hh : Computable (fun z : Fin 4 × ℚ × RationalPoint => z.2.1) := Computable.fst.comp Computable.snd
  have hi (i : Fin 4) : Computable (fun z : Fin 4 × ℚ × RationalPoint => decide (z.1 = i)) :=
    Primrec.eq.decide.to_comp.comp Computable.fst (Computable.const i)
  have hadd := Arithmetic.rat_add.to_comp
  exact (Computable.cond (hi 0) ((hadd.comp h0 hh).pair (h1.pair (h2.pair h3)))
    (Computable.cond (hi 1) (h0.pair ((hadd.comp h1 hh).pair (h2.pair h3)))
      (Computable.cond (hi 2) (h0.pair (h1.pair ((hadd.comp h2 hh).pair h3)))
        (h0.pair (h1.pair (h2.pair (hadd.comp h3 hh))))))).of_eq (by rintro ⟨i,h,q⟩; fin_cases i <;> rfl)

lemma shift_cast (i : Fin 4) (h : ℚ) (q : RationalPoint) :
    rationalPoint (shift i h q) = rationalPoint q + (h:ℝ) • direction i := by
  fin_cases i <;> ext j <;> simp [shift, rationalPoint, rationalVector, direction, e,
    EuclideanSpace.equiv] <;> fin_cases j <;> simp

noncomputable def wordJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × Space → E) : List (Fin 4) → ℝ × Space → E
  | [] => f
  | i::w => fun z => fderiv ℝ (wordJet f w) z (direction i)

lemma wordJet_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} (hf : ContDiff ℝ ∞ f) (w : List (Fin 4)) :
    ContDiff ℝ ∞ (wordJet f w) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma wordJet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} (hf : ContDiff ℝ ∞ f) (w : List (Fin 4)) (r : ℕ) (z : ℝ × Space) :
    ‖iteratedFDeriv ℝ r (wordJet f w) z‖ ≤ ‖iteratedFDeriv ℝ (r+w.length) f z‖ := by
  induction w generalizing r with
  | nil => simp [wordJet]
  | cons i w ih =>
    apply (Bounds.norm_directional_iterated _ (wordJet_smooth hf w) (direction i) r z).trans
    apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (direction_norm i))
    have hi : r + (i :: w).length = r + 1 + w.length := by simp only [List.length_cons]; omega
    rw [hi]
    exact ih (r+1)

lemma jet_lipschitz {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (C : ℝ)
    (hC : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ C) (x y : E) :
    ‖f x - f y‖ ≤ C * ‖x-y‖ := by
  exact (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => by simpa only [norm_iteratedFDeriv_one] using hC x) (Set.mem_univ y) (Set.mem_univ x)

lemma difference_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C)
    (q v : E) (hv : ‖v‖ ≤ 1) {h : ℝ} (hh : 0 < h) :
    |fderiv ℝ f q v - (f (q+h•v)-f q)/h| ≤ C*h := by
  have hLip (x y : E) : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x-y‖ :=
    jet_lipschitz (hf.fderiv_right (by simp)) C (fun x => by
      simpa only [norm_iteratedFDeriv_fderiv] using hbound x) x y
  have hdist : ‖(q+h•v)-q‖ ≤ h := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hh] using mul_le_mul_of_nonneg_left hv hh.le
  have hmv := (convex_closedBall q h).norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f q) (x := q) (y := q+h•v)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x hx => (hLip x q).trans (mul_le_mul_of_nonneg_left
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx) hC))
    (Metric.mem_closedBall_self hh.le) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hdist)
  have hmv' : |f (q+h•v)-f q-h*fderiv ℝ f q v| ≤ C*h*h := by
    have hx := hmv.trans (mul_le_mul_of_nonneg_left hdist (mul_nonneg hC hh.le))
    simpa only [add_sub_cancel_left, map_smul, smul_eq_mul, Real.norm_eq_abs] using hx
  rw [← abs_neg, neg_sub, div_sub' hh.ne', abs_div, abs_of_pos hh, div_le_iff₀ hh]
  simpa only [one_mul, mul_comm] using hmv'

lemma tolerance_add (m n : ℕ) : (tolerance (m+n) : ℝ) = (tolerance m : ℝ)*(tolerance n : ℝ) := by
  simp [tolerance, pow_add]

lemma nat_mul_tolerance (n : ℕ) : (n:ℝ)*(tolerance n:ℝ) ≤ 1 := by
  have hn : (n:ℝ) ≤ 2^n := by exact_mod_cast n.lt_two_pow_self.le
  calc
    _ ≤ (2:ℝ)^n * (tolerance n:ℝ) := mul_le_mul_of_nonneg_right hn (tolerance_pos n).le
    _ = 1 := by simp [tolerance]

lemma difference_precision (C k : ℕ) : (C:ℝ)*(tolerance (k+1+C):ℝ) ≤ tolerance (k+1) := by
  rw [tolerance_add, mul_left_comm]
  exact mul_le_of_le_one_right (tolerance_pos _).le (nat_mul_tolerance C)

end AlternatingNS.Effective

end JetNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/JetPrograms.lean =====
namespace OAI

section JetProgramsDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*}

def jetApprox (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (a : A) : List (Fin 4) → RationalPoint → ℕ → ℚ
  | [], q, k => b ((a,q),k)
  | i::w, q, k =>
    let n := k+1+B (a,w.length+2)
    let m := k+2+n
    (jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m) / tolerance n

attribute [local irreducible] jetApprox

lemma jetApprox_computable [Primcodable A] (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (hb : Computable b) (hB : Computable B) :
    Computable (fun z : A × List (Fin 4) × RationalPoint × ℕ => jetApprox b B z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let Q := A × List (Fin 4) × RationalPoint × ℕ
  let n (z : Q) := z.2.2.2+1+B (z.1,z.2.1.tail.length+2)
  let m (z : Q) := z.2.2.2+2+n z
  let left (z : Q) : Q := (z.1,z.2.1.tail,shift (z.2.1.head?.getD 0) (tolerance (n z)) z.2.2.1,m z)
  let right (z : Q) : Q := (z.1,z.2.1.tail,z.2.2.1,m z)
  have ha : Computable (fun z : Q => z.1) := Computable.fst
  have hw : Computable (fun z : Q => z.2.1) := Computable.fst.comp Computable.snd
  have hq : Computable (fun z : Q => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun z : Q => z.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ht : Computable (fun z : Q => z.2.1.tail) := Primrec.list_tail.to_comp.comp hw
  have hn : Computable n := Primrec.nat_add.to_comp.comp (Computable.succ.comp hk)
    (hB.comp (ha.pair (Primrec.nat_add.to_comp.comp (Computable.list_length.comp ht) (Computable.const 2))))
  have hm : Computable m := Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp hk (Computable.const 2)) hn
  have he : Computable (fun z : Q => tolerance (n z)) := tolerance_primrec.to_comp.comp hn
  have hl : Computable left := ha.pair (ht.pair ((shift_computable.comp
    ((Computable.option_getD (Primrec.list_head?.to_comp.comp hw) (Computable.const 0)).pair
      (he.pair hq))).pair hm))
  have hr : Computable right := ha.pair (ht.pair (hq.pair hm))
  have hbase : Computable (fun z : Q => b ((z.1,z.2.2.1),z.2.2.2)) :=
    hb.comp ((ha.pair hq).pair hk)
  have hop : Computable (fun z : Q × ℚ × ℚ => (z.2.1-z.2.2)/tolerance (n z.1)) :=
    Arithmetic.rat_div.to_comp.comp (Arithmetic.rat_sub.to_comp.comp
      (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
      (he.comp Computable.fst)
  obtain ⟨c,hc⟩ := binary_recursive_program (fun z : Q => z.2.1 = [])
    (Primrec.eq.decide.to_comp.comp hw (Computable.const []))
    (fun z => b ((z.1,z.2.2.1),z.2.2.2)) hbase left right hl hr
    (fun z : Q × ℚ × ℚ => (z.2.1-z.2.2)/tolerance (n z.1)) hop
  apply computable_of_execute c
  rintro ⟨a,w,q,k⟩
  induction w generalizing q k with
  | nil => simp [hc, jetApprox]
  | cons i w ih =>
    rw [hc]
    simp only [List.cons_ne_nil, ite_false]
    apply Part.mem_bind_iff.mpr
    refine ⟨_, ih (shift i (tolerance (n (a,i::w,q,k))) q) (m (a,i::w,q,k)), ?_⟩
    apply (Part.mem_map_iff _).mpr
    refine ⟨_, ih q (m (a,i::w,q,k)), ?_⟩
    rw [jetApprox]
    rfl

lemma jetApprox_error (f : A → ℝ × Space → ℝ) (sf : ∀ a, ContDiff ℝ ∞ (f a))
    (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (hb : ∀ a q k, |f a (rationalPoint q) - (b ((a,q),k) : ℝ)| ≤ tolerance k)
    (hB : ∀ a r z, ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,r)) :
    ∀ a w q k, |wordJet (f a) w (rationalPoint q) - (jetApprox b B a w q k : ℝ)| ≤ tolerance k := by
  intro a w
  induction w with
  | nil => simpa only [wordJet, jetApprox] using hb a
  | cons i w ih =>
    intro q k
    let C := B (a,w.length+2)
    let n := k+1+C
    let m := k+2+n
    have hd := difference_error (wordJet_smooth (sf a) w) (Nat.cast_nonneg C)
      (fun z => (wordJet_bound (sf a) w 2 z).trans (by rw [Nat.add_comm 2 w.length]; exact hB a (w.length+2) z))
      (rationalPoint q) (direction i) (direction_norm i) (tolerance_pos n)
    have he : |(wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - wordJet (f a) w (rationalPoint q)) /
        (tolerance n : ℝ) -
        ((jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m) / tolerance n : ℚ)| ≤
          2 * (tolerance m : ℝ) / tolerance n := by
      push_cast
      rw [← sub_div, abs_div, abs_of_pos (tolerance_pos n)]
      apply div_le_div_of_nonneg_right _ (tolerance_pos n).le
      calc
        _ = |(wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - (jetApprox b B a w (shift i (tolerance n) q) m : ℝ)) -
          (wordJet (f a) w (rationalPoint q) - (jetApprox b B a w q m : ℝ))| := by congr 1; ring
        _ ≤ _ := (abs_sub _ _).trans (by linarith [ih (shift i (tolerance n) q) m, ih q m])
    have hp : 2 * (tolerance m : ℝ) / tolerance n = tolerance (k+1) := by
      dsimp [m]
      rw [tolerance_add, mul_div_assoc, mul_div_cancel_right₀ _ (tolerance_pos n).ne']
      simp [tolerance, pow_add]; ring
    have hh := abs_sub_le (fderiv ℝ (wordJet (f a) w) (rationalPoint q) (direction i))
      ((wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - wordJet (f a) w (rationalPoint q))/(tolerance n : ℝ))
      (((jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m)/tolerance n : ℚ) : ℝ)
    rw [shift_cast] at he hh
    have hsum := hh.trans (add_le_add hd he)
    rw [hp] at hsum
    have hp' := difference_precision C k
    have ht : (tolerance (k+1) : ℝ)+(tolerance (k+1) : ℝ) = tolerance k := by simp [tolerance, pow_succ]; ring
    change |fderiv ℝ (wordJet (f a) w) (rationalPoint q) (direction i) - _| ≤ _
    unfold jetApprox
    exact hsum.trans (by linarith)

lemma named_wordJet [Primcodable A] {f : A → ℝ × Space → ℝ}
    (sf : ∀ a, ContDiff ℝ ∞ (f a))
    (hf : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2)))
    (B : A × ℕ → ℕ) (hB : Computable B)
    (hbound : ∀ a r z, ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,r)) :
    Named (fun z : (A × List (Fin 4)) × RationalPoint => wordJet (f z.1.1) z.1.2 (rationalPoint z.2)) := by
  obtain ⟨b,hb,h⟩ := hf
  refine ⟨fun z => jetApprox b B z.1.1.1 z.1.1.2 z.1.2 z.2, ?_, ?_⟩
  · have hp : Computable (fun z : (((A × List (Fin 4)) × RationalPoint) × ℕ) =>
        (z.1.1.1,z.1.1.2,z.1.2,z.2)) :=
      (Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
          ((Computable.snd.comp Computable.fst).pair Computable.snd))
    have hg := jetApprox_computable (A := A) b B hb hB
    have hcomp := Computable.comp hg hp
    exact hcomp
  · rintro ⟨⟨a,w⟩,q⟩ k
    exact jetApprox_error f sf b B (fun a q k => h (a,q) k) hbound a w q k

end AlternatingNS.Effective

end JetProgramsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/FieldPrograms.lean =====
namespace OAI

section FieldProgramsDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A E F : Type*} [Primcodable A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def JetBound (f : A → E → F) : Prop :=
  (∀ a, ContDiff ℝ ∞ (f a)) ∧ ∃ B : A × ℕ → ℕ, Computable B ∧
    ∀ a r x, ‖iteratedFDeriv ℝ r (f a) x‖ ≤ B (a,r)

lemma Certified.jetBound {f : A → ℝ × Space → F} (hf : Certified f) : JetBound f := by
  obtain ⟨sf,B,hB,h⟩ := hf
  exact ⟨sf, fun z => B (z.1,0,z.2), hB.comp (Computable.fst.pair ((Computable.const 0).pair Computable.snd)),
    fun a r z => by simpa using h a 0 r z⟩

lemma JetBound.congr {f g : A → E → F} (hf : JetBound f) (h : ∀ a x, f a x = g a x) : JetBound g := by
  rwa [← funext (fun a => funext (h a))]

lemma JetBound.param {B : Type*} [Primcodable B] {f : A → E → F} (hf : JetBound f)
    {g : B → A} (hg : Computable g) : JetBound (fun b => f (g b)) := by
  obtain ⟨sf,C,hC,h⟩ := hf
  exact ⟨fun b => sf (g b), fun z => C (g z.1,z.2), hC.comp ((hg.comp Computable.fst).pair Computable.snd), fun b => h (g b)⟩

lemma JetBound.comp_unit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : A → E → F} (hf : JetBound f) (L : A → G →L[ℝ] E) (hL : ∀ a, ‖L a‖ ≤ 1) :
    JetBound (fun a => f a ∘ L a) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => (sf a).comp (L a).contDiff, B, hB, fun a r z => ?_⟩
  exact (Bounds.norm_comp_linear (f a) (sf a) (L a) r z).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hL a))).trans (h a r _))

lemma JetBound.linear_unit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : A → E → F} (hf : JetBound f) (L : A → F →L[ℝ] G) (hL : ∀ a, ‖L a‖ ≤ 1) :
    JetBound (fun a => L a ∘ f a) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => (L a).contDiff.comp (sf a), B, hB, fun a r z => ?_⟩
  exact (Bounds.norm_postcomp_linear (f a) (sf a) (L a) r z).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (hL a)).trans (h a r z))

lemma Scaled.jetBound {s : A → ℕ → ℝ} {f : A → ℕ → E → F} (hf : Scaled s f)
    (hs : ∀ a n, 0 ≤ s a n) (S : A × ℕ → ℕ) (hS : Computable S)
    (sS : ∀ a n, s a n ≤ S (a,n)) : JetBound (fun a : A × ℕ => f a.1 a.2) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  refine ⟨fun a => sf a.1 a.2, fun z => B (z.1.1,z.2) * S z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp
      (hB.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (nat_pow.to_comp.comp (hS.comp Computable.fst) Computable.snd), ?_⟩
  rintro ⟨a,n⟩ r x
  simpa only [Nat.cast_mul, Nat.cast_pow] using (h a r n x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs a n) (sS a n) r) (Nat.cast_nonneg _))

lemma norm_proj (i : Fin 3) : ‖PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using PiLp.norm_apply_le x i)

lemma norm_fst : ‖ContinuousLinearMap.fst ℝ ℝ Space‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_fst_le x)

lemma norm_snd : ‖ContinuousLinearMap.snd ℝ ℝ Space‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_snd_le x)

lemma JetBound.named_wordJet {f : A → ℝ × Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2))) :
    Named (fun z : (A × List (Fin 4)) × RationalPoint => wordJet (f z.1.1) z.1.2 (rationalPoint z.2)) := by
  obtain ⟨sf,B,hB,h⟩ := hf
  exact AlternatingNS.Effective.named_wordJet sf hn B hB h

lemma JetBound.named_directional {f : A → ℝ × Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2)))
    (i : A → Fin 4) (hi : Computable i) :
    Named (fun z : A × RationalPoint => fderiv ℝ (f z.1) (rationalPoint z.2) (direction (i z.1))) := by
  have hw : Computable (fun z : A × RationalPoint => ((z.1,[i z.1]),z.2)) :=
    (Computable.fst.pair (Primrec.list_cons.to_comp.comp (hi.comp Computable.fst) (Computable.const []))).pair Computable.snd
  have hh := hf.named_wordJet hn |>.comp hw
  exact hh.congr (fun _ => rfl)

lemma Certified.sum3 {f : Fin 3 → A → ℝ × Space → F} (hf : ∀ i, Certified (f i)) :
    Certified (fun a z => ∑ i : Fin 3, f i a z) := by
  exact ((hf 0).add ((hf 1).add (hf 2))).congr (fun _ _ => by simp [Fin.sum_univ_succ])

lemma Certified.dx {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) (i : Fin 3) :
    Certified (fun a => Function.uncurry (dx i (f a))) :=
  (hf.directional (fun _ => (0,e i)) (fun _ => by simp [Prod.norm_def, Bounds.norm_e])).congr
    (fun a z => (Bounds.dx_eq_full_directional (f a) (hf.1 a) i z).symm)

lemma Certified.fullDt {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (Analytic.fullDt (f a))) :=
  (hf.directional (fun _ => (1,0)) (fun _ => by simp [Prod.norm_def])).congr
    (fun a z => (Bounds.fullDt_eq_full_directional (f a) (hf.1 a) z).symm)

lemma Certified.component {f : A → ℝ × Space → Space} (hf : Certified f) (i : A → Fin 3) :
    Certified (fun a z => f a z (i a)) :=
  hf.linear (fun a => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (i a)) (fun _ => 1) (Computable.const 1) (fun a => by simpa using norm_proj (i a))

lemma Certified.advection {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (advection (f a))) := by
  have hi (i : Fin 3) := (hf.component (fun _ => i)).smul (hf.dx i)
  exact (Certified.sum3 hi).congr (fun a z => (Bounds.advection_eq_sum (f a) z.1 z.2).symm)

lemma Certified.laplacian {f : A → Velocity} (hf : Certified (fun a => Function.uncurry (f a))) :
    Certified (fun a => Function.uncurry (laplacian (f a))) := Certified.sum3 (fun i => (hf.dx i).dx i)

noncomputable def fullForce (ν : ℝ) (M : Machine) (w : List ℕ) : Velocity :=
  fun t x => Analytic.fullDt (Construction.velocity M w) t x + advection (Construction.velocity M w) t x -
    ν • laplacian (Construction.velocity M w) t x

lemma force_certified (ν : ℝ) : Certified (fun z : Machine × List ℕ => Function.uncurry (fullForce ν z.1 z.2)) := by
  obtain ⟨D,hD⟩ := exists_nat_ge |ν|
  exact (velocity_certified.fullDt.add velocity_certified.advection).sub (velocity_certified.laplacian.csmul ν D hD)

lemma fullForce_half (ν : ℝ) (M : Machine) (w : List ℕ) :
    Bounds.HalfEq (fullForce ν M w) (Construction.force ν M w) := by
  intro t ht x
  simp only [fullForce, Construction.force, residual]
  rw [Analytic.dt_eq_full _ (Construction.velocity_smooth M w) t ht x]

end AlternatingNS.Effective

end FieldProgramsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/LocalNames.lean =====
namespace OAI

section LocalNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma Named.nat (f : A → ℕ) (hf : Computable f) : Named (fun a => (f a : ℝ)) :=
  (Named.rational (Arithmetic.rat_natCast.to_comp.comp hf)).congr (fun _ => Rat.cast_natCast _)

lemma Named.natPow (b n : A → ℕ) (hb : Computable b) (hn : Computable n) :
    Named (fun a => (b a : ℝ) ^ n a) :=
  (Named.rational (Arithmetic.rat_pow.to_comp.comp
    (Arithmetic.rat_natCast.to_comp.comp hb) hn)).congr (by intro a; simp)

lemma Named.invNatPow (b n : A → ℕ) (hb : Computable b) (hn : Computable n) :
    Named (fun a => ((b a : ℝ) ^ n a)⁻¹) :=
  (Named.rational (Arithmetic.rat_inv.to_comp.comp (Arithmetic.rat_pow.to_comp.comp
    (Arithmetic.rat_natCast.to_comp.comp hb) hn))).congr (by intro a; simp)

lemma Named.divNat {f : A → ℝ} (hf : Named f) (b : A → ℕ) (hb : Computable b) :
    Named (fun a => f a / b a) :=
  (hf.mul (Named.invNatPow b (fun _ => 1) hb (Computable.const 1))).congr
    (by intro a; simp [div_eq_mul_inv])

lemma Named.selector {f : A → ℝ} (hf : Named f) (b a : A → ℕ)
    (hb : Computable b) (ha : Computable a) :
    Named (fun z => Profiles.selector (b z) (a z) (f z)) := by
  have h1 := (((Named.const 8).mul (((Named.nat b hb).mul hf).sub
    ((Named.const 2).mul (Named.nat a ha)))).add (Named.const 2)).transition
  have h2 := (((Named.const 8).mul ((((Named.const 2).mul (Named.nat a ha)).add
    (Named.const 1)).sub ((Named.nat b hb).mul hf))).add (Named.const 2)).transition
  exact (h1.mul h2).congr (by intro; simp only [Profiles.selector, Rat.cast_ofNat, Rat.cast_one])

lemma read_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.readC (M z) (N z) (n z) (D z)) ∧
    Named (fun z => LocalRule.readB (M z) (N z) (n z) (D z)) ∧
    Named (fun z => LocalRule.readA (M z) (N z) (n z) (D z)) := by
  have hb := base.to_comp.comp hM
  have hs := exponent.to_comp.comp hN hn
  have hK := capacity.to_comp.comp hN hn
  have hbase (z : A) : 2 ≤ (M z).base := by have := (M z).base_ge_four; omega
  have hC := ((Named.natPow (fun z => (M z).base) _ hb hs).mul hD).decoder
    (fun z => (M z).base) hb hbase
  have hB := ((Named.natPow (fun z => (M z).base) _ hb
    (Primrec.nat_add.to_comp.comp (Computable.succ.comp hs) hK)).mul hD).decoder
    (fun z => (M z).base) hb hbase
  have hA := ((Named.natPow (fun z => (M z).base) _ hb (Computable.succ.comp hs)).mul hD).decoder
    (fun z => (M z).base) hb hbase
  exact ⟨hC,hB,hA.sub ((Named.invNatPow (fun z => (M z).base) _ hb hK).mul hB)⟩

lemma numerator_named (b K a l : A → ℕ) (r : A → Rule) (u v : A → ℝ)
    (hb : Computable b) (hK : Computable K) (ha : Computable a) (hl : Computable l)
    (hr : Computable r) (hu : Named u) (hv : Named v) :
    Named (fun z => LocalRule.branchNumerator (b z) (K z) (a z) (l z) (r z) (u z) (v z)) := by
  have h2a := Named.nat (fun z => 2 * a z) (Primrec.nat_mul.to_comp.comp (Computable.const 2) ha)
  have h2l := Named.nat (fun z => 2 * l z) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hl)
  have h2w := Named.nat (fun z => 2 * (r z).2.1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp (Computable.snd.comp hr)))
  have h2q := Named.nat (fun z => 2 * (r z).1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp hr))
  have hi (i : Fin 3) : Computable (fun z => decide ((r z).2.2 = i)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp (Computable.snd.comp hr)) (Computable.const i)
  have hL := Named.ite (fun z => (r z).2.2 = 0) (hi 0)
    (((Named.nat b hb).mul hu).sub h2l)
    (Named.ite (fun z => (r z).2.2 = 1) (hi 1) hu ((h2w.add hu).divNat b hb))
  have hR := ((Named.nat b hb).mul hv).sub h2a
  have hR' := Named.ite (fun z => (r z).2.2 = 0) (hi 0)
    ((h2l.add ((h2w.add hR).divNat b hb)).divNat b hb)
    (Named.ite (fun z => (r z).2.2 = 1) (hi 1) ((h2w.add hR).divNat b hb) hR)
  exact ((h2q.add hL).add ((Named.invNatPow b K hb hK).mul hR')).congr (by
    intro z; dsimp [LocalRule.branchNumerator, LocalRule.updateLeft, LocalRule.updateRight]
    push_cast; split_ifs <;> rfl)

lemma branch_named (M : A → Machine) (N n q a : A → ℕ) (u v : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hq : Computable q)
    (ha : Computable a) (hu : Named u) (hv : Named v) :
    Named (fun z => LocalRule.branch (M z) (N z) (n z) (q z) (a z) (u z) (v z)) := by
  let r := fun z => (M z).command (q z) (a z)
  have hr : Computable r := command.to_comp.comp (hM.pair (hq.pair ha))
  have hb := base.to_comp.comp hM
  have hK := capacity.to_comp.comp hN (Computable.succ.comp hn)
  have hsel := (hu.comp (g := (Prod.fst : A × ℕ → A)) Computable.fst).selector
    (fun z => (M z.1).base) Prod.snd (hb.comp Computable.fst) Computable.snd
  have hnum := numerator_named (fun z : A × ℕ => (M z.1).base)
    (fun z => Scales.K (N z.1) (n z.1+1)) (fun z => a z.1) Prod.snd (fun z => r z.1)
    (fun z => u z.1) (fun z => v z.1) (hb.comp Computable.fst) (hK.comp Computable.fst)
    (ha.comp Computable.fst) Computable.snd (hr.comp Computable.fst)
    (hu.comp Computable.fst) (hv.comp Computable.fst)
  have hsum := (hsel.mul hnum).sum_range (fun z => (M z).alphabet) (alphabet.to_comp.comp hM)
  have hother := numerator_named (fun z => (M z).base) (fun z => Scales.K (N z) (n z+1))
    a (fun _ => 0) r u v hb hK ha (Computable.const 0) hr hu hv
  have hi : Computable (fun z => decide ((r z).2.2 = 0)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp (Computable.snd.comp hr)) (Computable.const (0 : Fin 3))
  exact (Named.ite (fun z => (r z).2.2 = 0) hi hsum hother).congr (by intro z; rfl)

lemma writeCore_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => Bounds.writeCore (M z) (N z) (n z) (D z)) := by
  let P := (A × ℕ) × ℕ
  let M' := fun z : P => M z.1.1
  let N' := fun z : P => N z.1.1
  let n' := fun z : P => n z.1.1
  let D' := fun z : P => D z.1.1
  have hp : Computable (fun z : P => z.1.1) := Computable.fst.comp Computable.fst
  have hm : Computable M' := hM.comp hp
  have hnn : Computable n' := hn.comp hp
  have hnd : Computable N' := hN.comp hp
  obtain ⟨hC,hB,hA⟩ := read_named M' N' n' D' hm hnd hnn (hD.comp hp)
  have hb := base.to_comp.comp hm
  have hQ : Computable (fun z : P => z.1.2) := Computable.snd.comp Computable.fst
  have hterm := ((hC.selector (fun z => (M' z).base) (fun z => z.1.2) hb hQ).mul
    (hB.selector (fun z => (M' z).base) Prod.snd hb Computable.snd)).mul
    (branch_named M' N' n' (fun z => z.1.2) Prod.snd _ _ hm hnd hnn hQ Computable.snd hA hB)
  have hsum := (hterm.sum_range (fun z : A × ℕ => (M z.1).alphabet)
    (alphabet.to_comp.comp (hM.comp Computable.fst))).sum_range
      (fun z => (M z).states+1) (Computable.succ.comp (states.to_comp.comp hM))
  exact (hsum.divNat (fun z => (M z).base) (base.to_comp.comp hM)).congr (by
    intro z; dsimp [P,M',N',n',D',Bounds.writeCore]; ring)

lemma haltWeight_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.haltWeight (M z) (N z) (n z) (D z)) := by
  have hC := (read_named M N n D hM hN hn hD).1
  have hsel := (hC.comp (g := (Prod.fst : A × ℕ → A)) Computable.fst).selector
    (fun z => (M z.1).base) Prod.snd (base.to_comp.comp (hM.comp Computable.fst)) Computable.snd
  have hp : Computable (fun z : A × ℕ =>
      decide (z.2 = (M z.1).states ∨ z.2 ∈ (M z.1).haltingStates)) :=
    (Computable.cond
      (Primrec.eq.decide.to_comp.comp Computable.snd (states.to_comp.comp (hM.comp Computable.fst)))
      (Computable.const true)
      (member.decide.to_comp.comp (haltingStates.to_comp.comp (hM.comp Computable.fst)) Computable.snd)).of_eq
        (by intro z; simp)
  exact ((Named.ite _ hp hsel (Named.const 0)).sum_range
    (fun z => (M z).states+1) (Computable.succ.comp (states.to_comp.comp hM))).congr
    (by intro z; simp only [LocalRule.haltWeight, Function.comp_apply, Rat.cast_zero])

lemma write_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.write (M z) (N z) (n z) (D z)) := by
  have he := epsilon_named.comp ((hM.pair hN).pair (Computable.succ.comp hn))
  exact (he.mul (writeCore_named M N n D hM hN hn hD)).congr
    (fun z => (Bounds.write_factor _ _ _ _).symm)

lemma signal_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.signal (M z) (N z) (n z) (D z)) := by
  have he := epsilon_named.comp ((hM.pair hN).pair hn)
  have he' := epsilon_named.comp ((hM.pair hN).pair (Computable.succ.comp hn))
  exact ((he.sub he').add (((Named.const 2).mul he').mul
    (haltWeight_named M N n D hM hN hn hD))).congr (by intro z; simp [LocalRule.signal])

end AlternatingNS.Effective

end LocalNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/BaseNames.lean =====
namespace OAI

section BaseNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

def ratCoord (q : RationalVector) (i : Fin 3) : ℚ := ![q.1,q.2.1,q.2.2] i

lemma ratCoord_computable : Computable (fun z : RationalVector × Fin 3 => ratCoord z.1 z.2) := by
  have hi (i : Fin 3) : Computable (fun z : RationalVector × Fin 3 => decide (z.2 = i)) :=
    Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const i)
  exact (Computable.cond (hi 0) (Computable.fst.comp Computable.fst)
    (Computable.cond (hi 1) (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))).of_eq
        (by rintro ⟨q,i⟩; fin_cases i <;> rfl)

lemma ratCoord_cast (q : RationalVector) (i : Fin 3) :
    (ratCoord q i : ℝ) = rationalVector q i := by
  fin_cases i <;> rfl

lemma coord_named (q : A → RationalPoint) (i : A → Fin 3)
    (hq : Computable q) (hi : Computable i) :
    Named (fun a => (rationalPoint (q a)).2 (i a)) :=
  (Named.rational (ratCoord_computable.comp ((Computable.snd.comp hq).pair hi))).congr
    (fun a => ratCoord_cast (q a).2 (i a))

lemma cutoff_named (q : A → RationalPoint) (hq : Computable q) :
    Named (fun a => Spatial.cutoff (rationalPoint (q a)).2) := by
  have h (i : Fin 3) := coord_named q (fun _ => i) hq (Computable.const i)
  have ht (i : Fin 3) := (((Named.const 3).sub (h i)).transition).mul
    (((Named.const 3).add (h i)).transition)
  exact (((ht 0).mul (ht 1)).mul (ht 2)).congr (by
    intro a; simp [Spatial.cutoff, Fin.prod_univ_succ]; ring)

lemma direction_succ (i : Fin 3) : direction i.succ = (0,e i) := by
  fin_cases i <;> rfl

lemma JetBound.spatial_d_named {f : A → Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2).2))
    (i : A → Fin 3) (hi : Computable i) :
    Named (fun z : A × RationalPoint => Spatial.d (i z.1) (f z.1) (rationalPoint z.2).2) := by
  have hf' := hf.comp_unit (fun _ => ContinuousLinearMap.snd ℝ ℝ Space) (fun _ => norm_snd)
  have hd := hf'.named_directional hn (fun a => (i a).succ) (Primrec.fin_succ.to_comp.comp hi)
  apply hd.congr
  intro z
  rw [direction_succ]
  dsimp [Spatial.d, Function.comp_def]
  rw [fderiv_fun_comp _ ((hf.1 z.1).differentiable (by simp) _) (differentiableAt_snd)]
  simp [fderiv_snd]

noncomputable def slotPotential (p : (Machine × ℕ) × ℕ) (x : Space) : ℝ :=
  Spatial.cutoff x * Spatial.shearPotential (Construction.donorIndex p.2)
    (Construction.receiverIndex p.2) 0 (LocalRule.write p.1.1 p.1.2 p.2)
      (LocalRule.signal p.1.1 p.1.2 p.2) x

noncomputable def loadPotential (p : Machine × List ℕ) (x : Space) : ℝ :=
  Spatial.cutoff x * Spatial.shearPotential 2 1 0
    (fun _ => Scales.ε p.1.base p.2.length 0 * p.1.recordedBlock p.2 0)
    (fun _ => 1 - Scales.ε p.1.base p.2.length 0) x

lemma loadPotential_bound : JetBound loadPotential := by
  obtain ⟨hs,B,hB,h⟩ := loadingPotential_scaled
  refine ⟨fun p => hs p 0, B, hB, fun p r x => ?_⟩
  change ‖iteratedFDeriv ℝ r (fun x : Space => Spatial.cutoff x *
    Spatial.shearPotential 2 1 0 (fun _ => Scales.ε p.1.base p.2.length 0 * p.1.recordedBlock p.2 0)
      (fun _ => 1 - Scales.ε p.1.base p.2.length 0) x) x‖ ≤ _
  simpa only [one_pow, mul_one] using h p r 0 x

lemma slotPotential_bound : JetBound slotPotential := by
  obtain ⟨C,hC,hc⟩ := potential_bound
  let S : (Machine × ℕ) × ℕ → ℕ := fun p => p.1.1.base ^
    (Scales.s p.1.2 p.2 + 1 + Scales.K p.1.2 p.2)
  have hS : Computable S := nat_pow.to_comp.comp
    (base.to_comp.comp (Computable.fst.comp Computable.fst))
    (Primrec.nat_add.to_comp.comp
      (Computable.succ.comp (exponent.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
      (capacity.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
  refine ⟨fun p => Spatial.cutoff_smooth.mul (Spatial.shearPotential_smooth _ _ _ _ _
    (LocalRule.write_smooth p.1.1 p.1.2 p.2) (LocalRule.signal_smooth p.1.1 p.1.2 p.2)),
    fun z => C (z.1.1,z.2) * (1 + S z.1 ^ z.2),
    Primrec.nat_mul.to_comp.comp
      (hC.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (Primrec.nat_add.to_comp.comp (Computable.const 1)
        (nat_pow.to_comp.comp (hS.comp Computable.fst) Computable.snd)), ?_⟩
  intro p r x
  have e₁ : Scales.ε p.1.1.base p.1.2 p.2 ≤ 1 :=
    (le_abs_self _).trans (Bounds.inverse_power_bound _ _)
  have e₂ : Scales.ε p.1.1.base p.1.2 (p.2+1) ≤ 1 :=
    (le_abs_self _).trans (Bounds.inverse_power_bound _ _)
  have hsc : Bounds.readScale p.1.1 p.1.2 p.2 = (S p : ℝ) := by
    simp [Bounds.readScale, S]
  apply (hc p.1.1 p.1.2 r p.2 x).trans
  push_cast
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [hsc]
  exact add_le_add e₁ (mul_le_of_le_one_left (by positivity) e₂)

lemma donor_computable : Computable Construction.donorIndex := by
  exact (Computable.cond
    (Primrec.eq.decide.to_comp.comp (Primrec.nat_mod.to_comp.comp Computable.id (Computable.const 2)) (Computable.const 0))
    (Computable.const (1 : Fin 3)) (Computable.const 2)).of_eq (by intros; simp [Construction.donorIndex])

lemma receiver_computable : Computable Construction.receiverIndex := by
  exact (Computable.cond
    (Primrec.eq.decide.to_comp.comp (Primrec.nat_mod.to_comp.comp Computable.id (Computable.const 2)) (Computable.const 0))
    (Computable.const (2 : Fin 3)) (Computable.const 1)).of_eq (by intros; simp [Construction.receiverIndex])

lemma loadPotential_named :
    Named (fun z : (Machine × List ℕ) × RationalPoint => loadPotential z.1 (rationalPoint z.2).2) := by
  let P := (Machine × List ℕ) × RationalPoint
  have hM : Computable (fun z : P => z.1.1) := Computable.fst.comp Computable.fst
  have hw : Computable (fun z : P => z.1.2) := Computable.snd.comp Computable.fst
  have he := epsilon_named.comp ((hM.pair (Computable.list_length.comp hw)).pair (Computable.const 0))
  have hblock := (Named.rational (initialBlock_primrec.to_comp.comp hM hw)).congr
    (fun z : P => initialBlock_cast z.1.1 z.1.2)
  have hcoord (i : Fin 3) := coord_named (Prod.snd : P → RationalPoint) (fun _ => i)
    Computable.snd (Computable.const i)
  exact ((cutoff_named (Prod.snd : P → RationalPoint) Computable.snd).mul
    (((hcoord 0).mul (he.mul hblock)).sub ((hcoord 1).mul ((Named.const 1).sub he)))).congr
      (by intro z; simp only [loadPotential, Spatial.shearPotential, Rat.cast_one, Function.comp_def])

lemma slotPotential_named :
    Named (fun z : ((Machine × ℕ) × ℕ) × RationalPoint => slotPotential z.1 (rationalPoint z.2).2) := by
  let P := ((Machine × ℕ) × ℕ) × RationalPoint
  let M := fun z : P => z.1.1.1
  let N := fun z : P => z.1.1.2
  let n := fun z : P => z.1.2
  have hM : Computable M := Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hN : Computable N := Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hn : Computable n := Computable.snd.comp Computable.fst
  have hd := coord_named (Prod.snd : P → RationalPoint) (fun z => Construction.donorIndex (n z))
    Computable.snd (donor_computable.comp hn)
  have hi := coord_named (Prod.snd : P → RationalPoint) (fun z => Construction.receiverIndex (n z))
    Computable.snd (receiver_computable.comp hn)
  have h0 := coord_named (Prod.snd : P → RationalPoint) (fun _ => 0) Computable.snd (Computable.const 0)
  have hw := write_named M N n _ hM hN hn hd
  have hs := signal_named M N n _ hM hN hn hd
  exact ((cutoff_named (Prod.snd : P → RationalPoint) Computable.snd).mul
    ((h0.mul hw).sub (hi.mul hs))).congr (by intro z; rfl)

end AlternatingNS.Effective

end BaseNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/MixedPrograms.lean =====
namespace OAI

section MixedProgramsDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A E F : Type*} [Primcodable A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma wordJet_linear {f : ℝ × Space → E} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (w : List (Fin 4)) :
    wordJet (L ∘ f) w = L ∘ wordJet f w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext z
    simp only [wordJet, ih]
    rw [fderiv_comp _ L.differentiableAt ((wordJet_smooth hf w).differentiable (by simp) z), L.fderiv]
    rfl

lemma wordJet_component {f : ℝ × Space → Space} (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) (w : List (Fin 4)) :
    wordJet (fun z => f z i) w = fun z => wordJet f w z i :=
  wordJet_linear hf (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i) w

lemma JetBound.named_component_words {f : A → ℝ × Space → Space} (hf : JetBound f)
    (hn : Named (fun z : (A × Fin 3) × RationalPoint => f z.1.1 (rationalPoint z.2) z.1.2)) :
    Named (fun z : ((A × Fin 3) × List (Fin 4)) × RationalPoint =>
      wordJet (f z.1.1.1) z.1.2 (rationalPoint z.2) z.1.1.2) := by
  have hp := (hf.param (Computable.fst : Computable (Prod.fst : A × Fin 3 → A))).linear_unit
    (fun p => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) p.2) (fun p => norm_proj p.2)
  exact (hp.named_wordJet hn).congr (fun z => congrFun (wordJet_component (hf.1 z.1.1.1) z.1.1.2 z.1.2) (rationalPoint z.2))

lemma wordJet_append (f : ℝ × Space → E) (v w : List (Fin 4)) :
    wordJet f (v ++ w) = wordJet (wordJet f w) v := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [List.cons_append, wordJet, ih]

lemma wordJet_dx (f : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (i : Fin 3) (n : ℕ) :
    Function.uncurry ((dx i)^[n] f) = wordJet (Function.uncurry f) (List.replicate n i.succ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext z
    rw [Function.iterate_succ_apply']
    change dx i ((dx i)^[n] f) z.1 z.2 = _
    rw [Bounds.dx_eq_full_directional _ (Analytic.iterate_dx_smooth f hf i n), ih]
    simp only [List.replicate_succ, wordJet, direction_succ]

lemma wordJet_dt (f : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) :
    Bounds.HalfEq (dt^[n] f) (fun t x => wordJet (Function.uncurry f) (List.replicate n 0) (t,x)) := by
  induction n with
  | zero => exact fun _ _ _ => rfl
  | succ n ih =>
    intro t ht x
    rw [Function.iterate_succ_apply']
    have hh := ih.dt t ht x
    have hs := wordJet_smooth hf (List.replicate n 0)
    rw [Analytic.dt_eq_full (fun t x => wordJet (Function.uncurry f) (List.replicate n 0) (t,x)) hs t ht x,
      Bounds.fullDt_eq_full_directional (fun t x => wordJet (Function.uncurry f) (List.replicate n 0) (t,x)) hs (t,x)] at hh
    change dt (dt^[n] f) t x = fderiv ℝ (wordJet (Function.uncurry f) (List.replicate n 0)) (t,x) (1,0) at hh
    simpa only [List.replicate_succ, wordJet, direction, Matrix.cons_val_zero] using hh

def mixedWord (l : ℕ) (α : IndexCode) : List (Fin 4) :=
  List.replicate l 0 ++ (List.replicate α.1 1 ++
    (List.replicate α.2.1 2 ++ List.replicate α.2.2 3))

lemma wordJet_spatial (f : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (α : IndexCode) :
    Function.uncurry (spatial (index α) f) =
      wordJet (Function.uncurry f) (List.replicate α.1 1 ++
        (List.replicate α.2.1 2 ++ List.replicate α.2.2 3)) := by
  simp only [spatial, index, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [wordJet_dx _ (Analytic.iterate_dx_smooth _ (Analytic.iterate_dx_smooth f hf 2 _) 1 _),
    wordJet_dx _ (Analytic.iterate_dx_smooth f hf 2 _), wordJet_dx f hf]
  simp only [wordJet_append]
  rfl

lemma mixed_eq_wordJet (f : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (l : ℕ) (α : IndexCode) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    mixed l (index α) f t x = wordJet (Function.uncurry f) (mixedWord l α) (t,x) := by
  have h := wordJet_dt (spatial (index α) f) (Analytic.spatial_smooth f hf _) l t ht x
  rw [wordJet_spatial f hf α] at h
  simpa only [mixedWord, wordJet_append, mixed] using h

lemma replicate_primrec {B : Type*} [Primcodable B] (b : B) : Primrec (fun n => List.replicate n b) := by
  have h := Primrec.nat_rec₁ (f := fun _ : ℕ => fun w : List B => b :: w) ([] : List B)
    (Primrec.list_cons.comp (Primrec.const b) Primrec.snd)
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change b :: _ = List.replicate (n+1) b
    rw [ih, List.replicate_succ]

lemma mixedWord_computable : Computable₂ mixedWord := by
  have hr (i : Fin 4) := (replicate_primrec i).to_comp
  exact Primrec.list_append.to_comp.comp ((hr 0).comp Computable.fst)
    (Primrec.list_append.to_comp.comp ((hr 1).comp (Computable.fst.comp Computable.snd))
      (Primrec.list_append.to_comp.comp ((hr 2).comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))
        ((hr 3).comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))))

end AlternatingNS.Effective

end MixedProgramsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Compilers.lean =====
namespace OAI

section CompilersDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma space_norm_le_sum (v : Space) : ‖v‖ ≤ ∑ i : Fin 3, |v i| := by
  have he : (∑ i : Fin 3, v i • e i) = v := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply]
  calc
    ‖v‖ = ‖∑ i : Fin 3, v i • e i‖ := congrArg norm he.symm
    _ ≤ ∑ i : Fin 3, ‖v i • e i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, Bounds.norm_e, mul_one, Real.norm_eq_abs]

lemma rationalVector_error (q : RationalVector) (v : Space) (k : ℕ)
    (h : ∀ i, |v i - rationalVector q i| ≤ (tolerance (k+2) : ℝ)) :
    ‖rationalVector q - v‖ ≤ dyadicError k := by
  apply (space_norm_le_sum _).trans
  have hi (i : Fin 3) : |(rationalVector q-v) i| ≤ (tolerance (k+2) : ℝ) := by
    change |rationalVector q i-v i| ≤ _
    rw [abs_sub_comm]
    exact h i
  have hsum : (∑ i : Fin 3, |(rationalVector q-v) i|) ≤ 3 * (tolerance (k+2) : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin 3, (tolerance (k+2) : ℝ) := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp
  apply hsum.trans
  simp only [tolerance_cast, dyadicError, pow_add]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<1/2) k]

lemma mul_precision (C k : ℕ) : (C : ℝ) * (tolerance (k+C) : ℝ) ≤ tolerance k := by
  rw [tolerance_add, mul_left_comm]
  exact mul_le_of_le_one_right (tolerance_pos _).le (nat_mul_tolerance C)

abbrev EvalInput := ℕ × IndexCode × RationalPoint × ℕ
abbrev ModInput := ℕ × IndexCode × ℕ × ℕ
abbrev BoundInput := ℕ × ℕ × IndexCode

def sample (b : (((A × Fin 3) × List (Fin 4)) × RationalPoint) × ℕ → ℚ)
    (a : A) (q : EvalInput) (i : Fin 3) : ℚ :=
  b ((((a,i),mixedWord q.1 q.2.1),q.2.2.1),q.2.2.2+2)

def values (b : (((A × Fin 3) × List (Fin 4)) × RationalPoint) × ℕ → ℚ)
    (a : A) (q : EvalInput) : RationalVector :=
  (sample b a q 0,sample b a q 1,sample b a q 2)

lemma sample_computable (b : (((A × Fin 3) × List (Fin 4)) × RationalPoint) × ℕ → ℚ)
    (hb : Computable b) (i : Fin 3) : Computable₂ (fun a : A => fun q : EvalInput => sample b a q i) := by
  have hl : Computable (fun z : A × EvalInput => z.2.1) := Computable.fst.comp Computable.snd
  have hα : Computable (fun z : A × EvalInput => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hq : Computable (fun z : A × EvalInput => z.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hk : Computable (fun z : A × EvalInput => z.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact hb.comp ((((Computable.fst.pair (Computable.const i)).pair
    (mixedWord_computable.comp hl hα)).pair hq).pair
    (Primrec.nat_add.to_comp.comp hk (Computable.const 2)))

lemma values_computable (b : (((A × Fin 3) × List (Fin 4)) × RationalPoint) × ℕ → ℚ)
    (hb : Computable b) : Computable₂ (values b) :=
  (sample_computable b hb 0).pair ((sample_computable b hb 1).pair (sample_computable b hb 2))

def modulus (B : A × ℕ × ℕ → ℕ) (a : A) (q : ModInput) : ℕ :=
  q.2.2.2 + B (a,0,(mixedWord q.1 q.2.1).length+1)

lemma modulus_computable (B : A × ℕ × ℕ → ℕ) (hB : Computable B) : Computable₂ (modulus B) := by
  have hl : Computable (fun z : A × ModInput => z.2.1) := Computable.fst.comp Computable.snd
  have hα : Computable (fun z : A × ModInput => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun z : A × ModInput => z.2.2.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact Primrec.nat_add.to_comp.comp hk (hB.comp (Computable.fst.pair
    ((Computable.const 0).pair (Computable.succ.comp (Computable.list_length.comp
      (mixedWord_computable.comp hl hα))))))

def bound (B : A × ℕ × ℕ → ℕ) (a : A) (q : BoundInput) : ℕ :=
  B (a,q.1,(mixedWord q.2.1 q.2.2).length)

lemma bound_computable (B : A × ℕ × ℕ → ℕ) (hB : Computable B) : Computable₂ (bound B) := by
  have hJ : Computable (fun z : A × BoundInput => z.2.1) := Computable.fst.comp Computable.snd
  have hl : Computable (fun z : A × BoundInput => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hα : Computable (fun z : A × BoundInput => z.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact hB.comp (Computable.fst.pair (hJ.pair
    (Computable.list_length.comp (mixedWord_computable.comp hl hα))))

lemma Certified.programs {f : A → Velocity}
    (hf : Certified (fun a => Function.uncurry (f a)))
    (hn : Named (fun z : (A × Fin 3) × RationalPoint =>
      f z.1.1 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2)) :
    ∃ compile : A → FieldProgram, Computable compile ∧ ∀ a, ProgramFor (compile a) (f a) := by
  obtain ⟨b,hb,hbError⟩ := hf.jetBound.named_component_words hn
  obtain ⟨sf,B,hB,hBound⟩ := hf
  obtain ⟨ce,hce,he⟩ := compiler_of_computable (values b) (values_computable b hb)
  obtain ⟨cm,hcm,hm⟩ := compiler_of_computable (modulus B) (modulus_computable B hB)
  obtain ⟨cb,hcb,hc⟩ := compiler_of_computable (bound B) (bound_computable B hB)
  refine ⟨fun a => (ce a,cm a,cb a), hce.pair (hcm.pair hcb), fun a => ⟨?_,?_,?_⟩⟩
  · intro l α q k
    refine ⟨values b a (l,α,q,k),?_,fun ht => ?_⟩
    · have hh := he a (l,α,q,k)
      rcases q with ⟨t,x,y,z⟩
      simpa only [Returns, values, Encodable.encode_prod_val, Arithmetic.rationalCoding_encode] using hh
    · rw [mixed_eq_wordJet (f a) (sf a) l α _ (by change 0 ≤ (q.1 : ℝ); exact_mod_cast ht)]
      apply rationalVector_error
      intro i
      have hh := hbError (((a,i),mixedWord l α),q) (k+2)
      have heq : rationalVector (values b a (l,α,q,k)) i = (sample b a (l,α,q,k) i : ℝ) := by
        fin_cases i <;> rfl
      rw [heq]
      exact hh
  · intro l α R k
    refine ⟨modulus B a (l,α,R,k),hm a (l,α,R,k),fun z z' ht ht' _ _ hd => ?_⟩
    rw [mixed_eq_wordJet (f a) (sf a) l α z.1 ht z.2,
      mixed_eq_wordJet (f a) (sf a) l α z'.1 ht' z'.2]
    let C := B (a,0,(mixedWord l α).length+1)
    have hC (y : ℝ × Space) : ‖iteratedFDeriv ℝ 1 (wordJet (Function.uncurry (f a)) (mixedWord l α)) y‖ ≤ C := by
      have hC' : ‖iteratedFDeriv ℝ (1+(mixedWord l α).length) (Function.uncurry (f a)) y‖ ≤ C := by
        rw [Nat.add_comm 1 (mixedWord l α).length]
        simpa only [C, pow_zero, one_mul] using hBound a 0 ((mixedWord l α).length+1) y
      exact (wordJet_bound (sf a) (mixedWord l α) 1 y).trans hC'
    have hLip := jet_lipschitz (wordJet_smooth (sf a) (mixedWord l α)) C hC z z'
    exact hLip.trans ((mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg C)).trans (by
      simpa only [modulus, C, tolerance_cast] using mul_precision C k))
  · intro J l α
    refine ⟨bound B a (J,l,α),hc a (J,l,α),fun t ht x => ?_⟩
    rw [mixed_eq_wordJet (f a) (sf a) l α t ht x]
    have hnorm : ‖wordJet (Function.uncurry (f a)) (mixedWord l α) (t,x)‖ ≤
        ‖iteratedFDeriv ℝ (mixedWord l α).length (Function.uncurry (f a)) (t,x)‖ := by
      have hh := wordJet_bound (sf a) (mixedWord l α) 0 (t,x)
      rw [Nat.zero_add] at hh
      simpa only [norm_iteratedFDeriv_zero] using hh
    apply (mul_le_mul_of_nonneg_left hnorm (by positivity : (0:ℝ) ≤ (1+t+‖x‖)^J)).trans
    simpa only [bound, weight, abs_of_nonneg ht] using hBound a J (mixedWord l α).length (t,x)

end AlternatingNS.Effective

namespace AlternatingNS

lemma ProgramFor.congr_half {c : FieldProgram} {f g : Velocity}
    (hf : ProgramFor c f) (h : Bounds.HalfEq f g) : ProgramFor c g := by
  refine ⟨?_,?_,?_⟩
  · intro l α q k
    obtain ⟨v,hv,he⟩ := hf.1 l α q k
    refine ⟨v,hv,fun ht => ?_⟩
    rw [← h.mixed l (index α) _ (by change 0 ≤ (q.1 : ℝ); exact_mod_cast ht) _]
    exact he ht
  · intro l α R k
    obtain ⟨m,hm,he⟩ := hf.2.1 l α R k
    refine ⟨m,hm,fun z z' ht ht' hz hz' hd => ?_⟩
    rw [← h.mixed l (index α) _ ht _, ← h.mixed l (index α) _ ht' _]
    exact he z z' ht ht' hz hz' hd
  · intro J l α
    obtain ⟨B,hB,he⟩ := hf.2.2 J l α
    refine ⟨B,hB,fun t ht x => ?_⟩
    rw [← h.mixed l (index α) _ ht _]
    exact he t ht x

end AlternatingNS

end CompilersDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/VelocityNames.lean =====
namespace OAI

section VelocityNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma JetBound.curl_named {f : A → Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2).2))
    (i j : A → Fin 3) (hi : Computable i) (hj : Computable j) :
    Named (fun z : (A × Fin 3) × RationalPoint =>
      Spatial.curl (i z.1.1) (j z.1.1) (f z.1.1) (rationalPoint z.2).2 z.1.2) := by
  have hp : Computable (fun z : (A × Fin 3) × RationalPoint => (z.1.1,z.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have hdj := (hf.spatial_d_named hn j hj).comp hp
  have hdi := (hf.spatial_d_named hn i hi).comp hp
  have hqi : Computable (fun z : (A × Fin 3) × RationalPoint => decide (z.1.2 = i z.1.1)) := Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.fst)
    (hi.comp (Computable.fst.comp Computable.fst))
  have hqj : Computable (fun z : (A × Fin 3) × RationalPoint => decide (z.1.2 = j z.1.1)) := Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.fst)
    (hj.comp (Computable.fst.comp Computable.fst))
  exact ((Named.ite _ hqi hdj (Named.const 0)).sub
    (Named.ite _ hqj hdi (Named.const 0))).congr (by
      intro z; simp [Spatial.curl, Spatial.e_apply])

lemma loading_named : Named (fun z : ((Machine × List ℕ) × Fin 3) × RationalPoint =>
    Construction.loading z.1.1.1 z.1.1.2 (rationalPoint z.2).2 z.1.2) := by
  exact loadPotential_bound.curl_named loadPotential_named (fun _ => 1) (fun _ => 0)
    (Computable.const 1) (Computable.const 0)

lemma slot_named : Named (fun z : (((Machine × ℕ) × ℕ) × Fin 3) × RationalPoint =>
    Construction.slot z.1.1.1.1 z.1.1.1.2 z.1.1.2 (rationalPoint z.2).2 z.1.2) := by
  exact slotPotential_bound.curl_named slotPotential_named
    (fun p => Construction.receiverIndex p.2) (fun _ => 0)
    (receiver_computable.comp Computable.snd) (Computable.const 0)

lemma piece_named : Named (fun z : (((Machine × List ℕ) × ℕ) × Fin 3) × RationalPoint =>
    Construction.piece z.1.1.1.1 z.1.1.1.2 z.1.1.2 (rationalPoint z.2).2 z.1.2) := by
  let P := (((Machine × List ℕ) × ℕ) × Fin 3) × RationalPoint
  have hM : Computable (fun z : P => z.1.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hw : Computable (fun z : P => z.1.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hn : Computable (fun z : P => z.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun z : P => z.1.2) := Computable.snd.comp Computable.fst
  have hload := loading_named.comp (((hM.pair hw).pair hi).pair Computable.snd)
  have hslot := slot_named.comp ((((hM.pair (Computable.list_length.comp hw)).pair
    (Primrec.nat_sub.to_comp.comp hn (Computable.const 1))).pair hi).pair Computable.snd)
  exact (Named.ite (fun z : P => z.1.1.2 = 0)
    (Primrec.eq.decide.to_comp.comp hn (Computable.const 0)) hload hslot).congr
      (by rintro ⟨⟨⟨⟨M,w⟩,n⟩,i⟩,q⟩; cases n <;> rfl)

lemma clock_bound : JetBound (fun _ : Unit => Profiles.clock) := by
  have hclock := transition_scaled.affine (fun _ _ => zero_le_one) (fun _ _ => 2)
    (fun _ _ => -1/2) (fun _ => 2) (Computable.const 2) (by intros; norm_num)
  obtain ⟨hs,B,hB,h⟩ := hclock
  refine ⟨fun _ => Profiles.clock_smooth, B, hB, fun p r x => ?_⟩
  have he : (fun t => Real.smoothTransition (2 * t + -1/2)) = Profiles.clock := by
    funext t; unfold Profiles.clock; congr 1; ring
  simpa only [one_pow, mul_one, he] using h p r 0 x

lemma pulse_rational_named : Named (fun q : ℚ => Profiles.pulse (q : ℝ)) := by
  have hf := clock_bound.comp_unit (fun _ => ContinuousLinearMap.fst ℝ ℝ Space) (fun _ => norm_fst)
  have hn : Named (fun z : Unit × RationalPoint => Profiles.clock (rationalPoint z.2).1) := by
    have ht := Named.rational (Computable.fst.comp (Computable.snd : Computable (Prod.snd : Unit × RationalPoint → _)))
    exact (((Named.const 2).mul ht).sub (Named.const (1/2))).transition.congr (by
      intro z; simp [Profiles.clock, rationalPoint])
  have hd := hf.named_directional hn (fun _ => 0) (Computable.const 0)
  have hdc := hd.comp ((Computable.const ()).pair (Computable.id.pair
    ((Computable.const (0:ℚ)).pair ((Computable.const (0:ℚ)).pair (Computable.const (0:ℚ))))))
  apply hdc.congr
  intro q
  change fderiv ℝ (Profiles.clock ∘ Prod.fst) ((q:ℝ),_) (1,0) = deriv Profiles.clock (q:ℝ)
  rw [fderiv_comp _ (Profiles.clock_smooth.differentiable (by simp) _) differentiableAt_fst, fderiv_fst]
  rfl

lemma velocity_named : Named (fun z : ((Machine × List ℕ) × Fin 3) × RationalPoint =>
    Construction.velocity z.1.1.1 z.1.1.2 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2) := by
  let P := ((Machine × List ℕ) × Fin 3) × RationalPoint
  have hq : Computable (fun z : P => z.2.1) := Computable.fst.comp Computable.snd
  let N : P → ℕ := fun z => z.2.1.num.natAbs+1
  have hN : Computable N := Computable.succ.comp (Arithmetic.int_abs.to_comp.comp (Arithmetic.rat_num.to_comp.comp hq))
  have hterm : Named (fun z : P × ℕ => Profiles.pulse ((rationalPoint z.1.2).1 - z.2) *
      Construction.piece z.1.1.1.1 z.1.1.1.2 z.2 (rationalPoint z.1.2).2 z.1.1.2) := by
    have hh := pulse_rational_named.comp (Arithmetic.rat_sub.to_comp.comp
      (hq.comp Computable.fst) (Arithmetic.rat_natCast.to_comp.comp Computable.snd))
    have hp := piece_named.comp
      ((((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair Computable.snd).pair
        (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        (Computable.snd.comp Computable.fst))
    exact (hh.mul hp).congr (by intro z; simp [rationalPoint])
  apply (hterm.sum_range N hN).congr
  intro z
  have ht : (rationalPoint z.2).1 ≤ (N z : ℝ) := by
    have hr := le_trans (le_abs_self (z.2.1 : ℝ)) (abs_rat_cast_le_num z.2.1)
    dsimp [N, rationalPoint]; push_cast; linarith
  rw [Construction.velocity, TimeGlue.eq_sum _ Profiles.pulse_zero_left _ _ _ (N z) ht]
  simp [WithLp.ofLp_sum, Finset.sum_apply]

end AlternatingNS.Effective

end VelocityNamesDevelopment

end OAI

-- ===== The platform statement OAI.AlternatingNS.velocity_construction =====
open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory OAI OAI.AlternatingNS

theorem solution :
    ∃ (U : Machine × List ℕ → Velocity) (compileVelocity : Machine × List ℕ → FieldProgram)
      (K : Set Space),
      Computable compileVelocity ∧ IsCompact K ∧
      ∀ (M : Machine) (w : List ℕ), M.WellFormed → M.ValidInput w →
        ProgramFor (compileVelocity (M, w)) (U (M, w)) ∧
        Smooth (U (M, w)) ∧ SupportedIn (U (M, w)) K ∧ Rapid (U (M, w)) ∧
        (∀ x, U (M, w) 0 x = 0) ∧
        (∀ t, 0 ≤ t → ∀ x, div (U (M, w)) t x = 0) ∧
        ∀ γ : ℝ → Space, IsTrajectory (U (M, w)) observedParticle γ →
          ((∃ t : ℝ, 0 ≤ t ∧ 0 < γ t 0) ↔ M.Halts w) := by
  obtain ⟨cu, hcu, hu⟩ := Effective.Certified.programs
    Effective.velocity_certified Effective.velocity_named
  refine ⟨fun z => Construction.velocity z.1 z.2, cu, Spatial.box, hcu, Spatial.box_compact, ?_⟩
  intro M w hM hw
  obtain ⟨_, hUs, _, hUk, hNS, X, hX, hXu, hhalt⟩ :=
    Construction.smooth_forced_simulation 1 M hM w hw
  refine ⟨hu (M, w), hUs, hUk, Bounds.velocity_rapid M w, hNS.2.1,
    fun t ht x => (hNS.2.2 t ht x).1, ?_⟩
  intro γ hγ
  have heq : ∀ t, 0 ≤ t → γ t = X observedParticle t := hXu _ _ hγ
  rw [← hhalt]
  constructor
  · rintro ⟨t, ht, hpos⟩; exact ⟨t, ht, by rw [← heq t ht]; exact hpos⟩
  · rintro ⟨t, ht, hpos⟩; exact ⟨t, ht, by rw [heq t ht]; exact hpos⟩
