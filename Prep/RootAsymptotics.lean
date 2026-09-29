import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.LiminfLimsup

set_option autoImplicit false

/-!
# Root asymptotics

The analytic bridge from termwise exponential bounds `c ^ k ≤ u k ≤ C ^ k` on a
nonnegative sequence to `liminf`/`limsup` bounds on its `k`-th roots
`u k ^ (1 / k)`, as needed for Erdős Problem 77 (the limit of `R(k)^(1/k)`).
-/

namespace Prep

open Filter Topology

/-- If `x ≤ c ^ k` with `x, c ≥ 0` and `k ≠ 0`, then `x ^ (1/k) ≤ c`. -/
theorem rpow_one_div_le_of_le_pow {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) {k : ℕ} (hk : k ≠ 0)
    (h : x ≤ c ^ k) : x ^ (1 / (k : ℝ)) ≤ c := by
  have hkpos : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  calc x ^ (1 / (k : ℝ)) ≤ (c ^ k) ^ (1 / (k : ℝ)) := Real.rpow_le_rpow hx h hkpos
    _ = c := by rw [one_div]; exact Real.pow_rpow_inv_natCast hc hk

/-- If `c ^ k ≤ x` with `c ≥ 0` and `k ≠ 0`, then `c ≤ x ^ (1/k)`. -/
theorem le_rpow_one_div_of_pow_le {x c : ℝ} (hc : 0 ≤ c) {k : ℕ} (hk : k ≠ 0)
    (h : c ^ k ≤ x) : c ≤ x ^ (1 / (k : ℝ)) := by
  have hkpos : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  calc c = (c ^ k) ^ (1 / (k : ℝ)) := by
        rw [one_div]; exact (Real.pow_rpow_inv_natCast hc hk).symm
    _ ≤ x ^ (1 / (k : ℝ)) := Real.rpow_le_rpow (pow_nonneg hc k) h hkpos

/-- Roots of nonnegative reals are nonnegative. -/
theorem rpow_one_div_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ x ^ (1 / (k : ℝ)) :=
  Real.rpow_nonneg hx _

/-- A property holding from some index on holds eventually along `atTop`. -/
theorem eventually_le_of_forall_ge {α : Type*} (u : ℕ → α) (P : α → Prop) (N : ℕ)
    (h : ∀ k, N ≤ k → P (u k)) : ∀ᶠ k in atTop, P (u k) :=
  Filter.eventually_atTop.2 ⟨N, h⟩

/-- Eventual upper bound `u k ≤ c ^ k` gives `limsup (u k)^(1/k) ≤ c`. -/
theorem limsup_rpow_one_div_le (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᶠ k in atTop, u k ≤ c ^ k) :
    limsup (fun k : ℕ => u k ^ (1 / (k : ℝ))) atTop ≤ c := by
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun k : ℕ => u k ^ (1 / (k : ℝ))) :=
    isCoboundedUnder_le_of_le atTop (x := 0) (fun k => rpow_one_div_nonneg (hu k) k)
  refine limsup_le_of_le hcob ?_
  filter_upwards [h, eventually_ne_atTop 0] with k hk hk0
  exact rpow_one_div_le_of_le_pow (hu k) hc hk0 hk

/-- Eventual lower bound `c ^ k ≤ u k` (plus an eventual upper bound `u k ≤ C ^ k`,
needed so that the real `liminf` is meaningful) gives `c ≤ liminf (u k)^(1/k)`. -/
theorem le_liminf_rpow_one_div (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) {c C : ℝ} (hc : 0 ≤ c)
    (hC : 0 ≤ C) (hupper : ∀ᶠ k in atTop, u k ≤ C ^ k) (h : ∀ᶠ k in atTop, c ^ k ≤ u k) :
    c ≤ liminf (fun k : ℕ => u k ^ (1 / (k : ℝ))) atTop := by
  have hcob : IsCoboundedUnder (· ≥ ·) atTop (fun k : ℕ => u k ^ (1 / (k : ℝ))) := by
    refine isCoboundedUnder_ge_of_eventually_le atTop (x := C) ?_
    filter_upwards [hupper, eventually_ne_atTop 0] with k hk hk0
    exact rpow_one_div_le_of_le_pow (hu k) hC hk0 hk
  refine le_liminf_of_le hcob ?_
  filter_upwards [h, eventually_ne_atTop 0] with k hk hk0
  exact le_rpow_one_div_of_pow_le hc hk0 hk

/-- `√2 ^ k = 2 ^ (k / 2)`. -/
theorem sqrt_two_pow_eq (k : ℕ) : Real.sqrt 2 ^ k = (2 : ℝ) ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- `n ≤ 2 ^ (k / 2)` iff `n ^ 2 ≤ 2 ^ k` (as naturals). -/
theorem two_rpow_half_le_iff (k n : ℕ) :
    (n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2) ↔ n ^ 2 ≤ 2 ^ k := by
  have h2 : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ k := by
    rw [← sqrt_two_pow_eq, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have hpos : 0 ≤ (2 : ℝ) ^ ((k : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  rw [← pow_le_pow_iff_left₀ (Nat.cast_nonneg n) hpos two_ne_zero, h2]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- Headline upper bound: `R k ≤ 4 ^ k` for `k ≥ 1` gives `limsup R(k)^(1/k) ≤ 4`. -/
theorem limsup_le_four (R : ℕ → ℕ) (h : ∀ k, 1 ≤ k → (R k : ℝ) ≤ 4 ^ k) :
    limsup (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) atTop ≤ 4 :=
  limsup_rpow_one_div_le (fun k => (R k : ℝ)) (fun k => Nat.cast_nonneg _) (by norm_num)
    (Filter.eventually_atTop.2 ⟨1, h⟩)

/-- Headline lower bound: `2 ^ (k/2) ≤ R k` for `k ≥ 3` (together with the upper bound
`R k ≤ 4 ^ k`) gives `√2 ≤ liminf R(k)^(1/k)`. -/
theorem sqrt_two_le_liminf (R : ℕ → ℕ) (hupper : ∀ k, 1 ≤ k → (R k : ℝ) ≤ 4 ^ k)
    (hlower : ∀ k : ℕ, 3 ≤ k → (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (R k : ℝ)) :
    Real.sqrt 2 ≤ liminf (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) atTop :=
  le_liminf_rpow_one_div (fun k => (R k : ℝ)) (fun k => Nat.cast_nonneg _)
    (Real.sqrt_nonneg 2) (by norm_num)
    (Filter.eventually_atTop.2 ⟨1, hupper⟩)
    (Filter.eventually_atTop.2 ⟨3, fun k hk => by rw [sqrt_two_pow_eq]; exact hlower k hk⟩)

/-- The roots are bounded (below by `0`, eventually above by `4`), so `liminf ≤ limsup`. -/
theorem liminf_le_limsup_roots (R : ℕ → ℕ) (hupper : ∀ k, 1 ≤ k → (R k : ℝ) ≤ 4 ^ k) :
    liminf (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) atTop ≤
      limsup (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) atTop := by
  apply liminf_le_limsup
  · refine isBoundedUnder_of_eventually_le (a := 4) ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact rpow_one_div_le_of_le_pow (Nat.cast_nonneg _) (by norm_num) (by omega) (hupper k hk)
  · exact isBoundedUnder_of_eventually_ge (a := 0)
      (Eventually.of_forall fun k => rpow_one_div_nonneg (Nat.cast_nonneg _) k)

/-- `limsup_le_four` with the exponent spelled `(k : ℝ)⁻¹`. -/
theorem limsup_le_four' (R : ℕ → ℕ) (h : ∀ k, 1 ≤ k → (R k : ℝ) ≤ 4 ^ k) :
    limsup (fun k : ℕ => (R k : ℝ) ^ ((k : ℝ)⁻¹)) atTop ≤ 4 := by
  have := limsup_le_four R h
  simpa only [one_div] using this

/-- `sqrt_two_le_liminf` with the exponent spelled `(k : ℝ)⁻¹`. -/
theorem sqrt_two_le_liminf' (R : ℕ → ℕ) (hupper : ∀ k, 1 ≤ k → (R k : ℝ) ≤ 4 ^ k)
    (hlower : ∀ k : ℕ, 3 ≤ k → (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (R k : ℝ)) :
    Real.sqrt 2 ≤ liminf (fun k : ℕ => (R k : ℝ) ^ ((k : ℝ)⁻¹)) atTop := by
  have := sqrt_two_le_liminf R hupper hlower
  simpa only [one_div] using this

end Prep

#print axioms Prep.rpow_one_div_le_of_le_pow
#print axioms Prep.le_rpow_one_div_of_pow_le
#print axioms Prep.rpow_one_div_nonneg
#print axioms Prep.eventually_le_of_forall_ge
#print axioms Prep.limsup_rpow_one_div_le
#print axioms Prep.le_liminf_rpow_one_div
#print axioms Prep.sqrt_two_pow_eq
#print axioms Prep.two_rpow_half_le_iff
#print axioms Prep.limsup_le_four
#print axioms Prep.sqrt_two_le_liminf
#print axioms Prep.liminf_le_limsup_roots
#print axioms Prep.limsup_le_four'
#print axioms Prep.sqrt_two_le_liminf'
