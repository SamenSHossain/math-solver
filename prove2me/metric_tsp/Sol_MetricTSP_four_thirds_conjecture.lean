import Mathlib
import Definitions.Def_MetricTSP_model
import Theorems.Thm_MetricTSP_four_thirds_conjecture_of_five_le

set_option autoImplicit false

namespace MetricTSP.SmallCasesT1
open MetricTSP

theorem tspOpt_le_tourCost {n : ℕ} (c : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    tspOpt c ≤ tourCost c π := by
  unfold tspOpt
  apply csInf_le
  · have hfin : {t : ℝ | ∃ π : Equiv.Perm (Fin n), t = tourCost c π}.Finite := by
      have : {t : ℝ | ∃ π : Equiv.Perm (Fin n), t = tourCost c π} =
          Set.range (fun π : Equiv.Perm (Fin n) => tourCost c π) := by
        ext t; simp [eq_comm]
      rw [this]; exact Set.finite_range _
    exact hfin.bddBelow
  · exact ⟨π, rfl⟩

/-- uniform feasible point -/
noncomputable def unif (n : ℕ) : Fin n → Fin n → ℝ :=
  fun u v => if u = v then 0 else 2 / ((n : ℝ) - 1)

theorem unif_isHeldKarp {n : ℕ} (hn : 3 ≤ n) : IsHeldKarp (unif n) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v; simp only [unif, eq_comm]
  · intro v; simp [unif]
  · intro u v; unfold unif; split_ifs
    · exact le_rfl
    · positivity
  · intro u v; unfold unif; split_ifs
    · norm_num
    · rw [div_le_one hpos]; linarith
  · intro v
    have h : ∀ u : Fin n, unif n v u = 2 / ((n : ℝ) - 1) - (if v = u then 2 / ((n : ℝ) - 1) else 0) := by
      intro u; unfold unif; split_ifs <;> ring
    simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro S hS hSu
    have h : ∀ u ∈ S, ∑ v ∈ Sᶜ, unif n u v = ∑ v ∈ Sᶜ, 2 / ((n : ℝ) - 1) := by
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have : u ≠ v := by
        rintro rfl; simp at hv; exact hv hu
      simp [unif, this]
    rw [Finset.sum_congr rfl h]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_compl, Fintype.card_fin]
    have hk1 : 1 ≤ S.card := Finset.card_pos.mpr hS
    have hk2 : S.card < n := by
      have := (Finset.card_lt_iff_ne_univ S).mpr hSu
      simpa using this
    rw [Nat.cast_sub hk2.le]
    have hk1' : (1 : ℝ) ≤ S.card := by exact_mod_cast hk1
    have hk2' : (S.card : ℝ) + 1 ≤ n := by exact_mod_cast hk2
    rw [show (S.card : ℝ) * (((n : ℝ) - S.card) * (2 / ((n : ℝ) - 1)))
        = 2 * (S.card * ((n : ℝ) - S.card)) / ((n : ℝ) - 1) by ring]
    rw [le_div_iff₀ hpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1') (show (0:ℝ) ≤ (n:ℝ) - S.card - 1 by linarith)]

theorem hk_set_nonempty {n : ℕ} (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ) :
    {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}.Nonempty :=
  ⟨_, unif n, unif_isHeldKarp hn, rfl⟩

theorem le_hkValue_of_forall {n : ℕ} (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ) {a : ℝ}
    (h : ∀ x : Fin n → Fin n → ℝ, IsHeldKarp x → a ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v) :
    a ≤ hkValue c := by
  unfold hkValue
  apply le_csInf (hk_set_nonempty hn c)
  rintro t ⟨x, hx, rfl⟩
  exact h x hx

theorem cost_nonneg {n : ℕ} {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) (u v : Fin n) :
    0 ≤ c u v := by
  obtain ⟨hs, hd, ht⟩ := hc
  have := ht u v u
  rw [hd u, hs v u] at this
  linarith

theorem hkValue_nonneg {n : ℕ} (hn : 3 ≤ n) {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) :
    0 ≤ hkValue c := by
  apply le_hkValue_of_forall hn c
  intro x hx
  have : 0 ≤ ∑ u, ∑ v, c u v * x u v :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (cost_nonneg hc u v) (hx.2.2.1 u v)
  linarith

theorem le_obj_fin3 (c : Fin 3 → Fin 3 → ℝ) (hc : IsMetricCost c) (x : Fin 3 → Fin 3 → ℝ)
    (hx : IsHeldKarp x) : tspOpt c ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  obtain ⟨hcs, hcd, -⟩ := hc
  obtain ⟨hxs, hxd, -, hx1, hdeg, -⟩ := hx
  have t1 := tspOpt_le_tourCost c 1
  have e1 : tourCost c 1 = c 0 1 + c 1 2 + c 2 0 := by
    simp [tourCost, Fin.sum_univ_three]
  have d0 := hdeg 0
  have d1 := hdeg 1
  simp only [Fin.sum_univ_three] at d0 d1 ⊢
  rw [hxd] at d0 d1
  rw [hxs 1 0] at d1
  have a01 : x 0 1 = 1 := by linarith [hx1 0 1, hx1 0 2]
  have a02 : x 0 2 = 1 := by linarith [hx1 0 1, hx1 0 2]
  have a12 : x 1 2 = 1 := by linarith [hx1 0 1, hx1 1 2]
  rw [hcd, hcd, hcd, hxs 1 0, hxs 2 0, hxs 2 1, hcs 1 0, hcs 2 0, hcs 2 1, a01, a02, a12]
  rw [hcs 2 0] at e1
  linarith

theorem le_obj_fin4 (c : Fin 4 → Fin 4 → ℝ) (hc : IsMetricCost c) (x : Fin 4 → Fin 4 → ℝ)
    (hx : IsHeldKarp x) : tspOpt c ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  obtain ⟨hcs, hcd, -⟩ := hc
  obtain ⟨hxs, hxd, hx0, hx1, hdeg, -⟩ := hx
  have tab := tspOpt_le_tourCost c (Equiv.swap 2 3)
  have tae := tspOpt_le_tourCost c 1
  have tbe := tspOpt_le_tourCost c (Equiv.swap 1 2)
  have eab : tourCost c (Equiv.swap 2 3) = c 0 1 + c 1 3 + c 3 2 + c 2 0 := by
    simp [tourCost, Fin.sum_univ_four, Equiv.swap_apply_of_ne_of_ne]
  have eae : tourCost c 1 = c 0 1 + c 1 2 + c 2 3 + c 3 0 := by
    simp [tourCost, Fin.sum_univ_four]
  have ebe : tourCost c (Equiv.swap 1 2) = c 0 2 + c 2 1 + c 1 3 + c 3 0 := by
    simp [tourCost, Fin.sum_univ_four, Equiv.swap_apply_of_ne_of_ne]
  rw [eab] at tab
  rw [eae] at tae
  rw [ebe] at tbe
  have d0 := hdeg 0
  have d1 := hdeg 1
  have d2 := hdeg 2
  have d3 := hdeg 3
  simp only [Fin.sum_univ_four] at d0 d1 d2 d3 ⊢
  simp only [hxd, hcd, hxs 1 0, hxs 2 0, hxs 3 0, hxs 2 1, hxs 3 1, hxs 3 2,
    hcs 1 0, hcs 2 0, hcs 3 0, hcs 2 1, hcs 3 1, hcs 3 2] at d0 d1 d2 d3 tab tae tbe ⊢
  have h23 : x 2 3 = x 0 1 := by linarith
  have h13 : x 1 3 = x 0 2 := by linarith
  have h12 : x 1 2 = x 0 3 := by linarith
  have h03 : x 0 3 = 2 - x 0 1 - x 0 2 := by linarith
  rw [h23, h13, h12, h03]
  have ha := hx1 0 1
  have hb := hx1 0 2
  have he := hx1 0 3
  rw [h03] at he
  have ha0 := hx0 0 1
  have hb0 := hx0 0 2
  have he0 := hx0 0 3
  rw [h03] at he0
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr tab),
    mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr tae),
    mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr tbe)]

theorem tspOpt_le_hkValue_small (n : ℕ) (hn : 3 ≤ n) (hn4 : n ≤ 4)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ hkValue c := by
  apply le_hkValue_of_forall hn c
  intro x hx
  interval_cases n
  · exact le_obj_fin3 c hc x hx
  · exact le_obj_fin4 c hc x hx

theorem four_thirds_of_le_four (n : ℕ) (hn : 3 ≤ n) (hn4 : n ≤ 4)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 4 / 3 * hkValue c := by
  have h1 := tspOpt_le_hkValue_small n hn hn4 c hc
  have h2 := hkValue_nonneg hn hc
  linarith

end MetricTSP.SmallCasesT1

open MetricTSP in
theorem solution (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 4 / 3 * hkValue c := by
  by_cases h5 : 5 ≤ n
  · exact MetricTSP.four_thirds_conjecture_of_five_le n h5 c hc
  · exact MetricTSP.SmallCasesT1.four_thirds_of_le_four n hn (by omega) c hc
