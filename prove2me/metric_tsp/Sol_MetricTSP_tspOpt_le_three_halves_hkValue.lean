import Mathlib
import Definitions.Def_MetricTSP_model

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace MetricTSP.T3
open MetricTSP Finset

section PM

/-- cut value -/
def cut {V : Type*} [Fintype V] [DecidableEq V] (x : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, x u v

/-- fractional perfect matching polytope (Edmonds) -/
structure Feas {V : Type*} [Fintype V] [DecidableEq V] (x : V → V → ℝ) : Prop where
  symm : ∀ u v, x u v = x v u
  diag : ∀ v, x v v = 0
  nonneg : ∀ u v, 0 ≤ x u v
  deg : ∀ v, ∑ u, x v u = 1
  odd : ∀ S : Finset V, Odd S.card → 1 ≤ cut x S

/-- perfect matching as a fixed-point-free involution -/
def IsPM {V : Type*} (M : V → V) : Prop := ∀ v, M (M v) = v ∧ M v ≠ v

def PMProp (V : Type*) [Fintype V] [DecidableEq V] : Prop :=
  ∀ x : V → V → ℝ, Feas x → ∀ c : V → V → ℝ,
    ∃ M : V → V, IsPM M ∧ ∑ v, c v (M v) ≤ ∑ u, ∑ v, c u v * x u v

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma cut_compl (x : V → V → ℝ) (hs : ∀ u v, x u v = x v u) (S : Finset V) :
    cut x Sᶜ = cut x S := by
  unfold cut
  rw [compl_compl, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  exact hs _ _

lemma cut_eq_card_sub (x : V → V → ℝ) (hdeg : ∀ v, ∑ u, x v u = 1) (S : Finset V) :
    cut x S = S.card - ∑ u ∈ S, ∑ v ∈ S, x u v := by
  unfold cut
  have : ∀ u, ∑ v ∈ Sᶜ, x u v = 1 - ∑ v ∈ S, x u v := by
    intro u
    have h := Finset.sum_add_sum_compl S (x u)
    rw [hdeg u] at h; linarith
  rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_sub_distrib]
  simp

lemma cut_singleton (x : V → V → ℝ) (hdeg : ∀ v, ∑ u, x v u = 1) (hd : ∀ v, x v v = 0)
    (v : V) : cut x {v} = 1 := by
  rw [cut_eq_card_sub x hdeg]; simp [hd]

lemma cut_univ (x : V → V → ℝ) : cut x Finset.univ = 0 := by
  simp [cut]

lemma Feas.even_card {x : V → V → ℝ} (hx : Feas x) : Even (Fintype.card V) := by
  by_contra h
  have h1 := hx.odd Finset.univ (by rw [Finset.card_univ]; exact Nat.not_even_iff_odd.mp h)
  rw [cut_univ] at h1; linarith

lemma cut_lin (x d : V → V → ℝ) (t : ℝ) (S : Finset V) :
    cut (fun u v => x u v + t * d u v) S = cut x S + t * cut d S := by
  unfold cut
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- every even finset carries a perfect matching -/
lemma exists_pm_on (A : Finset V) (hA : Even A.card) :
    ∃ m : V → V, ∀ b ∈ A, m b ∈ A ∧ m b ≠ b ∧ m (m b) = b := by
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with hAe | ⟨a, ha⟩
    · exact ⟨id, by simp [hAe]⟩
    · have hc1 : 1 ≤ (A.erase a).card := by
        rw [Finset.card_erase_of_mem ha]
        have : A.card ≠ 1 := by intro h; rw [h] at hA; exact absurd hA (by decide)
        have := Finset.card_pos.mpr ⟨a, ha⟩
        omega
      obtain ⟨b, hb⟩ := Finset.card_pos.mp hc1
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have hbA : b ∈ A := Finset.mem_of_mem_erase hb
      set A' := (A.erase a).erase b with hA'
      have hA'sub : A' ⊂ A := by
        refine lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset ha)
      have hA'card : A'.card = A.card - 2 := by
        rw [hA', Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]; omega
      have hA'even : Even A'.card := by
        rw [hA'card]
        obtain ⟨k, hk⟩ := hA
        have : 2 ≤ A.card := by
          have := Finset.card_le_card (Finset.erase_subset a A)
          omega
        exact ⟨k - 1, by omega⟩
      obtain ⟨m', hm'⟩ := ih A' hA'sub hA'even
      refine ⟨fun v => if v = a then b else if v = b then a else m' v, ?_⟩
      intro v hv
      by_cases hva : v = a
      · subst hva
        simp [hba, hbA, Ne.symm hba]
      by_cases hvb : v = b
      · subst hvb
        simp [hba, ha, Ne.symm hba]
      · have hvA' : v ∈ A' := Finset.mem_erase.mpr ⟨hvb, Finset.mem_erase.mpr ⟨hva, hv⟩⟩
        obtain ⟨h1, h2, h3⟩ := hm' v hvA'
        have h1a : m' v ≠ a := fun h => by
          rw [h, hA'] at h1; simp at h1
        have h1b : m' v ≠ b := fun h => by
          rw [h, hA'] at h1; simp at h1
        have h1A : m' v ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h1)
        simp only [hva, hvb, if_false, h1a, h1b]
        exact ⟨h1A, h2, h3⟩

/-! ### Contraction by a map -/

section Contr
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- contracted weights -/
def contr (φ : V → W) (x : V → V → ℝ) : W → W → ℝ := fun p q =>
  if p = q then 0 else
    ∑ u ∈ Finset.univ.filter (fun u => φ u = p), ∑ v ∈ Finset.univ.filter (fun v => φ v = q), x u v

lemma sum_fiber_fiber (φ : V → W) (f : V → V → ℝ) (S S' : Finset W) :
    ∑ p ∈ S, ∑ q ∈ S', ∑ u ∈ Finset.univ.filter (fun u => φ u = p),
        ∑ v ∈ Finset.univ.filter (fun v => φ v = q), f u v =
      ∑ u ∈ Finset.univ.filter (fun u => φ u ∈ S), ∑ v ∈ Finset.univ.filter (fun v => φ v ∈ S'),
        f u v := by
  have h1 : ∀ u, ∑ q ∈ S', ∑ v ∈ Finset.univ.filter (fun v => φ v = q), f u v =
      ∑ v ∈ Finset.univ.filter (fun v => φ v ∈ S'), f u v := by
    intro u
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun v => φ v ∈ S'))
      (t := S') (g := φ) (fun v hv => (Finset.mem_filter.mp hv).2)]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hq, h⟩
    · intro h; exact h.2
  calc ∑ p ∈ S, ∑ q ∈ S', ∑ u ∈ Finset.univ.filter (fun u => φ u = p),
        ∑ v ∈ Finset.univ.filter (fun v => φ v = q), f u v
      = ∑ p ∈ S, ∑ u ∈ Finset.univ.filter (fun u => φ u = p),
          ∑ v ∈ Finset.univ.filter (fun v => φ v ∈ S'), f u v := by
        apply Finset.sum_congr rfl; intro p _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro u _
        exact h1 u
    _ = _ := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun u => φ u ∈ S))
          (t := S) (g := φ) (fun v hv => (Finset.mem_filter.mp hv).2)]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; exact ⟨h ▸ hp, h⟩
        · intro h; exact h.2

lemma contr_cut (φ : V → W) (x : V → V → ℝ) (S : Finset W) :
    cut (contr φ x) S = cut x (Finset.univ.filter (fun u => φ u ∈ S)) := by
  unfold cut
  have h : ∀ p ∈ S, ∀ q ∈ Sᶜ, contr φ x p q = ∑ u ∈ Finset.univ.filter (fun u => φ u = p),
      ∑ v ∈ Finset.univ.filter (fun v => φ v = q), x u v := by
    intro p hp q hq
    have : p ≠ q := by
      intro h; rw [h] at hp; exact (Finset.mem_compl.mp hq) hp
    simp [contr, this]
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => h p hp q hq))]
  rw [sum_fiber_fiber]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext v; simp

lemma contr_cost (φ : V → W) (x : V → V → ℝ) (C : W → W → ℝ) :
    ∑ p, ∑ q, C p q * contr φ x p q =
      ∑ u, ∑ v, (if φ u = φ v then 0 else C (φ u) (φ v) * x u v) := by
  have h : ∀ p q, C p q * contr φ x p q = ∑ u ∈ Finset.univ.filter (fun u => φ u = p),
      ∑ v ∈ Finset.univ.filter (fun v => φ v = q),
        (if φ u = φ v then 0 else C (φ u) (φ v) * x u v) := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      simp only [contr, if_true, mul_zero]
      symm
      apply Finset.sum_eq_zero; intro u hu
      apply Finset.sum_eq_zero; intro v hv
      simp only [Finset.mem_filter] at hu hv
      rw [hu.2, hv.2, if_pos rfl]
    · simp only [contr, hpq, if_false, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u hu
      apply Finset.sum_congr rfl; intro v hv
      simp only [Finset.mem_filter] at hu hv
      rw [hu.2, hv.2, if_neg hpq]
  simp_rw [h]
  rw [sum_fiber_fiber]
  simp

lemma odd_sum_of_odd {ι : Type*} (S : Finset ι) (f : ι → ℕ) (hS : Odd S.card)
    (hf : ∀ i ∈ S, Odd (f i)) : Odd (∑ i ∈ S, f i) := by
  classical
  have key : ∀ T : Finset ι, T ⊆ S → (∑ i ∈ T, f i) % 2 = T.card % 2 := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert a T ha ih =>
      intro hT
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have h1 := ih (fun i hi => hT (Finset.mem_insert_of_mem hi))
      have h2 := Nat.odd_iff.mp (hf a (hT (Finset.mem_insert_self a T)))
      omega
  rw [Nat.odd_iff, key S le_rfl, ← Nat.odd_iff]; exact hS

lemma contr_feas (φ : V → W) {x : V → V → ℝ} (hx : Feas x)
    (hodd : ∀ p, Odd (Finset.univ.filter (fun u => φ u = p)).card)
    (htight : ∀ p, cut x (Finset.univ.filter (fun u => φ u = p)) = 1) :
    Feas (contr φ x) where
  symm := by
    intro p q
    by_cases hpq : p = q
    · subst hpq; rfl
    · simp only [contr, hpq, Ne.symm hpq, if_false]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      exact hx.symm _ _
  diag := by intro p; simp [contr]
  nonneg := by
    intro p q
    unfold contr
    split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => hx.nonneg u v))
  deg := by
    intro p
    have h1 : ∑ q, contr φ x p q = cut (contr φ x) {p} := by
      unfold cut
      rw [Finset.sum_singleton]
      have := Finset.sum_add_sum_compl {p} (contr φ x p)
      rw [Finset.sum_singleton] at this
      simp only [contr, if_true] at this
      simp only [contr] at this ⊢
      linarith
    rw [h1, contr_cut]
    have : Finset.univ.filter (fun u => φ u ∈ ({p} : Finset W)) =
        Finset.univ.filter (fun u => φ u = p) := by
      ext u; simp
    rw [this, htight]
  odd := by
    intro S hS
    rw [contr_cut]
    apply hx.odd
    rw [Finset.card_eq_sum_card_fiberwise (f := φ) (s := Finset.univ.filter (fun u => φ u ∈ S))
      (t := S) (fun u hu => by simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and, Finset.mem_coe] at hu ⊢; exact hu)]
    apply odd_sum_of_odd S _ hS
    intro p hp
    have : (Finset.univ.filter (fun u => φ u ∈ S)).filter (fun u => φ u = p) =
        Finset.univ.filter (fun u => φ u = p) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨h ▸ hp, h⟩
    rw [this]; exact hodd p

end Contr


/-! ### One side of a tight cut -/

section Side
variable {V : Type} [Fintype V] [DecidableEq V]

lemma side_bound
    (IH : ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < Fintype.card V → PMProp W)
    {x : V → V → ℝ} (hx : Feas x) (U : Finset V) (hUc : Odd Uᶜ.card)
    (hlt : U.card + 1 < Fintype.card V) (hcut : cut x U = 1) (r : V) (hr : r ∉ U)
    (c : V → V → ℝ) (α : V → ℝ)
    (hα : ∀ a ∈ U, ∀ m : V → V, (∀ b ∈ U, b ≠ a → m b ∈ U ∧ m b ≠ a ∧ m b ≠ b ∧ m (m b) = b) →
      α a ≤ ∑ b ∈ U.erase a, c b (m b)) :
    ∑ a ∈ U, α a * ∑ w ∈ Uᶜ, x a w ≤ ∑ a ∈ U, ∑ b ∈ U, c a b * x a b := by
  classical
  have hrW : r ∈ insert r U := Finset.mem_insert_self r U
  set φ : V → {v // v ∈ insert r U} := fun v =>
    if h : v ∈ U then ⟨v, Finset.mem_insert_of_mem h⟩ else ⟨r, hrW⟩ with hφdef
  have hφU : ∀ v (h : v ∈ U), φ v = ⟨v, Finset.mem_insert_of_mem h⟩ := by
    intro v h; rw [hφdef]; dsimp only; rw [dif_pos h]
  have hφC : ∀ v, v ∉ U → φ v = ⟨r, hrW⟩ := by
    intro v h; rw [hφdef]; dsimp only; rw [dif_neg h]
  have hfib : ∀ p : {v // v ∈ insert r U}, Finset.univ.filter (fun u => φ u = p) =
      if p.val ∈ U then {p.val} else Uᶜ := by
    intro p
    obtain ⟨pv, hp⟩ := p
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hpU : pv ∈ U
    · simp only [hpU, if_true, Finset.mem_singleton]
      by_cases huU : u ∈ U
      · rw [hφU u huU, Subtype.mk.injEq]
      · rw [hφC u huU, Subtype.mk.injEq]
        constructor
        · intro h; subst h; exact absurd hpU hr
        · intro h; subst h; exact absurd hpU huU
    · have hpr : pv = r := by
        rcases Finset.mem_insert.mp hp with h | h
        · exact h
        · exact absurd h hpU
      subst hpr
      simp only [hpU, if_false, Finset.mem_compl]
      by_cases huU : u ∈ U
      · rw [hφU u huU]
        simp only [Subtype.mk.injEq]
        constructor
        · intro h; subst h; exact absurd huU hpU
        · intro h; exact absurd huU h
      · rw [hφC u huU]; simp [huU]
  have hodd : ∀ p, Odd (Finset.univ.filter (fun u => φ u = p)).card := by
    intro p; rw [hfib p]; split_ifs
    · simp
    · exact hUc
  have htight : ∀ p, cut x (Finset.univ.filter (fun u => φ u = p)) = 1 := by
    intro p; rw [hfib p]; split_ifs
    · exact cut_singleton x hx.deg hx.diag _
    · rw [cut_compl x hx.symm, hcut]
  have hcardW : Fintype.card {v // v ∈ insert r U} < Fintype.card V := by
    simp only [Fintype.card_coe]
    rw [Finset.card_insert_of_notMem hr]; exact hlt
  let C1 : V → V → ℝ := fun u v => if u ∈ U then (if v ∈ U then c u v else -α u) else 0
  obtain ⟨M1, hM1, hcost⟩ := IH {v // v ∈ insert r U} hcardW (contr φ x) (contr_feas φ hx hodd htight)
    (fun p q => C1 p.val q.val)
  rw [contr_cost] at hcost
  -- right-hand side
  have hterm : ∀ u v, (if φ u = φ v then 0 else C1 (φ u).val (φ v).val * x u v) =
      if u ∈ U then (if v ∈ U then c u v * x u v else -α u * x u v) else 0 := by
    intro u v
    by_cases huU : u ∈ U
    · by_cases hvU : v ∈ U
      · rw [hφU u huU, hφU v hvU]
        simp only [Subtype.mk.injEq, C1, huU, hvU, if_true]
        split_ifs with h
        · subst h; rw [hx.diag]; ring
        · rfl
      · rw [hφU u huU, hφC v hvU]
        have : u ≠ r := fun h => hr (h ▸ huU)
        simp only [Subtype.mk.injEq, this, if_false, C1, huU, hr, if_true, hvU]
    · rw [hφC u huU]
      simp only [C1, hr, if_false, huU]
      split_ifs <;> simp
  have hR : ∑ u, ∑ v, (if φ u = φ v then 0 else C1 (φ u).val (φ v).val * x u v) =
      ∑ a ∈ U, ∑ b ∈ U, c a b * x a b - ∑ a ∈ U, α a * ∑ w ∈ Uᶜ, x a w := by
    simp_rw [hterm]
    rw [← Finset.sum_add_sum_compl U]
    have h0 : ∑ u ∈ Uᶜ, ∑ v, (if u ∈ U then (if v ∈ U then c u v * x u v else -α u * x u v)
        else 0) = 0 := by
      apply Finset.sum_eq_zero; intro u hu
      rw [Finset.mem_compl] at hu; simp [hu]
    rw [h0, add_zero, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro u hu
    simp only [hu, if_true]
    rw [← Finset.sum_add_sum_compl U]
    have h1 : ∑ v ∈ U, (if v ∈ U then c u v * x u v else -α u * x u v) =
        ∑ v ∈ U, c u v * x u v := by
      apply Finset.sum_congr rfl; intro v hv; simp [hv]
    have h2 : ∑ v ∈ Uᶜ, (if v ∈ U then c u v * x u v else -α u * x u v) =
        -(α u * ∑ v ∈ Uᶜ, x u v) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro v hv
      rw [Finset.mem_compl] at hv; simp [hv]
    rw [h1, h2]; ring
  -- left-hand side is nonnegative
  set a0 := M1 ⟨r, hrW⟩ with ha0
  set a := a0.val with ha
  have ha0r : a0 ≠ ⟨r, hrW⟩ := (hM1 ⟨r, hrW⟩).2
  have haU : a ∈ U := by
    have h1 : a ∈ insert r U := a0.2
    rcases Finset.mem_insert.mp h1 with h | h
    · exact absurd (Subtype.ext h) ha0r
    · exact h
  set m : V → V := fun v => if h : v ∈ insert r U then (M1 ⟨v, h⟩).val else v with hmdef
  have hmW : ∀ z : {v // v ∈ insert r U}, m z.val = (M1 z).val := by
    intro z; rw [hmdef]; dsimp only; rw [dif_pos z.2]
  have hma : m a = r := by
    rw [show a = a0.val from rfl, hmW a0, ha0, (hM1 _).1]
  have hm_prop : ∀ b ∈ U, b ≠ a → m b ∈ U ∧ m b ≠ a ∧ m b ≠ b ∧ m (m b) = b := by
    intro b hb hba
    have hb' : b ∈ insert r U := Finset.mem_insert_of_mem hb
    have hmb : m b = (M1 ⟨b, hb'⟩).val := hmW ⟨b, hb'⟩
    set z := M1 ⟨b, hb'⟩ with hz
    have hzr : z ≠ ⟨r, hrW⟩ := by
      intro h
      have : M1 z = ⟨b, hb'⟩ := (hM1 _).1
      rw [h] at this
      apply hba
      have := congrArg Subtype.val this
      simp only at this
      rw [ha, ha0, this]
    have hzU : z.val ∈ U := by
      rcases Finset.mem_insert.mp z.2 with h | h
      · exact absurd (Subtype.ext h) hzr
      · exact h
    refine ⟨hmb ▸ hzU, ?_, ?_, ?_⟩
    · rw [hmb]
      intro h
      have hz0 : z = a0 := Subtype.ext h
      have e1 : M1 z = ⟨b, hb'⟩ := (hM1 _).1
      have e2 : M1 a0 = ⟨r, hrW⟩ := (hM1 _).1
      rw [hz0, e2] at e1
      have := congrArg Subtype.val e1
      simp only at this
      exact hr (this ▸ hb)
    · rw [hmb]; intro h
      exact (hM1 ⟨b, hb'⟩).2 (Subtype.ext h)
    · rw [hmb, hmW z, (hM1 _).1]
  have hαa := hα a haU m hm_prop
  have hL : ∑ z : {v // v ∈ insert r U}, C1 z.val (M1 z).val =
      -α a + ∑ b ∈ U.erase a, c b (m b) := by
    have e1 : ∑ z : {v // v ∈ insert r U}, C1 z.val (M1 z).val =
        ∑ z : {v // v ∈ insert r U}, C1 z.val (m z.val) := by
      apply Finset.sum_congr rfl; intro z _; rw [hmW z]
    rw [e1, Finset.sum_coe_sort (insert r U) (fun v => C1 v (m v)),
      Finset.sum_insert hr]
    have e2 : C1 r (m r) = 0 := by simp [C1, hr]
    rw [e2, zero_add, ← Finset.add_sum_erase U _ haU]
    have e3 : C1 a (m a) = -α a := by simp [C1, haU, hma, hr]
    rw [e3]
    congr 1
    apply Finset.sum_congr rfl; intro b hb
    have hbU := Finset.mem_of_mem_erase hb
    have hba := Finset.ne_of_mem_erase hb
    simp [C1, hbU, (hm_prop b hbU hba).1]
  rw [hR] at hcost
  rw [hL] at hcost
  linarith

lemma contraction
    (IH : ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < Fintype.card V → PMProp W)
    {x : V → V → ℝ} (hx : Feas x) (U : Finset V) (hUodd : Odd U.card) (h3 : 3 ≤ U.card)
    (h3' : 3 ≤ Uᶜ.card) (hcut : cut x U = 1) (c : V → V → ℝ) :
    ∃ M : V → V, IsPM M ∧ ∑ v, c v (M v) ≤ ∑ u, ∑ v, c u v * x u v := by
  classical
  have hcardV : U.card + Uᶜ.card = Fintype.card V := Finset.card_add_card_compl U
  have hUcodd : Odd Uᶜ.card := by
    obtain ⟨k, hk⟩ := hx.even_card
    obtain ⟨j, hj⟩ := hUodd
    exact ⟨k - j - 1, by omega⟩
  have hmin : ∀ (A : Finset V), Odd A.card → ∀ a ∈ A, ∃ m : V → V,
      (∀ b ∈ A, b ≠ a → m b ∈ A ∧ m b ≠ a ∧ m b ≠ b ∧ m (m b) = b) ∧
      ∀ m' : V → V, (∀ b ∈ A, b ≠ a → m' b ∈ A ∧ m' b ≠ a ∧ m' b ≠ b ∧ m' (m' b) = b) →
        ∑ b ∈ A.erase a, c b (m b) ≤ ∑ b ∈ A.erase a, c b (m' b) := by
    intro A hA a ha
    set P := Finset.univ.filter (fun m : V → V =>
      ∀ b ∈ A, b ≠ a → m b ∈ A ∧ m b ≠ a ∧ m b ≠ b ∧ m (m b) = b) with hP
    have hPne : P.Nonempty := by
      obtain ⟨m, hm⟩ := exists_pm_on (A.erase a)
        (by rw [Finset.card_erase_of_mem ha]; obtain ⟨k, hk⟩ := hA; exact ⟨k, by omega⟩)
      refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      intro b hb hba
      obtain ⟨h1, h2, h3⟩ := hm b (Finset.mem_erase.mpr ⟨hba, hb⟩)
      exact ⟨Finset.mem_of_mem_erase h1, Finset.ne_of_mem_erase h1, h2, h3⟩
    obtain ⟨m, hmP, hmmin⟩ := P.exists_min_image (fun m => ∑ b ∈ A.erase a, c b (m b)) hPne
    refine ⟨m, (Finset.mem_filter.mp hmP).2, ?_⟩
    intro m' hm'
    exact hmmin m' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'⟩)
  choose! mA hmA hmAmin using hmin
  set α : V → ℝ := fun a => ∑ b ∈ U.erase a, c b (mA U a b) with hαdef
  set β : V → ℝ := fun w => ∑ b ∈ Uᶜ.erase w, c b (mA Uᶜ w b) with hβdef
  obtain ⟨r1, hr1⟩ : Uᶜ.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r2, hr2⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
  have hS1 := side_bound IH hx U hUcodd (by omega) hcut r1 (Finset.mem_compl.mp hr1) c α
    (fun a ha m hm => hmAmin U hUodd a ha m hm)
  have hS2 := side_bound IH hx Uᶜ (by rw [compl_compl]; exact hUodd) (by omega)
    (by rw [cut_compl x hx.symm]; exact hcut) r2 (by rw [Finset.mem_compl, not_not]; exact hr2)
    c β (fun a ha m hm => hmAmin Uᶜ hUcodd a ha m hm)
  rw [compl_compl] at hS2
  set total := ∑ u, ∑ v, c u v * x u v with htotal
  have hdec : total = ∑ u ∈ U, ∑ v ∈ U, c u v * x u v + ∑ u ∈ U, ∑ v ∈ Uᶜ, c u v * x u v +
      ∑ u ∈ Uᶜ, ∑ v ∈ U, c u v * x u v + ∑ u ∈ Uᶜ, ∑ v ∈ Uᶜ, c u v * x u v := by
    rw [htotal, ← Finset.sum_add_sum_compl U]
    simp_rw [← Finset.sum_add_sum_compl U (fun v => c _ v * x _ v)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; ring
  set g : V → V → ℝ := fun a w => α a + β w + c a w + c w a with hg
  have hcross : ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w * g a w ≤ total := by
    have e1 : ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w * g a w =
        ∑ a ∈ U, α a * ∑ w ∈ Uᶜ, x a w + ∑ w ∈ Uᶜ, β w * ∑ a ∈ U, x w a +
        ∑ u ∈ U, ∑ v ∈ Uᶜ, c u v * x u v + ∑ u ∈ Uᶜ, ∑ v ∈ U, c u v * x u v := by
      have e2 : ∑ w ∈ Uᶜ, β w * ∑ a ∈ U, x w a = ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w * β w := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro w _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        rw [hx.symm]; ring
      have e3 : ∑ u ∈ Uᶜ, ∑ v ∈ U, c u v * x u v = ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w * c w a := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro w _
        apply Finset.sum_congr rfl; intro a _
        rw [hx.symm]; ring
      rw [e2, e3]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro a _
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro w _
      simp only [hg]; ring
    rw [e1, hdec]
    linarith
  have hone : ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w = 1 := hcut
  -- find a good pair
  obtain ⟨a, haU, w, hwU, hgood⟩ : ∃ a ∈ U, ∃ w ∈ Uᶜ, g a w ≤ total := by
    by_contra hcon
    push Not at hcon
    have : ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w * total < ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w * g a w := by
      rw [← Finset.sum_product', ← Finset.sum_product']
      apply Finset.sum_lt_sum
      · intro p hp
        rw [Finset.mem_product] at hp
        exact mul_le_mul_of_nonneg_left (hcon p.1 hp.1 p.2 hp.2).le (hx.nonneg _ _)
      · by_contra hall
        push Not at hall
        have hz : ∀ p ∈ U ×ˢ Uᶜ, x p.1 p.2 = 0 := by
          intro p hp
          have h1 := hall p hp
          rw [Finset.mem_product] at hp
          have h2 := hcon p.1 hp.1 p.2 hp.2
          rcases (hx.nonneg p.1 p.2).lt_or_eq with h | h
          · nlinarith
          · exact h.symm
        have : ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w = 0 := by
          rw [← Finset.sum_product']
          exact Finset.sum_eq_zero hz
        linarith
    have e : ∑ a ∈ U, ∑ w ∈ Uᶜ, x a w * total = total := by
      simp_rw [← Finset.sum_mul]; rw [hone, one_mul]
    linarith
  have hwU' : w ∉ U := Finset.mem_compl.mp hwU
  have haw : a ≠ w := fun h => hwU' (h ▸ haU)
  obtain hA := hmA U hUodd a haU
  obtain hB := hmA Uᶜ hUcodd w hwU
  set mU := mA U a
  set mC := mA Uᶜ w
  let M : V → V := fun v => if v = a then w else if v = w then a else if v ∈ U then mU v else mC v
  have hMa : M a = w := by simp [M]
  have hMw : M w = a := by simp [M, Ne.symm haw]
  have hMU : ∀ v ∈ U, v ≠ a → M v = mU v := by
    intro v hv hva
    have hvw : v ≠ w := fun h => hwU' (h ▸ hv)
    simp [M, hva, hvw, hv]
  have hMC : ∀ v ∉ U, v ≠ w → M v = mC v := by
    intro v hv hvw
    have hva : v ≠ a := fun h => hv (h ▸ haU)
    simp [M, hva, hvw, hv]
  refine ⟨M, ?_, ?_⟩
  · intro v
    by_cases hva : v = a
    · subst hva; rw [hMa, hMw]; exact ⟨rfl, Ne.symm haw⟩
    by_cases hvw : v = w
    · subst hvw; rw [hMw, hMa]; exact ⟨rfl, haw⟩
    by_cases hvU : v ∈ U
    · obtain ⟨h1, h2, h3, h4⟩ := hA v hvU hva
      rw [hMU v hvU hva, hMU _ h1 h2, h4]
      exact ⟨rfl, h3⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hB v (Finset.mem_compl.mpr hvU) hvw
      rw [hMC v hvU hvw, hMC _ (Finset.mem_compl.mp h1) h2, h4]
      exact ⟨rfl, h3⟩
  · have e1 : ∑ v ∈ U, c v (M v) = c a w + α a := by
      rw [← Finset.add_sum_erase U _ haU, hMa]
      congr 1
      apply Finset.sum_congr rfl; intro v hv
      rw [hMU v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv)]
    have e2 : ∑ v ∈ Uᶜ, c v (M v) = c w a + β w := by
      rw [← Finset.add_sum_erase Uᶜ _ hwU, hMw]
      congr 1
      apply Finset.sum_congr rfl; intro v hv
      rw [hMC v (Finset.mem_compl.mp (Finset.mem_of_mem_erase hv)) (Finset.ne_of_mem_erase hv)]
    rw [← Finset.sum_add_sum_compl U, e1, e2]
    simp only [hg] at hgood
    linarith

end Side

/-! ### Perturbation, kernel vectors, tight triples -/

section Perturb
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def suppCard (x : V → V → ℝ) : ℕ := (Finset.univ.filter (fun p : V × V => x p.1 p.2 ≠ 0)).card

def HasTight (x : V → V → ℝ) : Prop :=
  ∃ S : Finset V, Odd S.card ∧ 3 ≤ S.card ∧ 3 ≤ Sᶜ.card ∧ cut x S = 1

lemma cut_eq_neg_inner (d : V → V → ℝ) (hrow : ∀ v, ∑ u, d v u = 0) (S : Finset V) :
    cut d S = -∑ u ∈ S, ∑ v ∈ S, d u v := by
  unfold cut
  have : ∀ u, ∑ v ∈ Sᶜ, d u v = -∑ v ∈ S, d u v := by
    intro u; have h := Finset.sum_add_sum_compl S (d u); rw [hrow u] at h; linarith
  rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_neg_distrib]

lemma perturb {x : V → V → ℝ} (hx : Feas x)
    (hnt : ∀ S : Finset V, Odd S.card → 3 ≤ S.card → 3 ≤ Sᶜ.card → 1 < cut x S)
    (d : V → V → ℝ) (hds : ∀ u v, d u v = d v u) (hdd : ∀ v, d v v = 0)
    (hdr : ∀ v, ∑ u, d v u = 0) (hsupp : ∀ u v, x u v = 0 → d u v = 0)
    (hne : ∃ u v, d u v ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ Feas (fun u v => x u v + t * d u v) ∧
      (suppCard (fun u v => x u v + t * d u v) < suppCard x ∨
        HasTight (fun u v => x u v + t * d u v)) := by
  classical
  have hneg : ∃ p : V × V, d p.1 p.2 < 0 := by
    obtain ⟨u, v, huv⟩ := hne
    rcases lt_or_gt_of_ne huv with h | h
    · exact ⟨(u, v), h⟩
    · by_contra hcon
      push Not at hcon
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hcon (u, w))).mp (hdr u) v
        (Finset.mem_univ _)
      simp only at hz
      linarith
  set A := Finset.univ.filter (fun p : V × V => d p.1 p.2 < 0) with hA
  set B := Finset.univ.filter (fun S : Finset V => Odd S.card ∧ cut d S < 0) with hB
  set f1 : V × V → ℝ := fun p => x p.1 p.2 / (-d p.1 p.2) with hf1
  set f2 : Finset V → ℝ := fun S => (cut x S - 1) / (-cut d S) with hf2
  set R := A.image f1 ∪ B.image f2 with hR
  have hRne : R.Nonempty := by
    obtain ⟨p, hp⟩ := hneg
    exact ⟨f1 p, Finset.mem_union_left _ (Finset.mem_image_of_mem f1 (by simp [hA, hp]))⟩
  set t := R.min' hRne with ht
  have hBnt : ∀ S ∈ B, 3 ≤ S.card ∧ 3 ≤ Sᶜ.card := by
    intro S hS
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨hodd, hneg⟩ := hS
    have hev := hx.even_card
    have hsum : S.card + Sᶜ.card = Fintype.card V := Finset.card_add_card_compl S
    have hSc : Odd Sᶜ.card := by
      obtain ⟨k, hk⟩ := hev; obtain ⟨j, hj⟩ := hodd; exact ⟨k - j - 1, by omega⟩
    have h1 : S.card ≠ 1 := by
      intro h
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h
      rw [cut_eq_neg_inner d hdr] at hneg; simp [hdd] at hneg
    have h2 : Sᶜ.card ≠ 1 := by
      intro h
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
      rw [← cut_compl d hds, hv, cut_eq_neg_inner d hdr] at hneg; simp [hdd] at hneg
    obtain ⟨j, hj⟩ := hodd; obtain ⟨k, hk⟩ := hSc
    omega
  have hRpos : ∀ y ∈ R, 0 < y := by
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hxp : x p.1 p.2 ≠ 0 := fun h0 => by have := hsupp _ _ h0; linarith
      have hxpos : 0 < x p.1 p.2 := lt_of_le_of_ne (hx.nonneg _ _) (Ne.symm hxp)
      exact div_pos hxpos (by linarith)
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨h3, h3'⟩ := hBnt S hS
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      have := hnt S hS.1 h3 h3'
      exact div_pos (by linarith) (by linarith [hS.2])
  have htpos : 0 < t := hRpos t (Finset.min'_mem R hRne)
  have htA : ∀ p ∈ A, t ≤ f1 p := fun p hp =>
    Finset.min'_le R _ (Finset.mem_union_left _ (Finset.mem_image_of_mem f1 hp))
  have htB : ∀ S ∈ B, t ≤ f2 S := fun S hS =>
    Finset.min'_le R _ (Finset.mem_union_right _ (Finset.mem_image_of_mem f2 hS))
  refine ⟨t, htpos, ?_, ?_⟩
  · constructor
    · intro u v; rw [hx.symm u v, hds u v]
    · intro v; rw [hx.diag v, hdd v]; ring
    · intro u v
      by_cases h : d u v < 0
      · have := htA (u, v) (by simp [hA, h])
        simp only [hf1] at this
        rw [le_div_iff₀ (by linarith)] at this
        linarith
      · push Not at h
        have := hx.nonneg u v
        nlinarith
    · intro v
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx.deg v, hdr v]; ring
    · intro S hS
      rw [cut_lin]
      by_cases h : cut d S < 0
      · have := htB S (by simp [hB, hS, h])
        simp only [hf2] at this
        rw [le_div_iff₀ (by linarith)] at this
        linarith
      · push Not at h
        have := hx.odd S hS
        nlinarith
  · have htmem := Finset.min'_mem R hRne
    rw [← ht] at htmem
    rcases Finset.mem_union.mp htmem with h | h
    · left
      obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp h
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hdp : d p.1 p.2 ≠ 0 := ne_of_lt hp
      have hzero : x p.1 p.2 + t * d p.1 p.2 = 0 := by
        rw [← hpt]; simp only [hf1]; field_simp; ring
      have hxp : x p.1 p.2 ≠ 0 := fun h0 => by have := hsupp _ _ h0; linarith
      unfold suppCard
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨p, by simp [hxp], by simp [hzero]⟩
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        intro h0
        apply hq
        rw [h0, hsupp _ _ h0]; ring
    · right
      obtain ⟨S, hS, hSt⟩ := Finset.mem_image.mp h
      obtain ⟨h3, h3'⟩ := hBnt S hS
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      have hdS : cut d S ≠ 0 := ne_of_lt hS.2
      refine ⟨S, hS.1, h3, h3', ?_⟩
      rw [cut_lin, ← hSt]
      simp only [hf2]
      field_simp
      ring

lemma kernel {x : V → V → ℝ} (hx : Feas x)
    (h3 : ∀ v, 3 ≤ (Finset.univ.filter (fun u => x v u ≠ 0)).card) (hV : 0 < Fintype.card V) :
    ∃ d : V → V → ℝ, (∀ u v, d u v = d v u) ∧ (∀ v, d v v = 0) ∧ (∀ v, ∑ u, d v u = 0) ∧
      (∀ u v, x u v = 0 → d u v = 0) ∧ ∃ u v, d u v ≠ 0 := by
  classical
  set r : V → ℕ := fun v => (Fintype.equivFin V v : ℕ) with hr
  have hrinj : Function.Injective r := fun a b h =>
    (Fintype.equivFin V).injective (Fin.ext h)
  set P : V × V → Prop := fun p => r p.1 < r p.2 ∧ x p.1 p.2 ≠ 0 with hP
  set f : {p : V × V // P p} → (V → ℝ) := fun p w =>
    (if p.val.1 = w then 1 else 0) + (if p.val.2 = w then 1 else 0) with hf
  have hcard : Fintype.card V < Fintype.card {p : V × V // P p} := by
    rw [Fintype.card_subtype]
    set Z := Finset.univ.filter (fun p : V × V => x p.1 p.2 ≠ 0) with hZ
    set P1 := Finset.univ.filter P with hP1
    set P2 := Finset.univ.filter (fun p : V × V => r p.2 < r p.1 ∧ x p.1 p.2 ≠ 0) with hP2
    have hZeq : Z = P1 ∪ P2 := by
      ext p
      simp only [hZ, hP1, hP2, hP, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union]
      constructor
      · intro h
        have hne : p.1 ≠ p.2 := by
          intro he; apply h; rw [he, hx.diag]
        have : r p.1 ≠ r p.2 := fun h' => hne (hrinj h')
        rcases lt_or_gt_of_ne this with h1 | h1
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h1, h⟩
      · rintro (h | h)
        · exact h.2
        · exact h.2
    have hdisj : Disjoint P1 P2 := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [hP1, hP2, hP, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    have hP12 : P2.card = P1.card := by
      refine Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [hP1, hP2, hP, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
          Prod.snd_swap] at hp ⊢
        exact ⟨hp.1, by rw [hx.symm]; exact hp.2⟩
      · intro p hp
        simp only [hP1, hP2, hP, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
          Prod.snd_swap] at hp ⊢
        exact ⟨hp.1, by rw [hx.symm]; exact hp.2⟩
      · intro p _; simp
      · intro p _; simp
    have hZcard : Z.card = ∑ v, (Finset.univ.filter (fun u => x v u ≠ 0)).card := by
      rw [hZ, Finset.card_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro v _
      rw [Finset.card_filter]
    have hZ3 : 3 * Fintype.card V ≤ Z.card := by
      rw [hZcard]
      calc 3 * Fintype.card V = ∑ _v : V, 3 := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun v _ => h3 v)
    have hZc : Z.card = P1.card + P2.card := by
      rw [hZeq, Finset.card_union_of_disjoint hdisj]
    show Fintype.card V < P1.card
    omega
  have hli : ¬ LinearIndependent ℝ f := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at this
    omega
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  set G : V × V → ℝ := fun q => if h : P q then g ⟨q, h⟩ else 0 with hG
  have hGP : ∀ q, ¬ P q → G q = 0 := by intro q hq; simp [hG, hq]
  have key : ∀ w, ∑ q : V × V, G q * ((if q.1 = w then 1 else 0) + (if q.2 = w then 1 else 0))
      = 0 := by
    intro w
    have hw := congrFun hg w
    rw [Finset.sum_apply] at hw
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hw
    have e : ∑ q : V × V, G q * ((if q.1 = w then 1 else 0) + (if q.2 = w then 1 else 0)) =
        ∑ p : {p : V × V // P p}, g p * f p w := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter P))
        (fun q _ hq => by
          have : ¬ P q := by simpa using hq
          rw [hGP q this, zero_mul])]
      rw [Finset.sum_subtype (p := P) (Finset.univ.filter P) (fun q => by simp)]
      apply Finset.sum_congr rfl; intro p _
      simp only [hG, hf, dif_pos p.2]
    rw [e, hw]
  refine ⟨fun u v => G (u, v) + G (v, u), ?_, ?_, ?_, ?_, ?_⟩
  · intro u v; ring
  · intro v
    have : ¬ P (v, v) := by simp [hP]
    simp [hGP _ this]
  · intro w
    have hk := key w
    rw [Fintype.sum_prod_type] at hk
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero] at hk
    rw [Finset.sum_add_distrib]
    have e1 : ∑ u, ∑ v, (if u = w then G (u, v) else 0) = ∑ v, G (w, v) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro v _
      rw [Finset.sum_ite_eq']; simp
    have e2 : ∑ u, ∑ v, (if v = w then G (u, v) else 0) = ∑ u, G (u, w) := by
      apply Finset.sum_congr rfl; intro u _
      rw [Finset.sum_ite_eq']; simp
    rw [e1, e2] at hk
    exact hk
  · intro u v h
    have h1 : ¬ P (u, v) := by simp [hP, h]
    have h2 : ¬ P (v, u) := by simp [hP, hx.symm v u, h]
    simp [hGP _ h1, hGP _ h2]
  · refine ⟨i0.val.1, i0.val.2, ?_⟩
    have h1 : P i0.val := i0.2
    have h2 : ¬ P (i0.val.2, i0.val.1) := by
      simp only [hP, not_and]; intro h; have := h1.1; omega
    have e : G (i0.val.1, i0.val.2) = g i0 := by
      simp only [hG]; rw [dif_pos h1]
    simp only
    rw [hGP _ h2, add_zero, e]
    exact hi0

lemma tight3 {x : V → V → ℝ} (hx : Feas x) (h6 : 6 ≤ Fintype.card V) (v : V)
    (hv : (Finset.univ.filter (fun u => x v u ≠ 0)).card ≤ 2) : HasTight x := by
  classical
  set Nv := Finset.univ.filter (fun u => x v u ≠ 0) with hNv
  have hvN : v ∉ Nv := by simp [hNv, hx.diag]
  have hsumN : ∑ u ∈ Nv, x v u = 1 := by
    rw [← hx.deg v]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu; simpa [hNv] using hu
  obtain ⟨a, b, hab, hav, hbv, hNsub⟩ : ∃ a b, a ≠ b ∧ a ≠ v ∧ b ≠ v ∧ Nv ⊆ {a, b} := by
    rcases Nat.lt_or_ge Nv.card 2 with h | h
    · have hne : Nv.Nonempty := by
        by_contra h0
        rw [Finset.not_nonempty_iff_eq_empty] at h0
        rw [h0] at hsumN; simp at hsumN
      have h1 : Nv.card = 1 := by have := hne.card_pos; omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      have hav : a ≠ v := by intro h; apply hvN; rw [ha, h]; simp
      obtain ⟨b, hb1, hb2⟩ : ∃ b, b ≠ v ∧ b ≠ a := by
        by_contra hcon
        push Not at hcon
        have hsub : (Finset.univ : Finset V) ⊆ {v, a} := by
          intro b _
          by_cases hbv : b = v
          · simp [hbv]
          · simp [hcon b hbv]
        have := Finset.card_le_card hsub
        rw [Finset.card_univ] at this
        have := Finset.card_le_two (a := v) (b := a)
        omega
      exact ⟨a, b, Ne.symm hb2, hav, hb1, by rw [ha]; simp⟩
    · have h2 : Nv.card = 2 := by omega
      obtain ⟨a, b, hab, hNab⟩ := Finset.card_eq_two.mp h2
      refine ⟨a, b, hab, ?_, ?_, hNab.le⟩
      · intro h; apply hvN; rw [hNab, h]; simp
      · intro h; apply hvN; rw [hNab, h]; simp
  have hvab : x v a + x v b = 1 := by
    rw [← hsumN, ← Finset.sum_pair hab]
    symm
    apply Finset.sum_subset hNsub
    intro u _ hu; simpa [hNv] using hu
  set S : Finset V := {v, a, b} with hS
  have hScard : S.card = 3 := by
    rw [Finset.card_eq_three]; exact ⟨v, a, b, Ne.symm hav, Ne.symm hbv, hab, rfl⟩
  have hinner : ∑ u ∈ S, ∑ w ∈ S, x u w = 2 * (x v a + x v b + x a b) := by
    have hv1 : v ∉ ({a, b} : Finset V) := by simp [Ne.symm hav, Ne.symm hbv]
    have ha1 : a ∉ ({b} : Finset V) := by simp [hab]
    rw [hS, Finset.sum_insert hv1, Finset.sum_insert ha1, Finset.sum_singleton]
    simp only [Finset.sum_insert hv1, Finset.sum_insert ha1, Finset.sum_singleton]
    rw [hx.diag v, hx.diag a, hx.diag b, hx.symm a v, hx.symm b v, hx.symm b a]
    ring
  have hcutS : cut x S = 1 - 2 * x a b := by
    rw [cut_eq_card_sub x hx.deg, hScard, hinner]; push_cast; linarith
  have h1 := hx.odd S (by rw [hScard]; decide)
  have hab0 : x a b = 0 := by linarith [hx.nonneg a b]
  have hSc : S.card + Sᶜ.card = Fintype.card V := Finset.card_add_card_compl S
  exact ⟨S, by rw [hScard]; decide, by omega, by omega, by rw [hcutS, hab0]; ring⟩

end Perturb

/-! ### Small cases and the perfect matching polytope theorem -/

section Main

lemma pm_of_equiv {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (e : V ≃ Fin k)
    (hfin : ∀ y : Fin k → Fin k → ℝ, (∀ i j, y i j = y j i) → (∀ i, y i i = 0) →
      (∀ i j, 0 ≤ y i j) → (∀ i, ∑ j, y i j = 1) → ∀ c' : Fin k → Fin k → ℝ,
        ∃ M' : Fin k → Fin k, IsPM M' ∧ ∑ i, c' i (M' i) ≤ ∑ i, ∑ j, c' i j * y i j) :
    PMProp V := by
  intro x hx c
  obtain ⟨M', hM', hc⟩ := hfin (fun i j => x (e.symm i) (e.symm j))
    (fun i j => hx.symm _ _) (fun i => hx.diag _) (fun i j => hx.nonneg _ _)
    (fun i => by rw [Equiv.sum_comp e.symm (fun u => x (e.symm i) u)]; exact hx.deg _)
    (fun i j => c (e.symm i) (e.symm j))
  refine ⟨fun v => e.symm (M' (e v)), ?_, ?_⟩
  · intro v
    refine ⟨by simp [(hM' (e v)).1], ?_⟩
    intro h
    apply (hM' (e v)).2
    have := congrArg e h
    simpa using this
  · have e1 : ∑ v, c v (e.symm (M' (e v))) = ∑ i, c (e.symm i) (e.symm (M' i)) := by
      rw [← Equiv.sum_comp e.symm]; simp
    have e2 : ∑ u, ∑ v, c u v * x u v =
        ∑ i, ∑ j, c (e.symm i) (e.symm j) * x (e.symm i) (e.symm j) := by
      rw [← Equiv.sum_comp e.symm]
      apply Finset.sum_congr rfl; intro i _
      rw [← Equiv.sum_comp e.symm]
    rw [e1, e2]; exact hc

lemma pm_fin2 : ∀ y : Fin 2 → Fin 2 → ℝ, (∀ i j, y i j = y j i) → (∀ i, y i i = 0) →
      (∀ i j, 0 ≤ y i j) → (∀ i, ∑ j, y i j = 1) → ∀ c' : Fin 2 → Fin 2 → ℝ,
        ∃ M' : Fin 2 → Fin 2, IsPM M' ∧ ∑ i, c' i (M' i) ≤ ∑ i, ∑ j, c' i j * y i j := by
  intro y hs hd _ hdeg c'
  have h0 := hdeg 0
  have h1 := hdeg 1
  simp only [Fin.sum_univ_two] at h0 h1
  rw [hd] at h0 h1
  refine ⟨![1, 0], by unfold IsPM; decide, ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hd 0, hd 1]
  have : y 0 1 = 1 := by linarith
  have : y 1 0 = 1 := by linarith
  simp [*]

lemma pm_fin4 : ∀ y : Fin 4 → Fin 4 → ℝ, (∀ i j, y i j = y j i) → (∀ i, y i i = 0) →
      (∀ i j, 0 ≤ y i j) → (∀ i, ∑ j, y i j = 1) → ∀ c' : Fin 4 → Fin 4 → ℝ,
        ∃ M' : Fin 4 → Fin 4, IsPM M' ∧ ∑ i, c' i (M' i) ≤ ∑ i, ∑ j, c' i j * y i j := by
  intro y hs hd hn hdeg c'
  have h0 := hdeg 0
  have h1 := hdeg 1
  have h2 := hdeg 2
  have h3 := hdeg 3
  simp only [Fin.sum_univ_four] at h0 h1 h2 h3
  rw [hd] at h0 h1 h2 h3
  rw [hs 1 0] at h1
  rw [hs 2 0, hs 2 1] at h2
  rw [hs 3 0, hs 3 1, hs 3 2] at h3
  have e23 : y 2 3 = y 0 1 := by linarith
  have e13 : y 1 3 = y 0 2 := by linarith
  have e12 : y 1 2 = y 0 3 := by linarith
  set a := y 0 1
  set b := y 0 2
  set e := y 0 3
  have ha : 0 ≤ a := hn 0 1
  have hb : 0 ≤ b := hn 0 2
  have he : 0 ≤ e := hn 0 3
  have hsum : ∑ i, ∑ j, c' i j * y i j =
      a * (c' 0 1 + c' 1 0 + c' 2 3 + c' 3 2) + b * (c' 0 2 + c' 2 0 + c' 1 3 + c' 3 1) +
      e * (c' 0 3 + c' 3 0 + c' 1 2 + c' 2 1) := by
    simp only [Fin.sum_univ_four]
    rw [hd 0, hd 1, hd 2, hd 3, hs 1 0, hs 2 0, hs 2 1, hs 3 0, hs 3 1, hs 3 2, e23, e13, e12]
    ring
  rw [hsum]
  set K1 := c' 0 1 + c' 1 0 + c' 2 3 + c' 3 2
  set K2 := c' 0 2 + c' 2 0 + c' 1 3 + c' 3 1
  set K3 := c' 0 3 + c' 3 0 + c' 1 2 + c' 2 1
  have hab : a + b + e = 1 := by linarith
  have hK1 : a * K1 + b * K1 + e * K1 = K1 := by rw [← add_mul, ← add_mul, hab, one_mul]
  have hK2 : a * K2 + b * K2 + e * K2 = K2 := by rw [← add_mul, ← add_mul, hab, one_mul]
  have hK3 : a * K3 + b * K3 + e * K3 = K3 := by rw [← add_mul, ← add_mul, hab, one_mul]
  by_cases c12 : K1 ≤ K2
  · by_cases c13 : K1 ≤ K3
    · refine ⟨![1, 0, 3, 2], by unfold IsPM; decide, ?_⟩
      have : ∑ i, c' i (![1, 0, 3, 2] i) = K1 := by
        rw [Fin.sum_univ_four]; rfl
      rw [this]; linarith [mul_le_mul_of_nonneg_left c12 hb, mul_le_mul_of_nonneg_left c13 he]
    · refine ⟨![3, 2, 1, 0], by unfold IsPM; decide, ?_⟩
      have : ∑ i, c' i (![3, 2, 1, 0] i) = K3 := by
        rw [Fin.sum_univ_four]; show c' 0 3 + c' 1 2 + c' 2 1 + c' 3 0 = K3; simp only [K3]; ring
      push Not at c13
      rw [this]; linarith [mul_le_mul_of_nonneg_left c13.le ha, mul_le_mul_of_nonneg_left (c13.le.trans c12) hb]
  · by_cases c23 : K2 ≤ K3
    · refine ⟨![2, 3, 0, 1], by unfold IsPM; decide, ?_⟩
      have : ∑ i, c' i (![2, 3, 0, 1] i) = K2 := by
        rw [Fin.sum_univ_four]; show c' 0 2 + c' 1 3 + c' 2 0 + c' 3 1 = K2; simp only [K2]; ring
      push Not at c12
      rw [this]; linarith [mul_le_mul_of_nonneg_left c12.le ha, mul_le_mul_of_nonneg_left c23 he]
    · refine ⟨![3, 2, 1, 0], by unfold IsPM; decide, ?_⟩
      have : ∑ i, c' i (![3, 2, 1, 0] i) = K3 := by
        rw [Fin.sum_univ_four]; show c' 0 3 + c' 1 2 + c' 2 1 + c' 3 0 = K3; simp only [K3]; ring
      push Not at c12 c23
      rw [this]; linarith [mul_le_mul_of_nonneg_left (c23.le.trans c12.le) ha, mul_le_mul_of_nonneg_left c23.le hb]

theorem pm_main : ∀ (N : ℕ) (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V = N → PMProp V := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro V _ _ hN x hx c
  have IH' : ∀ (W : Type) [Fintype W] [DecidableEq W],
      Fintype.card W < Fintype.card V → PMProp W :=
    fun W _ _ hW => IH _ (hN ▸ hW) W rfl
  have hev := hx.even_card
  rw [hN] at hev
  obtain ⟨k, hk⟩ := hev
  rcases (show N = 0 ∨ N = 2 ∨ N = 4 ∨ 6 ≤ N by omega) with h0 | h2 | h4 | h6
  · have hE : IsEmpty V := Fintype.card_eq_zero_iff.mp (hN.trans h0)
    refine ⟨id, fun v => (IsEmpty.false v).elim, ?_⟩
    simp [Finset.univ_eq_empty]
  · exact pm_of_equiv (Fintype.equivFinOfCardEq (hN.trans h2)) pm_fin2 x hx c
  · exact pm_of_equiv (Fintype.equivFinOfCardEq (hN.trans h4)) pm_fin4 x hx c
  · have main : ∀ s, ∀ x : V → V → ℝ, Feas x → suppCard x = s →
        ∃ M : V → V, IsPM M ∧ ∑ v, c v (M v) ≤ ∑ u, ∑ v, c u v * x u v := by
      intro s
      induction s using Nat.strong_induction_on with
      | _ s IHs =>
      intro x hx hs
      by_cases hT : HasTight x
      · obtain ⟨S, hSo, hS3, hS3', hSc⟩ := hT
        exact contraction IH' hx S hSo hS3 hS3' hSc c
      · have hnt : ∀ S : Finset V, Odd S.card → 3 ≤ S.card → 3 ≤ Sᶜ.card → 1 < cut x S := by
          intro S h1 h2 h3
          rcases (hx.odd S h1).lt_or_eq with h | h
          · exact h
          · exact absurd ⟨S, h1, h2, h3, h.symm⟩ hT
        have h3 : ∀ v, 3 ≤ (Finset.univ.filter (fun u => x v u ≠ 0)).card := by
          intro v; by_contra h; push Not at h
          exact hT (tight3 hx (by omega) v (by omega))
        obtain ⟨d, hds, hdd, hdr, hsupp, hne⟩ := kernel hx h3 (by omega)
        have key : ∀ d' : V → V → ℝ, (∀ u v, d' u v = d' v u) → (∀ v, d' v v = 0) →
            (∀ v, ∑ u, d' v u = 0) → (∀ u v, x u v = 0 → d' u v = 0) → (∃ u v, d' u v ≠ 0) →
            ∑ u, ∑ v, c u v * d' u v ≤ 0 →
            ∃ M : V → V, IsPM M ∧ ∑ v, c v (M v) ≤ ∑ u, ∑ v, c u v * x u v := by
          intro d' h1 h2 h3 h4 h5 hD
          obtain ⟨t, ht, hfeas, hcase⟩ := perturb hx hnt d' h1 h2 h3 h4 h5
          have hcost : ∑ u, ∑ v, c u v * (x u v + t * d' u v) ≤ ∑ u, ∑ v, c u v * x u v := by
            have : ∑ u, ∑ v, c u v * (x u v + t * d' u v) =
                ∑ u, ∑ v, c u v * x u v + t * ∑ u, ∑ v, c u v * d' u v := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl; intro u _
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl; intro v _; ring
            rw [this]; nlinarith
          rcases hcase with hlt | htight
          · obtain ⟨M, hM, hMc⟩ := IHs _ (hs ▸ hlt) _ hfeas rfl
            exact ⟨M, hM, hMc.trans hcost⟩
          · obtain ⟨S, hSo, hS3, hS3', hSc⟩ := htight
            obtain ⟨M, hM, hMc⟩ := contraction IH' hfeas S hSo hS3 hS3' hSc c
            exact ⟨M, hM, hMc.trans hcost⟩
        by_cases hD : ∑ u, ∑ v, c u v * d u v ≤ 0
        · exact key d hds hdd hdr hsupp hne hD
        · apply key (fun u v => -d u v)
          · intro u v; rw [hds]
          · intro v; rw [hdd]; ring
          · intro v; rw [Finset.sum_neg_distrib, hdr]; ring
          · intro u v h; rw [hsupp u v h]; ring
          · obtain ⟨u, v, h⟩ := hne; exact ⟨u, v, neg_ne_zero.mpr h⟩
          · have : ∑ u, ∑ v, c u v * -d u v = -∑ u, ∑ v, c u v * d u v := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl; intro u _
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl; intro v _; ring
            rw [this]; linarith
    exact main _ x hx rfl

end Main

end PM

/-! ### Euler closed walks in ℕ-matrix multigraphs -/

section Euler
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- edge-count matrix of a walk (each step counted in both orientations) -/
def ec : List V → V → V → ℕ
  | a :: b :: l, u, v => (if a = u ∧ b = v then 1 else 0) + (if a = v ∧ b = u then 1 else 0) +
      ec (b :: l) u v
  | _, _, _ => 0

/-- cost of a walk -/
def wc (c : V → V → ℝ) : List V → ℝ
  | a :: b :: l => c a b + wc c (b :: l)
  | _ => 0

lemma ec_nil (u v : V) : ec ([] : List V) u v = 0 := rfl
lemma ec_single (a u v : V) : ec [a] u v = 0 := rfl
lemma ec_cons_cons (a b : V) (l : List V) (u v : V) :
    ec (a :: b :: l) u v = (if a = u ∧ b = v then 1 else 0) + (if a = v ∧ b = u then 1 else 0) +
      ec (b :: l) u v := rfl

lemma ec_symm (L : List V) (u v : V) : ec L u v = ec L v u := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      rw [ec_cons_cons, ec_cons_cons, ih]; ring

lemma ec_split (A B : List V) (x : V) (u v : V) :
    ec (A ++ x :: B) u v = ec (A ++ [x]) u v + ec (x :: B) u v := by
  induction A with
  | nil => simp [ec_single]
  | cons a A ih =>
    cases A with
    | nil => simp [ec_cons_cons, ec_single]
    | cons b A =>
      simp only [List.cons_append] at ih ⊢
      rw [ec_cons_cons, ec_cons_cons, ih]; ring

lemma wc_split (c : V → V → ℝ) (A B : List V) (x : V) :
    wc c (A ++ x :: B) = wc c (A ++ [x]) + wc c (x :: B) := by
  induction A with
  | nil => simp [wc]
  | cons a A ih =>
    cases A with
    | nil => simp [wc]
    | cons b A =>
      simp only [List.cons_append, wc] at ih ⊢
      rw [ih]; ring

/-- last element of `a :: l` -/
def lastOf : V → List V → V
  | a, [] => a
  | _, b :: l => lastOf b l

lemma getLast?_eq_lastOf (a : V) (l : List V) : (a :: l).getLast? = some (lastOf a l) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => rw [List.getLast?_cons_cons, ih]; rfl

lemma exists_concat_lastOf (a : V) (l : List V) : ∃ A, a :: l = A ++ [lastOf a l] := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    obtain ⟨A, hA⟩ := ih b
    refine ⟨a :: A, ?_⟩
    show a :: b :: l = (a :: A) ++ [lastOf b l]
    rw [hA]; rfl

lemma sum_ite_and_left {M : Type*} [AddCommMonoid M] (p : Prop) [Decidable p] (b : V)
    (f : V → M) : ∑ v, (if p ∧ b = v then f v else 0) = if p then f b else 0 := by
  by_cases hp : p <;> simp [hp]

lemma sum_ite_and_right {M : Type*} [AddCommMonoid M] (p : Prop) [Decidable p] (b : V)
    (f : V → M) : ∑ v, (if b = v ∧ p then f v else 0) = if p then f b else 0 := by
  by_cases hp : p <;> simp [hp]

lemma ec_deg (a : V) (l : List V) (u : V) :
    ∑ v, ec (a :: l) u v + (if a = u then 1 else 0) + (if lastOf a l = u then 1 else 0) =
      2 * (a :: l).count u := by
  induction l generalizing a with
  | nil =>
    simp only [ec_single, Finset.sum_const_zero, zero_add, lastOf, List.count_cons,
      List.count_nil, beq_iff_eq]
    split_ifs <;> simp_all
  | cons b l ih =>
    have h := ih b
    simp only [ec_cons_cons, Finset.sum_add_distrib]
    rw [sum_ite_and_left (a = u) b (fun _ => (1 : ℕ)), sum_ite_and_right (b = u) a (fun _ => (1 : ℕ))]
    have hlast : lastOf a (b :: l) = lastOf b l := rfl
    rw [hlast, List.count_cons]
    simp only [beq_iff_eq]
    generalize (if lastOf b l = u then 1 else 0) = D at h ⊢
    generalize (if a = u then 1 else 0) = A at h ⊢
    generalize (if b = u then 1 else 0) = B at h ⊢
    omega

lemma ec_pos_mem (L : List V) (u v : V) (h : 0 < ec L u v) : u ∈ L ∧ v ∈ L := by
  induction L with
  | nil => simp [ec_nil] at h
  | cons a l ih =>
    cases l with
    | nil => simp [ec_single] at h
    | cons b l =>
      rw [ec_cons_cons] at h
      by_cases h1 : 0 < ec (b :: l) u v
      · obtain ⟨h2, h3⟩ := ih h1
        exact ⟨List.mem_cons_of_mem _ h2, List.mem_cons_of_mem _ h3⟩
      · split_ifs at h with hA hB hB
        · obtain ⟨rfl, rfl⟩ := hA; simp
        · obtain ⟨rfl, rfl⟩ := hA; simp
        · obtain ⟨rfl, rfl⟩ := hB; simp
        · omega

lemma ec_total (a : V) (l : List V) : ∑ u, ∑ v, ec (a :: l) u v = 2 * l.length := by
  induction l generalizing a with
  | nil => simp [ec_single]
  | cons b l ih =>
    simp only [ec_cons_cons, Finset.sum_add_distrib, ih b]
    have e1 : ∑ u, ∑ v, (if a = u ∧ b = v then 1 else 0 : ℕ) = 1 := by
      simp_rw [sum_ite_and_left _ b (fun _ => (1 : ℕ))]
      simp
    have e2 : ∑ u, ∑ v, (if a = v ∧ b = u then 1 else 0 : ℕ) = 1 := by
      simp_rw [sum_ite_and_right _ a (fun _ => (1 : ℕ))]
      simp
    rw [e1, e2]; simp; ring

lemma wc_eq (c : V → V → ℝ) (hc : ∀ u v, c u v = c v u) (L : List V) :
    2 * wc c L = ∑ u, ∑ v, c u v * (ec L u v : ℝ) := by
  induction L with
  | nil => simp [wc, ec_nil]
  | cons a l ih =>
    cases l with
    | nil => simp [wc, ec_single]
    | cons b l =>
      rw [wc, mul_add, ih]
      simp only [ec_cons_cons, Nat.cast_add, mul_add, Finset.sum_add_distrib]
      have e1 : ∑ u, ∑ v, c u v * ((if a = u ∧ b = v then 1 else 0 : ℕ) : ℝ) = c a b := by
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
        simp_rw [sum_ite_and_left _ b (fun v => c _ v)]
        simp
      have e2 : ∑ u, ∑ v, c u v * ((if a = v ∧ b = u then 1 else 0 : ℕ) : ℝ) = c b a := by
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
        simp_rw [sum_ite_and_right _ a (fun v => c _ v)]
        simp
      rw [e1, e2, hc b a]; ring

/-- closed walk from `v0` -/
def IsClosed (v0 : V) (L : List V) : Prop := L.head? = some v0 ∧ L.getLast? = some v0

lemma closed_deg_even {v0 : V} {L : List V} (hL : IsClosed v0 L) (u : V) :
    Even (∑ v, ec L u v) := by
  obtain ⟨hh, hl⟩ := hL
  cases L with
  | nil => simp at hh
  | cons a l =>
    have h := ec_deg a l u
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rw [getLast?_eq_lastOf, Option.some.injEq] at hl
    rw [hl] at h
    rw [Nat.even_iff]
    split_ifs at h <;> omega

lemma trail_extend (rem : V → V → ℕ) (hsym : ∀ u v, rem u v = rem v u)
    (hdiag : ∀ v, rem v v = 0) (heven : ∀ u, Even (∑ v, rem u v)) (u : V) :
    ∀ s : ℕ, ∀ l : List V, 1 ≤ l.length → (∀ a b, ec (u :: l) a b ≤ rem a b) →
      ∑ a, ∑ b, rem a b - ∑ a, ∑ b, ec (u :: l) a b = s →
      ∃ C : List V, IsClosed u C ∧ 2 ≤ C.length ∧ ∀ a b, ec C a b ≤ rem a b := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
  intro l hlen hle hs
  set z := lastOf u l with hz
  by_cases hzu : z = u
  · refine ⟨u :: l, ⟨rfl, by rw [getLast?_eq_lastOf, ← hz, hzu]⟩, by simp; omega, hle⟩
  · have hdeg := ec_deg u l z
    rw [if_neg (Ne.symm hzu), if_pos hz.symm] at hdeg
    have hlt : ∑ v, ec (u :: l) z v < ∑ v, rem z v := by
      have hle' : ∑ v, ec (u :: l) z v ≤ ∑ v, rem z v := Finset.sum_le_sum (fun v _ => hle z v)
      rcases hle'.lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨k, hk⟩ := heven z
        omega
    obtain ⟨w, -, hw⟩ := Finset.exists_lt_of_sum_lt hlt
    have hzw : z ≠ w := by
      intro h; rw [h, hdiag] at hw; omega
    obtain ⟨A, hA⟩ := exists_concat_lastOf u l
    rw [← hz] at hA
    have hsplit : ∀ p q, ec (u :: (l ++ [w])) p q = ec (u :: l) p q + ec [z, w] p q := by
      intro p q
      have e : u :: (l ++ [w]) = A ++ z :: [w] := by
        rw [← List.cons_append, hA]; simp
      rw [e, ec_split, ← hA]
    have hle2 : ∀ p q, ec (u :: (l ++ [w])) p q ≤ rem p q := by
      intro p q
      rw [hsplit]
      simp only [ec_cons_cons, ec_single, add_zero]
      by_cases h1 : z = p ∧ w = q
      · obtain ⟨rfl, rfl⟩ := h1
        have : ¬ (z = w ∧ w = z) := fun h => hzw h.1
        simp only [and_self, if_true, this, if_false]
        have := hw; omega
      · by_cases h2 : z = q ∧ w = p
        · obtain ⟨rfl, rfl⟩ := h2
          simp only [h1, if_false, and_self, if_true]
          rw [ec_symm, hsym]; have := hw; omega
        · simp only [h1, h2, if_false]; simpa using hle p q
    have hsum : ∑ p, ∑ q, ec (u :: (l ++ [w])) p q = ∑ p, ∑ q, ec (u :: l) p q + 2 := by
      have e1 : ∑ p, ∑ q, ec (u :: (l ++ [w])) p q =
          ∑ p, ∑ q, ec (u :: l) p q + ∑ p, ∑ q, ec [z, w] p q := by
        simp only [hsplit, Finset.sum_add_distrib]
      rw [e1, ec_total z [w]]; simp
    have hrem : ∑ p, ∑ q, ec (u :: (l ++ [w])) p q ≤ ∑ p, ∑ q, rem p q :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hle2 p q))
    exact IH _ (by omega) (l ++ [w]) (by simp) hle2 rfl

lemma cycle_exists (rem : V → V → ℕ) (hsym : ∀ u v, rem u v = rem v u)
    (hdiag : ∀ v, rem v v = 0) (heven : ∀ u, Even (∑ v, rem u v)) (u : V)
    (hu : 0 < ∑ v, rem u v) :
    ∃ C : List V, IsClosed u C ∧ 2 ≤ C.length ∧ ∀ a b, ec C a b ≤ rem a b := by
  obtain ⟨w, -, hw⟩ := Finset.exists_lt_of_sum_lt
    (show ∑ v, (0 : ℕ) < ∑ v, rem u v by simpa using hu)
  have huw : u ≠ w := by intro h; rw [h, hdiag] at hw; omega
  have hle : ∀ a b, ec [u, w] a b ≤ rem a b := by
    intro a b
    simp only [ec_cons_cons, ec_single, add_zero]
    by_cases h1 : u = a ∧ w = b
    · obtain ⟨rfl, rfl⟩ := h1
      have : ¬ (u = w ∧ w = u) := fun h => huw h.1
      simp only [and_self, if_true, this, if_false]; omega
    · by_cases h2 : u = b ∧ w = a
      · obtain ⟨rfl, rfl⟩ := h2
        simp only [h1, if_false, and_self, if_true]; rw [hsym]; omega
      · simp [h1, h2]
  exact trail_extend rem hsym hdiag heven u _ [w] (by simp) hle rfl

theorem euler (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u) (hdiag : ∀ v, m v v = 0)
    (heven : ∀ u, Even (∑ v, m u v)) (v0 : V)
    (hconn : ∀ S : Finset V, v0 ∈ S → S ≠ Finset.univ → ∃ u ∈ S, ∃ w ∉ S, 0 < m u w) :
    ∃ L : List V, IsClosed v0 L ∧ ∀ a b, ec L a b = m a b := by
  suffices H : ∀ s : ℕ, ∀ L : List V, IsClosed v0 L → (∀ a b, ec L a b ≤ m a b) →
      ∑ a, ∑ b, m a b - ∑ a, ∑ b, ec L a b = s →
      ∃ L : List V, IsClosed v0 L ∧ ∀ a b, ec L a b = m a b by
    exact H _ [v0] ⟨rfl, rfl⟩ (fun a b => by simp [ec_single]) rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
  intro L hL hle hs
  by_cases hall : ∀ a b, ec L a b = m a b
  · exact ⟨L, hL, hall⟩
  push Not at hall
  obtain ⟨a, b, hab⟩ := hall
  have hablt : ec L a b < m a b := lt_of_le_of_ne (hle a b) hab
  set rem : V → V → ℕ := fun p q => m p q - ec L p q with hrem
  -- a vertex of L with a remaining edge
  obtain ⟨u, huL, hupos⟩ : ∃ u ∈ L, 0 < ∑ v, rem u v := by
    by_cases hS : L.toFinset = Finset.univ
    · refine ⟨a, ?_, ?_⟩
      · have : a ∈ L.toFinset := by rw [hS]; exact Finset.mem_univ a
        exact List.mem_toFinset.mp this
      · apply lt_of_lt_of_le _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
        simp only [hrem]; omega
    · have hv0 : v0 ∈ L.toFinset := by
        obtain ⟨hh, _⟩ := hL
        cases L with
        | nil => simp at hh
        | cons x l => simp only [List.head?_cons, Option.some.injEq] at hh; simp [hh]
      obtain ⟨u, hu, w, hw, huw⟩ := hconn L.toFinset hv0 hS
      refine ⟨u, List.mem_toFinset.mp hu, ?_⟩
      have hec : ec L u w = 0 := by
        by_contra h
        exact hw (List.mem_toFinset.mpr (ec_pos_mem L u w (Nat.pos_of_ne_zero h)).2)
      apply lt_of_lt_of_le _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))
      simp only [hrem]; omega
  have hremsym : ∀ p q, rem p q = rem q p := by
    intro p q; simp only [hrem]; rw [hsym, ec_symm]
  have hremdiag : ∀ p, rem p p = 0 := by intro p; simp [hrem, hdiag]
  have hremeven : ∀ p, Even (∑ q, rem p q) := by
    intro p
    have e : ∑ q, rem p q = ∑ q, m p q - ∑ q, ec L p q := by
      simp only [hrem]
      exact Finset.sum_tsub_distrib _ (fun q _ => hle p q)
    have h1 := heven p
    have h2 := closed_deg_even hL p
    have h3 : ∑ q, ec L p q ≤ ∑ q, m p q := Finset.sum_le_sum (fun q _ => hle p q)
    rw [e]
    obtain ⟨k1, hk1⟩ := h1; obtain ⟨k2, hk2⟩ := h2
    exact ⟨k1 - k2, by omega⟩
  obtain ⟨C, hC, hClen, hCle⟩ := cycle_exists rem hremsym hremdiag hremeven u hupos
  obtain ⟨P, Q, hPQ⟩ := List.append_of_mem huL
  -- C = u :: C1 = C0 ++ [u]
  obtain ⟨hCh, hCl⟩ := hC
  have hCne : C ≠ [] := by intro h; rw [h] at hClen; simp at hClen
  obtain ⟨C1, hC1⟩ : ∃ C1, C = u :: C1 := by
    cases C with
    | nil => exact absurd rfl hCne
    | cons x l => simp only [List.head?_cons, Option.some.injEq] at hCh; exact ⟨l, by rw [hCh]⟩
  obtain ⟨C0, hC0⟩ : ∃ C0, C = C0 ++ [u] := by
    rw [hC1, getLast?_eq_lastOf, Option.some.injEq] at hCl
    obtain ⟨A, hA⟩ := exists_concat_lastOf u C1
    rw [hCl] at hA
    exact ⟨A, by rw [hC1, hA]⟩
  set L' := P ++ C ++ Q with hL'
  have hecL' : ∀ p q, ec L' p q = ec L p q + ec C p q := by
    intro p q
    have e1 : L' = (P ++ C0) ++ u :: Q := by rw [hL', hC0]; simp
    have e2 : P ++ C0 ++ [u] = P ++ u :: C1 := by
      rw [List.append_assoc, ← hC0, hC1]
    rw [e1, ec_split (P ++ C0) Q u, e2, ec_split P C1 u, ← hC1, hPQ, ec_split P Q u]; ring
  have hle' : ∀ p q, ec L' p q ≤ m p q := by
    intro p q
    rw [hecL']
    have := hCle p q
    have := hle p q
    simp only [hrem] at *
    omega
  have hL'closed : IsClosed v0 L' := by
    obtain ⟨hh, hl⟩ := hL
    rw [hPQ] at hh hl
    constructor
    · rw [hL', hC1]
      cases P with
      | nil => simpa using hh
      | cons x P => simpa using hh
    · rw [hL', hC0]
      cases Q with
      | nil =>
        simp only [List.append_nil] at hl ⊢
        rw [← List.append_assoc, List.getLast?_concat]
        rw [List.getLast?_concat] at hl
        exact hl
      | cons x Q =>
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil x Q)]
        rw [show P ++ u :: x :: Q = (P ++ [u]) ++ x :: Q by simp,
          List.getLast?_append_of_ne_nil _ (List.cons_ne_nil x Q)] at hl
        exact hl
  have hCtot : 0 < ∑ p, ∑ q, ec C p q := by
    rw [hC1, ec_total]
    have : 1 ≤ C1.length := by rw [hC1] at hClen; simp at hClen; omega
    omega
  have htot : ∑ p, ∑ q, ec L' p q = ∑ p, ∑ q, ec L p q + ∑ p, ∑ q, ec C p q := by
    simp only [hecL', Finset.sum_add_distrib]
  have hbound : ∑ p, ∑ q, ec L' p q ≤ ∑ p, ∑ q, m p q :=
    Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hle' p q))
  exact IH _ (by omega) L' hL'closed hle' rfl

end Euler

/-! ### From closed walks to tours (shortcutting) -/

section Tour

/-- cost of the walk starting at `a` and then visiting the list `l` in order -/
def walk {α : Type*} (c : α → α → ℝ) : α → List α → ℝ
  | _, [] => 0
  | a, b :: l => c a b + walk c b l

/-- cyclic cost of a list -/
def cyc {α : Type*} (c : α → α → ℝ) : List α → ℝ
  | [] => 0
  | a :: l => walk c a (l ++ [a])

lemma walk_append_two {α : Type*} (c : α → α → ℝ) (M : List α) (x a y : α) :
    walk c x (M ++ [a, y]) = walk c x (M ++ [a]) + c a y := by
  induction M generalizing x with
  | nil => simp [walk]
  | cons b M ih =>
    simp only [List.cons_append, walk]
    rw [ih]; ring

lemma cyc_cons_eq_append {α : Type*} (c : α → α → ℝ) (a : α) (l : List α) :
    cyc c (a :: l) = cyc c (l ++ [a]) := by
  cases l with
  | nil => simp
  | cons b l' =>
    simp only [cyc, List.cons_append, walk]
    have := walk_append_two c l' b a b
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    rw [this]; ring

lemma cyc_append_comm {α : Type*} (c : α → α → ℝ) (A B : List α) :
    cyc c (A ++ B) = cyc c (B ++ A) := by
  induction A generalizing B with
  | nil => simp
  | cons a A ih =>
    rw [List.cons_append, cyc_cons_eq_append, List.append_assoc, ih]
    simp

lemma walk_ofFn {α : Type*} (c : α → α → ℝ) :
    ∀ (m : ℕ) (f : Fin (m + 1) → α),
      walk c (f 0) (List.ofFn fun i : Fin m => f i.succ) =
        ∑ i : Fin m, c (f i.castSucc) (f i.succ)
  | 0, f => by simp [walk]
  | m + 1, f => by
    rw [List.ofFn_succ]
    simp only [walk]
    rw [Fin.sum_univ_succ]
    have := walk_ofFn c m (fun i => f i.succ)
    rw [this]
    rfl

lemma walk_append_one {α : Type*} (c : α → α → ℝ) (M : List α) (x y : α) :
    walk c x (M ++ [y]) = walk c x M + c ((x :: M).getLast (by simp)) y := by
  induction M generalizing x with
  | nil => simp [walk]
  | cons b M ih =>
    simp only [List.cons_append, walk]
    rw [ih, List.getLast_cons_cons]; ring

lemma cyc_ofFn {α : Type*} (c : α → α → ℝ) (m : ℕ) (f : Fin (m + 1) → α) :
    cyc c (List.ofFn f) = ∑ i, c (f i) (f (finRotate (m + 1) i)) := by
  rw [List.ofFn_succ]
  simp only [cyc]
  rw [walk_append_one, walk_ofFn]
  rw [Fin.sum_univ_castSucc]
  have hl : (f 0 :: List.ofFn fun i : Fin m => f i.succ).getLast (by simp) = f (Fin.last m) := by
    have e : (f 0 :: List.ofFn fun i : Fin m => f i.succ) = List.ofFn f := List.ofFn_succ.symm
    rw [List.getLast_congr _ (by simp) e, List.getLast_ofFn]
    rfl
  rw [hl, finRotate_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]
  simp

lemma exists_perm_of_list {n : ℕ} (c : Fin n → Fin n → ℝ) (T : List (Fin n)) (hT : T.Nodup)
    (hlen : T.length = n) (hn : 1 ≤ n) : ∃ π : Equiv.Perm (Fin n), tourCost c π = cyc c T := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let f : Fin (m + 1) → Fin (m + 1) := fun i => T[i.val]'(by omega)
  have hf : Function.Injective f := by
    intro i j h
    simp only [f] at h
    rw [hT.getElem_inj_iff] at h
    exact Fin.ext h
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  have hT' : List.ofFn f = T := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      rw [List.getElem_ofFn]
  rw [← hT', cyc_ofFn]
  rfl

lemma tspOpt_le_tourCost {n : ℕ} (c : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    tspOpt c ≤ tourCost c π := by
  unfold tspOpt
  apply csInf_le
  · refine ((Set.finite_range (tourCost c)).subset ?_).bddBelow
    rintro t ⟨σ, rfl⟩
    exact ⟨σ, rfl⟩
  · exact ⟨π, rfl⟩

lemma wc_cons_eq_walk {α : Type*} [Fintype α] [DecidableEq α] (c : α → α → ℝ) (a : α)
    (l : List α) : wc c (a :: l) = walk c a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => rw [wc, ih, walk]

lemma cyc_cons_ge {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (x : Fin n)
    (R : List (Fin n)) (hR : R ≠ []) : cyc c R ≤ cyc c (x :: R) := by
  obtain ⟨hsymm, hdiag, htri⟩ := hc
  obtain ⟨r, R', rfl⟩ : ∃ r R', R = r :: R' := by
    cases R with
    | nil => exact absurd rfl hR
    | cons r R' => exact ⟨r, R', rfl⟩
  simp only [cyc, List.cons_append, walk]
  rw [walk_append_one, walk_append_one]
  have := htri ((r :: R').getLast (by simp)) x r
  linarith

lemma cyc_remove {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (A B : List (Fin n))
    (x : Fin n) (hAB : A ++ B ≠ []) : cyc c (A ++ B) ≤ cyc c (A ++ x :: B) := by
  rw [cyc_append_comm c A (x :: B), cyc_append_comm c A B, List.cons_append]
  apply cyc_cons_ge c hc
  intro h
  apply hAB
  rw [List.append_eq_nil_iff] at h ⊢
  exact ⟨h.2, h.1⟩

lemma dedup_cyc {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    ∀ (k : ℕ) (K : List (Fin n)), K.length = k →
      ∃ K' : List (Fin n), K'.Nodup ∧ (∀ y, y ∈ K' ↔ y ∈ K) ∧ cyc c K' ≤ cyc c K := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro K hK
  by_cases hnd : K.Nodup
  · exact ⟨K, hnd, fun _ => Iff.rfl, le_rfl⟩
  · rw [List.nodup_iff_count_le_one] at hnd
    push Not at hnd
    obtain ⟨x, hx⟩ := hnd
    have hxK : x ∈ K := List.count_pos_iff.mp (by omega)
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hxK
    have hcnt : List.count x (A ++ x :: B) = List.count x A + List.count x B + 1 := by
      simp [List.count_append, List.count_cons]; ring
    have hxAB : x ∈ A ++ B := by
      rw [List.mem_append]
      by_contra h
      push Not at h
      have h1 := List.count_eq_zero_of_not_mem h.1
      have h2 := List.count_eq_zero_of_not_mem h.2
      omega
    have hlen : (A ++ B).length < k := by
      rw [← hK]; simp
    obtain ⟨K', hnd', hmem, hcost⟩ := IH _ hlen (A ++ B) rfl
    refine ⟨K', hnd', ?_, hcost.trans (cyc_remove c hc A B x (List.ne_nil_of_mem hxAB))⟩
    intro y
    rw [hmem]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl h
      · subst h; simpa using hxAB
      · exact Or.inr h

theorem tour_le_multigraph {n : ℕ} (hn : 2 ≤ n) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (m : Fin n → Fin n → ℕ) (hsym : ∀ u v, m u v = m v u) (hdiag : ∀ v, m v v = 0)
    (heven : ∀ u, Even (∑ v, m u v))
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → ∃ u ∈ S, ∃ w ∉ S, 0 < m u w) :
    tspOpt c ≤ (1 / 2) * ∑ u, ∑ v, c u v * (m u v : ℝ) := by
  set v0 : Fin n := ⟨0, by omega⟩
  obtain ⟨L, hL, hLm⟩ := euler m hsym hdiag heven v0
    (fun S hS hSu => hconn S ⟨v0, hS⟩ hSu)
  have hcost : 2 * wc c L = ∑ u, ∑ v, c u v * (m u v : ℝ) := by
    rw [wc_eq c hc.1 L]; simp_rw [hLm]
  -- every vertex lies on L
  have hall : ∀ y, y ∈ L := by
    have hv0 : v0 ∈ L.toFinset := by
      obtain ⟨hh, _⟩ := hL
      cases L with
      | nil => simp at hh
      | cons x l => simp only [List.head?_cons, Option.some.injEq] at hh; simp [hh]
    by_contra h
    push Not at h
    obtain ⟨y, hy⟩ := h
    have hS : L.toFinset ≠ Finset.univ := by
      intro hE
      apply hy
      have : y ∈ L.toFinset := by rw [hE]; exact Finset.mem_univ y
      exact List.mem_toFinset.mp this
    obtain ⟨u, hu, w, hw, huw⟩ := hconn L.toFinset ⟨v0, hv0⟩ hS
    rw [← hLm] at huw
    exact hw (List.mem_toFinset.mpr (ec_pos_mem L u w huw).2)
  -- L = v0 :: l = A ++ [v0]
  obtain ⟨hh, hl⟩ := hL
  obtain ⟨l, rfl⟩ : ∃ l, L = v0 :: l := by
    cases L with
    | nil => simp at hh
    | cons x l => simp only [List.head?_cons, Option.some.injEq] at hh; exact ⟨l, by rw [hh]⟩
  rw [getLast?_eq_lastOf, Option.some.injEq] at hl
  obtain ⟨A, hA⟩ := exists_concat_lastOf v0 l
  rw [hl] at hA
  have hAne : A ≠ [] := by
    intro hA0
    rw [hA0] at hA
    simp only [List.nil_append, List.cons.injEq] at hA
    have hl0 := hA.2
    have h1 : (⟨1, by omega⟩ : Fin n) ∈ v0 :: l := hall _
    rw [hl0] at h1
    simp [v0] at h1
  obtain ⟨A', rfl⟩ : ∃ A', A = v0 :: A' := by
    cases A with
    | nil => exact absurd rfl hAne
    | cons x A' =>
      simp only [List.cons_append, List.cons.injEq] at hA
      exact ⟨A', by rw [hA.1]⟩
  have hcycA : cyc c (v0 :: A') = wc c (v0 :: l) := by
    rw [hA, cyc, List.cons_append, wc_cons_eq_walk]
  have hmemA : ∀ y, y ∈ v0 :: A' := by
    intro y
    have := hall y
    rw [hA, List.mem_append] at this
    rcases this with h | h
    · exact h
    · simp at h; rw [h]; exact List.mem_cons_self
  obtain ⟨K', hnd, hmem, hK'⟩ := dedup_cyc c hc _ (v0 :: A') rfl
  have hlen : K'.length = n := by
    have h1 : K'.toFinset = Finset.univ := by
      ext y; simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact (hmem y).mpr (hmemA y)
    rw [← List.toFinset_card_of_nodup hnd, h1, Finset.card_univ, Fintype.card_fin]
  obtain ⟨π, hπ⟩ := exists_perm_of_list c K' hnd hlen (by omega)
  have := tspOpt_le_tourCost c π
  rw [hπ] at this
  linarith

end Tour

/-! ### Doubling the non-terminal vertices: T-joins from perfect matchings -/

section Double
variable {n : ℕ}

/-- doubled vertex set: one copy of each city, plus a second copy of each city outside `T` -/
abbrev DV (T : Finset (Fin n)) : Type := Fin n ⊕ {w // w ∈ Tᶜ}

def rho {T : Finset (Fin n)} : DV T → Fin n
  | Sum.inl v => v
  | Sum.inr w => w.val

def multN (T : Finset (Fin n)) (w : Fin n) : ℕ := if w ∈ T then 1 else 2

lemma multN_pos (T : Finset (Fin n)) (w : Fin n) : (0 : ℝ) < multN T w := by
  unfold multN; split_ifs <;> norm_num

lemma sum_rho {T : Finset (Fin n)} {M : Type*} [AddCommMonoid M] (G : Fin n → M) :
    ∑ z : DV T, G (rho z) = ∑ w, multN T w • G w := by
  rw [Fintype.sum_sum_type]
  simp only [rho]
  rw [Finset.sum_coe_sort Tᶜ G]
  rw [← Finset.sum_add_sum_compl T (fun w => multN T w • G w)]
  rw [← Finset.sum_add_sum_compl T G]
  have h1 : ∑ w ∈ T, multN T w • G w = ∑ w ∈ T, G w := by
    apply Finset.sum_congr rfl; intro w hw; simp [multN, hw]
  have h2 : ∑ w ∈ Tᶜ, multN T w • G w = ∑ w ∈ Tᶜ, G w + ∑ w ∈ Tᶜ, G w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w hw
    rw [Finset.mem_compl] at hw
    simp [multN, hw, two_nsmul]
  rw [h1, h2, add_assoc]

/-- number of copies of `w` in `S'` -/
def sc {T : Finset (Fin n)} (S' : Finset (DV T)) (w : Fin n) : ℕ :=
  (S'.filter (fun z => rho z = w)).card

lemma sum_rho_on {T : Finset (Fin n)} {M : Type*} [AddCommMonoid M] (S' : Finset (DV T))
    (G : Fin n → M) : ∑ z ∈ S', G (rho z) = ∑ w, sc S' w • G w := by
  rw [← Finset.sum_fiberwise S' rho (fun z => G (rho z))]
  apply Finset.sum_congr rfl; intro w _
  rw [sc, ← Finset.sum_const]
  apply Finset.sum_congr rfl; intro z hz
  rw [(Finset.mem_filter.mp hz).2]

lemma sc_univ {T : Finset (Fin n)} (w : Fin n) : sc (Finset.univ : Finset (DV T)) w = multN T w := by
  have h := sum_rho_on (T := T) Finset.univ (fun v => if v = w then 1 else 0)
  rw [sum_rho (T := T) (fun v => if v = w then 1 else 0)] at h
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  exact h.symm

lemma sc_le {T : Finset (Fin n)} (S' : Finset (DV T)) (w : Fin n) : sc S' w ≤ multN T w := by
  rw [← sc_univ]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

lemma sc_compl {T : Finset (Fin n)} (S' : Finset (DV T)) (w : Fin n) :
    sc S'ᶜ w + sc S' w = multN T w := by
  rw [← sc_univ, sc, sc, sc, ← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.filter_union, Finset.union_comm, Finset.union_compl]
  · exact Finset.disjoint_filter_filter (disjoint_compl_left)

/-- the doubled fractional matching -/
noncomputable def yD (T : Finset (Fin n)) (x : Fin n → Fin n → ℝ) (z z' : DV T) : ℝ :=
  x (rho z) (rho z') / (2 * (multN T (rho z) : ℝ) * (multN T (rho z') : ℝ)) +
    (if rho z = rho z' ∧ z ≠ z' then 1 / 2 else 0)

lemma multN_cases (T : Finset (Fin n)) (w : Fin n) : (multN T w : ℝ) = 1 ∨ (multN T w : ℝ) = 2 := by
  unfold multN; split_ifs <;> simp

lemma sumA_row (T : Finset (Fin n)) (x : Fin n → Fin n → ℝ) (v : Fin n) :
    ∑ z' : DV T, x v (rho z') / (2 * (multN T v : ℝ) * (multN T (rho z') : ℝ)) =
      ∑ w, x v w / (2 * (multN T v : ℝ)) := by
  rw [sum_rho (T := T) (fun w => x v w / (2 * (multN T v : ℝ) * (multN T w : ℝ)))]
  apply Finset.sum_congr rfl; intro w _
  rw [nsmul_eq_mul]
  have := multN_pos T w
  have := multN_pos T v
  field_simp

lemma sumB_row (T : Finset (Fin n)) (z : DV T) :
    ∑ z' : DV T, (if rho z = rho z' ∧ z ≠ z' then (1 : ℝ) / 2 else 0) =
      ((multN T (rho z) : ℝ) - 1) / 2 := by
  have e : ∀ z' : DV T, (if rho z = rho z' ∧ z ≠ z' then (1 : ℝ) / 2 else 0) =
      (if rho z' = rho z then (1 : ℝ) / 2 else 0) - (if z' = z then (1 : ℝ) / 2 else 0) := by
    intro z'
    by_cases h1 : z' = z
    · subst h1; simp
    · have : z ≠ z' := Ne.symm h1
      by_cases h2 : rho z' = rho z
      · simp [h1, h2, this]
      · simp [h1, h2, Ne.symm h2]
  simp_rw [e]
  rw [Finset.sum_sub_distrib, sum_rho (T := T) (fun w => if w = rho z then (1 : ℝ) / 2 else 0)]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul]
  ring

lemma yD_feas (_hn : 1 ≤ n) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) (T : Finset (Fin n))
    (hT : Even T.card) : Feas (yD T x) := by
  obtain ⟨hsymm, hdiag, hnn, _, hdeg, hcut⟩ := hx
  constructor
  · intro z z'
    unfold yD
    rw [hsymm, mul_assoc, mul_assoc, mul_comm (multN T (rho z) : ℝ)]
    congr 1
    by_cases h : rho z = rho z' ∧ z ≠ z'
    · rw [if_pos h, if_pos ⟨h.1.symm, Ne.symm h.2⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, Ne.symm h'.2⟩)]
  · intro z; simp [yD, hdiag]
  · intro z z'
    unfold yD
    have := multN_pos T (rho z)
    have := multN_pos T (rho z')
    apply add_nonneg
    · exact div_nonneg (hnn _ _) (by positivity)
    · split_ifs <;> norm_num
  · intro z
    unfold yD
    rw [Finset.sum_add_distrib, sumA_row, sumB_row]
    rw [← Finset.sum_div, hdeg]
    rcases multN_cases T (rho z) with h | h <;> rw [h] <;> norm_num
  · intro S' hS'
    -- notation
    set s : Fin n → ℕ := sc S' with hs
    set m : Fin n → ℕ := multN T with hm
    have hsle : ∀ w, s w ≤ m w := fun w => sc_le S' w
    have hsc : ∀ w, sc S'ᶜ w = m w - s w := by
      intro w; have := sc_compl S' w; simp only [hs, hm] at *; omega
    have hmpos : ∀ w, (0 : ℝ) < m w := multN_pos T
    have hm2 : ∀ w, m w ≤ 2 := by intro w; simp only [hm, multN]; split_ifs <;> omega
    obtain ⟨f, hf⟩ : ∃ f : Fin n → ℝ, f = fun w => (s w : ℝ) / (m w : ℝ) := ⟨_, rfl⟩
    have hf01 : ∀ w, 0 ≤ f w ∧ f w ≤ 1 := by
      intro w
      have h1 := hmpos w
      have h2 : (s w : ℝ) ≤ m w := by exact_mod_cast hsle w
      rw [hf]
      exact ⟨div_nonneg (Nat.cast_nonneg _) h1.le, (div_le_one h1).mpr h2⟩
    -- the cut splits into two parts
    have hcutA : ∑ z ∈ S', ∑ z' ∈ S'ᶜ,
        x (rho z) (rho z') / (2 * (m (rho z) : ℝ) * (m (rho z') : ℝ)) =
        (1 / 2) * ∑ v, ∑ w, f v * (1 - f w) * x v w := by
      have inner : ∀ v, ∑ z' ∈ S'ᶜ, x v (rho z') / (2 * (m v : ℝ) * (m (rho z') : ℝ)) =
          ∑ w, (1 - f w) * x v w / (2 * (m v : ℝ)) := by
        intro v
        rw [sum_rho_on S'ᶜ (fun w => x v w / (2 * (m v : ℝ) * (m w : ℝ)))]
        apply Finset.sum_congr rfl; intro w _
        rw [nsmul_eq_mul, hsc w, Nat.cast_sub (hsle w)]
        have := hmpos w
        have := hmpos v
        simp only [hf]
        field_simp
      simp_rw [inner]
      rw [sum_rho_on S' (fun v => ∑ w, (1 - f w) * x v w / (2 * (m v : ℝ)))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _
      rw [nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro w _
      have := hmpos v
      simp only [hf]
      field_simp
      rw [hs]; ring
    have hcutB : ∑ z ∈ S', ∑ z' ∈ S'ᶜ, (if rho z = rho z' ∧ z ≠ z' then (1 : ℝ) / 2 else 0) =
        (1 / 2) * ∑ w, (s w : ℝ) * ((m w : ℝ) - s w) := by
      have inner : ∀ z ∈ S', ∑ z' ∈ S'ᶜ, (if rho z = rho z' ∧ z ≠ z' then (1 : ℝ) / 2 else 0) =
          ((m (rho z) : ℝ) - s (rho z)) / 2 := by
        intro z hz
        have e : ∀ z' ∈ S'ᶜ, (if rho z = rho z' ∧ z ≠ z' then (1 : ℝ) / 2 else 0) =
            (if rho z' = rho z then (1 : ℝ) / 2 else 0) := by
          intro z' hz'
          have : z ≠ z' := by
            intro h; rw [h] at hz; exact (Finset.mem_compl.mp hz') hz
          by_cases h2 : rho z' = rho z
          · simp [h2, this]
          · simp [h2, Ne.symm h2]
        rw [Finset.sum_congr rfl e]
        rw [sum_rho_on S'ᶜ (fun w => if w = rho z then (1 : ℝ) / 2 else 0)]
        simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          nsmul_eq_mul]
        rw [hsc, Nat.cast_sub (hsle _)]; ring
      rw [Finset.sum_congr rfl inner]
      rw [sum_rho_on S' (fun w => ((m w : ℝ) - s w) / 2)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro w _
      rw [nsmul_eq_mul]; ring
    have hcut_eq : cut (yD T x) S' = (1 / 2) * ∑ v, ∑ w, f v * (1 - f w) * x v w +
        (1 / 2) * ∑ w, (s w : ℝ) * ((m w : ℝ) - s w) := by
      unfold cut yD
      rw [← hm]
      simp_rw [Finset.sum_add_distrib]
      rw [hcutA, hcutB]
    rw [hcut_eq]
    have hA0 : 0 ≤ ∑ v, ∑ w, f v * (1 - f w) * x v w := by
      apply Finset.sum_nonneg; intro v _; apply Finset.sum_nonneg; intro w _
      have hv := hf01 v; have hw := hf01 w
      exact mul_nonneg (mul_nonneg hv.1 (by linarith)) (hnn v w)
    have hBterm : ∀ w, 0 ≤ (s w : ℝ) * ((m w : ℝ) - s w) := by
      intro w
      have h2 : (s w : ℝ) ≤ m w := by exact_mod_cast hsle w
      exact mul_nonneg (by positivity) (by linarith)
    set H := Finset.univ.filter (fun w => 0 < s w ∧ s w < m w) with hH
    have hHterm : ∀ w ∈ H, (1 : ℝ) ≤ (s w : ℝ) * ((m w : ℝ) - s w) := by
      intro w hw
      simp only [hH, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have h1 : (1 : ℝ) ≤ s w := by exact_mod_cast hw.1
      have h2 : (s w : ℝ) + 1 ≤ m w := by exact_mod_cast hw.2
      nlinarith
    have hBH : (H.card : ℝ) ≤ ∑ w, (s w : ℝ) * ((m w : ℝ) - s w) := by
      calc (H.card : ℝ) = ∑ w ∈ H, (1 : ℝ) := by simp
        _ ≤ ∑ w ∈ H, (s w : ℝ) * ((m w : ℝ) - s w) := Finset.sum_le_sum hHterm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => hBterm w)
    rcases Nat.lt_or_ge H.card 2 with hH2 | hH2
    · rcases Nat.lt_or_ge H.card 1 with hH1 | hH1
      · -- no split vertex
        have hH0 : H = ∅ := Finset.card_eq_zero.mp (by omega)
        have hsplit : ∀ w, s w = 0 ∨ s w = m w := by
          intro w
          by_contra h
          push Not at h
          have : w ∈ H := by
            simp only [hH, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨Nat.pos_of_ne_zero h.1, lt_of_le_of_ne (hsle w) h.2⟩
          rw [hH0] at this; simp at this
        set S0 := Finset.univ.filter (fun w => 0 < s w) with hS0
        have hf0 : ∀ w, f w = if w ∈ S0 then 1 else 0 := by
          intro w
          simp only [hf, hS0, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hsplit w with h | h
          · simp [h]
          · have := hmpos w
            have hpos : 0 < s w := by rw [h]; exact_mod_cast this
            rw [if_pos hpos, h, div_self this.ne']
        have hcardS' : S'.card = ∑ w, s w := by
          rw [Finset.card_eq_sum_card_fiberwise (f := rho) (t := Finset.univ)
            (fun z _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
          rfl
        have hS0ne : S0.Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          have : ∀ w, s w = 0 := by
            intro w
            by_contra h'
            have : w ∈ S0 := by simp [hS0]; omega
            rw [h] at this; simp at this
          rw [hcardS', Finset.sum_eq_zero (fun w _ => this w)] at hS'
          simp at hS'
        have hS0u : S0 ≠ Finset.univ := by
          intro h
          have hall : ∀ w, s w = m w := by
            intro w
            have : w ∈ S0 := by rw [h]; exact Finset.mem_univ w
            simp only [hS0, Finset.mem_filter, Finset.mem_univ, true_and] at this
            rcases hsplit w with h' | h'
            · omega
            · exact h'
          have hsum : ∑ w, s w = T.card + 2 * Tᶜ.card := by
            rw [Finset.sum_congr rfl (fun w _ => hall w)]
            rw [← Finset.sum_add_sum_compl T]
            simp only [hm, multN]
            rw [Finset.sum_congr rfl (fun w hw => if_pos hw),
              Finset.sum_congr rfl (fun w hw => if_neg (Finset.mem_compl.mp hw))]
            simp [mul_comm]
          rw [hcardS', hsum] at hS'
          obtain ⟨k, hk⟩ := hT
          obtain ⟨j, hj⟩ := hS'
          omega
        have hc2 := hcut S0 hS0ne hS0u
        have hAeq : ∑ v, ∑ w, f v * (1 - f w) * x v w = ∑ u ∈ S0, ∑ w ∈ S0ᶜ, x u w := by
          simp_rw [hf0]
          rw [← Finset.sum_add_sum_compl S0]
          have h0 : ∑ v ∈ S0ᶜ, ∑ w, (if v ∈ S0 then (1 : ℝ) else 0) *
              (1 - if w ∈ S0 then 1 else 0) * x v w = 0 := by
            apply Finset.sum_eq_zero; intro v hv
            rw [Finset.mem_compl] at hv; simp [hv]
          rw [h0, add_zero]
          apply Finset.sum_congr rfl; intro v hv
          rw [← Finset.sum_add_sum_compl S0]
          have h1 : ∑ w ∈ S0, (if v ∈ S0 then (1 : ℝ) else 0) *
              (1 - if w ∈ S0 then 1 else 0) * x v w = 0 := by
            apply Finset.sum_eq_zero; intro w hw; simp [hw]
          rw [h1, zero_add]
          apply Finset.sum_congr rfl; intro w hw
          rw [Finset.mem_compl] at hw; simp [hv, hw]
        rw [hAeq]
        have := Finset.sum_nonneg (fun w (_ : w ∈ Finset.univ) => hBterm w)
        linarith
      · -- exactly one split vertex
        have hH1' : H.card = 1 := by omega
        obtain ⟨h, hHh⟩ := Finset.card_eq_one.mp hH1'
        have hhH : h ∈ H := by rw [hHh]; simp
        simp only [hH, Finset.mem_filter, Finset.mem_univ, true_and] at hhH
        have hmh : m h = 2 := by have := hm2 h; omega
        have hsh : s h = 1 := by omega
        have hfh : f h = 1 / 2 := by simp only [hf, hsh, hmh]; norm_num
        have hA : 1 ≤ ∑ v, ∑ w, f v * (1 - f w) * x v w := by
          have hg : ∀ v w, 0 ≤ f v * (1 - f w) * x v w := by
            intro v w
            have hv := hf01 v; have hw := hf01 w
            exact mul_nonneg (mul_nonneg hv.1 (by linarith)) (hnn v w)
          have step1 : ∑ v, ∑ w, f v * (1 - f w) * x v w =
              ∑ w, f h * (1 - f w) * x h w + ∑ v ∈ Finset.univ.erase h, ∑ w, f v * (1 - f w) * x v w := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h)]
          have step2 : ∑ v ∈ Finset.univ.erase h, f v * (1 - f h) * x v h ≤
              ∑ v ∈ Finset.univ.erase h, ∑ w, f v * (1 - f w) * x v w := by
            apply Finset.sum_le_sum; intro v _
            exact Finset.single_le_sum (fun w _ => hg v w) (Finset.mem_univ h)
          have step3 : ∑ v ∈ Finset.univ.erase h, f v * (1 - f h) * x v h =
              ∑ v, f v * (1 - f h) * x h v := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h)]
            rw [hdiag h, mul_zero, zero_add]
            apply Finset.sum_congr rfl; intro v _; rw [hsymm]
          have step4 : ∑ w, f h * (1 - f w) * x h w + ∑ v, f v * (1 - f h) * x h v = 1 := by
            rw [hfh, ← Finset.sum_add_distrib]
            have : ∀ w, 1 / 2 * (1 - f w) * x h w + f w * (1 - 1 / 2) * x h w = 1 / 2 * x h w := by
              intro w; ring
            simp_rw [this]
            rw [← Finset.mul_sum, hdeg]; norm_num
          linarith
        have hB : (1 : ℝ) ≤ ∑ w, (s w : ℝ) * ((m w : ℝ) - s w) := by
          have := hBH; rw [hH1'] at this; simpa using this
        linarith
    · have : (2 : ℝ) ≤ H.card := by exact_mod_cast hH2
      linarith

lemma rho_eq_iff {T : Finset (Fin n)} (z : DV T) (u : Fin n) :
    rho z = u ↔ z = Sum.inl u ∨ ∃ h : u ∈ Tᶜ, z = Sum.inr ⟨u, h⟩ := by
  cases z with
  | inl v => simp [rho]
  | inr w =>
    obtain ⟨w, hw⟩ := w
    simp only [rho, reduceCtorEq, false_or, Sum.inr.injEq, Subtype.mk.injEq]
    constructor
    · intro h; subst h; exact ⟨hw, rfl⟩
    · rintro ⟨_, h⟩; exact h

theorem tjoin_exists (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) (T : Finset (Fin n)) (hT : Even T.card) :
    ∃ J : Fin n → Fin n → ℕ, (∀ u v, J u v = J v u) ∧ (∀ v, J v v = 0) ∧
      (∀ u, (∑ v, J u v) % 2 = if u ∈ T then 1 else 0) ∧
      ∑ u, ∑ v, c u v * (J u v : ℝ) ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  obtain ⟨hcs, hcd, _⟩ := hc
  have hfeas := yD_feas hn x hx T hT
  obtain ⟨M, hM, hMc⟩ := pm_main _ (DV T) rfl (yD T x) hfeas (fun z z' => c (rho z) (rho z'))
  set J : Fin n → Fin n → ℕ := fun u v =>
    if u = v then 0 else (Finset.univ.filter (fun z : DV T => rho z = u ∧ rho (M z) = v)).card
    with hJ
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · intro u v
    simp only [hJ]
    by_cases huv : u = v
    · subst huv; rfl
    · rw [if_neg huv, if_neg (Ne.symm huv)]
      refine Finset.card_bij' (fun z _ => M z) (fun z _ => M z) ?_ ?_ ?_ ?_
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [(hM z).1]; exact ⟨hz.2, hz.1⟩
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [(hM z).1]; exact ⟨hz.2, hz.1⟩
      · intro z _; exact (hM z).1
      · intro z _; exact (hM z).1
  · intro v; simp [hJ]
  · intro u
    have hdeg : ∑ v, J u v = (Finset.univ.filter (fun z : DV T => rho z = u ∧ rho (M z) ≠ u)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun z => rho (M z)) (t := Finset.univ)
        (fun z _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
      apply Finset.sum_congr rfl; intro v _
      simp only [hJ]
      by_cases huv : u = v
      · subst huv
        rw [if_pos rfl]
        symm
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        tauto
      · rw [if_neg huv]
        congr 1
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]; exact Ne.symm huv⟩, h2⟩
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hdeg]
    by_cases huT : u ∈ T
    · rw [if_pos huT]
      have hfib : Finset.univ.filter (fun z : DV T => rho z = u ∧ rho (M z) ≠ u) = {Sum.inl u} := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, _⟩
          rcases (rho_eq_iff z u).mp h1 with h | ⟨h, _⟩
          · exact h
          · exact absurd huT (Finset.mem_compl.mp h)
        · rintro rfl
          refine ⟨rfl, ?_⟩
          intro h
          rcases (rho_eq_iff _ u).mp h with h' | ⟨h', _⟩
          · exact (hM _).2 h'
          · exact absurd huT (Finset.mem_compl.mp h')
      rw [hfib]; rfl
    · rw [if_neg huT]
      have huT' : u ∈ Tᶜ := Finset.mem_compl.mpr huT
      set a : DV T := Sum.inl u
      set b : DV T := Sum.inr ⟨u, huT'⟩
      have hab : a ≠ b := by simp [a, b]
      have hfibu : ∀ z : DV T, rho z = u ↔ z = a ∨ z = b := by
        intro z
        rw [rho_eq_iff]
        constructor
        · rintro (h | ⟨_, h⟩)
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨huT', h⟩
      by_cases hMa : M a = b
      · have hMb : M b = a := by rw [← hMa, (hM a).1]
        have : Finset.univ.filter (fun z : DV T => rho z = u ∧ rho (M z) ≠ u) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro z _ hz
          rcases (hfibu z).mp hz.1 with h | h
          · apply hz.2; rw [h, hMa]; exact (hfibu b).mpr (Or.inr rfl)
          · apply hz.2; rw [h, hMb]; exact (hfibu a).mpr (Or.inl rfl)
        rw [this]; rfl
      · have hMb : M b ≠ a := by
          intro h; apply hMa; rw [← h, (hM b).1]
        have hMa' : rho (M a) ≠ u := by
          intro h
          rcases (hfibu _).mp h with h' | h'
          · exact (hM a).2 h'
          · exact hMa h'
        have hMb' : rho (M b) ≠ u := by
          intro h
          rcases (hfibu _).mp h with h' | h'
          · exact hMb h'
          · exact (hM b).2 h'
        have : Finset.univ.filter (fun z : DV T => rho z = u ∧ rho (M z) ≠ u) = {a, b} := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨h1, _⟩; exact (hfibu z).mp h1
          · rintro (h | h)
            · subst h; exact ⟨(hfibu _).mpr (Or.inl rfl), hMa'⟩
            · subst h; exact ⟨(hfibu _).mpr (Or.inr rfl), hMb'⟩
        rw [this, Finset.card_pair hab]
  · -- cost
    have hL : ∑ u, ∑ v, c u v * (J u v : ℝ) = ∑ z : DV T, c (rho z) (rho (M z)) := by
      symm
      rw [← Finset.sum_fiberwise (Finset.univ : Finset (DV T)) (fun z => (rho z, rho (M z)))
        (fun z => c (rho z) (rho (M z)))]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      have e : ∀ z ∈ Finset.univ.filter (fun z : DV T => (rho z, rho (M z)) = (u, v)),
          c (rho z) (rho (M z)) = c u v := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hz
        rw [hz.1, hz.2]
      rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]
      simp only [hJ]
      by_cases huv : u = v
      · subst huv; rw [hcd]; simp
      · have hfe : Finset.univ.filter (fun z : DV T => (rho z, rho (M z)) = (u, v)) =
            Finset.univ.filter (fun z : DV T => rho z = u ∧ rho (M z) = v) := by
          ext z; simp [Prod.mk.injEq]
        rw [hfe, if_neg huv]; ring
    have hR : ∑ z : DV T, ∑ z' : DV T, c (rho z) (rho z') * yD T x z z' =
        (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
      have e1 : ∀ z z' : DV T, c (rho z) (rho z') * yD T x z z' =
          c (rho z) (rho z') * x (rho z) (rho z') /
            (2 * (multN T (rho z) : ℝ) * (multN T (rho z') : ℝ)) := by
        intro z z'
        unfold yD
        by_cases h : rho z = rho z' ∧ z ≠ z'
        · rw [if_pos h, h.1, hcd, hx.2.1]; ring
        · rw [if_neg h]; ring
      simp_rw [e1]
      have e2 : ∀ z : DV T, ∑ z' : DV T, c (rho z) (rho z') * x (rho z) (rho z') /
          (2 * (multN T (rho z) : ℝ) * (multN T (rho z') : ℝ)) =
          ∑ w, c (rho z) w * x (rho z) w / (2 * (multN T (rho z) : ℝ)) := by
        intro z
        rw [sum_rho (T := T) (fun w => c (rho z) w * x (rho z) w /
          (2 * (multN T (rho z) : ℝ) * (multN T w : ℝ)))]
        apply Finset.sum_congr rfl; intro w _
        rw [nsmul_eq_mul]
        have := multN_pos T w
        have := multN_pos T (rho z)
        field_simp
      simp_rw [e2]
      rw [sum_rho (T := T) (fun v => ∑ w, c v w * x v w / (2 * (multN T v : ℝ)))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _
      rw [nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro w _
      have := multN_pos T v
      field_simp
    rw [hL]
    rw [← hR]
    exact hMc

end Double

/-! ### Prim order and layer-cake bound (adapted from the track-2 development) -/

section Prim

/-- Prim invariant for the first `k` vertices of the order `v`, with parent function `p`. -/
def PrimInv {n : ℕ} (c : Fin n → Fin n → ℝ) (k : ℕ) (v : ℕ → Fin n) (p : ℕ → ℕ) : Prop :=
  (∀ i j, i < k → j < k → v i = v j → i = j) ∧
  ∀ m, 1 ≤ m → m < k → p m < m ∧
    ∀ i < m, ∀ w : Fin n, (∀ j < m, v j ≠ w) → c (v (p m)) (v m) ≤ c (v i) w

lemma prim_exists {n : ℕ} (c : Fin n → Fin n → ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ v p, PrimInv c k v p := by
  induction k, hk1 using Nat.le_induction with
  | base =>
    refine ⟨fun _ => ⟨0, by omega⟩, fun _ => 0, ?_, ?_⟩
    · intro i j hi hj _; omega
    · intro m h1 h2; omega
  | succ k hk ih =>
    obtain ⟨v, p, hinj, hprim⟩ := ih (by omega)
    have hO : ∃ w : Fin n, ∀ j < k, v j ≠ w := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ (Finset.range k).image v := by
        intro w _
        obtain ⟨j, hj, hjw⟩ := h w
        exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, hjw⟩
      have := Finset.card_le_card hsub
      simp at this
      have h2 := Finset.card_image_le (s := Finset.range k) (f := v)
      simp at h2
      omega
    obtain ⟨w1, hw1⟩ := hO
    set O := (Finset.univ : Finset (Fin n)).filter (fun w => ∀ j < k, v j ≠ w) with hOdef
    have hPne : ((Finset.range k) ×ˢ O).Nonempty :=
      ⟨(0, w1), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), by simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]; exact hw1⟩⟩
    obtain ⟨⟨i0, w0⟩, hmem, hmin⟩ :=
      ((Finset.range k) ×ˢ O).exists_min_image (fun q => c (v q.1) q.2) hPne
    rw [Finset.mem_product] at hmem
    have hi0 : i0 < k := Finset.mem_range.mp hmem.1
    have hw0 : ∀ j < k, v j ≠ w0 := by simpa [O] using hmem.2
    refine ⟨fun j => if j = k then w0 else v j, fun j => if j = k then i0 else p j, ?_, ?_⟩
    · intro i j hi hj hij
      by_cases hik : i = k <;> by_cases hjk : j = k
      · omega
      · simp only [hik, hjk, if_true, if_false] at hij
        exact absurd hij.symm (hw0 j (by omega))
      · simp only [hik, hjk, if_true, if_false] at hij
        exact absurd hij (hw0 i (by omega))
      · simp only [hik, hjk, if_false] at hij
        exact hinj i j (by omega) (by omega) hij
    · intro m h1 h2
      by_cases hmk : m = k
      · subst hmk
        simp only [if_true]
        refine ⟨hi0, ?_⟩
        intro i hi w hw
        have hw' : ∀ j < m, v j ≠ w := by
          intro j hj
          have := hw j hj
          simpa [show j ≠ m by omega] using this
        have := hmin (i, w) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, by simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]; exact hw'⟩)
        simpa [show i ≠ m by omega, show i0 ≠ m by omega] using this
      · have hm : m < k := by omega
        obtain ⟨hpm, hpm2⟩ := hprim m h1 hm
        simp only [hmk, if_false, show p m ≠ k by omega]
        refine ⟨hpm, ?_⟩
        intro i hi w hw
        have hw' : ∀ j < m, v j ≠ w := by
          intro j hj
          have := hw j hj
          simpa [show j ≠ k by omega] using this
        simpa [show i ≠ k by omega] using hpm2 i hi w hw'


/-- Discrete layer-cake comparison. -/
lemma layer_cake_aux {κ ι : Type*} (s : Finset κ) (s' : Finset ι) (W : ι → ℝ)
    (hW : ∀ i ∈ s', 0 ≤ W i) :
    ∀ (N : ℕ) (g : κ → ℝ) (f : ι → ℝ), (∀ k ∈ s, 0 ≤ g k) → (∀ i ∈ s', 0 ≤ f i) →
      (∀ t : ℝ, 0 ≤ t → ((s.filter (fun k => t < g k)).card : ℝ) ≤
          ∑ i ∈ s'.filter (fun i => t < f i), W i) →
      ∀ P : Finset ℝ, P.card ≤ N → (∀ x ∈ P, 0 < x) →
        (∀ k ∈ s, 0 < g k → g k ∈ P) → (∀ i ∈ s', 0 < f i → f i ∈ P) →
      ∑ k ∈ s, g k ≤ ∑ i ∈ s', W i * f i := by
  intro N
  induction N with
  | zero =>
    intro g f hg hf _ P hP _ hgP _
    have hPe : P = ∅ := Finset.card_eq_zero.mp (by omega)
    have h0 : ∀ k ∈ s, g k = 0 := by
      intro k hk
      rcases (hg k hk).lt_or_eq with h | h
      · have := hgP k hk h; simp [hPe] at this
      · exact h.symm
    rw [Finset.sum_eq_zero h0]
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hW i hi) (hf i hi))
  | succ N ih =>
    intro g f hg hf hgf P hP hPpos hgP hfP
    rcases P.eq_empty_or_nonempty with hPe | hPne
    · have h0 : ∀ k ∈ s, g k = 0 := by
        intro k hk
        rcases (hg k hk).lt_or_eq with h | h
        · have := hgP k hk h; simp [hPe] at this
        · exact h.symm
      rw [Finset.sum_eq_zero h0]
      exact Finset.sum_nonneg (fun i hi => mul_nonneg (hW i hi) (hf i hi))
    set m := P.min' hPne with hm
    have hmP : m ∈ P := P.min'_mem hPne
    have hmpos : 0 < m := hPpos m hmP
    have hgm : ∀ k ∈ s, 0 < g k → m ≤ g k := fun k hk h => P.min'_le _ (hgP k hk h)
    have hfm : ∀ i ∈ s', 0 < f i → m ≤ f i := fun i hi h => P.min'_le _ (hfP i hi h)
    set g' : κ → ℝ := fun k => if 0 < g k then g k - m else 0 with hg'
    set f' : ι → ℝ := fun i => if 0 < f i then f i - m else 0 with hf'
    -- decompositions
    have hgdec : ∑ k ∈ s, g k = ∑ k ∈ s, g' k + m * (s.filter (fun k => 0 < g k)).card := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [g']
      split_ifs with h
      · push_cast; ring
      · push_cast; have := hg k hk; linarith [le_antisymm (not_lt.mp h) this]
    have hfdec : ∑ i ∈ s', W i * f i =
        ∑ i ∈ s', W i * f' i + m * ∑ i ∈ s'.filter (fun i => 0 < f i), W i := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [f']
      split_ifs with h
      · ring
      · have := hf i hi; have := le_antisymm (not_lt.mp h) this; rw [this]; ring
    have hzero := hgf 0 le_rfl
    -- new hypotheses
    have hg'nn : ∀ k ∈ s, 0 ≤ g' k := by
      intro k hk; simp only [g']; split_ifs with h
      · linarith [hgm k hk h]
      · exact le_rfl
    have hf'nn : ∀ i ∈ s', 0 ≤ f' i := by
      intro i hi; simp only [f']; split_ifs with h
      · linarith [hfm i hi h]
      · exact le_rfl
    have hgf' : ∀ t : ℝ, 0 ≤ t → ((s.filter (fun k => t < g' k)).card : ℝ) ≤
        ∑ i ∈ s'.filter (fun i => t < f' i), W i := by
      intro t ht
      have e1 : s.filter (fun k => t < g' k) = s.filter (fun k => t + m < g k) := by
        apply Finset.filter_congr
        intro k hk
        simp only [g']
        split_ifs with h
        · constructor <;> intro h' <;> linarith
        · constructor
          · intro h'; linarith
          · intro h'; linarith [hg k hk, not_lt.mp h]
      have e2 : s'.filter (fun i => t < f' i) = s'.filter (fun i => t + m < f i) := by
        apply Finset.filter_congr
        intro i hi
        simp only [f']
        split_ifs with h
        · constructor <;> intro h' <;> linarith
        · constructor
          · intro h'; linarith
          · intro h'; linarith [hf i hi, not_lt.mp h]
      rw [e1, e2]
      exact hgf (t + m) (by linarith)
    have key := ih g' f' hg'nn hf'nn hgf' ((P.erase m).image (fun x => x - m))
      (by
        calc ((P.erase m).image (fun x => x - m)).card ≤ (P.erase m).card := Finset.card_image_le
          _ = P.card - 1 := Finset.card_erase_of_mem hmP
          _ ≤ N := by omega)
      (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        have hy1 := Finset.ne_of_mem_erase hy
        have hy2 := P.min'_le y (Finset.mem_of_mem_erase hy)
        have : m < y := lt_of_le_of_ne hy2 (Ne.symm hy1)
        linarith)
      (by
        intro k hk hpos
        simp only [g'] at hpos ⊢
        split_ifs with h
        · rw [if_pos h] at hpos
          refine Finset.mem_image.mpr ⟨g k, Finset.mem_erase.mpr ⟨?_, hgP k hk h⟩, rfl⟩
          intro he; rw [he] at hpos; simp at hpos
        · rw [if_neg h] at hpos; exact absurd hpos (lt_irrefl 0))
      (by
        intro i hi hpos
        simp only [f'] at hpos ⊢
        split_ifs with h
        · rw [if_pos h] at hpos
          refine Finset.mem_image.mpr ⟨f i, Finset.mem_erase.mpr ⟨?_, hfP i hi h⟩, rfl⟩
          intro he; rw [he] at hpos; simp at hpos
        · rw [if_neg h] at hpos; exact absurd hpos (lt_irrefl 0))
    rw [hgdec, hfdec]
    have := mul_le_mul_of_nonneg_left hzero hmpos.le
    linarith

lemma layer_cake {κ ι : Type*} (s : Finset κ) (s' : Finset ι) (W : ι → ℝ)
    (hW : ∀ i ∈ s', 0 ≤ W i) (g : κ → ℝ) (f : ι → ℝ) (hg : ∀ k ∈ s, 0 ≤ g k)
    (hf : ∀ i ∈ s', 0 ≤ f i)
    (hgf : ∀ t : ℝ, 0 ≤ t → ((s.filter (fun k => t < g k)).card : ℝ) ≤
          ∑ i ∈ s'.filter (fun i => t < f i), W i) :
    ∑ k ∈ s, g k ≤ ∑ i ∈ s', W i * f i := by
  classical
  let P : Finset ℝ := ((s.image g) ∪ (s'.image f)).filter (fun x => 0 < x)
  refine layer_cake_aux s s' W hW P.card g f hg hf hgf P le_rfl ?_ ?_ ?_
  · intro x hx; exact (Finset.mem_filter.mp hx).2
  · intro k hk h
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem g hk), h⟩
  · intro i hi h
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem f hi), h⟩

lemma cut_partition {n : ℕ} (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) (ℓ : Fin n → ℕ)
    (h2 : 2 ≤ ((Finset.univ : Finset (Fin n)).image ℓ).card) :
    (2 * ((Finset.univ : Finset (Fin n)).image ℓ).card : ℝ) ≤
      ∑ u, ∑ w, (if ℓ u ≠ ℓ w then x u w else 0) := by
  obtain ⟨-, -, -, -, -, hcut⟩ := hx
  set I := (Finset.univ : Finset (Fin n)).image ℓ with hI
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := I) (g := ℓ)
    (fun u _ => Finset.mem_image_of_mem ℓ (Finset.mem_univ u))]
  rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro j hj
  set S := (Finset.univ : Finset (Fin n)).filter (fun u => ℓ u = j) with hS
  have hSne : S.Nonempty := by
    obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hj
    exact ⟨u, by simp [S, hu]⟩
  have hSuniv : S ≠ Finset.univ := by
    obtain ⟨j', hj', hne⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) j
    obtain ⟨u', -, hu'⟩ := Finset.mem_image.mp hj'
    intro hE
    have : u' ∈ S := by rw [hE]; exact Finset.mem_univ _
    simp [S] at this
    exact hne (hu'.symm.trans this)
  have := hcut S hSne hSuniv
  refine this.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : ℓ u = j := by simpa [S] using hu
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext w; simp [S, hu', eq_comm]
  · intros; rfl


lemma sum_d_le {n : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) (v : ℕ → Fin n) (p : ℕ → ℕ)
    (hP : PrimInv c n v p) :
    ∑ m ∈ Finset.Ico 1 n, c (v (p m)) (v m) ≤
      ∑ q : Fin n × Fin n, ((1 / 2) * (1 - 1 / (n : ℝ)) * x q.1 q.2) * c q.1 q.2 := by
  obtain ⟨hsymm, hdiag, htri⟩ := hc
  have hcnn : ∀ u w, 0 ≤ c u w := by
    intro u w; have := htri u w u; rw [hdiag, hsymm w u] at this; linarith
  have hxnn := hx.2.2.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; exact_mod_cast hn
    linarith
  obtain ⟨hinj, hprim⟩ := hP
  apply layer_cake (Finset.Ico 1 n) Finset.univ
  · intro q _; exact mul_nonneg (mul_nonneg (by norm_num) hfac) (hxnn _ _)
  · intro k _; exact hcnn _ _
  · intro q _; exact hcnn _ _
  intro t ht
  set g : ℕ → ℝ := fun m => c (v (p m)) (v m) with hg
  set K := (Finset.Ico 1 n).filter (fun k => t < g k) with hK
  -- rewrite RHS
  have hR : ∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => t < c q.1 q.2),
      (1 / 2) * (1 - 1 / (n : ℝ)) * x q.1 q.2 =
      (1 / 2) * (1 - 1 / (n : ℝ)) * ∑ u, ∑ w, (if t < c u w then x u w else 0) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro w _
    split_ifs <;> simp
  rw [hR]
  have hXnn : 0 ≤ ∑ u, ∑ w, (if t < c u w then x u w else 0) := by
    apply Finset.sum_nonneg; intro u _; apply Finset.sum_nonneg; intro w _
    split_ifs
    · exact hxnn _ _
    · exact le_rfl
  rcases Nat.eq_zero_or_pos K.card with hr | hr
  · rw [hr]; push_cast
    exact mul_nonneg (mul_nonneg (by norm_num) hfac) hXnn
  -- the partition
  set ℓ : Fin n → ℕ := fun w => (K.filter (fun k => ∀ i < k, v i ≠ w)).card with hℓdef
  have hKmem : ∀ k ∈ K, 1 ≤ k ∧ k < n ∧ t < g k := by
    intro k hk
    simp only [hK, Finset.mem_filter, Finset.mem_Ico] at hk
    exact ⟨hk.1.1, hk.1.2, hk.2⟩
  have hℓ : ∀ u w, c u w ≤ t → ℓ u = ℓ w := by
    intro u w huw
    simp only [hℓdef]
    congr 1
    apply Finset.filter_congr
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := hKmem k hk
    have hPk := (hprim k hk1 hk2).2
    constructor
    · intro hu i hi hiw
      have := hPk i hi u hu
      rw [hiw, hsymm w u] at this
      simp only [hg] at hk3
      linarith
    · intro hw i hi hiu
      have := hPk i hi w hw
      rw [hiu] at this
      simp only [hg] at hk3
      linarith
  have hℓv : ∀ k < n, ℓ (v k) = (K.filter (fun k' => k' ≤ k)).card := by
    intro k hk
    simp only [hℓdef]
    congr 1
    apply Finset.filter_congr
    intro k' hk'
    obtain ⟨_, hk'2, _⟩ := hKmem k' hk'
    constructor
    · intro h
      by_contra hlt
      exact h k (by omega) rfl
    · intro h i hi heq
      have := hinj i k (by omega) hk heq
      omega
  have hmono : ∀ a b, a < b → b ∈ K → ℓ (v a) < ℓ (v b) := by
    intro a b hab hb
    obtain ⟨_, hb2, _⟩ := hKmem b hb
    rw [hℓv a (by omega), hℓv b hb2]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_filter]; exact ⟨hb, le_rfl⟩
      · simp only [Finset.mem_filter, not_and, not_le]; intro _; exact hab
    · intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, by omega⟩
  have h0K : (0 : ℕ) ∉ K := by
    intro h; have := (hKmem 0 h).1; omega
  have hinjOn : Set.InjOn (fun k => ℓ (v k)) ↑(insert 0 K) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hbK : b ∈ K := hb.resolve_left (by omega)
      have := hmono a b hlt hbK; omega
    · have haK : a ∈ K := ha.resolve_left (by omega)
      have := hmono b a hlt haK; omega
  have himg : K.card + 1 ≤ ((Finset.univ : Finset (Fin n)).image ℓ).card := by
    have h1 := Finset.card_image_of_injOn hinjOn
    rw [Finset.card_insert_of_notMem h0K] at h1
    rw [← h1]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem ℓ (Finset.mem_univ _)
  have hcut := cut_partition x hx ℓ (by omega)
  have hcmp : ∑ u, ∑ w, (if ℓ u ≠ ℓ w then x u w else 0) ≤
      ∑ u, ∑ w, (if t < c u w then x u w else 0) := by
    apply Finset.sum_le_sum; intro u _; apply Finset.sum_le_sum; intro w _
    by_cases h1 : ℓ u ≠ ℓ w
    · have h2 : t < c u w := by
        by_contra h3; exact h1 (hℓ u w (not_lt.mp h3))
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
      split_ifs
      · exact hxnn _ _
      · exact le_rfl
  have hrn : K.card + 1 ≤ n := by
    have hsub : K ⊆ Finset.Ico 1 n := Finset.filter_subset _ _
    have := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at this
    omega
  have hX : 2 * ((K.card : ℝ) + 1) ≤ ∑ u, ∑ w, (if t < c u w then x u w else 0) := by
    have : ((K.card : ℝ) + 1) ≤ (((Finset.univ : Finset (Fin n)).image ℓ).card : ℝ) := by
      exact_mod_cast himg
    linarith
  have hkey : (K.card : ℝ) ≤ (1 - 1 / (n : ℝ)) * ((K.card : ℝ) + 1) := by
    have h1 : ((K.card : ℝ) + 1) / n ≤ 1 := by
      rw [div_le_one hnpos]; exact_mod_cast hrn
    have : (1 - 1 / (n : ℝ)) * ((K.card : ℝ) + 1) = ((K.card : ℝ) + 1) - ((K.card : ℝ) + 1) / n := by
      ring
    rw [this]; linarith
  calc (K.card : ℝ) ≤ (1 - 1 / (n : ℝ)) * ((K.card : ℝ) + 1) := hkey
    _ = (1 / 2) * (1 - 1 / (n : ℝ)) * (2 * ((K.card : ℝ) + 1)) := by ring
    _ ≤ (1 / 2) * (1 - 1 / (n : ℝ)) * ∑ u, ∑ w, (if t < c u w then x u w else 0) :=
      mul_le_mul_of_nonneg_left hX (mul_nonneg (by norm_num) hfac)


lemma hk_nonempty {n : ℕ} (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ) :
    {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}.Nonempty := by
  have hn1 : (2 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  set a : ℝ := 2 / ((n : ℝ) - 1) with ha
  have ha0 : 0 ≤ a := by positivity
  let x : Fin n → Fin n → ℝ := fun u v => if u = v then 0 else a
  refine ⟨_, x, ?_, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    by_cases h : u = v
    · simp [x, h]
    · simp [x, h, Ne.symm h]
  · intro v; simp [x]
  · intro u v; simp only [x]; split_ifs
    · exact le_rfl
    · exact ha0
  · intro u v; simp only [x]; split_ifs
    · norm_num
    · rw [ha, div_le_one hpos]; linarith
  · intro v
    simp only [x]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.univ : Finset (Fin n)).filter (fun u => ¬ v = u)).card = n - 1 := by
      have e : (Finset.univ : Finset (Fin n)).filter (fun u => ¬ v = u) =
          (Finset.univ : Finset (Fin n)).erase v := by
        rw [← Finset.filter_ne]
      rw [e, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    rw [this, Nat.cast_sub (by omega), ha]
    push_cast
    field_simp
  · intro S hS hSu
    have hinner : ∀ u ∈ S, ∑ v ∈ Sᶜ, x u v = Sᶜ.card * a := by
      intro u hu
      rw [Finset.sum_congr rfl (g := fun _ => a), Finset.sum_const, nsmul_eq_mul]
      intro v hv
      have : u ≠ v := by
        intro h; rw [h] at hu; exact (Finset.mem_compl.mp hv) hu
      simp [x, this]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
    have hK1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    have hlt : S.card < n := by
      have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hSu)
      simpa using this
    have hsum : S.card + Sᶜ.card = n := by
      rw [Finset.card_add_card_compl, Fintype.card_fin]
    have hM1 : (1 : ℝ) ≤ Sᶜ.card := by
      have : 1 ≤ Sᶜ.card := by omega
      exact_mod_cast this
    have hsumR : (S.card : ℝ) + Sᶜ.card = n := by exact_mod_cast hsum
    have hKM : (n : ℝ) - 1 ≤ (S.card : ℝ) * Sᶜ.card := by nlinarith
    calc (2 : ℝ) = ((n : ℝ) - 1) * a := by rw [ha]; field_simp
      _ ≤ (S.card : ℝ) * Sᶜ.card * a := mul_le_mul_of_nonneg_right hKM ha0
      _ = (S.card : ℝ) * (Sᶜ.card * a) := by ring


end Prim

/-! ### The Prim tree as a multigraph, and the final bound -/

section Final
variable {n : ℕ}

/-- multiplicity matrix of the Prim tree -/
def treeM (v : ℕ → Fin n) (p : ℕ → ℕ) (u w : Fin n) : ℕ :=
  ((Finset.Ico 1 n).filter (fun k => (v k = u ∧ v (p k) = w) ∨ (v k = w ∧ v (p k) = u))).card

lemma treeM_symm (v : ℕ → Fin n) (p : ℕ → ℕ) (u w : Fin n) : treeM v p u w = treeM v p w u := by
  unfold treeM
  congr 1
  apply Finset.filter_congr
  intro k _
  exact or_comm

lemma treeM_diag (v : ℕ → Fin n) (p : ℕ → ℕ)
    (hinj : ∀ i j, i < n → j < n → v i = v j → i = j)
    (hp : ∀ k, 1 ≤ k → k < n → p k < k) (u : Fin n) : treeM v p u u = 0 := by
  unfold treeM
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk h
  rw [Finset.mem_Ico] at hk
  have hpk := hp k hk.1 hk.2
  have : v k = v (p k) := by
    rcases h with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2]
  have := hinj k (p k) hk.2 (by omega) this
  omega

lemma treeM_cost (v : ℕ → Fin n) (p : ℕ → ℕ)
    (hinj : ∀ i j, i < n → j < n → v i = v j → i = j)
    (hp : ∀ k, 1 ≤ k → k < n → p k < k) (c : Fin n → Fin n → ℝ) :
    ∑ u, ∑ w, c u w * (treeM v p u w : ℝ) =
      ∑ k ∈ Finset.Ico 1 n, (c (v k) (v (p k)) + c (v (p k)) (v k)) := by
  have e1 : ∀ u w, c u w * (treeM v p u w : ℝ) = ∑ k ∈ Finset.Ico 1 n,
      ((if v k = u ∧ v (p k) = w then c u w else 0) + (if v k = w ∧ v (p k) = u then c u w else 0)) := by
    intro u w
    unfold treeM
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mem_Ico] at hk
    have hne : v k ≠ v (p k) := by
      intro h
      have := hinj k (p k) hk.2 (by have := hp k hk.1 hk.2; omega) h
      have := hp k hk.1 hk.2; omega
    push_cast
    by_cases h1 : v k = u ∧ v (p k) = w
    · have h2 : ¬ (v k = w ∧ v (p k) = u) := by
        intro h2; apply hne; rw [h1.1, h2.2]
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]; ring
    · by_cases h2 : v k = w ∧ v (p k) = u
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]; ring
      · rw [if_neg (by tauto), if_neg h1, if_neg h2]; ring
  simp_rw [e1]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm), Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun u _ => sum_ite_and_left (v k = u) (v (p k)) (c u))]
  rw [Finset.sum_congr rfl (fun u _ => sum_ite_and_right (v (p k) = u) (v k) (c u))]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp

lemma treeM_conn (v : ℕ → Fin n) (p : ℕ → ℕ)
    (hinj : ∀ i j, i < n → j < n → v i = v j → i = j)
    (hp : ∀ k, 1 ≤ k → k < n → p k < k)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSu : S ≠ Finset.univ) :
    ∃ a ∈ S, ∃ b ∉ S, 0 < treeM v p a b := by
  have hsurj : ∀ y : Fin n, ∃ k < n, v k = y := by
    have himg : (Finset.range n).image v = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn, Finset.card_range, Fintype.card_fin]
      intro i hi j hj h
      exact hinj i j (by simpa using hi) (by simpa using hj) h
    intro y
    have : y ∈ (Finset.range n).image v := by rw [himg]; exact Finset.mem_univ y
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp this
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  have hmem : ∀ k, 1 ≤ k → k < n → ∀ a b,
      ((v k = a ∧ v (p k) = b) ∨ (v k = b ∧ v (p k) = a)) → 0 < treeM v p a b := by
    intro k h1 h2 a b h
    unfold treeM
    apply Finset.card_pos.mpr
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h1, h2⟩, h⟩⟩
  by_cases h0 : v 0 ∈ S
  · have hex : ∃ k, k < n ∧ v k ∉ S := by
      obtain ⟨y, hy⟩ : ∃ y, y ∉ S := by
        by_contra h; push Not at h; exact hSu (Finset.eq_univ_iff_forall.mpr h)
      obtain ⟨k, hk, rfl⟩ := hsurj y
      exact ⟨k, hk, hy⟩
    have hk0 := Nat.find_spec hex
    have hk0pos : 1 ≤ Nat.find hex := by
      by_contra h
      have h' : Nat.find hex = 0 := by omega
      rw [h'] at hk0; exact hk0.2 h0
    have hpk := hp _ hk0pos hk0.1
    have hin : v (p (Nat.find hex)) ∈ S := by
      by_contra h
      exact Nat.find_min hex hpk ⟨by omega, h⟩
    exact ⟨_, hin, _, hk0.2, hmem _ hk0pos hk0.1 _ _ (Or.inr ⟨rfl, rfl⟩)⟩
  · have hex : ∃ k, k < n ∧ v k ∈ S := by
      obtain ⟨y, hy⟩ := hS
      obtain ⟨k, hk, rfl⟩ := hsurj y
      exact ⟨k, hk, hy⟩
    have hk0 := Nat.find_spec hex
    have hk0pos : 1 ≤ Nat.find hex := by
      by_contra h
      have h' : Nat.find hex = 0 := by omega
      rw [h'] at hk0; exact h0 hk0.2
    have hpk := hp _ hk0pos hk0.1
    have hin : v (p (Nat.find hex)) ∉ S := by
      intro h
      exact Nat.find_min hex hpk ⟨by omega, h⟩
    exact ⟨_, hk0.2, _, hin, hmem _ hk0pos hk0.1 _ _ (Or.inl ⟨rfl, rfl⟩)⟩

lemma sum_mod_two_eq_card {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) % 2 = (s.filter (fun i => f i % 2 = 1)).card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp [ha])]; omega
    · omega

theorem tsp_le_LP (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    tspOpt c ≤ 3 / 4 * ∑ u, ∑ w, c u w * x u w := by
  have hcs := hc.1
  have hcnn : ∀ u w, 0 ≤ c u w := by
    intro u w; have := hc.2.2 u w u; rw [hc.2.1, hc.1 w u] at this; linarith
  obtain ⟨v, p, hP⟩ := prim_exists c n (by omega) le_rfl
  have hinj := hP.1
  have hp : ∀ k, 1 ≤ k → k < n → p k < k := fun k h1 h2 => (hP.2 k h1 h2).1
  set T := Finset.univ.filter (fun u => (∑ w, treeM v p u w) % 2 = 1) with hT
  have htot : ∑ u, ∑ w, treeM v p u w = 2 * (n - 1) := by
    have h := treeM_cost v p hinj hp (fun _ _ => (1 : ℝ))
    simp only [one_mul, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h
    have h' : ((∑ u, ∑ w, treeM v p u w : ℕ) : ℝ) = ((2 * (n - 1) : ℕ) : ℝ) := by
      push_cast
      rw [h, Nat.cast_sub (by omega)]
      push_cast; ring
    exact_mod_cast h'
  have hTeven : Even T.card := by
    have h := sum_mod_two_eq_card Finset.univ (fun u => ∑ w, treeM v p u w)
    rw [htot] at h
    rw [Nat.even_iff]
    simp only [hT]
    omega
  obtain ⟨J, hJs, hJd, hJdeg, hJc⟩ := tjoin_exists (by omega) c hc x hx T hTeven
  set H : Fin n → Fin n → ℕ := fun u w => treeM v p u w + J u w with hH
  have hHs : ∀ u w, H u w = H w u := by
    intro u w; simp only [hH]; rw [treeM_symm, hJs]
  have hHd : ∀ u, H u u = 0 := by
    intro u; simp only [hH]; rw [treeM_diag v p hinj hp, hJd]
  have hHeven : ∀ u, Even (∑ w, H u w) := by
    intro u
    simp only [hH, Finset.sum_add_distrib]
    rw [Nat.even_iff]
    have h1 := hJdeg u
    by_cases huT : u ∈ T
    · rw [if_pos huT] at h1
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at huT
      omega
    · rw [if_neg huT] at h1
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at huT
      omega
  have hHconn : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
      ∃ u ∈ S, ∃ w ∉ S, 0 < H u w := by
    intro S hS hSu
    obtain ⟨a, ha, b, hb, hab⟩ := treeM_conn v p hinj hp S hS hSu
    exact ⟨a, ha, b, hb, by simp only [hH]; omega⟩
  have htour := tour_le_multigraph (by omega) c hc H hHs hHd hHeven hHconn
  have hsplit : ∑ u, ∑ w, c u w * (H u w : ℝ) =
      ∑ u, ∑ w, c u w * (treeM v p u w : ℝ) + ∑ u, ∑ w, c u w * (J u w : ℝ) := by
    simp only [hH, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  rw [treeM_cost v p hinj hp c] at hsplit
  have hsym2 : ∑ k ∈ Finset.Ico 1 n, (c (v k) (v (p k)) + c (v (p k)) (v k)) =
      2 * ∑ k ∈ Finset.Ico 1 n, c (v (p k)) (v k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [hcs (v k) (v (p k))]; ring
  have hd := sum_d_le (by omega) c hc x hx v p hP
  have hR : ∑ q : Fin n × Fin n, ((1 / 2) * (1 - 1 / (n : ℝ)) * x q.1 q.2) * c q.1 q.2 =
      (1 / 2) * ((1 - 1 / (n : ℝ)) * ∑ u, ∑ w, c u w * x u w) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro w _
    ring
  rw [hR] at hd
  have hS0 : 0 ≤ ∑ u, ∑ w, c u w * x u w :=
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun w _ => mul_nonneg (hcnn u w) (hx.2.2.1 u w)))
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfac : 0 ≤ 1 / (n : ℝ) := by positivity
  have h1 : (1 - 1 / (n : ℝ)) * ∑ u, ∑ w, c u w * x u w ≤ ∑ u, ∑ w, c u w * x u w := by
    nlinarith
  rw [hsplit, hsym2] at htour
  linarith

end Final

end MetricTSP.T3

open MetricTSP in
theorem solution (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 3 / 2 * hkValue c := by
  have hK : (0 : ℝ) < 3 / 2 := by norm_num
  have hle : tspOpt c / (3 / 2) ≤ hkValue c := by
    unfold hkValue
    apply le_csInf (MetricTSP.T3.hk_nonempty hn c)
    rintro t ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hK]
    have := MetricTSP.T3.tsp_le_LP hn c hc x hx
    linarith
  rw [div_le_iff₀ hK] at hle
  linarith
