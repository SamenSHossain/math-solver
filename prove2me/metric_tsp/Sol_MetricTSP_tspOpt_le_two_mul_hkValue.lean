import Mathlib
import Definitions.Def_MetricTSP_model

set_option autoImplicit false

namespace MetricTSP.T2
open MetricTSP Finset

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

lemma cyc_insert {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (u v : Fin n) (L : List (Fin n)) :
    cyc c (u :: v :: L) ≤ cyc c (u :: L) + 2 * c u v := by
  obtain ⟨hsymm, hdiag, htri⟩ := hc
  cases L with
  | nil =>
    simp [cyc, walk]
    rw [hsymm v u, hdiag u]; linarith [htri u v u]
  | cons w L =>
    simp only [cyc, List.cons_append, walk]
    have h1 := htri v u w
    rw [hsymm v u] at h1
    linarith

lemma walk_ofFn {α : Type*} (c : α → α → ℝ) :
    ∀ (m : ℕ) (f : Fin (m + 1) → α),
      walk c (f 0) (List.ofFn fun i : Fin m => f i.succ) = ∑ i : Fin m, c (f i.castSucc) (f i.succ)
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

lemma tour_build {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (v : ℕ → Fin n)
    (p : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k) (hp : ∀ m, 1 ≤ m → m < k → p m < m) :
    ∃ T : List (Fin n), T.Perm ((List.range k).map v) ∧
      cyc c T ≤ 2 * ∑ m ∈ Finset.Ico 1 k, c (v (p m)) (v m) := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨[v 0], by simp, ?_⟩
    simp [cyc, walk, hc.2.1]
  | succ k hk ih =>
    obtain ⟨T, hTperm, hTcost⟩ := ih (fun m h1 h2 => hp m h1 (by omega))
    have hu : v (p k) ∈ T :=
      hTperm.mem_iff.mpr (List.mem_map.mpr ⟨p k, List.mem_range.mpr (hp k hk (by omega)), rfl⟩)
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hu
    refine ⟨v (p k) :: v k :: (B ++ A), ?_, ?_⟩
    · rw [List.range_succ, List.map_append]
      have h1 : (v (p k) :: v k :: (B ++ A)).Perm (v k :: (A ++ v (p k) :: B)) := by
        refine (List.Perm.swap _ _ _).trans ?_
        refine List.Perm.cons _ ?_
        have : v (p k) :: (B ++ A) = (v (p k) :: B) ++ A := rfl
        rw [this]
        exact List.perm_append_comm
      refine h1.trans ?_
      refine (List.perm_append_singleton _ _).symm.trans ?_
      simpa using hTperm.append_right [v k]
    · have h1 := cyc_insert c hc (v (p k)) (v k) (B ++ A)
      have h2 : cyc c (v (p k) :: (B ++ A)) = cyc c (A ++ v (p k) :: B) := by
        have : v (p k) :: (B ++ A) = (v (p k) :: B) ++ A := rfl
        rw [this, cyc_append_comm]
      rw [Finset.sum_Ico_succ_top hk]
      linarith

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


lemma tspOpt_le_tourCost {n : ℕ} (c : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    tspOpt c ≤ tourCost c π := by
  unfold tspOpt
  apply csInf_le
  · refine ((Set.finite_range (tourCost c)).subset ?_).bddBelow
    rintro t ⟨σ, rfl⟩
    exact ⟨σ, rfl⟩
  · exact ⟨π, rfl⟩

lemma tspOpt_le_LP {n : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    tspOpt c ≤ (1 - 1 / (n : ℝ)) * ∑ u, ∑ w, c u w * x u w := by
  obtain ⟨v, p, hP⟩ := prim_exists c n hn le_rfl
  obtain ⟨T, hTperm, hTcost⟩ := tour_build c hc v p n hn (fun m h1 h2 => (hP.2 m h1 h2).1)
  have hnd : ((List.range n).map v).Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj h
    exact hP.1 i j (List.mem_range.mp hi) (List.mem_range.mp hj) h
  have hTnd : T.Nodup := hTperm.nodup_iff.mpr hnd
  have hTlen : T.length = n := by rw [hTperm.length_eq]; simp
  obtain ⟨π, hπ⟩ := exists_perm_of_list c T hTnd hTlen hn
  have hsum := sum_d_le hn c hc x hx v p hP
  have hR : ∑ q : Fin n × Fin n, ((1 / 2) * (1 - 1 / (n : ℝ)) * x q.1 q.2) * c q.1 q.2 =
      (1 / 2) * ((1 - 1 / (n : ℝ)) * ∑ u, ∑ w, c u w * x u w) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro w _
    ring
  have h1 := tspOpt_le_tourCost c π
  rw [hπ] at h1
  rw [hR] at hsum
  linarith

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

end MetricTSP.T2

open MetricTSP in
theorem solution (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 2 * (1 - 1 / (n : ℝ)) * hkValue c := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : 0 < 2 * (1 - 1 / (n : ℝ)) := by
    have : 1 / (n : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hle : tspOpt c / (2 * (1 - 1 / (n : ℝ))) ≤ hkValue c := by
    unfold hkValue
    apply le_csInf (MetricTSP.T2.hk_nonempty hn c)
    rintro t ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hK]
    have := MetricTSP.T2.tspOpt_le_LP (by omega) c hc x hx
    linarith
  rw [div_le_iff₀ hK] at hle
  linarith
