import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Erdős's 1947 lower bound for diagonal Ramsey numbers

P. Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947), 292–294,
proved that `R(k) > 2^{k/2}` for `k ≥ 3` by counting: among the `2^{C(n,2)}` graphs on `n`
vertices, at most `C(n,k) · 2 · 2^{C(n,2) - C(k,2)}` contain a `k`-set that is a clique or an
independent set, and this is less than `2^{C(n,2)}` as soon as `2 · C(n,k) < 2^{C(k,2)}`, which
holds when `n ≤ 2^{k/2}` and `k ≥ 3`.

We formalize this in a definition-free way: the conclusion is the existence of a graph on
`Fin n` that is `k`-clique-free and whose complement is `k`-clique-free (no independent `k`-set).

Two-colourings are modelled as functions `Sym2 (Fin n) → Bool`; the values on the diagonal
are irrelevant, which lets us avoid identifying the edge set of the complete graph.
-/

namespace Prep

open SimpleGraph Finset

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Functions `α → Bool` that are constantly `c` on `A` correspond to arbitrary functions on
the complement of `A`. -/
def constOnEquiv (A : Finset α) (c : Bool) :
    {f : α → Bool // ∀ a ∈ A, f a = c} ≃ ({a : α // a ∉ A} → Bool) where
  toFun f := fun a => f.1 a.1
  invFun g := ⟨fun a => if h : a ∈ A then c else g ⟨a, h⟩, fun a ha => dif_pos ha⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ A
    · simp only [dif_pos ha]
      exact (f.2 a ha).symm
    · simp only [dif_neg ha]
  right_inv g := by
    funext a
    simp only [dif_neg a.2]

/-- The number of `Bool`-valued functions that are constantly `c` on a set `A` of arguments. -/
theorem card_constOn (A : Finset α) (c : Bool) :
    Fintype.card {f : α → Bool // ∀ a ∈ A, f a = c} = 2 ^ (Fintype.card α - A.card) := by
  rw [Fintype.card_congr (constOnEquiv A c), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_coe]

/-- `Finset.filter` version of `card_constOn`. -/
theorem card_filter_constOn (A : Finset α) (c : Bool) :
    (Finset.univ.filter (fun f : α → Bool => ∀ a ∈ A, f a = c)).card
      = 2 ^ (Fintype.card α - A.card) := by
  rw [← card_constOn A c, Fintype.card_subtype]

end Counting

/-- A two-colouring of the pairs of `Fin n` (values on the diagonal are irrelevant). -/
abbrev Colouring (n : ℕ) := Sym2 (Fin n) → Bool

/-- `S` is monochromatic of colour `c` under `f`. -/
def MonoOn {n : ℕ} (f : Colouring n) (S : Finset (Fin n)) (c : Bool) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f s(x, y) = c

instance {n : ℕ} (S : Finset (Fin n)) (c : Bool) :
    DecidablePred (fun f : Colouring n => MonoOn f S c) := by
  intro f
  unfold MonoOn
  infer_instance

/-- The unordered pairs of distinct elements of `S`. -/
def pairs {n : ℕ} (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  S.offDiag.image (Function.uncurry Sym2.mk)

theorem card_pairs {n : ℕ} (S : Finset (Fin n)) : (pairs S).card = S.card.choose 2 :=
  Sym2.card_image_offDiag S

theorem monoOn_iff {n : ℕ} (f : Colouring n) (S : Finset (Fin n)) (c : Bool) :
    MonoOn f S c ↔ ∀ e ∈ pairs S, f e = c := by
  constructor
  · intro h e he
    unfold pairs at he
    rw [Finset.mem_image] at he
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := he
    rw [Finset.mem_offDiag] at hxy
    exact h x hxy.1 y hxy.2.1 hxy.2.2
  · intro h x hx y hy hxy
    apply h
    unfold pairs
    rw [Finset.mem_image]
    exact ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩, rfl⟩

/-- Exactly `2 ^ (N - C(|S|, 2))` colourings make `S` monochromatic of colour `c`, where `N` is
the number of unordered pairs (with repetition) of `Fin n`. -/
theorem card_monoOn {n : ℕ} (S : Finset (Fin n)) (c : Bool) :
    (Finset.univ.filter (fun f : Colouring n => MonoOn f S c)).card
      = 2 ^ (Fintype.card (Sym2 (Fin n)) - S.card.choose 2) := by
  have h : (Finset.univ.filter (fun f : Colouring n => MonoOn f S c))
      = Finset.univ.filter (fun f : Colouring n => ∀ e ∈ pairs S, f e = c) :=
    Finset.filter_congr (fun f _ => monoOn_iff f S c)
  rw [h, card_filter_constOn, card_pairs]

/-- The colourings in which some `k`-set is monochromatic. -/
def bad (n k : ℕ) : Finset (Colouring n) :=
  ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion fun S =>
    Finset.univ.filter (fun f => MonoOn f S true) ∪ Finset.univ.filter (fun f => MonoOn f S false)

/-- The union bound. -/
theorem card_bad_le (n k : ℕ) :
    (bad n k).card ≤ n.choose k * (2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2)) := by
  unfold bad
  refine Finset.card_biUnion_le.trans ?_
  have hS : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (Finset.univ.filter (fun f => MonoOn f S true) ∪
        Finset.univ.filter (fun f => MonoOn f S false)).card
        ≤ 2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2) := by
    intro S hS
    have hk : S.card = k := (Finset.mem_powersetCard.1 hS).2
    refine (Finset.card_union_le _ _).trans ?_
    rw [card_monoOn, card_monoOn, hk]
    omega
  refine (Finset.sum_le_sum hS).trans ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Erdős's counting argument.** If `2 · C(n,k) < 2^{C(k,2)}` then some two-colouring of the
pairs of `Fin n` has no monochromatic `k`-set. -/
theorem exists_good_colouring (n k : ℕ) (_hk : 2 ≤ k) (h : 2 * n.choose k < 2 ^ k.choose 2) :
    ∃ f : Colouring n, ∀ S : Finset (Fin n), S.card = k → ∀ c : Bool, ¬ MonoOn f S c := by
  have hcard : (Finset.univ : Finset (Colouring n)).card = 2 ^ Fintype.card (Sym2 (Fin n)) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hlt : (bad n k).card < (Finset.univ : Finset (Colouring n)).card := by
    rw [hcard]
    refine (card_bad_le n k).trans_lt ?_
    by_cases hkn : k ≤ n
    · have hle : k.choose 2 ≤ Fintype.card (Sym2 (Fin n)) := by
        obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), S.card = k := by
          obtain ⟨S, hS⟩ := Finset.powersetCard_nonempty.2
            (show k ≤ (Finset.univ : Finset (Fin n)).card by simpa using hkn)
          exact ⟨S, (Finset.mem_powersetCard.1 hS).2⟩
        rw [← hS, ← card_pairs S]
        exact Finset.card_le_univ _
      calc n.choose k * (2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2))
          = (2 * n.choose k) * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2) := by ring
        _ < 2 ^ k.choose 2 * 2 ^ (Fintype.card (Sym2 (Fin n)) - k.choose 2) :=
            mul_lt_mul_of_pos_right h (by positivity)
        _ = 2 ^ Fintype.card (Sym2 (Fin n)) := by rw [← pow_add, Nat.add_sub_cancel' hle]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp only [zero_mul]
      positivity
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨f, fun S hS c hmono => hf ?_⟩
  rw [bad, Finset.mem_biUnion]
  refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩, ?_⟩
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  cases c
  · exact Or.inr ⟨Finset.mem_univ _, hmono⟩
  · exact Or.inl ⟨Finset.mem_univ _, hmono⟩

/-- The graph whose edges are the `true`-coloured pairs. -/
def graphOf {n : ℕ} (f : Colouring n) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ f s(x, y) = true
  symm := by
    constructor
    intro x y ⟨hxy, hf⟩
    exact ⟨hxy.symm, by rwa [Sym2.eq_swap]⟩
  loopless := by
    constructor
    intro x ⟨hxx, _⟩
    exact hxx rfl

theorem graphOf_adj {n : ℕ} (f : Colouring n) (x y : Fin n) :
    (graphOf f).Adj x y ↔ x ≠ y ∧ f s(x, y) = true := Iff.rfl

theorem graphOf_compl_adj {n : ℕ} (f : Colouring n) (x y : Fin n) :
    (graphOf f)ᶜ.Adj x y ↔ x ≠ y ∧ f s(x, y) = false := by
  rw [compl_adj, graphOf_adj]
  constructor
  · rintro ⟨hxy, h⟩
    refine ⟨hxy, ?_⟩
    cases hf : f s(x, y)
    · rfl
    · exact absurd ⟨hxy, hf⟩ h
  · rintro ⟨hxy, hf⟩
    exact ⟨hxy, fun h => by rw [hf] at h; exact Bool.false_ne_true h.2⟩

theorem monoOn_true_of_isNClique {n k : ℕ} (f : Colouring n) (S : Finset (Fin n))
    (h : (graphOf f).IsNClique k S) : MonoOn f S true := by
  intro x hx y hy hxy
  exact (h.isClique hx hy hxy).2

theorem monoOn_false_of_isNClique_compl {n k : ℕ} (f : Colouring n) (S : Finset (Fin n))
    (h : (graphOf f)ᶜ.IsNClique k S) : MonoOn f S false := by
  intro x hx y hy hxy
  exact ((graphOf_compl_adj f x y).1 (h.isClique hx hy hxy)).2

/-- **Erdős (1947), counting form.** If `2 · C(n,k) < 2^{C(k,2)}` (and `k ≥ 2`) then there is a
graph on `n` vertices with no `k`-clique and no independent set of size `k`. -/
theorem erdos_lower_bound_count (n k : ℕ) (hk : 2 ≤ k) (h : 2 * n.choose k < 2 ^ k.choose 2) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  obtain ⟨f, hf⟩ := exists_good_colouring n k hk h
  refine ⟨graphOf f, ?_, ?_⟩
  · intro S hS
    exact hf S hS.card_eq true (monoOn_true_of_isNClique f S hS)
  · intro S hS
    exact hf S hS.card_eq false (monoOn_false_of_isNClique_compl f S hS)

/-! ### The numerical estimate `2 · C(n,k) < 2^{C(k,2)}` when `n² ≤ 2^k`, `k ≥ 3` -/

theorem four_mul_two_pow_lt_factorial_sq (k : ℕ) (hk : 3 ≤ k) : 4 * 2 ^ k < (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, pow_succ, mul_pow]
    have h1 : 2 ≤ (k + 1) ^ 2 := by nlinarith
    nlinarith [ih, h1, Nat.factorial_pos k]

theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)

theorem two_mul_choose_lt_two_pow_choose_two (k n : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ k.choose 2 := by
  have hfac : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have hsq : (k.factorial) ^ 2 * (2 * n.choose k) ^ 2 ≤ 4 * 2 ^ (k * k) := by
    calc (k.factorial) ^ 2 * (2 * n.choose k) ^ 2 = 4 * (k.factorial * n.choose k) ^ 2 := by ring
      _ ≤ 4 * (n ^ k) ^ 2 := by gcongr
      _ = 4 * (n ^ 2) ^ k := by ring
      _ ≤ 4 * (2 ^ k) ^ k := by gcongr
      _ = 4 * 2 ^ (k * k) := by rw [← pow_mul]
  have hkk : k * k = k * (k - 1) + k := by
    have h1 : 1 ≤ k := by omega
    calc k * k = k * (k - 1 + 1) := by rw [Nat.sub_add_cancel h1]
      _ = k * (k - 1) + k := by ring
  have h4 := four_mul_two_pow_lt_factorial_sq k hk
  have hpos : 0 < 2 ^ (k * (k - 1)) := by positivity
  have hlt : (k.factorial) ^ 2 * (2 * n.choose k) ^ 2 < (k.factorial) ^ 2 * 2 ^ (k * (k - 1)) := by
    calc (k.factorial) ^ 2 * (2 * n.choose k) ^ 2 ≤ 4 * 2 ^ (k * k) := hsq
      _ = (4 * 2 ^ k) * 2 ^ (k * (k - 1)) := by rw [hkk, pow_add]; ring
      _ < (k.factorial) ^ 2 * 2 ^ (k * (k - 1)) := mul_lt_mul_of_pos_right h4 hpos
  have hlt2 : (2 * n.choose k) ^ 2 < 2 ^ (k * (k - 1)) :=
    lt_of_mul_lt_mul_left hlt (by positivity)
  have hlt3 : (2 * n.choose k) ^ 2 < (2 ^ k.choose 2) ^ 2 := by
    rw [← pow_mul, show k.choose 2 * 2 = k * (k - 1) by rw [mul_comm]; exact two_mul_choose_two k]
    exact hlt2
  exact (Nat.pow_lt_pow_iff_left two_ne_zero).1 hlt3

/-! ### Headline statements -/

/-- **Erdős (1947).** For `k ≥ 3` and `n² ≤ 2^k` (i.e. `n ≤ 2^{k/2}`), there is a graph on `n`
vertices with no `k`-clique and no independent `k`-set; hence `R(k) > 2^{k/2}`. -/
theorem erdos_lower_bound (k n : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  erdos_lower_bound_count n k (by omega) (two_mul_choose_lt_two_pow_choose_two k n hk hn)

/-- `n ≤ 2^{k/2}` (as reals) implies `n² ≤ 2^k`. -/
theorem sq_le_two_pow_of_le_two_rpow_half (k n : ℕ) (hn : (n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2)) :
    n ^ 2 ≤ 2 ^ k := by
  have h2 : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
    rw [show ((k : ℝ) / 2 * ((2 : ℕ) : ℝ)) = (k : ℝ) by push_cast; ring]
    exact Real.rpow_natCast 2 k
  have h3 := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
  rw [h2] at h3
  exact_mod_cast h3

/-- Real-exponent form of `erdos_lower_bound`. -/
theorem erdos_lower_bound_real (k n : ℕ) (hk : 3 ≤ k)
    (hn : (n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  erdos_lower_bound k n hk (sq_le_two_pow_of_le_two_rpow_half k n hn)

/-- The concrete vertex count `2 ^ (k / 2)` (natural-number division). -/
theorem erdos_lower_bound_two_pow_half (k : ℕ) (hk : 3 ≤ k) :
    ∃ G : SimpleGraph (Fin (2 ^ (k / 2))), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  apply erdos_lower_bound k _ hk
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The concrete vertex count `⌊2^{k/2}⌋₊`. -/
theorem erdos_lower_bound_floor (k : ℕ) (hk : 3 ≤ k) :
    ∃ G : SimpleGraph (Fin ⌊(2 : ℝ) ^ ((k : ℝ) / 2)⌋₊), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  erdos_lower_bound_real k _ hk (Nat.floor_le (by positivity))

end Prep

#print axioms Prep.card_filter_constOn
#print axioms Prep.card_monoOn
#print axioms Prep.exists_good_colouring
#print axioms Prep.erdos_lower_bound_count
#print axioms Prep.two_mul_choose_lt_two_pow_choose_two
#print axioms Prep.erdos_lower_bound
#print axioms Prep.erdos_lower_bound_real
#print axioms Prep.erdos_lower_bound_two_pow_half
#print axioms Prep.erdos_lower_bound_floor
