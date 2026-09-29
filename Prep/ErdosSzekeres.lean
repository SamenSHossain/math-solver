import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Erdős–Szekeres upper bound for two-colour Ramsey numbers

We formalize the classical Erdős–Szekeres (1935) bound in a definition-free way using
Mathlib's `SimpleGraph`: on any vertex set `A` with at least `(s + t).choose s` elements,
a graph `G` contains an `(s+1)`-clique inside `A` or its complement `Gᶜ` contains a
`(t+1)`-clique inside `A` (an independent set of `G`).

Consequences: the diagonal bound `R(k+1, k+1) ≤ (2k).choose k ≤ 4^k`.
-/

namespace Prep

open SimpleGraph Finset

/-- **Erdős–Szekeres, relative form.** In any graph `G`, a finite set `A` of vertices with
`(s + t).choose s ≤ A.card` contains an `(s+1)`-clique of `G` or an `(t+1)`-clique of `Gᶜ`. -/
theorem erdos_szekeres_on {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (s t : ℕ) (A : Finset V), (s + t).choose s ≤ A.card →
      (∃ S : Finset V, S ⊆ A ∧ G.IsNClique (s + 1) S) ∨
        (∃ T : Finset V, T ⊆ A ∧ Gᶜ.IsNClique (t + 1) T) := by
  intro s
  induction s with
  | zero =>
    intro t A hA
    rw [Nat.zero_add, Nat.choose_zero_right] at hA
    obtain ⟨v, hv⟩ : A.Nonempty := Finset.one_le_card.mp hA
    exact Or.inl ⟨{v}, Finset.singleton_subset_iff.mpr hv, isNClique_singleton.mpr rfl⟩
  | succ s ihs =>
    intro t
    induction t with
    | zero =>
      intro A hA
      rw [Nat.add_zero, Nat.choose_self] at hA
      obtain ⟨v, hv⟩ : A.Nonempty := Finset.one_le_card.mp hA
      exact Or.inr ⟨{v}, Finset.singleton_subset_iff.mpr hv, isNClique_singleton.mpr rfl⟩
    | succ t iht =>
      intro A hA
      have hpos : 0 < A.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hA
      obtain ⟨v, hv⟩ : A.Nonempty := Finset.card_pos.mp hpos
      -- neighbours and non-neighbours of `v` inside `A` (excluding `v` itself)
      obtain ⟨N, hN⟩ : ∃ N : Finset V, N = (A.erase v).filter (fun w => G.Adj v w) := ⟨_, rfl⟩
      obtain ⟨M, hM⟩ : ∃ M : Finset V, M = (A.erase v).filter (fun w => ¬ G.Adj v w) := ⟨_, rfl⟩
      have hNM : N.card + M.card = A.card - 1 := by
        rw [hN, hM, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
      have hsplit : (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) ≤ A.card := by
        have h1 : (s + 1 + (t + 1)).choose (s + 1)
            = (s + (t + 1)).choose s + (s + (t + 1)).choose (s + 1) := by
          rw [show s + 1 + (t + 1) = (s + (t + 1)) + 1 by omega]
          exact Nat.choose_succ_succ' _ _
        rw [show s + 1 + t = s + (t + 1) by omega]
        omega
      have hNsub : N ⊆ A := by
        rw [hN]; exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hMsub : M ⊆ A := by
        rw [hM]; exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      rcases le_or_gt ((s + (t + 1)).choose s) N.card with hle | hlt
      · -- many neighbours: use the induction hypothesis for `(s, t + 1)` on `N`
        rcases ihs (t + 1) N hle with ⟨S, hSN, hS⟩ | ⟨T, hTN, hT⟩
        · left
          refine ⟨insert v S, Finset.insert_subset hv (hSN.trans hNsub), ?_⟩
          apply hS.insert
          intro b hb
          have hbN := hSN hb
          rw [hN, Finset.mem_filter] at hbN
          exact hbN.2
        · exact Or.inr ⟨T, hTN.trans hNsub, hT⟩
      · -- many non-neighbours: use the induction hypothesis for `(s + 1, t)` on `M`
        have hle' : (s + 1 + t).choose (s + 1) ≤ M.card := by omega
        rcases iht M hle' with ⟨S, hSM, hS⟩ | ⟨T, hTM, hT⟩
        · exact Or.inl ⟨S, hSM.trans hMsub, hS⟩
        · right
          refine ⟨insert v T, Finset.insert_subset hv (hTM.trans hMsub), ?_⟩
          apply hT.insert
          intro b hb
          have hbM := hTM hb
          rw [hM, Finset.mem_filter, Finset.mem_erase] at hbM
          rw [compl_adj]
          exact ⟨fun h => hbM.1.1 h.symm, hbM.2⟩

/-- **Erdős–Szekeres.** A graph on at least `(s + t).choose s` vertices contains an
`(s+1)`-clique or an independent set of size `t+1` (a `(t+1)`-clique of `Gᶜ`). -/
theorem erdos_szekeres {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s t : ℕ) (h : (s + t).choose s ≤ Fintype.card V) :
    (∃ S : Finset V, G.IsNClique (s + 1) S) ∨ (∃ T : Finset V, Gᶜ.IsNClique (t + 1) T) := by
  have h' : (s + t).choose s ≤ (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]; exact h
  rcases erdos_szekeres_on G s t Finset.univ h' with ⟨S, -, hS⟩ | ⟨T, -, hT⟩
  · exact Or.inl ⟨S, hS⟩
  · exact Or.inr ⟨T, hT⟩

/-- Contrapositive form: no graph on `≥ (s + t).choose s` vertices is simultaneously
`(s+1)`-clique-free and `(t+1)`-independent-set-free. -/
theorem erdos_szekeres_cliqueFree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s t : ℕ) (h : (s + t).choose s ≤ Fintype.card V) :
    ¬ (G.CliqueFree (s + 1) ∧ Gᶜ.CliqueFree (t + 1)) := by
  rintro ⟨h1, h2⟩
  rcases erdos_szekeres G s t h with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact h1 S hS
  · exact h2 T hT

/-- Diagonal case: `(2k).choose k` vertices force a `(k+1)`-clique or `(k+1)`-independent set. -/
theorem erdos_szekeres_diag {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (h : (2 * k).choose k ≤ Fintype.card V) :
    (∃ S : Finset V, G.IsNClique (k + 1) S) ∨ (∃ T : Finset V, Gᶜ.IsNClique (k + 1) T) := by
  rw [two_mul] at h
  exact erdos_szekeres G k k h

/-- The diagonal bound on the concrete vertex type `Fin ((2k).choose k)`. -/
theorem erdos_szekeres_fin (k : ℕ) (G : SimpleGraph (Fin ((2 * k).choose k)))
    [DecidableRel G.Adj] :
    (∃ S : Finset (Fin ((2 * k).choose k)), G.IsNClique (k + 1) S) ∨
      (∃ T : Finset (Fin ((2 * k).choose k)), Gᶜ.IsNClique (k + 1) T) :=
  erdos_szekeres_diag G k (by rw [Fintype.card_fin])

/-- The diagonal bound on `Fin n` for any `n ≥ (2k).choose k`. -/
theorem erdos_szekeres_fin_of_le (k n : ℕ) (hn : (2 * k).choose k ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (∃ S : Finset (Fin n), G.IsNClique (k + 1) S) ∨ (∃ T : Finset (Fin n), Gᶜ.IsNClique (k + 1) T) :=
  erdos_szekeres_diag G k (by rw [Fintype.card_fin]; exact hn)

/-- The central binomial coefficient is at most `4^k`. -/
theorem choose_two_mul_le_four_pow (k : ℕ) : (2 * k).choose k ≤ 4 ^ k := by
  rw [← Nat.centralBinom_eq_two_mul_choose]
  exact Nat.centralBinom_le_four_pow k

/-- The central binomial coefficient is strictly less than `4^(k+1)`. -/
theorem choose_two_mul_lt_four_pow_succ (k : ℕ) : (2 * k).choose k < 4 ^ (k + 1) := by
  have h1 := choose_two_mul_le_four_pow k
  have h2 : 0 < 4 ^ k := pow_pos (by norm_num) k
  rw [pow_succ]
  omega

/-- `R(k+1, k+1) ≤ 4^k`: every graph on `4^k` vertices has a `(k+1)`-clique or a
`(k+1)`-independent set. -/
theorem erdos_szekeres_four_pow (k : ℕ) (G : SimpleGraph (Fin (4 ^ k))) [DecidableRel G.Adj] :
    (∃ S : Finset (Fin (4 ^ k)), G.IsNClique (k + 1) S) ∨
      (∃ T : Finset (Fin (4 ^ k)), Gᶜ.IsNClique (k + 1) T) :=
  erdos_szekeres_fin_of_le k (4 ^ k) (choose_two_mul_le_four_pow k) G

/-- Classical indexing: for `1 ≤ k`, every graph on `(2k-2).choose (k-1)` vertices has a
`k`-clique or a `k`-independent set, i.e. `R(k, k) ≤ (2k-2).choose (k-1)`. -/
theorem erdos_szekeres_fin_classical (k : ℕ) (hk : 1 ≤ k)
    (G : SimpleGraph (Fin ((2 * k - 2).choose (k - 1)))) [DecidableRel G.Adj] :
    (∃ S : Finset (Fin ((2 * k - 2).choose (k - 1))), G.IsNClique k S) ∨
      (∃ T : Finset (Fin ((2 * k - 2).choose (k - 1))), Gᶜ.IsNClique k T) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 2 * (j + 1) - 2 = 2 * j := by omega
  have h2 : j + 1 - 1 = j := by omega
  exact erdos_szekeres_diag G j (by rw [Fintype.card_fin, h1, h2])

end Prep

#print axioms Prep.erdos_szekeres_on
#print axioms Prep.erdos_szekeres
#print axioms Prep.erdos_szekeres_cliqueFree
#print axioms Prep.erdos_szekeres_diag
#print axioms Prep.erdos_szekeres_fin
#print axioms Prep.erdos_szekeres_fin_of_le
#print axioms Prep.choose_two_mul_le_four_pow
#print axioms Prep.choose_two_mul_lt_four_pow_succ
#print axioms Prep.erdos_szekeres_four_pow
#print axioms Prep.erdos_szekeres_fin_classical
