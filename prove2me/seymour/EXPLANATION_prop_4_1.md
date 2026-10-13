**Proof sketch: complete reduction (no `sorry`) of Proposition 4.1 to the pruning lemma `OAI.SeymourSecondNeighborhood.Pruning.lemma_3_1` (imported as a platform theorem), following Section 4 of the manuscript.**

Extremal argument, formalized exactly along the suggested lines. Assume r is oriented, every vertex has an in-neighbour, and r is a strict expander (|U| + |F²(U)| < 2|F(U)| for all nonempty proper U, where F = fwd r).

Definitions (namespace Sol_..._prop_4_1): for families P, Q ⊆ V×V put
  F1 P = {(i,j) : ∃ p, (p,j) ∈ P ∧ r p i}  (advance first coordinate), 
  F2 Q = {(i,j) : ∃ s, (i,s) ∈ Q ∧ r s j}  (advance second coordinate),
  Δ = diagonal, d(P,Q) = |V×V \ (F1 P ∪ F2 Q)|, 
  Ω = {(P,Q) : Disjoint (F1 P) (F2 Q), Δ ⊆ P, Δ ⊆ Q} (a Finset, as a filter of powerset ×ˢ powerset),
  col P j = image of Prod.fst on the fibre {z ∈ P : z.2 = j}.

(1) compat_Δ: (Δ,Δ) ∈ Ω — a common point of F1 Δ and F2 Δ would give r z.2 z.1 and r z.1 z.2, contradicting asymmetry. Hence Ω is nonempty and Finset.exists_max_image yields (P,Q) ∈ Ω maximizing obj(P,Q) = |P| + |Q| + d(P,Q).

(2) Column inequality (column_ineq): col (F1 P) j = F(col P j) (col_F1), the fibre {z ∈ P : z.2 = j} has the same cardinality as col P j (Prod.fst is injective on it, card_fiber), so by Finset.card_eq_sum_card_fiberwise (f = Prod.snd) |P| = Σ_j |col P j|, |F1 P| = Σ_j |F(col P j)|, |F1(F1 P)| = Σ_j |F²(col P j)|. If every column is nonempty and proper, the strict expander hypothesis applies to each column and Finset.sum_lt_sum_of_nonempty (V nonempty) gives |P| + |F1(F1 P)| < 2|F1 P|. The row version (row_ineq) is obtained by symmetry: F2 Q = swap(F1(swap Q)) (F2_eq_swap), swap is injective and involutive on finsets, so the column inequality for swap Q yields |Q| + |F2(F2 Q)| < 2|F2 Q|.

(3) Column/row hypotheses for the extremal (P,Q) (col_P_hyp, col_Q_hyp): j ∈ col P j since (j,j) ∈ Δ ⊆ P; if col P j = univ then, with w → j and p → w (PosIndeg), (w,j) ∈ F1 P and (w,j) ∈ F2 Q (via (w,w) ∈ Q), contradicting disjointness. Rows analogously using (i,w) with w → i and some s → w.

(4) Set R = univ \ F2(F2 Q), C = univ \ F1(F1 P). Cardinality bookkeeping: |R| + |F2(F2 Q)| = |V×V|, |C| + |F1(F1 P)| = |V×V|, d(P,Q) + |F1 P ∪ F2 Q| = |V×V|, |F1 P ∪ F2 Q| = |F1 P| + |F2 Q| (disjoint). Together with (2) this gives |R| + |C| > |P| + |Q| + 2 d(P,Q).

(5) Δ ⊆ R and Δ ⊆ C (Δ_sub_R, Δ_sub_C): (v,v) ∈ F2(F2 Q) gives (v,s) ∈ F2 Q with s → v, but then (v,s) ∈ F1 P via (s,s) ∈ P, contradicting disjointness; symmetrically for F1(F1 P).

(6) Diagonal members are conflict-free (diag_free_L, diag_free_R): a conflict of (v,v) with (i,s) ∈ C means v → i and s → v, then (v,s) ∈ F1 P and (i,s) ∈ F1(F1 P), contradicting (i,s) ∈ C; a conflict of (p,j) ∈ R with (v,v) means p → v and v → j, then (p,v) ∈ F2 Q and (p,j) ∈ F2(F2 Q), contradicting (p,j) ∈ R.

(7) pointsH r R C ⊆ univ \ (F1 P ∪ F2 Q) (pointsH_card_le), hence |pointsH| ≤ d(P,Q): for a conflict ((p,j),(i,s)) with p → i, s → j, if (p,s) ∈ F1 P then (i,s) ∈ F1(F1 P) contradicting (i,s) ∈ C; if (p,s) ∈ F2 Q then (p,j) ∈ F2(F2 Q) contradicting (p,j) ∈ R.

(8) Apply Pruning.lemma_3_1 r R C: R' ⊆ R, C' ⊆ C with no conflicts, retention of conflict-free members, and |R \ R'| + |C \ C'| ≤ |pointsH r R C| + |uncovered r R C R' C'|. No conflicts gives Disjoint (F1 R') (F2 C') (compat_of_noconf: a common point z yields (p,z.2) ∈ R', (z.1,s) ∈ C' with p → z.1, s → z.2, i.e. a conflict). By (5),(6) and retention, Δ ⊆ R' and Δ ⊆ C', so (R',C') ∈ Ω. uncovered r R C R' C' ⊆ univ \ (F1 R' ∪ F2 C') (uncovered_card_le: a point of F1 R' is covered on the left by (p,z.2) ∈ R', a point of F2 C' on the right by (z.1,s) ∈ C'), so |uncovered| ≤ d(R',C').

(9) With |R \ R'| + |R'| = |R|, |C \ C'| + |C'| = |C| and the bounds from (4),(7),(8): |R'| + |C'| + d(R',C') ≥ |R| + |C| − d(P,Q) > |P| + |Q| + d(P,Q), i.e. obj(R',C') > obj(P,Q), contradicting maximality (hmax (R',C') ∈ Ω). The final contradiction is discharged by omega from the collected ℕ-linear cardinality identities/inequalities.