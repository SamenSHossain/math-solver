import Mathlib
import Definitions.Def_SeymourSecondNeighborhood

/-!
# Second-neighborhood mission: image operators, subset deficit, strict expansion, blow-up,
and the conflict structure for the pruning lemma

Auxiliary notions used to state the lemmas of the manuscript
*A proof of Seymour's second-neighborhood conjecture* (OpenAI, 2026).
-/

noncomputable section

open Finset

namespace OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One-step image `F(U) = {y | ∃ x ∈ U, x → y}` (the union of the out-neighborhoods; `U` is not
subtracted). -/
def fwd (r : V → V → Prop) (U : Finset V) : Finset V := by
  classical
  exact univ.filter (fun y => ∃ x ∈ U, r x y)

/-- Every vertex has an in-neighbor. -/
def PosIndeg (r : V → V → Prop) : Prop := ∀ v, ∃ u, r u v

/-- The subset deficit (3): `|F²(S) \ F(S)| < |F(S) \ S|` for every nonempty proper `S`. -/
def SubsetDeficit (r : V → V → Prop) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ univ → (fwd r (fwd r S) \ fwd r S).card < (fwd r S \ S).card

/-- Strict expansion (2)/(17): `|U| + |F²(U)| < 2 |F(U)|` for every nonempty proper `U`. -/
def StrictExpander (r : V → V → Prop) : Prop :=
  ∀ U : Finset V, U.Nonempty → U ≠ univ → U.card + (fwd r (fwd r U)).card < 2 * (fwd r U).card

/-- The lexicographic blow-up `D[T_m]`: each vertex is replaced by a transitive tournament on
`Fin m` (arcs from smaller to larger labels), and every arc `v → w` of `D` becomes all arcs from the
block at `v` to the block at `w`. -/
def blowup (r : V → V → Prop) (m : ℕ) : V × Fin m → V × Fin m → Prop :=
  fun x y => r x.1 y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

end OAI.SeymourSecondNeighborhood

namespace OAI.SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A left member `(p, j)` and a right member `(i, s)` conflict when `p → i` and `s → j`. -/
def Conflict (arrow : X → X → Prop) (l c : X × X) : Prop := arrow l.1 c.1 ∧ arrow c.2 l.2

/-- A left member `(p, j)` covers the point `(i, j)` when `p → i`. -/
def CoversL (arrow : X → X → Prop) (l z : X × X) : Prop := z.2 = l.2 ∧ arrow l.1 z.1

/-- A right member `(i, s)` covers the point `(i, j)` when `s → j`. -/
def CoversR (arrow : X → X → Prop) (c z : X × X) : Prop := z.1 = c.1 ∧ arrow c.2 z.2

/-- The conflicting pairs of two families. -/
def conflicts (arrow : X → X → Prop) (R C : Finset (X × X)) : Finset ((X × X) × (X × X)) := by
  classical
  exact (R ×ˢ C).filter (fun lc => Conflict arrow lc.1 lc.2)

/-- `Z = {(i, j) : some (p, j) ∈ R conflicts with some (i, s) ∈ C}`. -/
def pointsZ (arrow : X → X → Prop) (R C : Finset (X × X)) : Finset (X × X) :=
  (conflicts arrow R C).image (fun lc => (lc.2.1, lc.1.2))

/-- `H = {(p, s) : some (p, j) ∈ R conflicts with some (i, s) ∈ C}`. -/
def pointsH (arrow : X → X → Prop) (R C : Finset (X × X)) : Finset (X × X) :=
  (conflicts arrow R C).image (fun lc => (lc.1.1, lc.2.2))

/-- The points of `Z` covered by no member of `R' ∪ C'`. -/
def uncovered (arrow : X → X → Prop) (R C R' C' : Finset (X × X)) : Finset (X × X) := by
  classical
  exact (pointsZ arrow R C).filter
    (fun z => (∀ l ∈ R', ¬ CoversL arrow l z) ∧ (∀ c ∈ C', ¬ CoversR arrow c z))

end OAI.SeymourSecondNeighborhood.Pruning
