import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lemma_2_2 [Nonempty V] (r : V → V → Prop) (hr : IsOriented r)
    (hbad : ∀ v, ¬ GoodVertex r v)
    (hmin_arcs : ∀ r' : V → V → Prop, (∀ a b, r' a b → r a b) → (∃ a b, r a b ∧ ¬ r' a b) →
      ∃ v, GoodVertex r' v)
    (hmin_order : ∀ W : Finset V, W.Nonempty → W ≠ univ →
      ∃ v : W, GoodVertex (fun a b : W => r a b) v) :
    PosIndeg r ∧ SubsetDeficit r := by
  sorry

end OAI.SeymourSecondNeighborhood
