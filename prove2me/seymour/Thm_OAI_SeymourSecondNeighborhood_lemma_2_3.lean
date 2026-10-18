import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lemma_2_3 (r : V → V → Prop) (hr : IsOriented r) (hin : PosIndeg r)
    (hdef : SubsetDeficit r) (m : ℕ) (hm : Fintype.card V < m) :
    IsOriented (blowup r m) ∧ PosIndeg (blowup r m) ∧ StrictExpander (blowup r m) := by
  sorry

end OAI.SeymourSecondNeighborhood
