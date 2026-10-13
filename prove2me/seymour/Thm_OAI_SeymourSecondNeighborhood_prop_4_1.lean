import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem prop_4_1 [Nonempty V] (r : V → V → Prop) (hr : IsOriented r) (hin : PosIndeg r) :
    ¬ StrictExpander r := by
  sorry

end OAI.SeymourSecondNeighborhood
