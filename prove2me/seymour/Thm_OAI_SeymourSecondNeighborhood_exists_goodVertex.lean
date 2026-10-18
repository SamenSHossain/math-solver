-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SeymourSecondNeighborhood.lean; bytes 762..872
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Union
import Definitions.Def_SeymourSecondNeighborhood

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

variable [Fintype V] [DecidableEq V]

variable [Nonempty V]

theorem exists_goodVertex (r : V → V → Prop) (hr : IsOriented r) :
    ∃ v, GoodVertex r v := by
  sorry

end SeymourSecondNeighborhood
end OAI
