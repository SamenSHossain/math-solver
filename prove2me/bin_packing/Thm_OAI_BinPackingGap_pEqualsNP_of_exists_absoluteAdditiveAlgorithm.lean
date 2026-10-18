import Mathlib
import Definitions.Def_BinPackingGap

namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

theorem pEqualsNP_of_exists_absoluteAdditiveAlgorithm
    (h : ∃ c : Nat, Nonempty (AbsoluteAdditiveAlgorithm c)) : PEqualsNP := by
  sorry

end BinPackingGap
end
end OAI
