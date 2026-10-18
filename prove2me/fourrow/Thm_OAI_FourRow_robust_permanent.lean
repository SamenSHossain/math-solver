-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FourRowPermanent.lean; bytes 910..1234
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FourRowPermanent

namespace OAI

noncomputable section

namespace FourRow

open scoped BigOperators

theorem robust_permanent :
  ∃ p₀ : ℝ, 4 / 3 < p₀ ∧ p₀ < 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Law,
      IsProbability ν → totalVariation ν < ε → UniformMarginals ν →
      ∀ f : Functions, (∀ i j, 0 ≤ f i j) →
        permanentExpectation ν f ≤ ∏ i, lpNorm p₀ (f i) := by
  sorry

end FourRow
end
end OAI
