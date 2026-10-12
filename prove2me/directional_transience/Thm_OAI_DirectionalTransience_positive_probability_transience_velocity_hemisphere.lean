-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/VelocityHemisphere.lean; bytes 3394..4247
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_VelocityHemisphere

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

theorem positive_probability_transience_velocity_hemisphere
    {d : ℕ} (hd : 3 ≤ d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : ℓ ≠ 0)
    (hpos : 0 < annealedLaw ν (TransientPaths ℓ)) :
    ∃ v : Vector d,
      v ≠ 0 ∧ 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 ∧
      (∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v) ∧
      {u : Vector d | dot u u = 1 ∧ annealedLaw ν (TransientPaths u) = 1} =
        {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} ∧
      {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} =
        {u : Vector d | dot u u = 1 ∧ 0 < dot v u} ∧
      (∀ u : Vector d, dot u u = 1 → dot v u ≤ 0 →
        annealedLaw ν (TransientPaths u) = 0) := by
  sorry

end DirectionalTransience
end OAI
