import Mathlib
import Definitions.Def_VelocityHemisphere

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

theorem uniformElliptic_directional_zero_one {d : ℕ} (hd : 3 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : ℓ ≠ 0) :
    annealedLaw ν (TransientPaths ℓ) = 0 ∨ annealedLaw ν (TransientPaths ℓ) = 1 := by
  sorry

end DirectionalTransience
end OAI
