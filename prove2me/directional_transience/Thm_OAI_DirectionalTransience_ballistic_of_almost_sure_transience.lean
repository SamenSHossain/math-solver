import Mathlib
import Definitions.Def_VelocityHemisphere

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

theorem ballistic_of_almost_sure_transience {d : ℕ} (hd : 2 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : annealedLaw ν (TransientPaths ℓ) = 1) :
    ∃ v : Vector d, 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 := by
  sorry

end DirectionalTransience
end OAI
