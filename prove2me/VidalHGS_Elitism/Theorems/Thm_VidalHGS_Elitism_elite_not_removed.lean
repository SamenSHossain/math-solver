import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

namespace VidalHGS.Elitism

/-- Section 4.6, pp. 16–17, Proposition: using the Biased Fitness function, an individual
`J ∉ X` that is part of the `nbElit` best individuals of the subpopulation `P` in terms of
fitness is not removed by the survivor-selection procedure, which removes `nOff` (the paper's
`λ`) individuals, provided `nbElit + nOff ≤ |P|` (Table 1: `nbElit = el × μ ≤ μ`, and the
procedure reduces `μ + λ` individuals to `μ`). -/
theorem elite_not_removed {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (nOff : ℕ) (P P' : Finset α) (J : α)
    (hrun : SurvivorRun c δ Δ nbElit best nOff P P') (hsize : nbElit + nOff ≤ P.card)
    (hJ : J ∈ P) (hJX : J ∉ cloneSet c δ best P) (helite : IsElite c nbElit P J) :
    J ∈ P' := by sorry

end VidalHGS.Elitism
