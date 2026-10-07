import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

namespace VidalHGS.Elitism

/-- Section 4.6, p. 17, proof of the Proposition: an individual `J` among the `nbElit` best
in terms of fitness has
`BF(J) ≤ (nbElit − 1)/(nbIndiv − 1) + 1 − nbElit/(nbIndiv − 1) < 1`,
provided `nbElit ≤ nbIndiv − 1`. -/
theorem elite_biasedFitness_lt_one {α : Type*} [DecidableEq α]
    (c : α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (P : Finset α) (J : α)
    (hsize : nbElit + 1 ≤ P.card) (hJ : J ∈ P) (helite : IsElite c nbElit P J) :
    biasedFitness c Δ nbElit P J ≤
        ((nbElit : ℝ) - 1) / ((P.card : ℝ) - 1) + 1 - (nbElit : ℝ) / ((P.card : ℝ) - 1) ∧
      biasedFitness c Δ nbElit P J < 1 := by sorry

end VidalHGS.Elitism
