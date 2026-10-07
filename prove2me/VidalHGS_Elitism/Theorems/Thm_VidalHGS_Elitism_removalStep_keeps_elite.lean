import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

namespace VidalHGS.Elitism

/-- Section 4.6, p. 17, proof of the Proposition: one removal step of the survivor-selection
procedure does not remove an individual `J ∉ X` that is among the `nbElit` best in terms of
fitness, provided `nbElit ≤ nbIndiv − 1`. -/
theorem removalStep_keeps_elite {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (P Q : Finset α) (J : α)
    (hstep : RemovalStep c δ Δ nbElit best P Q) (hsize : nbElit + 1 ≤ P.card)
    (hJ : J ∈ P) (hJX : J ∉ cloneSet c δ best P) (helite : IsElite c nbElit P J) :
    J ∈ Q := by sorry

end VidalHGS.Elitism
