import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

namespace VidalHGS.Elitism

/-- Section 4.6, p. 17, proof of the Proposition: when `X = ∅` (so that costs in `P` are
pairwise distinct), the individual `W` with the worst fitness has `fit(W) = 1` and
`BF(W) ≥ 1`, provided `nbElit ≤ nbIndiv − 1` and `nbIndiv ≥ 2`. -/
theorem worst_biasedFitness_ge_one {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (P : Finset α) (W : α)
    (hX : cloneSet c δ best P = ∅) (hcard : 2 ≤ P.card) (hsize : nbElit + 1 ≤ P.card)
    (hW : W ∈ P) (hworst : ∀ K ∈ P, c K ≤ c W) :
    fitRank c P W = 1 ∧ 1 ≤ biasedFitness c Δ nbElit P W := by sorry

end VidalHGS.Elitism
