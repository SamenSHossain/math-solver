import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem conjugate_fluctuation_average {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (i k : Fin n) :
    fluctuationAverage β (fun x => conjugate β x i * x k) = if i = k then 1 else 0 := by sorry
end OnsagerReciprocal
