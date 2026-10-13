import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
theorem timeCorrelation_hasDerivAt {n : ℕ} (β lam : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (i k : Fin n) (t : ℝ) :
    HasDerivAt (fun s => timeCorrelation β lam s i k)
      (-∑ l : Fin n, kineticCoeff β lam i l *
        fluctuationAverage β (fun x => meanConjugate β lam t x l * x k)) t := by sorry
end OnsagerReciprocal
