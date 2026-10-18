import Definitions.Def_FdVersusFdSucc_defs

open Filter

namespace FdVersusFdSucc

/-- Soundness of `F_d`: every formula with an `F_d`-proof is a tautology. -/
theorem depth_frege_sound (d : ℕ) (π : List Sequent) (A : Formula)
    (h : IsDepthProofOf d π A) : A.IsTautology := by sorry

end FdVersusFdSucc
