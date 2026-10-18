import Definitions.Def_FdVersusFdSucc_defs

open Filter

namespace FdVersusFdSucc

/-- Completeness of `F_d` for depth-`d` formulas: every tautology of depth at most `d` has an
`F_d`-proof. -/
theorem depth_frege_complete (d : ℕ) (A : Formula) (hd : A.depth ≤ d)
    (hA : A.IsTautology) : ∃ π : List Sequent, IsDepthProofOf d π A := by sorry

end FdVersusFdSucc
