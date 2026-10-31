import Definitions.Def_SymmetricRendezvousLine_defs

open SymmetricRendezvousLine

/-- The symmetric value is an infimum over *all* mixed strategies, while the discrete value is
the infimum of the same quantity over the subfamily of strategies supported on integer
zigzags; an infimum over a larger family is smaller. -/
theorem solution : symmetricRendezvousValue ≤ discreteSymmetricRendezvousValue :=
  le_iInf₂ fun S _ => iInf_le (fun S : MixedStrategy => expectedMeetingTime S S) S
