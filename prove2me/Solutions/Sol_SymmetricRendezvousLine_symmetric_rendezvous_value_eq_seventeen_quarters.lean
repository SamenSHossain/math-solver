import Definitions.Def_SymmetricRendezvousLine_defs
import Theorems.Thm_SymmetricRendezvousLine_symmetric_rendezvous_value_eq_discrete
import Theorems.Thm_SymmetricRendezvousLine_symmetric_rendezvous_value_le_discrete
import Theorems.Thm_SymmetricRendezvousLine_discrete_symmetric_rendezvous_value_le_seventeen_quarters
import Theorems.Thm_SymmetricRendezvousLine_discrete_symmetric_rendezvous_value_ge_seventeen_quarters

open SymmetricRendezvousLine

/-- Reduction of the Han–Du–Vera–Zuluaga conjecture `R = 17/4` to its two halves in the
discrete (integer-zigzag) model, glued by the HDVZ reduction `R = R_disc`:

* upper half: `R ≤ R_disc ≤ 17/4` — the first inequality is trivial (infimum over a larger
  family), the second asks for integer-zigzag symmetric strategies with expected meeting time
  arbitrarily close to `17/4`;
* lower half: `17/4 ≤ R_disc = R` — the first inequality is a lower-bound certificate over all
  integer-zigzag strategies, the equality is the HDVZ dominance theorem. -/
theorem solution : symmetricRendezvousValue = 17 / 4 := by
  apply le_antisymm
  · exact symmetric_rendezvous_value_le_discrete.trans
      discrete_symmetric_rendezvous_value_le_seventeen_quarters
  · rw [symmetric_rendezvous_value_eq_discrete]
    exact discrete_symmetric_rendezvous_value_ge_seventeen_quarters
