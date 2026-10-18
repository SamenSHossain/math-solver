import Mathlib
import Definitions.Def_ExactQuantumFactoring

namespace OAI

namespace ExactQuantumFactoring

open scoped BigOperators

/-- **Circuits preserve total probability.** Every circuit over the fixed 20-gate alphabet acts
unitarily, so the output state on any classical input has total squared amplitude `1`. -/
theorem outputState_normSq_sum (c : Circuit) (ℓ N : ℕ) :
    ∑ x : Basis c.qubits, Complex.normSq (c.outputState ℓ N x) = 1 := by
  sorry

end ExactQuantumFactoring
end OAI
