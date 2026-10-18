import Mathlib
import Definitions.Def_ExactQuantumFactoring

namespace OAI

namespace ExactQuantumFactoring

open scoped BigOperators

/-- **Exact factoring core: no amplitude on wrong outputs.** A uniform, polynomial-size circuit
family over the fixed gate set whose output state on every input `N ≥ 2` of bit length `ℓ` has zero
amplitude on every basis state that does not encode the complete sorted prime factorization of `N`. -/
theorem zero_amplitude_core :
    ∃ family : ℕ → Circuit, Uniform family ∧ PolynomialResources family ∧
      ∀ (ℓ N : ℕ), 2 ≤ N → N.size = ℓ →
        ℓ + (paddedLength ℓ)^2 ≤ (family ℓ).qubits ∧
        ∀ x : Basis (family ℓ).qubits,
          ¬ CorrectEncoding N (paddedLength ℓ) (outputList ℓ x) →
            (family ℓ).outputState ℓ N x = 0 := by
  sorry

end ExactQuantumFactoring
end OAI
