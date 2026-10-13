/-
Proof of the platform statement `OAI.ExactQuantumFactoring.zero_amplitude_core`.

The circuit family and its properties come from the platform definitions
`OAI_QuantumFactoring_Part01` ... `OAI_QuantumFactoring_Part38`, a port of OpenAI's formalization
(https://github.com/openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/Computability/QuantumFactoring/, Copyright OpenAI, Apache License 2.0). The use of
`PhysicalTree.finalCircuit` follows that repository's Main.lean. Zero amplitude on wrong outputs is
derived from probability one together with total probability one (`Circuit.output_normalized` from the
same port; the platform theorem `OAI.ExactQuantumFactoring.outputState_normSq_sum` states the same fact).
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part38

set_option autoImplicit false

open scoped BigOperators
open OAI.ExactQuantumFactoring

namespace OAI.ExactQuantumFactoring.ZeroAmp

/-- Probability one on correct outputs forces zero amplitude on every incorrect output. -/
lemma zero_of_correctProbability_one (c : Circuit) (ℓ N : ℕ)
    (h : c.correctProbability ℓ N = 1) (x : Basis c.qubits)
    (hx : ¬ CorrectEncoding N (paddedLength ℓ) (outputList ℓ x)) :
    c.outputState ℓ N x = 0 := by
  classical
  have htot := c.output_normalized ℓ N
  unfold Circuit.correctProbability at h
  -- the incorrect part of the total probability is zero
  have hsplit : ∑ y : Basis c.qubits, Complex.normSq (c.outputState ℓ N y) =
      (∑ y : Basis c.qubits, if CorrectEncoding N (paddedLength ℓ) (outputList ℓ y) then
          Complex.normSq (c.outputState ℓ N y) else 0) +
      ∑ y : Basis c.qubits, if CorrectEncoding N (paddedLength ℓ) (outputList ℓ y) then
          0 else Complex.normSq (c.outputState ℓ N y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have hbad : ∑ y : Basis c.qubits, (if CorrectEncoding N (paddedLength ℓ) (outputList ℓ y) then
      0 else Complex.normSq (c.outputState ℓ N y)) = 0 := by
    linarith
  have hnn : ∀ y ∈ (Finset.univ : Finset (Basis c.qubits)),
      0 ≤ (if CorrectEncoding N (paddedLength ℓ) (outputList ℓ y) then 0
        else Complex.normSq (c.outputState ℓ N y)) := by
    intro y _; split_ifs
    · exact le_refl 0
    · exact Complex.normSq_nonneg _
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hbad x (Finset.mem_univ x)
  rw [if_neg hx] at hterm
  exact Complex.normSq_eq_zero.mp hterm

end OAI.ExactQuantumFactoring.ZeroAmp

theorem solution :
    ∃ family : ℕ → Circuit, Uniform family ∧ PolynomialResources family ∧
      ∀ (ℓ N : ℕ), 2 ≤ N → N.size = ℓ →
        ℓ + (paddedLength ℓ)^2 ≤ (family ℓ).qubits ∧
        ∀ x : Basis (family ℓ).qubits,
          ¬ CorrectEncoding N (paddedLength ℓ) (outputList ℓ x) →
            (family ℓ).outputState ℓ N x = 0 := by
  refine ⟨PhysicalTree.finalCircuit, PhysicalTree.finalCircuit_uniform,
    PhysicalTree.finalCircuit_resources, fun ℓ N hN hsize => ?_⟩
  obtain ⟨hq, hp⟩ := PhysicalTree.finalCircuit_spec ℓ N hN hsize
  exact ⟨hq, fun x hx => OAI.ExactQuantumFactoring.ZeroAmp.zero_of_correctProbability_one _ ℓ N hp x hx⟩
