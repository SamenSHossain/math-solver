import Mathlib
import Definitions.Def_ExactQuantumFactoring
import Theorems.Thm_OAI_ExactQuantumFactoring_outputState_normSq_sum
import Theorems.Thm_OAI_ExactQuantumFactoring_zero_amplitude_core

set_option autoImplicit false

open scoped BigOperators
open OAI.ExactQuantumFactoring

namespace OAI.ExactQuantumFactoring.RedQF

/-- If the output state vanishes off the correct outputs, the correct probability is the total
probability, which is `1`. -/
lemma correctProbability_eq_one (c : Circuit) (ℓ N : ℕ)
    (h : ∀ x : Basis c.qubits,
      ¬ CorrectEncoding N (paddedLength ℓ) (outputList ℓ x) → c.outputState ℓ N x = 0) :
    c.correctProbability ℓ N = 1 := by
  classical
  rw [← outputState_normSq_sum c ℓ N]
  unfold Circuit.correctProbability
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rfl
  · rw [h x hx, map_zero]

end OAI.ExactQuantumFactoring.RedQF

open OAI.ExactQuantumFactoring in
theorem solution : MainTheorem := by
  obtain ⟨family, hU, hP, hcore⟩ := zero_amplitude_core
  refine ⟨family, hU, hP, fun ℓ N hN hsize => ?_⟩
  obtain ⟨hq, hzero⟩ := hcore ℓ N hN hsize
  exact ⟨hq, OAI.ExactQuantumFactoring.RedQF.correctProbability_eq_one (family ℓ) ℓ N hzero⟩
