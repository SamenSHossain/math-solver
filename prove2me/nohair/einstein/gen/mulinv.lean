private lemma mul_inv_KS (f : ℝ) (k : Fin 4 → ℝ) (hnull : -(k 0) ^ 2 + k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 = 0) :
    (Matrix.of fun μ ν => minkowski μ ν + f * k μ * k ν) *
      (Matrix.of fun μ ν => minkowski μ ν - f * ![-k 0, k 1, k 2, k 3] μ * ![-k 0, k 1, k 2, k 3] ν) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four]
  linear_combination (norm := skip) (-f ^ 2 * k i * ![-k 0, k 1, k 2, k 3] j) * hnull
  fin_cases i <;> fin_cases j <;> simp [minkowski] <;> ring
