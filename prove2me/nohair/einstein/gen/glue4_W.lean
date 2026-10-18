
/-- The atom `W = 1/(r² + a² k₃²)`. -/
noncomputable def Wf (a : ℝ) (w : E4) : ℝ := 1 / (ksRadius a w ^ 2 + a ^ 2 * ksNull a w 3 ^ 2)

theorem ks_W (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    Wf a z * (ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2) = 1 := by
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  unfold Wf
  field_simp
