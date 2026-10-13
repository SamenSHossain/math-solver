
/-! ## Metric, inverse metric and Christoffel symbols on `U` -/

theorem hasCP_K (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (l : Fin 4) :
    HasCP (fun w => ksNull a w l) z
      (dKt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) l) := by
  fin_cases l
  · exact (HasCP.cst 1 z).congr_d (fun k => by fin_cases k <;> simp [dKt])
  · exact hasCP_K1 a z hz
  · exact hasCP_K2 a z hz
  · exact hasCP_K3 a z hz

theorem profile_eq (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ksProfile m a e z = fA a m e (ksRadius a z) (Wf a z) := by
  show ksRadius a z ^ 2 * (2 * m * ksRadius a z - e ^ 2) / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) = _
  rw [ks_x3 a z hz]
  unfold fA Wf
  have hR : ksRadius a z ≠ 0 := hz.ne'
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  field_simp
  try ring

theorem cp_metric (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (l k j : Fin 4) :
    coordPartial (fun w => kerrNewmanMetric m a e w l k) j z
      = dgA a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) l k j := by
  have h := (HasCP.cst (minkowski l k) z).add
    (((hasCP_profile m a e z hz).mul (hasCP_K a z hz l)).mul (hasCP_K a z hz k))
  have h2 := h.eq j
  beta_reduce at h2
  have e1 : (fun w => kerrNewmanMetric m a e w l k)
      = (fun w => minkowski l k + ksProfile m a e w * ksNull a w l * ksNull a w k) := rfl
  rw [e1, h2, profile_eq m a e z hz]
  simp only [dgA, Kv, ← ksNull_eq_Kv a z]
  ring

theorem invMetric_eq (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    invMetric (kerrNewmanMetric m a e) z = Matrix.of (fun i l =>
      ginvA a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) i l) := by
  have hnull := ks_null a z hz
  have hG : kerrNewmanMetric m a e z = Matrix.of fun μ ν =>
      minkowski μ ν + ksProfile m a e z * ksNull a z μ * ksNull a z ν := rfl
  unfold invMetric
  rw [hG, Matrix.inv_eq_right_inv (mul_inv_KS _ _ hnull)]
  ext i l
  simp only [Matrix.of_apply, ginvA, Ks, profile_eq m a e z hz, ksNull_zero, minkowski_eq]

theorem chr_eq (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i j k : Fin 4) :
    christoffel (kerrNewmanMetric m a e) z i j k
      = chrS a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) i j k := by
  simp only [christoffel, chrS, invMetric_eq m a e z hz, Matrix.of_apply, cp_metric m a e z hz]
