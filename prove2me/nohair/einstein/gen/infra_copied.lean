private lemma ksRadius_eq' (a : ℝ) : ksRadius a = fun w : E4 => Real.sqrt ((w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 - a ^ 2 +
    Real.sqrt ((w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * w 3 ^ 2)) / 2) := rfl

private lemma ks_Q_pos (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    0 < (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2 +
      Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)) / 2 := by
  rw [ksRadius_eq'] at hz
  exact Real.sqrt_pos.mp hz

private lemma ks_sq (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ksRadius a z ^ 2 = (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2 +
      Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)) / 2 := by
  have h := ks_Q_pos a z hz
  rw [ksRadius_eq']
  exact Real.sq_sqrt h.le

private lemma ks_S_sq (a : ℝ) (z : E4) :
    Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2) ^ 2
      = (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2 :=
  Real.sq_sqrt (by positivity)

private lemma ks_C (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ksRadius a z ^ 4 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) * ksRadius a z ^ 2 - a ^ 2 * z 3 ^ 2 = 0 := by
  have h1 := ks_sq a z hz
  have h2 := ks_S_sq a z
  set S := Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)
  set P := z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2
  set r := ksRadius a z
  linear_combination (r ^ 2 - P / 2 + S / 2) * h1 + (1 / 4 : ℝ) * h2

private lemma ks_S_eq (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)
      = 2 * ksRadius a z ^ 2 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) := by
  have h1 := ks_sq a z hz
  linarith

private lemma ks_D_pos (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    0 < (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2 := by
  have h1 := ks_sq a z hz
  have hr2 : 0 < ksRadius a z ^ 2 := by positivity
  rcases (show (0:ℝ) ≤ (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2 by positivity).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, Real.sqrt_zero] at h1
    have hP : (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 = 0 := by nlinarith [sq_nonneg (a * z 3)]
    have hP' : z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hP
    rw [hP'] at h1
    linarith

private lemma ks_S_pos (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    0 < 2 * ksRadius a z ^ 2 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) := by
  rw [← ks_S_eq a z hz]
  exact Real.sqrt_pos.mpr (ks_D_pos a z hz)

private lemma ks_den_pos (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    0 < ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 := by positivity

private lemma ksRadius_differentiableAt (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private lemma line_apply (z v : E4) (t : ℝ) (j : Fin 4) : (z + t • v) j = z j + t * v j := by simp

private lemma hasDerivAt_line_coord (z v : E4) (j : Fin 4) :
    HasDerivAt (fun t : ℝ => z j + t * v j) (v j) 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v j)).const_add (z j)

private lemma hasDerivAt_ksRadius_line (a : ℝ) (z v : E4) (hz : 0 < ksRadius a z) :
    HasDerivAt (fun t : ℝ => ksRadius a (z + t • v))
      (ksRadius a z * (ksRadius a z ^ 2 * (z 1 * v 1 + z 2 * v 2) + (ksRadius a z ^ 2 + a ^ 2) * z 3 * v 3)
        / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)) 0 := by
  have e : (fun t : ℝ => ksRadius a (z + t • v)) = fun t : ℝ =>
      Real.sqrt (((z 1 + t * v 1) ^ 2 + (z 2 + t * v 2) ^ 2 + (z 3 + t * v 3) ^ 2 - a ^ 2 +
        Real.sqrt (((z 1 + t * v 1) ^ 2 + (z 2 + t * v 2) ^ 2 + (z 3 + t * v 3) ^ 2 - a ^ 2) ^ 2
          + 4 * a ^ 2 * (z 3 + t * v 3) ^ 2)) / 2) := by
    funext t
    rw [ksRadius_eq']
    simp only [line_apply]
  rw [e]
  have h1 := hasDerivAt_line_coord z v 1
  have h2 := hasDerivAt_line_coord z v 2
  have h3 := hasDerivAt_line_coord z v 3
  have hP := (((h1.pow 2).add (h2.pow 2)).add (h3.pow 2)).sub_const (a ^ 2)
  have hD := (hP.pow 2).add ((h3.pow 2).const_mul (4 * a ^ 2))
  have hD0 := ks_D_pos a z hz
  have hQ0 := ks_Q_pos a z hz
  have hSq := hD.sqrt (by simpa using hD0.ne')
  have hQ := (hP.add hSq).div_const 2
  have hR := hQ.sqrt (by simpa using hQ0.ne')
  convert hR using 1
  · rfl
  have hr0 : Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2 + Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)) / 2) = ksRadius a z := rfl
  simp only [zero_mul, add_zero, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat,
    show (2:ℕ) - 1 = 1 from rfl, pow_one]
  rw [hr0]
  have hSe := ks_S_eq a z hz
  have hS := ks_S_pos a z hz
  rw [← hSe] at hS
  have hC := ks_C a z hz
  have hden := ks_den_pos a z hz
  have hr1 := hz
  set S := Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)
  set r := ksRadius a z
  field_simp
  linear_combination (2*(2*a^2*r^2*(v 3)*(z 3) - a^2*(v 1)*(z 3)^2*(z 1) - a^2*(v 2)*(z 3)^2*(z 2) - a^2*(v 3)*(z 3)^3 + r^4*(v 1)*(z 1) + r^4*(v 2)*(z 2) + r^4*(v 3)*(z 3))) * hSe + (4*(a^2*(v 3)*(z 3) + r^2*(v 1)*(z 1) + r^2*(v 2)*(z 2) + r^2*(v 3)*(z 3))) * hC

private lemma fderiv_eq_of_line {g : E4 → ℝ} {z v : E4} {c : ℝ} (hg : DifferentiableAt ℝ g z)
    (h : HasDerivAt (fun t : ℝ => g (z + t • v)) c 0) : fderiv ℝ g z v = c := by
  have h1 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have h2 : HasFDerivAt g (fderiv ℝ g z) (z + (0:ℝ) • v) := by
    simpa using hg.hasFDerivAt
  exact (h2.comp_hasDerivAt (0:ℝ) h1).unique h

private lemma hasDerivAt_k1_aux {R X1 X2 : ℝ → ℝ} {dr d1 d2 : ℝ} (a : ℝ) (hR : HasDerivAt R dr 0)
    (h1 : HasDerivAt X1 d1 0) (h2 : HasDerivAt X2 d2 0) (hne : R 0 ^ 2 + a ^ 2 ≠ 0) :
    HasDerivAt (fun t => (R t * X1 t + a * X2 t) / (R t ^ 2 + a ^ 2))
      (((dr * X1 0 + R 0 * d1 + a * d2) * (R 0 ^ 2 + a ^ 2)
        - (R 0 * X1 0 + a * X2 0) * (2 * R 0 * dr)) / (R 0 ^ 2 + a ^ 2) ^ 2) 0 := by
  have := ((hR.fun_mul h1).fun_add (h2.const_mul a)).fun_div ((hR.fun_pow 2).add_const (a ^ 2)) hne
  refine this.congr_deriv ?_
  norm_num

private lemma hasDerivAt_k2_aux {R X1 X2 : ℝ → ℝ} {dr d1 d2 : ℝ} (a : ℝ) (hR : HasDerivAt R dr 0)
    (h1 : HasDerivAt X1 d1 0) (h2 : HasDerivAt X2 d2 0) (hne : R 0 ^ 2 + a ^ 2 ≠ 0) :
    HasDerivAt (fun t => (R t * X2 t - a * X1 t) / (R t ^ 2 + a ^ 2))
      (((dr * X2 0 + R 0 * d2 - a * d1) * (R 0 ^ 2 + a ^ 2)
        - (R 0 * X2 0 - a * X1 0) * (2 * R 0 * dr)) / (R 0 ^ 2 + a ^ 2) ^ 2) 0 := by
  have := ((hR.fun_mul h2).fun_sub (h1.const_mul a)).fun_div ((hR.fun_pow 2).add_const (a ^ 2)) hne
  refine this.congr_deriv ?_
  norm_num

private lemma hasDerivAt_k3_aux {R X3 : ℝ → ℝ} {dr d3 : ℝ} (hR : HasDerivAt R dr 0)
    (h3 : HasDerivAt X3 d3 0) (hne : R 0 ≠ 0) :
    HasDerivAt (fun t => X3 t / R t) ((d3 * R 0 - X3 0 * dr) / R 0 ^ 2) 0 :=
  h3.fun_div hR hne

private lemma ksNull_zero (a : ℝ) (w : E4) : ksNull a w 0 = 1 := rfl
private lemma ksNull_one (a : ℝ) (w : E4) :
    ksNull a w 1 = (ksRadius a w * w 1 + a * w 2) / (ksRadius a w ^ 2 + a ^ 2) := rfl
private lemma ksNull_two (a : ℝ) (w : E4) :
    ksNull a w 2 = (ksRadius a w * w 2 - a * w 1) / (ksRadius a w ^ 2 + a ^ 2) := rfl
private lemma ksNull_three (a : ℝ) (w : E4) : ksNull a w 3 = w 3 / ksRadius a w := rfl

/-- directional derivative of `r` -/
private noncomputable def drf (a : ℝ) (z v : E4) : ℝ :=
  ksRadius a z * (ksRadius a z ^ 2 * (z 1 * v 1 + z 2 * v 2) + (ksRadius a z ^ 2 + a ^ 2) * z 3 * v 3)
    / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)

private noncomputable def dk1f (a : ℝ) (z v : E4) : ℝ :=
  ((drf a z v * z 1 + ksRadius a z * v 1 + a * v 2) * (ksRadius a z ^ 2 + a ^ 2)
    - (ksRadius a z * z 1 + a * z 2) * (2 * ksRadius a z * drf a z v)) / (ksRadius a z ^ 2 + a ^ 2) ^ 2

private noncomputable def dk2f (a : ℝ) (z v : E4) : ℝ :=
  ((drf a z v * z 2 + ksRadius a z * v 2 - a * v 1) * (ksRadius a z ^ 2 + a ^ 2)
    - (ksRadius a z * z 2 - a * z 1) * (2 * ksRadius a z * drf a z v)) / (ksRadius a z ^ 2 + a ^ 2) ^ 2

private noncomputable def dk3f (a : ℝ) (z v : E4) : ℝ :=
  (v 3 * ksRadius a z - z 3 * drf a z v) / ksRadius a z ^ 2

private lemma ksNull_differentiableAt (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    DifferentiableAt ℝ (fun w => ksNull a w i) z := by
  have hr := ksRadius_differentiableAt a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' : ksRadius a z ≠ 0 := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · show DifferentiableAt ℝ (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · show DifferentiableAt ℝ (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

private lemma fderiv_k1 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (v : E4) :
    fderiv ℝ (fun w => ksNull a w 1) z v = dk1f a z v := by
  apply fderiv_eq_of_line (ksNull_differentiableAt a z hz 1)
  have hR := hasDerivAt_ksRadius_line a z v hz
  have := hasDerivAt_k1_aux a hR (hasDerivAt_line_coord z v 1) (hasDerivAt_line_coord z v 2)
    (by simp only [zero_smul, add_zero]; positivity)
  have e : (fun t : ℝ => ksNull a (z + t • v) 1) = fun t => (ksRadius a (z + t • v) * (z 1 + t * v 1)
      + a * (z 2 + t * v 2)) / (ksRadius a (z + t • v) ^ 2 + a ^ 2) := by
    funext t; rw [ksNull_one, line_apply, line_apply]
  rw [e]
  refine this.congr_deriv ?_
  simp only [zero_smul, add_zero, zero_mul]
  rfl

private lemma fderiv_k2 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (v : E4) :
    fderiv ℝ (fun w => ksNull a w 2) z v = dk2f a z v := by
  apply fderiv_eq_of_line (ksNull_differentiableAt a z hz 2)
  have hR := hasDerivAt_ksRadius_line a z v hz
  have := hasDerivAt_k2_aux a hR (hasDerivAt_line_coord z v 1) (hasDerivAt_line_coord z v 2)
    (by simp only [zero_smul, add_zero]; positivity)
  have e : (fun t : ℝ => ksNull a (z + t • v) 2) = fun t => (ksRadius a (z + t • v) * (z 2 + t * v 2)
      - a * (z 1 + t * v 1)) / (ksRadius a (z + t • v) ^ 2 + a ^ 2) := by
    funext t; rw [ksNull_two, line_apply, line_apply]
  rw [e]
  refine this.congr_deriv ?_
  simp only [zero_smul, add_zero, zero_mul]
  rfl

private lemma fderiv_k3 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (v : E4) :
    fderiv ℝ (fun w => ksNull a w 3) z v = dk3f a z v := by
  apply fderiv_eq_of_line (ksNull_differentiableAt a z hz 3)
  have hR := hasDerivAt_ksRadius_line a z v hz
  have := hasDerivAt_k3_aux hR (hasDerivAt_line_coord z v 3)
    (by simp only [zero_smul, add_zero]; exact hz.ne')
  have e : (fun t : ℝ => ksNull a (z + t • v) 3) = fun t => (z 3 + t * v 3) / ksRadius a (z + t • v) := by
    funext t; rw [ksNull_three, line_apply]
  rw [e]
  refine this.congr_deriv ?_
  simp only [zero_smul, add_zero, zero_mul]
  rfl

private lemma fderiv_k0 (a : ℝ) (z : E4) : fderiv ℝ (fun w => ksNull a w 0) z = 0 := by
  simp only [ksNull_zero]
  exact fderiv_const_apply _

private lemma ks_null (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    -(ksNull a z 0) ^ 2 + ksNull a z 1 ^ 2 + ksNull a z 2 ^ 2 + ksNull a z 3 ^ 2 = 0 := by
  rw [ksNull_zero, ksNull_one, ksNull_two, ksNull_three]
  have hC := ks_C a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hr := hz.ne'
  set r := ksRadius a z
  field_simp
  linear_combination (-a^2 - r^2) * hC

