
/-! ## Curvature at the point `y` -/

theorem isOpen_U (a : ℝ) : IsOpen {z : E4 | 0 < ksRadius a z} :=
  isOpen_lt continuous_const (continuous_ksRadius a)

theorem cp_chr (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (i j k c : Fin 4) :
    coordPartial (fun z => christoffel (kerrNewmanMetric m a e) z i j k) c y
      = coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2)
          (ksNull a w 3) (Wf a w) i j k) c y := by
  unfold coordPartial
  rw [Filter.EventuallyEq.fderiv_eq]
  filter_upwards [(isOpen_U a).mem_nhds hy] with z hz
  exact chr_closed m a e z hz i j k

theorem trace_cp_zero (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (σ ν : Fin 4) :
    ∑ ρ, coordPartial (fun z => christoffel (kerrNewmanMetric m a e) z ρ ρ σ) ν y = 0 := by
  simp only [cp_chr m a e y hy]
  have hsum : (fun w => ∑ ρ, Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2)
      (ksNull a w 3) (Wf a w) ρ ρ σ) =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_U a).mem_nhds hy] with z hz
    exact trGam a m e _ _ _ _ _ (ks_rel a z hz) (ks_W a z hz) σ
  have h1 := fderiv_fun_sum (𝕜 := ℝ) (u := Finset.univ) (x := y)
    (A := fun ρ w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3)
      (Wf a w) ρ ρ σ)
    (fun ρ _ => diff_tr m a e y hy ρ σ)
  unfold coordPartial
  rw [← ContinuousLinearMap.sum_apply, ← h1, hsum.fderiv_eq]
  simp

theorem ricci_eq (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (σ ν : Fin 4) :
    ricci (kerrNewmanMetric m a e) y σ ν
      = RicA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) σ ν := by
  have hrel := ks_rel a y hy
  have hW := ks_W a y hy
  unfold ricci riemann
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, trace_cp_zero m a e y hy σ ν]
  simp only [cp_chr m a e y hy, cp_div m a e y hy, chr_closed m a e y hy, Finset.sum_sub_distrib]
  have htr : ∑ ρ, ∑ l, Gam a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) ρ ρ l
      * Gam a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) l ν σ = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, trGam a m e _ _ _ _ _ hrel hW, zero_mul, Finset.sum_const_zero]
  rw [htr, ← ricS a m e _ _ _ _ _ hrel hW σ ν]
  unfold RicS
  ring

theorem scal_eq (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    scalarCurvature (kerrNewmanMetric m a e) y = 0 := by
  unfold scalarCurvature
  simp only [invMetric_eq m a e y hy, Matrix.of_apply, ricci_eq m a e y hy]
  exact scal_zero a m e _ _ _ _ _ (ks_rel a y hy) (ks_W a y hy)

theorem einstein_eq (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (μ ν : Fin 4) :
    einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = RicA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) μ ν := by
  unfold einsteinTensor
  rw [scal_eq m a e y hy, ricci_eq m a e y hy]
  ring

/-! ## The Maxwell side at `y` -/

theorem pot_eq (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    e * ksRadius a z ^ 3 / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) = HA a e (ksRadius a z) (Wf a z) := by
  rw [ks_x3 a z hz]
  unfold HA Wf
  have hR : ksRadius a z ≠ 0 := hz.ne'
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  field_simp
  try ring

theorem field_closed (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (μ ν : Fin 4) :
    kerrNewmanField a e y μ ν
      = FA a e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) μ ν := by
  have hH := hasCP_H a e y hy
  have hA : ∀ β, HasCP (fun w => kerrNewmanPotential a e w β) y
      (fun k => dHA a e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) k
          * ksNull a y β
        + e * ksRadius a y ^ 3 / (ksRadius a y ^ 4 + a ^ 2 * y 3 ^ 2)
          * dKt a (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) β k) :=
    fun β => hH.mul (hasCP_K a y hy β)
  show coordPartial (fun w => kerrNewmanPotential a e w ν) μ y
    - coordPartial (fun w => kerrNewmanPotential a e w μ) ν y = _
  rw [(hA ν).eq μ, (hA μ).eq ν, pot_eq a e y hy,
    ← fS a e _ _ _ _ _ (ks_rel a y hy) (ks_W a y hy) μ ν]
  simp only [FS, Kv, ← ksNull_eq_Kv a y]

theorem metric_closed (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (μ ν : Fin 4) :
    kerrNewmanMetric m a e y μ ν
      = gA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) μ ν := by
  show minkowski μ ν + ksProfile m a e y * ksNull a y μ * ksNull a y ν = _
  rw [profile_eq m a e y hy, minkowski_eq]
  simp only [gA, Kv, ← ksNull_eq_Kv a y]

theorem maxwell_eq (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (μ ν : Fin 4) :
    maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν
      = RicA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) μ ν := by
  have hrel := ks_rel a y hy
  have hW := ks_W a y hy
  have hraise : ∀ α β, raiseBoth (kerrNewmanMetric m a e) (kerrNewmanField a e) y α β
      = FupA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) α β := by
    intro α β
    unfold raiseBoth
    simp only [invMetric_eq m a e y hy, Matrix.of_apply, field_closed a e y hy]
    exact fU a m e _ _ _ _ _ hrel hW α β
  unfold maxwellSource
  simp only [hraise, invMetric_eq m a e y hy, Matrix.of_apply, field_closed a e y hy,
    metric_closed m a e y hy]
  rw [fF a m e _ _ _ _ _ hrel hW, ← tS a m e _ _ _ _ _ hrel hW μ ν]
  rfl

end NoHair.KNE

open NoHair in
theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν := by
  intro μ ν
  rw [NoHair.KNE.einstein_eq m a e y hy, NoHair.KNE.maxwell_eq m a e y hy]
