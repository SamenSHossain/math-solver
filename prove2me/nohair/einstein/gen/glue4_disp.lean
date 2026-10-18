theorem chrS_Gam (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (i j k : Fin 4) :
    chrS a m e R K1 K2 K3 W i j k = Gam a m e R K1 K2 K3 W i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact chrS_Gam_000 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_001 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_002 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_003 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_001 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_011 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_012 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_013 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_002 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_012 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_022 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_023 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_003 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_013 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_023 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_033 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_100 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_101 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_102 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_103 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_101 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_111 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_112 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_113 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_102 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_112 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_122 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_123 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_103 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_113 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_123 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_133 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_200 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_201 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_202 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_203 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_201 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_211 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_212 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_213 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_202 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_212 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_222 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_223 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_203 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_213 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_223 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_233 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_300 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_301 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_302 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_303 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_301 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_311 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_312 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_313 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_302 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_312 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_322 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_323 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_303 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_313 a m e R K1 K2 K3 W hrel hW
  · rw [chrS_symm]; exact chrS_Gam_323 a m e R K1 K2 K3 W hrel hW
  · exact chrS_Gam_333 a m e R K1 K2 K3 W hrel hW

theorem chr_closed (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i j k : Fin 4) :
    christoffel (kerrNewmanMetric m a e) z i j k
      = Gam a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) i j k := by
  rw [chr_eq m a e z hz]
  exact chrS_Gam a m e _ _ _ _ _ (ks_rel a z hz) (ks_W a z hz) i j k

theorem cp_div (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (ρ ν σ : Fin 4) :
    coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) ρ ν σ) ρ y = dDivT a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) ρ ν σ := by
  fin_cases ρ <;> fin_cases ν <;> fin_cases σ <;> simp only [Gam, dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact cp_time a (fun R K1 K2 K3 => G000 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G001 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G002 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G003 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G001 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G011 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G012 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G013 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G002 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G012 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G022 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G023 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G003 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G013 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G023 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact cp_time a (fun R K1 K2 K3 => G033 a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2))) y
  · exact (dG100 m a e y hy).2
  · exact (dG101 m a e y hy).2
  · exact (dG102 m a e y hy).2
  · exact (dG103 m a e y hy).2
  · exact (dG101 m a e y hy).2
  · exact (dG111 m a e y hy).2
  · exact (dG112 m a e y hy).2
  · exact (dG113 m a e y hy).2
  · exact (dG102 m a e y hy).2
  · exact (dG112 m a e y hy).2
  · exact (dG122 m a e y hy).2
  · exact (dG123 m a e y hy).2
  · exact (dG103 m a e y hy).2
  · exact (dG113 m a e y hy).2
  · exact (dG123 m a e y hy).2
  · exact (dG133 m a e y hy).2
  · exact (dG200 m a e y hy).2
  · exact (dG201 m a e y hy).2
  · exact (dG202 m a e y hy).2
  · exact (dG203 m a e y hy).2
  · exact (dG201 m a e y hy).2
  · exact (dG211 m a e y hy).2
  · exact (dG212 m a e y hy).2
  · exact (dG213 m a e y hy).2
  · exact (dG202 m a e y hy).2
  · exact (dG212 m a e y hy).2
  · exact (dG222 m a e y hy).2
  · exact (dG223 m a e y hy).2
  · exact (dG203 m a e y hy).2
  · exact (dG213 m a e y hy).2
  · exact (dG223 m a e y hy).2
  · exact (dG233 m a e y hy).2
  · exact (dG300 m a e y hy).2
  · exact (dG301 m a e y hy).2
  · exact (dG302 m a e y hy).2
  · exact (dG303 m a e y hy).2
  · exact (dG301 m a e y hy).2
  · exact (dG311 m a e y hy).2
  · exact (dG312 m a e y hy).2
  · exact (dG313 m a e y hy).2
  · exact (dG302 m a e y hy).2
  · exact (dG312 m a e y hy).2
  · exact (dG322 m a e y hy).2
  · exact (dG323 m a e y hy).2
  · exact (dG303 m a e y hy).2
  · exact (dG313 m a e y hy).2
  · exact (dG323 m a e y hy).2
  · exact (dG333 m a e y hy).2

theorem diff_tr (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (ρ σ : Fin 4) :
    DifferentiableAt ℝ (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) ρ ρ σ) y := by
  fin_cases ρ <;> fin_cases σ <;> simp only [Gam, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact dG000 m a e y hy
  · exact dG001 m a e y hy
  · exact dG002 m a e y hy
  · exact dG003 m a e y hy
  · exact (dG101 m a e y hy).1
  · exact (dG111 m a e y hy).1
  · exact (dG112 m a e y hy).1
  · exact (dG113 m a e y hy).1
  · exact (dG202 m a e y hy).1
  · exact (dG212 m a e y hy).1
  · exact (dG222 m a e y hy).1
  · exact (dG223 m a e y hy).1
  · exact (dG303 m a e y hy).1
  · exact (dG313 m a e y hy).1
  · exact (dG323 m a e y hy).1
  · exact (dG333 m a e y hy).1
theorem trGam (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (σ : Fin 4) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ σ = 0 := by
  fin_cases σ
  · exact trGam_0 a m e R K1 K2 K3 W hrel hW
  · exact trGam_1 a m e R K1 K2 K3 W hrel hW
  · exact trGam_2 a m e R K1 K2 K3 W hrel hW
  · exact trGam_3 a m e R K1 K2 K3 W hrel hW

theorem Gam_symm (a m e R K1 K2 K3 W : ℝ) (i j k : Fin 4) : Gam a m e R K1 K2 K3 W i j k = Gam a m e R K1 K2 K3 W i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

theorem dDivT_symm (a m e R K1 K2 K3 W : ℝ) (i j k : Fin 4) : dDivT a m e R K1 K2 K3 W i j k = dDivT a m e R K1 K2 K3 W i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]

theorem RicA_symm (a m e R K1 K2 K3 W : ℝ) (i j : Fin 4) : RicA a m e R K1 K2 K3 W i j = RicA a m e R K1 K2 K3 W j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem RicS_symm (a m e R K1 K2 K3 W : ℝ) (σ ν : Fin 4) : RicS a m e R K1 K2 K3 W σ ν = RicS a m e R K1 K2 K3 W ν σ := by
  unfold RicS
  congr 1
  · exact Finset.sum_congr rfl (fun ρ _ => dDivT_symm a m e R K1 K2 K3 W ρ ν σ)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [Gam_symm a m e R K1 K2 K3 W p σ q, Gam_symm a m e R K1 K2 K3 W q p ν]
    ring

theorem ricS (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    RicS a m e R K1 K2 K3 W μ ν = RicA a m e R K1 K2 K3 W μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact ricS_00 a m e R K1 K2 K3 W hrel hW
  · exact ricS_01 a m e R K1 K2 K3 W hrel hW
  · exact ricS_02 a m e R K1 K2 K3 W hrel hW
  · exact ricS_03 a m e R K1 K2 K3 W hrel hW
  · rw [RicS_symm, RicA_symm]; exact ricS_01 a m e R K1 K2 K3 W hrel hW
  · exact ricS_11 a m e R K1 K2 K3 W hrel hW
  · exact ricS_12 a m e R K1 K2 K3 W hrel hW
  · exact ricS_13 a m e R K1 K2 K3 W hrel hW
  · rw [RicS_symm, RicA_symm]; exact ricS_02 a m e R K1 K2 K3 W hrel hW
  · rw [RicS_symm, RicA_symm]; exact ricS_12 a m e R K1 K2 K3 W hrel hW
  · exact ricS_22 a m e R K1 K2 K3 W hrel hW
  · exact ricS_23 a m e R K1 K2 K3 W hrel hW
  · rw [RicS_symm, RicA_symm]; exact ricS_03 a m e R K1 K2 K3 W hrel hW
  · rw [RicS_symm, RicA_symm]; exact ricS_13 a m e R K1 K2 K3 W hrel hW
  · rw [RicS_symm, RicA_symm]; exact ricS_23 a m e R K1 K2 K3 W hrel hW
  · exact ricS_33 a m e R K1 K2 K3 W hrel hW

theorem fS (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    FS a e R K1 K2 K3 W μ ν = FA a e R K1 K2 K3 W μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact fS_00 a e R K1 K2 K3 W hrel hW
  · exact fS_01 a e R K1 K2 K3 W hrel hW
  · exact fS_02 a e R K1 K2 K3 W hrel hW
  · exact fS_03 a e R K1 K2 K3 W hrel hW
  · exact fS_10 a e R K1 K2 K3 W hrel hW
  · exact fS_11 a e R K1 K2 K3 W hrel hW
  · exact fS_12 a e R K1 K2 K3 W hrel hW
  · exact fS_13 a e R K1 K2 K3 W hrel hW
  · exact fS_20 a e R K1 K2 K3 W hrel hW
  · exact fS_21 a e R K1 K2 K3 W hrel hW
  · exact fS_22 a e R K1 K2 K3 W hrel hW
  · exact fS_23 a e R K1 K2 K3 W hrel hW
  · exact fS_30 a e R K1 K2 K3 W hrel hW
  · exact fS_31 a e R K1 K2 K3 W hrel hW
  · exact fS_32 a e R K1 K2 K3 W hrel hW
  · exact fS_33 a e R K1 K2 K3 W hrel hW

theorem fU (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    ∑ α, ∑ β, ginvA a m e R K1 K2 K3 W μ α * ginvA a m e R K1 K2 K3 W ν β * FA a e R K1 K2 K3 W α β = FupA a m e R K1 K2 K3 W μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact fU_00 a m e R K1 K2 K3 W hrel hW
  · exact fU_01 a m e R K1 K2 K3 W hrel hW
  · exact fU_02 a m e R K1 K2 K3 W hrel hW
  · exact fU_03 a m e R K1 K2 K3 W hrel hW
  · exact fU_10 a m e R K1 K2 K3 W hrel hW
  · exact fU_11 a m e R K1 K2 K3 W hrel hW
  · exact fU_12 a m e R K1 K2 K3 W hrel hW
  · exact fU_13 a m e R K1 K2 K3 W hrel hW
  · exact fU_20 a m e R K1 K2 K3 W hrel hW
  · exact fU_21 a m e R K1 K2 K3 W hrel hW
  · exact fU_22 a m e R K1 K2 K3 W hrel hW
  · exact fU_23 a m e R K1 K2 K3 W hrel hW
  · exact fU_30 a m e R K1 K2 K3 W hrel hW
  · exact fU_31 a m e R K1 K2 K3 W hrel hW
  · exact fU_32 a m e R K1 K2 K3 W hrel hW
  · exact fU_33 a m e R K1 K2 K3 W hrel hW

theorem tS (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    TS a m e R K1 K2 K3 W μ ν = RicA a m e R K1 K2 K3 W μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact tS_00 a m e R K1 K2 K3 W hrel hW
  · exact tS_01 a m e R K1 K2 K3 W hrel hW
  · exact tS_02 a m e R K1 K2 K3 W hrel hW
  · exact tS_03 a m e R K1 K2 K3 W hrel hW
  · exact tS_10 a m e R K1 K2 K3 W hrel hW
  · exact tS_11 a m e R K1 K2 K3 W hrel hW
  · exact tS_12 a m e R K1 K2 K3 W hrel hW
  · exact tS_13 a m e R K1 K2 K3 W hrel hW
  · exact tS_20 a m e R K1 K2 K3 W hrel hW
  · exact tS_21 a m e R K1 K2 K3 W hrel hW
  · exact tS_22 a m e R K1 K2 K3 W hrel hW
  · exact tS_23 a m e R K1 K2 K3 W hrel hW
  · exact tS_30 a m e R K1 K2 K3 W hrel hW
  · exact tS_31 a m e R K1 K2 K3 W hrel hW
  · exact tS_32 a m e R K1 K2 K3 W hrel hW
  · exact tS_33 a m e R K1 K2 K3 W hrel hW
