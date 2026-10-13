/-
Kerr–Newman satisfies the Einstein equation (Kerr–Schild coordinates): block Assembly.
Assembly: the trace of the Christoffel symbols vanishes, the Ricci tensor and scalar curvature at a point with r > 0, and the Einstein equation G_{μν} = 2 (F_{μα} F_ν^α - ¼ g_{μν} F²).
The development is split into parts only so that each piece compiles within the platform limits.
-/
import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Christoffel
import Definitions.Def_NoHair_KerrNewmanEinstein_Div1
import Definitions.Def_NoHair_KerrNewmanEinstein_Div2
import Definitions.Def_NoHair_KerrNewmanEinstein_Div3
import Definitions.Def_NoHair_KerrNewmanEinstein_Div4
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci1
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci2
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci3
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci4
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci5
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci6
import Definitions.Def_NoHair_KerrNewmanEinstein_MaxwellF
import Definitions.Def_NoHair_KerrNewmanEinstein_MaxwellT

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

open scoped BigOperators
open NoHair

namespace NoHair.KNE

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

theorem trGam_0 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ 0 = 0 := by
  simp only [Gam, G000, G101, G202, G303, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-2 * R ^ (3 : ℕ) * W ^ (3 : ℕ) * m ^ (2 : ℕ) + 3 * R ^ (2 : ℕ) * W ^ (3 : ℕ) * m * e ^ (2 : ℕ) + 2 * R * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m ^ (2 : ℕ) - R * W ^ (3 : ℕ) * e ^ (4 : ℕ) - K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ))) * hrel + (0) * hW

theorem trGam_1 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ 1 = 0 := by
  simp only [Gam, G001, G111, G212, G313, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-3 * R ^ (4 : ℕ) * K1 * W ^ (3 : ℕ) * m - 2 * R ^ (3 : ℕ) * K1 * W ^ (3 : ℕ) * m ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * K1 * W ^ (3 : ℕ) * e ^ (2 : ℕ) + R ^ (3 : ℕ) * K2 * W ^ (3 : ℕ) * a * m + R ^ (2 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m + 3 * R ^ (2 : ℕ) * K1 * W ^ (3 : ℕ) * m * e ^ (2 : ℕ) - R ^ (2 : ℕ) * K2 * W ^ (3 : ℕ) * a * e ^ (2 : ℕ) + 2 * R * K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m ^ (2 : ℕ) - R * K1 * W ^ (3 : ℕ) * e ^ (4 : ℕ) - 3 * R * K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * m - K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ) + K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * e ^ (2 : ℕ))) * hrel + (0) * hW

theorem trGam_2 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ 2 = 0 := by
  simp only [Gam, G002, G112, G222, G323, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-3 * R ^ (4 : ℕ) * K2 * W ^ (3 : ℕ) * m - R ^ (3 : ℕ) * K1 * W ^ (3 : ℕ) * a * m - 2 * R ^ (3 : ℕ) * K2 * W ^ (3 : ℕ) * m ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * K2 * W ^ (3 : ℕ) * e ^ (2 : ℕ) + R ^ (2 : ℕ) * K1 * W ^ (3 : ℕ) * a * e ^ (2 : ℕ) + R ^ (2 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m + 3 * R ^ (2 : ℕ) * K2 * W ^ (3 : ℕ) * m * e ^ (2 : ℕ) + 3 * R * K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * m + 2 * R * K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m ^ (2 : ℕ) - R * K2 * W ^ (3 : ℕ) * e ^ (4 : ℕ) - K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * e ^ (2 : ℕ) - K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ))) * hrel + (0) * hW

theorem trGam_3 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ 3 = 0 := by
  simp only [Gam, G003, G113, G223, G333, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-3 * R ^ (4 : ℕ) * K3 * W ^ (3 : ℕ) * m - 2 * R ^ (3 : ℕ) * K3 * W ^ (3 : ℕ) * m ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * K3 * W ^ (3 : ℕ) * e ^ (2 : ℕ) + R ^ (2 : ℕ) * K3 ^ (3 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m - 3 * R ^ (2 : ℕ) * K3 * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m + 3 * R ^ (2 : ℕ) * K3 * W ^ (3 : ℕ) * m * e ^ (2 : ℕ) + 2 * R * K3 ^ (3 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m ^ (2 : ℕ) + 2 * R * K3 * W ^ (3 : ℕ) * a ^ (2 : ℕ) * e ^ (2 : ℕ) - R * K3 * W ^ (3 : ℕ) * e ^ (4 : ℕ) + K3 ^ (3 : ℕ) * W ^ (3 : ℕ) * a ^ (4 : ℕ) * m - K3 ^ (3 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ))) * hrel + (0) * hW

theorem scal_zero (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ σ, ∑ ν, ginvA a m e R K1 K2 K3 W σ ν * RicA a m e R K1 K2 K3 W σ ν = 0 := by
  simp only [ginvA, RicA, Ks, fA, etaT, Ric00, Ric01, Ric02, Ric03, Ric11, Ric12, Ric13, Ric22, Ric23, Ric33, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((4 * R ^ (3 : ℕ) * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * m * e ^ (2 : ℕ) + 4 * R ^ (3 : ℕ) * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * m * e ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * W ^ (4 : ℕ) * m * e ^ (2 : ℕ) - 8 * R ^ (2 : ℕ) * K1 * K2 * W ^ (4 : ℕ) * a * m * e ^ (2 : ℕ) + 4 * R ^ (2 : ℕ) * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * m ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (2 : ℕ) * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (4 : ℕ) + 4 * R ^ (2 : ℕ) * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * m ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (2 : ℕ) * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (4 : ℕ) - 4 * R ^ (2 : ℕ) * W ^ (4 : ℕ) * m ^ (2 : ℕ) * e ^ (2 : ℕ) - R ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (4 : ℕ) + 4 * R * K1 * K2 * W ^ (4 : ℕ) * a * e ^ (4 : ℕ) - 4 * R * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ) - 4 * R * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * m * e ^ (4 : ℕ) + 2 * R * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ) - 4 * R * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * m * e ^ (4 : ℕ) + 4 * R * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ) + 4 * R * W ^ (4 : ℕ) * m * e ^ (4 : ℕ) + 2 * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (4 : ℕ) + K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (6 : ℕ) - K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (4 : ℕ) + K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (6 : ℕ) - 2 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (4 : ℕ) - W ^ (4 : ℕ) * e ^ (6 : ℕ))) * hrel + (0) * hW

theorem trGam (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (σ : Fin 4) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ σ = 0 := by
  fin_cases σ
  · exact trGam_0 a m e R K1 K2 K3 W hrel hW
  · exact trGam_1 a m e R K1 K2 K3 W hrel hW
  · exact trGam_2 a m e R K1 K2 K3 W hrel hW
  · exact trGam_3 a m e R K1 K2 K3 W hrel hW

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


/-- The Einstein equation for the Kerr–Newman metric in Kerr–Schild coordinates (wherever `r > 0`). -/
theorem kerrNewman_einstein_holds (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν := by
  intro μ ν
  rw [einstein_eq m a e y hy, maxwell_eq m a e y hy]

end NoHair.KNE
