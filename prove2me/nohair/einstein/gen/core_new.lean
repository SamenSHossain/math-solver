
namespace NoHair.KNE

/-! ## Atoms `R = r, K1, K2, K3` (components of `k`) on `U = {r > 0}` -/

theorem ks_x1 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    z 1 = ksRadius a z * ksNull a z 1 - a * ksNull a z 2 := by
  rw [ksNull_one, ksNull_two]
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem ks_x2 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    z 2 = a * ksNull a z 1 + ksRadius a z * ksNull a z 2 := by
  rw [ksNull_one, ksNull_two]
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem ks_x3 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    z 3 = ksRadius a z * ksNull a z 3 := by
  rw [ksNull_three]
  have hne : ksRadius a z ≠ 0 := hz.ne'
  field_simp

theorem ks_rel (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ksNull a z 1 ^ 2 + ksNull a z 2 ^ 2 + ksNull a z 3 ^ 2 = 1 := by
  have h := ks_null a z hz
  rw [ksNull_zero] at h
  linarith

theorem ksNull_eq_Kv (a : ℝ) (z : E4) :
    ksNull a z = ![1, ksNull a z 1, ksNull a z 2, ksNull a z 3] := by
  funext i
  fin_cases i <;> rfl

/-! ## Coordinate partials along lines -/

/-- `f` is differentiable at `z` with coordinate partials `d k`. -/
structure HasCP (f : E4 → ℝ) (z : E4) (d : Fin 4 → ℝ) : Prop where
  diff : DifferentiableAt ℝ f z
  line : ∀ k, HasDerivAt (fun t : ℝ => f (z + t • coordBasis k)) (d k) 0

namespace HasCP

variable {f g : E4 → ℝ} {z : E4} {df dg : Fin 4 → ℝ}

theorem eq (h : HasCP f z df) (k : Fin 4) : coordPartial f k z = df k :=
  fderiv_eq_of_line h.diff (h.line k)

theorem cst (c : ℝ) (z : E4) : HasCP (fun _ => c) z (fun _ => 0) :=
  ⟨differentiableAt_const c, fun _ => hasDerivAt_const _ c⟩

theorem add (hf : HasCP f z df) (hg : HasCP g z dg) :
    HasCP (fun w => f w + g w) z (fun k => df k + dg k) :=
  ⟨hf.diff.add hg.diff, fun k => (hf.line k).fun_add (hg.line k)⟩

theorem sub (hf : HasCP f z df) (hg : HasCP g z dg) :
    HasCP (fun w => f w - g w) z (fun k => df k - dg k) :=
  ⟨hf.diff.sub hg.diff, fun k => (hf.line k).fun_sub (hg.line k)⟩

theorem neg (hf : HasCP f z df) : HasCP (fun w => -f w) z (fun k => -df k) :=
  ⟨hf.diff.neg, fun k => (hf.line k).fun_neg⟩

theorem mul (hf : HasCP f z df) (hg : HasCP g z dg) :
    HasCP (fun w => f w * g w) z (fun k => df k * g z + f z * dg k) :=
  ⟨hf.diff.mul hg.diff, fun k => by
    have h := (hf.line k).fun_mul (hg.line k)
    simp only [zero_smul, add_zero] at h
    exact h⟩

theorem div (hf : HasCP f z df) (hg : HasCP g z dg) (hne : g z ≠ 0) :
    HasCP (fun w => f w / g w) z (fun k => (df k * g z - f z * dg k) / g z ^ 2) :=
  ⟨by have h1 := hf.diff; have h2 := hg.diff; fun_prop (disch := exact hne), fun k => by
    have h := (hf.line k).fun_div (hg.line k) (by simpa only [zero_smul, add_zero] using hne)
    simp only [zero_smul, add_zero] at h
    exact h⟩

theorem pow (hf : HasCP f z df) (n : ℕ) :
    HasCP (fun w => f w ^ n) z (fun k => (n : ℝ) * f z ^ (n - 1) * df k) :=
  ⟨hf.diff.pow n, fun k => by
    have h := (hf.line k).fun_pow n
    simp only [zero_smul, add_zero] at h
    exact h⟩

theorem of_fderiv (hd : DifferentiableAt ℝ f z) (h : ∀ k, fderiv ℝ f z (coordBasis k) = df k) :
    HasCP f z df :=
  ⟨hd, fun k => by
    have h1 : HasDerivAt (fun t : ℝ => z + t • coordBasis k) (coordBasis k) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coordBasis k)).const_add z
    have h2 : HasFDerivAt f (fderiv ℝ f z) (z + (0:ℝ) • coordBasis k) := by
      simpa using hd.hasFDerivAt
    have h3 := h2.comp_hasDerivAt (0:ℝ) h1
    rw [h k] at h3
    exact h3⟩

theorem congr_d (h : HasCP f z df) (hd : ∀ k, df k = dg k) : HasCP f z dg :=
  ⟨h.diff, fun k => (hd k) ▸ h.line k⟩

end HasCP

/-- Build a `HasCP` derivation of an explicit expression from atom facts in the context. -/
macro "hascp" : tactic => `(tactic| (repeat' (first
  | assumption
  | exact HasCP.cst _ _
  | apply HasCP.add
  | apply HasCP.sub
  | apply HasCP.neg
  | apply HasCP.mul
  | apply HasCP.pow
  | apply HasCP.div)))

theorem hasCP_coord (z : E4) (j : Fin 4) : HasCP (fun w => w j) z (fun k => coordBasis k j) :=
  ⟨by fun_prop, fun k => by simpa [line_apply] using hasDerivAt_line_coord z (coordBasis k) j⟩

/-- Coordinate partials vanish in the time direction for functions of the spatial atoms. -/
theorem time_shift (z : E4) (t : ℝ) (j : Fin 4) (hj : j ≠ 0) : (z + t • coordBasis 0) j = z j := by
  rw [line_apply]
  simp [coordBasis, hj]

theorem ksRadius_time (a : ℝ) (z : E4) (t : ℝ) : ksRadius a (z + t • coordBasis 0) = ksRadius a z := by
  simp only [ksRadius, time_shift z t 1 (by decide), time_shift z t 2 (by decide),
    time_shift z t 3 (by decide)]

theorem ksNull_time (a : ℝ) (z : E4) (t : ℝ) (i : Fin 4) : ksNull a (z + t • coordBasis 0) i = ksNull a z i := by
  simp only [ksNull, ksRadius_time, time_shift z t 1 (by decide), time_shift z t 2 (by decide),
    time_shift z t 3 (by decide)]

theorem cp_time (a : ℝ) (Φ : ℝ → ℝ → ℝ → ℝ → ℝ) (y : E4) :
    coordPartial (fun w => Φ (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3)) 0 y = 0 := by
  unfold coordPartial
  by_cases hd : DifferentiableAt ℝ (fun w => Φ (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3)) y
  · apply fderiv_eq_of_line hd
    simp only [ksRadius_time, ksNull_time]
    exact hasDerivAt_const _ _
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl
