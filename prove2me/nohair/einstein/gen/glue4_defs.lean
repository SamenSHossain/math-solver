
/-! ## Algebraic building blocks (polynomials in the atoms `R K1 K2 K3 W`) -/

/-- Minkowski components as an explicit table. -/
noncomputable def etaT : Fin 4 → Fin 4 → ℝ :=
  ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

theorem minkowski_eq (i l : Fin 4) : minkowski i l = etaT i l := by
  fin_cases i <;> fin_cases l <;> simp [minkowski, etaT]

/-- `k_μ` in atom form. -/
noncomputable def Kv (K1 K2 K3 : ℝ) : Fin 4 → ℝ := ![1, K1, K2, K3]
/-- `k^μ = η^{μν} k_ν` in atom form. -/
noncomputable def Ks (K1 K2 K3 : ℝ) : Fin 4 → ℝ := ![-1, K1, K2, K3]
/-- The Kerr–Schild profile `f = (2 m r - e²) W`. -/
noncomputable def fA (a m e R W : ℝ) : ℝ := (2 * m * R - e ^ 2) * W
/-- `∂_j g_{lk}` (`dgA l k j`). -/
noncomputable def dgA (a m e R K1 K2 K3 W : ℝ) (l k j : Fin 4) : ℝ :=
  dfA a m e R K1 K2 K3 W j * Kv K1 K2 K3 l * Kv K1 K2 K3 k
    + fA a m e R W * dKt a R K1 K2 K3 W l j * Kv K1 K2 K3 k
    + fA a m e R W * Kv K1 K2 K3 l * dKt a R K1 K2 K3 W k j
/-- Inverse metric `g^{il} = η^{il} - f k^i k^l`. -/
noncomputable def ginvA (a m e R K1 K2 K3 W : ℝ) (i l : Fin 4) : ℝ :=
  etaT i l - fA a m e R W * Ks K1 K2 K3 i * Ks K1 K2 K3 l
/-- The Christoffel formula on atom data. -/
noncomputable def chrS (a m e R K1 K2 K3 W : ℝ) (i j k : Fin 4) : ℝ :=
  ∑ l, (1 / 2 : ℝ) * ginvA a m e R K1 K2 K3 W i l *
    (dgA a m e R K1 K2 K3 W l k j + dgA a m e R K1 K2 K3 W l j k - dgA a m e R K1 K2 K3 W j k l)

theorem chrS_symm (a m e R K1 K2 K3 W : ℝ) (i j k : Fin 4) :
    chrS a m e R K1 K2 K3 W i j k = chrS a m e R K1 K2 K3 W i k j := by
  unfold chrS
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold dgA
  ring

/-- Ricci tensor from closed-form Christoffel data (the trace term vanishes). -/
noncomputable def RicS (a m e R K1 K2 K3 W : ℝ) (σ ν : Fin 4) : ℝ :=
  ∑ ρ, dDivT a m e R K1 K2 K3 W ρ ν σ
    - ∑ ρ, ∑ l, Gam a m e R K1 K2 K3 W ρ ν l * Gam a m e R K1 K2 K3 W l ρ σ

/-- `H = e r W`, the potential factor `A = H k`. -/
noncomputable def HA (a e R W : ℝ) : ℝ := e * R * W

/-- `F_{μν} = ∂_μ (H k_ν) - ∂_ν (H k_μ)` on atom data. -/
noncomputable def FS (a e R K1 K2 K3 W : ℝ) (μ ν : Fin 4) : ℝ :=
  (dHA a e R K1 K2 K3 W μ * Kv K1 K2 K3 ν + HA a e R W * dKt a R K1 K2 K3 W ν μ)
    - (dHA a e R K1 K2 K3 W ν * Kv K1 K2 K3 μ + HA a e R W * dKt a R K1 K2 K3 W μ ν)

/-- Metric `g_{μν} = η_{μν} + f k_μ k_ν` on atom data. -/
noncomputable def gA (a m e R K1 K2 K3 W : ℝ) (μ ν : Fin 4) : ℝ :=
  etaT μ ν + fA a m e R W * Kv K1 K2 K3 μ * Kv K1 K2 K3 ν

/-- The Maxwell source on atom data. -/
noncomputable def TS (a m e R K1 K2 K3 W : ℝ) (μ ν : Fin 4) : ℝ :=
  2 * ((∑ α, ∑ β, FA a e R K1 K2 K3 W μ α * ginvA a m e R K1 K2 K3 W α β * FA a e R K1 K2 K3 W ν β)
    - (1 / 4 : ℝ) * gA a m e R K1 K2 K3 W μ ν * FFA a m e R K1 K2 K3 W)
