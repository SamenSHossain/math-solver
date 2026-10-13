import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- The decision space `ℝⁿ` of problem (1.1) (Ghadimi & Lan, arXiv:1309.5549v1, p. 2), with its
Euclidean inner product `⟪·, ·⟫_ℝ` and norm `‖·‖`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- A run of the randomized stochastic gradient (RSG) method, recursion (2.2)
(arXiv:1309.5549v1, §2.1, p. 5): on a sample space `Ω`, with noise variables `ξ k : Ω → Ξ`,
stochastic gradient oracle `G : ℝⁿ → Ξ → ℝⁿ`, stepsizes `γ` and initial point `x1`, the iterates
satisfy `x 1 = x1` and `x (k + 1) = x k − γ k • G (x k) (ξ k)` for every `k ≥ 1`, pointwise in
`ω`. Indices are 1-based as in the paper; `x 0` and `ξ 0` are unused and carry no condition. The
paper stops at step `R`; the iterates up to `x R` do not depend on whether the recursion is
continued beyond `R`, so the full trajectory is recorded. -/
def IsRSGRun {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (γ : ℕ → ℝ) (x1 : E n)
    (ξ : ℕ → Ω → Ξ) (x : ℕ → Ω → E n) : Prop :=
  (∀ ω, x 1 ω = x1) ∧ ∀ k : ℕ, 1 ≤ k → ∀ ω, x (k + 1) ω = x k ω - γ k • G (x k ω) (ξ k ω)

/-- The oracle error `δ_k = G(x_k, ξ_k) − ∇f(x_k)` (arXiv:1309.5549v1, proof of Theorem 2.1,
p. 6), where `g` is the gradient map `∇f`. -/
def rsgNoise {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (g : E n → E n) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → E n) (k : ℕ) (ω : Ω) : E n :=
  G (x k ω) (ξ k ω) - g (x k ω)

/-- The probability mass function (2.3) of the random output index (arXiv:1309.5549v1,
Theorem 2.1, p. 6): `P_R(k) = (2γ_k − Lγ_k²) / Σ_{j=1}^N (2γ_j − Lγ_j²)`. It is meant for
`k ∈ {1, …, N}`; the theorems that use it assume `0 < γ_k < 2/L` and `N ≥ 1`, which make the
denominator positive. -/
noncomputable def rsgPMF (L : ℝ) (γ : ℕ → ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  (2 * γ k - L * γ k ^ 2) / ∑ j ∈ Finset.Icc 1 N, (2 * γ j - L * γ j ^ 2)

/-- Assumption A1 (arXiv:1309.5549v1, p. 2, Eqs. (1.2)–(1.3)) along an RSG trajectory `x`, with
gradient map `g = ∇f`, oracle `G`, noise `ξ`, filtration `ℱ` on `Ω` and noise level `σ ≥ 0`.
For every `k ≥ 1`:
* `ξ k` is `ℱ k`-measurable (the noise is adapted; `ℱ (k-1)` plays the role of the history
  `ξ_[k-1]`);
* (1.2), in the conditional form used by (2.10): `G(x_k, ξ_k)` is integrable and
  `E[G(x_k, ξ_k) | ℱ_{k-1}] = ∇f(x_k)` almost surely;
* (1.3): `‖G(x_k, ξ_k) − ∇f(x_k)‖²` is integrable with expectation at most `σ²`.

The noise variables need not be independent, and may depend on the past iterates, as the paper
stresses. Any filtration to which `ξ` is adapted is admissible; the natural one
`ℱ k = σ(ξ_1, …, ξ_k)` (with `ℱ 0` trivial) is the paper's. -/
structure AssumptionA1 {n : ℕ} {Ω Ξ : Type*} [m : MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (g : E n → E n) (G : E n → Ξ → E n)
    (ξ : ℕ → Ω → Ξ) (x : ℕ → Ω → E n) (σ : ℝ) : Prop where
  sigma_nonneg : 0 ≤ σ
  adapted : ∀ k : ℕ, 1 ≤ k → Measurable[ℱ k] (ξ k)
  integrable_oracle : ∀ k : ℕ, 1 ≤ k → Integrable (fun ω => G (x k ω) (ξ k ω)) μ
  unbiased : ∀ k : ℕ, 1 ≤ k →
    μ[fun ω => G (x k ω) (ξ k ω) | ℱ (k - 1)] =ᵐ[μ] fun ω => g (x k ω)
  integrable_sq_error : ∀ k : ℕ, 1 ≤ k →
    Integrable (fun ω => ‖G (x k ω) (ξ k ω) - g (x k ω)‖ ^ 2) μ
  variance_bound : ∀ k : ℕ, 1 ≤ k →
    ∫ ω, ‖G (x k ω) (ξ k ω) - g (x k ω)‖ ^ 2 ∂μ ≤ σ ^ 2

/-- The random output index `R` of the RSG method (arXiv:1309.5549v1, §2.1, Step 0, p. 5, and
(2.3), p. 6): `R : Ω → ℕ` is measurable, takes values in `{1, …, N}`, and
`Prob{R = k} = P_R(k)` for `k = 1, …, N`, with `P_R` the mass function (2.3). Independence of `R`
from the noise is a separate hypothesis of the theorems that use `R`. -/
def IsRandomOutputIndex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R : Ω → ℕ) (L : ℝ)
    (γ : ℕ → ℝ) (N : ℕ) : Prop :=
  Measurable R ∧ (∀ ω, R ω ∈ Finset.Icc 1 N) ∧
    ∀ k ∈ Finset.Icc 1 N, μ {ω | R ω = k} = ENNReal.ofReal (rsgPMF L γ N k)

/-- The constant `D_f = [2(f(x_1) − f*)/L]^{1/2}` of (2.5) (arXiv:1309.5549v1, p. 6). -/
noncomputable def Df {n : ℕ} (f : E n → ℝ) (x1 : E n) (fstar L : ℝ) : ℝ :=
  Real.sqrt (2 * (f x1 - fstar) / L)

/-- The constant `D_X = ‖x_1 − x*‖` of (2.7) (arXiv:1309.5549v1, p. 6). -/
noncomputable def DX {n : ℕ} (x1 xstar : E n) : ℝ :=
  ‖x1 - xstar‖

end GhadimiLan.RSG
