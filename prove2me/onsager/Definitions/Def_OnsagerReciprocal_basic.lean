import Mathlib

/-!
# Onsager reciprocal relations — basic objects (abstract formulation)

Source: Wikipedia, "Onsager reciprocal relations", section "Abstract formulation" and its
"Proof" subsection (oldid=1355014688), following Landau–Lifshitz, *Statistical Physics, Part 1*.

* `x = (x₁, …, xₙ)` are fluctuations from equilibrium, distributed with the (unnormalized)
  Gaussian weight `w(x) = exp(-½ βᵢₖ xᵢ xₖ)`.
* `Xᵢ = βᵢₖ xₖ` are the thermodynamic conjugate quantities.
* In the quasi-stationary regime `ẋ = -λ x`; the mean value of the fluctuation at time `t`,
  starting from the value `x₀` at `t = 0`, is `ξ(t) = exp(-t λ) x₀`, and `Ξ(t) = β ξ(t)`.
* `γ = λ β⁻¹` are the kinetic coefficients.
-/

namespace OnsagerReciprocal

open Matrix MeasureTheory

variable {n : ℕ}

/-- The unnormalized Gaussian fluctuation weight `w(x) = exp(-½ ∑ᵢₖ βᵢₖ xᵢ xₖ)`. -/
noncomputable def fluctuationWeight (β : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * (x ⬝ᵥ (β *ᵥ x)))

/-- The equilibrium average `⟨f⟩ = (∫ f(x) w(x) dx) / (∫ w(x) dx)` with respect to the
Gaussian fluctuation distribution (Lebesgue measure on `ℝⁿ`). -/
noncomputable def fluctuationAverage (β : Matrix (Fin n) (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫ x, f x * fluctuationWeight β x) / ∫ x, fluctuationWeight β x

/-- The thermodynamic conjugate quantities `Xᵢ = βᵢₖ xₖ`. -/
def conjugate (β : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  β *ᵥ x

/-- The mean value `ξ(t) = exp(-t λ) x₀` of the fluctuation at time `t`, given that it takes
the value `x₀` at `t = 0`; it is the solution of `ξ̇ = -λ ξ`, `ξ(0) = x₀`. -/
noncomputable def meanFluctuation (lam : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (x₀ : Fin n → ℝ) : Fin n → ℝ :=
  NormedSpace.exp ((-t) • lam) *ᵥ x₀

/-- The mean value `Ξ(t) = β ξ(t)` of the conjugate quantities at time `t`. -/
noncomputable def meanConjugate (β lam : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (x₀ : Fin n → ℝ) : Fin n → ℝ :=
  β *ᵥ meanFluctuation lam t x₀

/-- The kinetic coefficients `γ = λ β⁻¹`, i.e. `γᵢₖ = λᵢₗ (β⁻¹)ₗₖ`. -/
noncomputable def kineticCoeff (β lam : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  lam * β⁻¹

/-- The time correlation `⟨xᵢ(t) xₖ(0)⟩ = ⟨ξᵢ(t) xₖ⟩` in the equilibrium ensemble. -/
noncomputable def timeCorrelation (β lam : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (i k : Fin n) : ℝ :=
  fluctuationAverage β (fun x => meanFluctuation lam t x i * x k)

end OnsagerReciprocal
