import Mathlib

namespace TailRiskSharing.VaRConv

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.1 p. 5: atomless (classical sense; Mathlib's `NoAtoms` is only "singletons are null"). -/
def IsAtomless (P : Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < P s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < P t ∧ P t < P s

/-- §2.1 p. 5: distribution function `F_X(x) = P(X ≤ x)`. -/
noncomputable def distFn (P : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ := P.real {ω | X ω ≤ x}

/-- §2.2 p. 6: left VaR, `VaR^L_α(X) = inf {x | F_X(x) ≥ 1 - α}` (small-α convention). -/
noncomputable def VaRL (P : Measure Ω) (α : ℝ) (X : Ω → ℝ) : ℝ := sInf {x | 1 - α ≤ distFn P X x}

/-- §2.2 p. 6: right VaR, `VaR^R_α(X) = inf {x | F_X(x) > 1 - α}`. -/
noncomputable def VaRR (P : Measure Ω) (α : ℝ) (X : Ω → ℝ) : ℝ := sInf {x | 1 - α < distFn P X x}

/-- §2.1 p. 5: the domain `L⁰` of all (measurable) random variables. -/
def L0 : Set (Ω → ℝ) := {X | Measurable X}

/-- (4), p. 7: the allocations `A_n(X)` of `X` (pointwise sum). -/
def Allocations (dom : Set (Ω → ℝ)) (n : ℕ) (X : Ω → ℝ) : Set (Fin n → Ω → ℝ) :=
  {Xs | (∀ i, Xs i ∈ dom) ∧ ∀ ω, ∑ i, Xs i ω = X ω}

/-- (5), p. 7: the inf-convolution `□ᵢ ρᵢ (X)`, valued in `[-∞, ∞]`. -/
noncomputable def infConv (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) :
    EReal :=
  ⨅ Xs ∈ Allocations dom n X, ((∑ i, ρ i (Xs i) : ℝ) : EReal)

/-- p. 7: `Xs` is an optimal allocation of `X` for `(ρ₁, …, ρₙ)`. -/
def IsOptimalAllocation (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ)
    (Xs : Fin n → Ω → ℝ) : Prop :=
  Xs ∈ Allocations dom n X ∧ ((∑ i, ρ i (Xs i) : ℝ) : EReal) = infConv dom ρ X

/-- (5), p. 7, for two agents of which the first may take the value `-∞` (footnote 2, p. 5):
`(F □ ρ)(X) = inf {F(Y) + ρ(Z) : Y, Z ∈ 𝒳, Y + Z = X}`. It is the iterated inf-convolution
`(ρ₁ □ ⋯ □ ρₙ₋₁) □ ρₙ` of the proof of Theorem 1(i), p. 10. Since `ρ` is real-valued, the sum
`F(Y) + ρ(Z)` never meets the undefined form `-∞ + ∞`. -/
noncomputable def infConv2E (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) (ρ : (Ω → ℝ) → ℝ)
    (X : Ω → ℝ) : EReal :=
  ⨅ YZ ∈ {YZ : (Ω → ℝ) × (Ω → ℝ) | YZ.1 ∈ dom ∧ YZ.2 ∈ dom ∧ ∀ ω, YZ.1 ω + YZ.2 ω = X ω},
    F YZ.1 + ((ρ YZ.2 : ℝ) : EReal)

/-- §3 p. 9: the two versions of VaR, `Λ ∈ {L, R}`. -/
inductive Side
  | L
  | R
  deriving DecidableEq

/-- §3 p. 9: `VaR^Λ_α` for `Λ ∈ {L, R}`. -/
noncomputable def VaRS (P : Measure Ω) : Side → ℝ → (Ω → ℝ) → ℝ
  | .L => VaRL P
  | .R => VaRR P

/-- Theorem 1(i), p. 9: `Λ = L` if `Λ₁ = ⋯ = Λₙ = L`, and `Λ = R` otherwise. -/
def aggSide {n : ℕ} (Λs : Fin n → Side) : Side :=
  if ∀ i, Λs i = Side.L then Side.L else Side.R

/-- Theorem 1(ii), p. 9: `(A₁, …, Aₙ)` is a (measurable) partition of `Ω`: measurable, pairwise
disjoint, with union `Ω`. Some `Aᵢ` may be empty. -/
def IsMeasPartition {n : ℕ} (A : Fin n → Set Ω) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧ (⋃ i, A i) = Set.univ

/-- (9), p. 9: the allocation `Xᵢ = (X - v) 1_{Aᵢ} + v / n`, `i = 1, …, n`, where `v` is meant to be
`VaR^Λ_α(X)`. -/
noncomputable def partitionAllocation {n : ℕ} (X : Ω → ℝ) (v : ℝ) (A : Fin n → Set Ω) :
    Fin n → Ω → ℝ :=
  fun i ω => (X ω - v) * (A i).indicator 1 ω + v / n

end TailRiskSharing.VaRConv
