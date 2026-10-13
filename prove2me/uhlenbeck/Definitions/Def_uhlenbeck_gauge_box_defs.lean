import Mathlib

/-!
# Definitions for the mission "Uhlenbeck, Equations of Gauge Theory I"

Source: K. Uhlenbeck, *Equations of Gauge Theory*, notes by L. Fredrickson
(Grosswald lectures, Temple University, 2012), Section 3.1, pp. 29–32.

Everything is set on the trivial `SU(n)`-bundle over (a closed box in) `ℝ⁴` with the
Euclidean metric.  A connection is `d + A` with `A = ∑ μ, A μ dx^μ`, each `A μ` taking values
in `su(n)` (traceless skew-Hermitian `n × n` complex matrices).  A Lie-algebra-valued two-form
at a point is stored through its coefficient family `F μ ν` (so `F = ∑_{μ<ν} F μ ν dx^μ ∧ dx^ν`).
-/

open scoped Matrix ContDiff

namespace UhlenbeckGauge

/-- Euclidean four-space, with coordinates `x 0, x 1, x 2, x 3`. -/
abbrev R4 : Type := Fin 4 → ℝ

/-- `n × n` complex matrices. -/
abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

/-- Membership in the Lie algebra `su(n)`: skew-Hermitian and traceless. -/
def IsSuN {n : ℕ} (X : Mat n) : Prop :=
  Xᴴ = -X ∧ Matrix.trace X = 0

/-- The Levi-Civita symbol `ε_{μνρσ}` on `Fin 4`: the determinant of the matrix whose rows are the
standard basis vectors `e_μ, e_ν, e_ρ, e_σ`.  It is the sign of the permutation `(μ ν ρ σ)` when
the indices are distinct, and `0` otherwise; `ε_{0123} = 1`. -/
def levi (μ ν ρ σ : Fin 4) : ℂ :=
  ((Matrix.of fun i : Fin 4 => (Pi.single (![μ, ν, ρ, σ] i) (1 : ℤ) : Fin 4 → ℤ)).det : ℂ)

/-- A matrix-valued two-form at a point of `ℝ⁴`, stored by its coefficients `F μ ν`. -/
abbrev TwoForm (n : ℕ) : Type := Fin 4 → Fin 4 → Mat n

/-- The coefficient family of a two-form is antisymmetric. -/
def IsAntisymm {n : ℕ} (F : TwoForm n) : Prop :=
  ∀ μ ν, F ν μ = -F μ ν

/-- The two-form takes values in `su(n)`. -/
def IsSuNValued {n : ℕ} (F : TwoForm n) : Prop :=
  ∀ μ ν, IsSuN (F μ ν)

/-- The Euclidean Hodge star on two-forms in `ℝ⁴`:
`(⋆F)_{μν} = ½ ∑_{ρ,σ} ε_{μνρσ} F_{ρσ}`. -/
noncomputable def hodgeStar {n : ℕ} (F : TwoForm n) : TwoForm n :=
  fun μ ν => ∑ ρ, ∑ σ, ((1 / 2 : ℂ) * levi μ ν ρ σ) • F ρ σ

/-- The pointwise norm squared `|F|² = ∑_{μ<ν} ⟨F_{μν}, F_{μν}⟩`, where
`⟨X, Y⟩ = Re tr(X Yᴴ)` is the Frobenius inner product of matrices. -/
noncomputable def normSq {n : ℕ} (F : TwoForm n) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then (Matrix.trace (F μ ν * (F μ ν)ᴴ)).re else 0

/-- The coefficient of `tr(F ∧ F)` with respect to `dx⁰ ∧ dx¹ ∧ dx² ∧ dx³`:
`¼ ∑ ε_{μνρσ} tr(F_{μν} F_{ρσ})`. -/
noncomputable def trWedge {n : ℕ} (F : TwoForm n) : ℂ :=
  (1 / 4 : ℂ) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, levi μ ν ρ σ * Matrix.trace (F μ ν * F ρ σ)

/-- Self-duality `F = ⋆F`. -/
def IsSelfDual {n : ℕ} (F : TwoForm n) : Prop :=
  hodgeStar F = F

/-- Anti-self-duality `F = -⋆F`. -/
def IsAntiSelfDual {n : ℕ} (F : TwoForm n) : Prop :=
  hodgeStar F = -F

/-- A connection on the trivial bundle over `ℝ⁴`: the coefficients `A x μ` of
`A = ∑ μ, A μ dx^μ`. -/
abbrev Connection (n : ℕ) : Type := R4 → Fin 4 → Mat n

/-- An `SU(n)`-connection: every matrix entry of every coefficient `A μ` is a smooth (`C^∞`)
function `ℝ⁴ → ℂ`, and each `A x μ` lies in `su(n)`. -/
def IsSUConnection {n : ℕ} (A : Connection n) : Prop :=
  (∀ μ i j, ContDiff ℝ ∞ (fun x => A x μ i j)) ∧ ∀ x μ, IsSuN (A x μ)

/-- The partial derivative `∂_μ f (x)` of a matrix-valued function on `ℝ⁴`, taken entrywise. -/
noncomputable def partialDeriv {n : ℕ} (μ : Fin 4) (f : R4 → Mat n) (x : R4) : Mat n :=
  Matrix.of fun i j => fderiv ℝ (fun y => f y i j) x (Pi.single μ 1)

/-- The curvature `F_A = dA + A ∧ A`, with coefficients
`(F_A)_{μν} = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]`. -/
noncomputable def curvature {n : ℕ} (A : Connection n) (x : R4) : TwoForm n :=
  fun μ ν => partialDeriv μ (fun y => A y ν) x - partialDeriv ν (fun y => A y μ) x
    + (A x μ * A x ν - A x ν * A x μ)

/-- The components `K^μ` of the Chern–Simons three-form
`CS(A) = tr(A ∧ dA + ⅔ A ∧ A ∧ A) = ∑_μ K^μ ι_{∂_μ}(dx⁰ ∧ dx¹ ∧ dx² ∧ dx³)`:
`K^μ = ∑ ε_{μνρσ} tr(A_ν ∂_ρ A_σ + ⅔ A_ν A_ρ A_σ)`. -/
noncomputable def chernSimonsCurrent {n : ℕ} (A : Connection n) (μ : Fin 4) (x : R4) : ℂ :=
  ∑ ν, ∑ ρ, ∑ σ, levi μ ν ρ σ *
    Matrix.trace (A x ν * partialDeriv ρ (fun y => A y σ) x
      + (2 / 3 : ℂ) • (A x ν * A x ρ * A x σ))

/-- The integral of the Chern–Simons three-form over the (outward oriented) boundary of the
closed box `[a, b] ⊂ ℝ⁴`: the sum over directions `μ` of the integrals of `K^μ` over the face
`x_μ = b_μ` minus those over the face `x_μ = a_μ`. -/
noncomputable def boundaryChernSimons {n : ℕ} (a b : R4) (A : Connection n) : ℂ :=
  ∑ μ : Fin 4,
    ((∫ y in Set.Icc (a ∘ μ.succAbove) (b ∘ μ.succAbove),
        chernSimonsCurrent A μ (Fin.insertNth μ (b μ) y)) -
      ∫ y in Set.Icc (a ∘ μ.succAbove) (b ∘ μ.succAbove),
        chernSimonsCurrent A μ (Fin.insertNth μ (a μ) y))

/-- The Yang–Mills functional on the box `[a, b]`: `Ym(D_A) = ∫_{[a,b]} |F_A|² dvol`. -/
noncomputable def yangMills {n : ℕ} (a b : R4) (A : Connection n) : ℝ :=
  ∫ x in Set.Icc a b, normSq (curvature A x)

/-- The point `x` lies on the boundary of the box `[a, b]`. -/
def OnBoxBoundary (a b x : R4) : Prop :=
  x ∈ Set.Icc a b ∧ ∃ μ, x μ = a μ ∨ x μ = b μ

end UhlenbeckGauge
