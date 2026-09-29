import Mathlib

/-!
# Gale transforms of finite point configurations

Basic objects for the mission *Gale data and combinatorial type*.

A configuration is a family `a : Fin n → ℝ^d` (repetitions allowed, points need not be in
convex position).  Its *affine dependences* are the coefficient vectors `c` with
`∑ cᵢ = 0` and `∑ cᵢ aᵢ = 0`.  A *Gale transform* of `a` is a family `g : Fin n → ℝ^m`
such that the `m` coordinate vectors `(g₁ₖ, …, gₙₖ)`, `k < m`, form a basis of the space of
affine dependences (so `m = n - 1 - dim aff(a)`).  A subset `S ⊆ Fin n` is a *face set* of `a`
if some supporting affine functional vanishes exactly on the points indexed by `S`; the *Gale
condition* on `T ⊆ Fin n` says that the origin lies in the relative interior of the convex hull
of the Gale vectors indexed by `T`.
-/

namespace GaleTransform

variable {n d d' m m' : ℕ}

/-- The space of affine dependences of the configuration `a : Fin n → ℝ^d`:
coefficient vectors `c` with `∑ i, c i = 0` and `∑ i, c i • a i = 0`. -/
def affDep (a : Fin n → (Fin d → ℝ)) : Submodule ℝ (Fin n → ℝ) where
  carrier := {c | ∑ i, c i = 0 ∧ ∑ i, c i • a i = 0}
  add_mem' := by
    rintro c c' ⟨hc1, hc2⟩ ⟨hc1', hc2'⟩
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hc1, hc1', add_zero]
    · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hc2, hc2', add_zero]
  zero_mem' := by simp
  smul_mem' := by
    rintro r c ⟨hc1, hc2⟩
    refine ⟨?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hc1, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hc2, smul_zero]

theorem mem_affDep_iff (a : Fin n → (Fin d → ℝ)) (c : Fin n → ℝ) :
    c ∈ affDep a ↔ ∑ i, c i = 0 ∧ ∑ i, c i • a i = 0 := Iff.rfl

/-- `g : Fin n → ℝ^m` is a *Gale transform* of `a : Fin n → ℝ^d` when the `m` coordinate
vectors `i ↦ g i k` (`k : Fin m`) form a basis of the space of affine dependences of `a`. -/
def IsGaleTransform (a : Fin n → (Fin d → ℝ)) (g : Fin n → (Fin m → ℝ)) : Prop :=
  LinearIndependent ℝ (fun k : Fin m => fun i : Fin n => g i k) ∧
    Submodule.span ℝ (Set.range fun k : Fin m => fun i : Fin n => g i k) = affDep a

/-- `S` is a *face set* of the configuration `a`: there is an affine functional `f` that is
nonnegative on every point of the configuration and vanishes exactly on the points indexed
by `S`.  Both `∅` and `Set.univ` are face sets (the empty face and the whole polytope). -/
def IsFaceSet (a : Fin n → (Fin d → ℝ)) (S : Set (Fin n)) : Prop :=
  ∃ f : (Fin d → ℝ) →ᵃ[ℝ] ℝ, (∀ i, 0 ≤ f (a i)) ∧ ∀ i, f (a i) = 0 ↔ i ∈ S

/-- The *Gale condition* on an index set `T`: the origin lies in the relative interior of the
convex hull of the Gale vectors `g i`, `i ∈ T`. -/
def GaleCond (g : Fin n → (Fin m → ℝ)) (T : Set (Fin n)) : Prop :=
  (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ (convexHull ℝ (g '' T))

/-- Two configurations on the same index set are *combinatorially equivalent* via the
relabeling `σ` when `σ` maps face sets to face sets and back. -/
def CombEquiv (a : Fin n → (Fin d → ℝ)) (a' : Fin n → (Fin d' → ℝ)) (σ : Fin n ≃ Fin n) :
    Prop :=
  ∀ S : Set (Fin n), IsFaceSet a S ↔ IsFaceSet a' (σ '' S)

/-- Two families of Gale vectors carry the same *Gale data* via the relabeling `σ` when `σ`
preserves the Gale condition on every index set. -/
def GaleEquiv (g : Fin n → (Fin m → ℝ)) (g' : Fin n → (Fin m' → ℝ)) (σ : Fin n ≃ Fin n) :
    Prop :=
  ∀ T : Set (Fin n), GaleCond g T ↔ GaleCond g' (σ '' T)

end GaleTransform
