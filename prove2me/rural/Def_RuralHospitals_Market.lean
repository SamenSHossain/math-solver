import Mathlib

/-!
# Many-to-one matching markets (doctors and hospitals) with strict preferences

Model for the rural hospitals theorem (Roth 1984, 1986; McVitie–Wilson 1970).
Preferences are encoded by injective rank functions (smaller rank = more preferred),
which makes them strict total orders.  The option `none` stands for "remaining
unmatched" (for a doctor) or "leaving the position empty" (for a hospital), so each
side may find some partners unacceptable.  Hospital preferences over groups of
doctors are responsive to the ranking of individual doctors.
-/

namespace RuralHospitals

open Finset

/-- A many-to-one matching market between a finite set `D` of doctors and a finite set
`H` of hospitals, with strict preferences and hospital capacities. -/
structure Market (D H : Type*) [Fintype D] [Fintype H] where
  /-- `docRank d o` is the rank doctor `d` gives to outcome `o`
  (`some h` = working at `h`, `none` = unmatched); smaller is better. -/
  docRank : D → Option H → ℕ
  /-- Doctors' preferences are strict. -/
  docRank_injective : ∀ d, Function.Injective (docRank d)
  /-- `hospRank h o` is the rank hospital `h` gives to `o`
  (`some d` = doctor `d`, `none` = an empty position); smaller is better. -/
  hospRank : H → Option D → ℕ
  /-- Hospitals' preferences are strict. -/
  hospRank_injective : ∀ h, Function.Injective (hospRank h)
  /-- The number of positions of each hospital. -/
  capacity : H → ℕ

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]

/-- An assignment of doctors: `μ d = some h` means `d` works at `h`,
`μ d = none` means `d` is unmatched. -/
abbrev Assignment (D H : Type*) := D → Option H

/-- The set of doctors assigned to hospital `h` under `μ`. -/
def assigned (μ : Assignment D H) (h : H) : Finset D :=
  univ.filter (fun d => μ d = some h)

namespace Market

variable (M : Market D H)

/-- `μ` is a matching: no hospital receives more doctors than it has positions. -/
def IsMatching (μ : Assignment D H) : Prop :=
  ∀ h, (assigned μ h).card ≤ M.capacity h

/-- Individual rationality: every doctor weakly prefers her assignment to being
unmatched, and every hospital strictly prefers each of its doctors to an empty position. -/
def IsIndividuallyRational (μ : Assignment D H) : Prop :=
  (∀ d, M.docRank d (μ d) ≤ M.docRank d none) ∧
  (∀ d h, μ d = some h → M.hospRank h (some d) < M.hospRank h none)

/-- `(d, h)` blocks `μ`: doctor `d` strictly prefers `h` to her assignment, `h` finds
`d` acceptable, and `h` either has an empty position or strictly prefers `d` to one of
its assigned doctors. -/
def IsBlockingPair (μ : Assignment D H) (d : D) (h : H) : Prop :=
  M.docRank d (some h) < M.docRank d (μ d) ∧
  M.hospRank h (some d) < M.hospRank h none ∧
  ((assigned μ h).card < M.capacity h ∨
    ∃ d' ∈ assigned μ h, M.hospRank h (some d) < M.hospRank h (some d'))

/-- A stable matching: a matching that is individually rational and has no blocking pair. -/
def IsStable (μ : Assignment D H) : Prop :=
  M.IsMatching μ ∧ M.IsIndividuallyRational μ ∧ ∀ d h, ¬ M.IsBlockingPair μ d h

end Market

end RuralHospitals
