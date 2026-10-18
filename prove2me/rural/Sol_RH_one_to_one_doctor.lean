import Mathlib
import Definitions.Def_RuralHospitals_Market
import Theorems.Thm_RuralHospitals_rural_hospitals_theorem

set_option autoImplicit false

open RuralHospitals Finset

theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (hcap : ∀ h, M.capacity h = 1) (μ ν : Assignment D H)
    (hμ : M.IsStable μ) (hν : M.IsStable ν) (d : D) (hd : μ d = none) :
    ν d = none := by
  have h1 := (rural_hospitals_theorem M μ ν hμ hν).1 d
  rw [hd, Option.isSome_none] at h1
  exact Option.not_isSome_iff_eq_none.mp (by simp [← h1])
