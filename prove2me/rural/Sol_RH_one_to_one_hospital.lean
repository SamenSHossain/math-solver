import Mathlib
import Definitions.Def_RuralHospitals_Market
import Theorems.Thm_RuralHospitals_rural_hospitals_theorem

set_option autoImplicit false

open RuralHospitals Finset

theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (hcap : ∀ h, M.capacity h = 1) (μ ν : Assignment D H)
    (hμ : M.IsStable μ) (hν : M.IsStable ν) (h : H) (hh : assigned μ h = ∅) :
    assigned ν h = ∅ := by
  have h2 := (rural_hospitals_theorem M μ ν hμ hν).2.1 h
  rw [hh, Finset.card_empty] at h2
  exact Finset.card_eq_zero.mp h2.symm
