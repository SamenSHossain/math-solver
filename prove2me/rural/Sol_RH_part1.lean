import Mathlib
import Definitions.Def_RuralHospitals_Market
import Theorems.Thm_RuralHospitals_rural_hospitals_theorem

set_option autoImplicit false

open RuralHospitals Finset

theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν) :
    (∀ d, (μ d).isSome = (ν d).isSome) ∧
      ∀ h, (assigned μ h).card = (assigned ν h).card :=
  ⟨(rural_hospitals_theorem M μ ν hμ hν).1, (rural_hospitals_theorem M μ ν hμ hν).2.1⟩
