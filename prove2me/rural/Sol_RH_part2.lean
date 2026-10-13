import Mathlib
import Definitions.Def_RuralHospitals_Market
import Theorems.Thm_RuralHospitals_rural_hospitals_theorem

set_option autoImplicit false

open RuralHospitals Finset

theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν)
    (h : H) (hh : (assigned μ h).card < M.capacity h) :
    assigned ν h = assigned μ h :=
  (rural_hospitals_theorem M μ ν hμ hν).2.2 h hh
