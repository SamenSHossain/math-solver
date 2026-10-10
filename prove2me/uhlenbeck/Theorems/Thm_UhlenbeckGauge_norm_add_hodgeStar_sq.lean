import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem norm_add_hodgeStar_sq {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F)
    (hsu : IsSuNValued F) :
    ((normSq (F + hodgeStar F) : ℝ) : ℂ) = 2 * (normSq F : ℂ) - 2 * trWedge F ∧
    ((normSq (F - hodgeStar F) : ℝ) : ℂ) = 2 * (normSq F : ℂ) + 2 * trWedge F := by sorry

end UhlenbeckGauge
