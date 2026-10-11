import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting
import Definitions.Def_TailRiskSharing_VaRTail_Setting

namespace TailRiskSharing.TailConv

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.1 p. 5: the domain `L^∞` of essentially bounded random variables. -/
def Linf (P : Measure Ω) : Set (Ω → ℝ) :=
  {X | Measurable X ∧ ∃ C : ℝ, ∀ᵐ ω ∂P, |X ω| ≤ C}

/-- §2.2 p. 5, for `[-∞, ∞)`-valued risk measures: law-invariant. -/
def IsLawInvariantE (P : Measure Ω) (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) : Prop :=
  ∀ X ∈ dom, ∀ Y ∈ dom, (∀ x, TailRiskSharing.VaRConv.distFn P X x = TailRiskSharing.VaRConv.distFn P Y x) → F X = F Y

/-- §5 p. 17: (sup-norm) continuity from above: `ρ(X_k) → ρ(X)` whenever `X_k ≥ X` a.s. and
`ess-sup |X_k - X| → 0`. The convergence `ess-sup |X_k - X| → 0` is written as "for every `η > 0`,
eventually `|X_k - X| ≤ η` a.s.", which is the same condition and does not go through the real
`essSup`, whose value on an essentially unbounded function is a junk `0`. -/
def IsSupNormContinuousFromAbove (P : Measure Ω) (dom : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (Xs : ℕ → Ω → ℝ) (X : Ω → ℝ), (∀ k, Xs k ∈ dom) → X ∈ dom →
    (∀ k, ∀ᵐ ω ∂P, X ω ≤ Xs k ω) →
    (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ᵐ ω ∂P, |Xs k ω - X ω| ≤ η) →
    Tendsto (fun k => ρ (Xs k)) atTop (𝓝 (ρ X))

end TailRiskSharing.TailConv
