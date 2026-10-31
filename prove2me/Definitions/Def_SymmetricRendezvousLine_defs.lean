import Mathlib

open MeasureTheory

namespace SymmetricRendezvousLine

/-- A feasible path for one player, written in that player's own frame: the player
starts at the origin of its own frame and moves with speed at most `1`, i.e. the path
is `1`-Lipschitz on `[0, ∞)`. Values at negative times are irrelevant. -/
def IsFeasiblePath (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |f s - f t| ≤ |s - t|

/-- A mixed strategy: a probability space `(Ω, P)` together with a random feasible path
`ω ↦ path ω`, measurable in `ω` at every fixed time. -/
structure MixedStrategy where
  /-- The sample space of the player's private randomisation. -/
  Ω : Type
  /-- The σ-algebra on the sample space. -/
  [mΩ : MeasurableSpace Ω]
  /-- The probability measure on the sample space. -/
  P : Measure Ω
  /-- `P` is a probability measure. -/
  [isProb : IsProbabilityMeasure P]
  /-- The random path, in the player's own frame. -/
  path : Ω → ℝ → ℝ
  /-- Every realised path is feasible. -/
  path_feasible : ∀ ω, IsFeasiblePath (path ω)
  /-- The position at each fixed time is a random variable. -/
  path_measurable : ∀ t : ℝ, Measurable fun ω => path ω t

attribute [instance] MixedStrategy.mΩ MixedStrategy.isProb

/-- The meeting time of two trajectories `x, y` on the line: the first time `t ≥ 0` with
`x t = y t`, and `∞` if they never meet. -/
noncomputable def meetingTime (x y : ℝ → ℝ) : ENNReal :=
  ⨅ (t : ℝ) (_ : 0 ≤ t ∧ x t = y t), ENNReal.ofReal t

/-- The orientation of a player's own "forward" direction relative to the line
(unknown to the player): `true ↦ +1`, `false ↦ -1`. -/
def orient (b : Bool) : ℝ := if b then 1 else -1

/-- Expected meeting time when player I (starting at `0`) uses `S₁` and player II
(starting at `2`) uses `S₂`, with independent randomisations. Each player's forward
direction is an independent fair coin, so each of the four orientation pairs has
probability `1/4`. -/
noncomputable def expectedMeetingTime (S₁ S₂ : MixedStrategy) : ENNReal :=
  (1 / 4 : ENNReal) * ∑ b₁ : Bool, ∑ b₂ : Bool,
    ∫⁻ p, meetingTime (fun t => orient b₁ * S₁.path p.1 t)
        (fun t => 2 + orient b₂ * S₂.path p.2 t) ∂(S₁.P.prod S₂.P)

/-- The symmetric rendezvous value `R` on the line: the infimum, over all mixed strategies
`S`, of the expected meeting time when both players use the same strategy `S`. -/
noncomputable def symmetricRendezvousValue : ENNReal :=
  ⨅ S : MixedStrategy, expectedMeetingTime S S

/-- The asymmetric rendezvous value on the line: players may use different strategies. -/
noncomputable def asymmetricRendezvousValue : ENNReal :=
  ⨅ (S₁ : MixedStrategy) (S₂ : MixedStrategy), expectedMeetingTime S₁ S₂

/-- A path that starts at `0`, moves at full speed `1`, and changes direction only at
integer times. -/
def IsIntegerZigzag (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ ∀ n : ℕ, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    ∀ t ∈ Set.Icc (n : ℝ) (n + 1), f t = f n + s * (t - n)

/-- The symmetric rendezvous value restricted to mixed strategies all of whose paths are
integer zigzags. -/
noncomputable def discreteSymmetricRendezvousValue : ENNReal :=
  ⨅ (S : MixedStrategy) (_ : ∀ ω, IsIntegerZigzag (S.path ω)), expectedMeetingTime S S

end SymmetricRendezvousLine
