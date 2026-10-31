import Mathlib

namespace StrategicPolicy.StochasticOpt

/-- Decision policies: `π x` is the probability `π(d = 1 | x)` of a positive decision at
feature value `x`, so it lies in `[0, 1]` (p. 3; "0 ≤ π(x_j) ≤ 1", p. 5). -/
def Policies (m : ℕ) : Set (Fin m → ℝ) :=
  {π | ∀ x, π x ∈ Set.Icc (0 : ℝ) 1}

/-- The argmax set of (5): the feature values `k` maximizing `π k - c i k` for an individual
starting at `i` (benefit `b(x) = π(x)`, p. 3). -/
noncomputable def argmaxSet {m : ℕ} (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ) (i : Fin m) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun k => ∀ l, π l - c i l ≤ π k - c i k)

/-- The maximizers of (5) with the highest outcome `q` (standing assumption (ii), p. 4). -/
noncomputable def tieSet {m : ℕ} (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ) (i : Fin m) :
    Finset (Fin m) := by
  classical
  exact (argmaxSet c π i).filter (fun k => ∀ l ∈ argmaxSet c π i, q l ≤ q k)

theorem argmaxSet_nonempty {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (π : Fin m → ℝ)
    (i : Fin m) : (argmaxSet c π i).Nonempty := by
  classical
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m))
    (fun k => π k - c i k) Finset.univ_nonempty
  exact ⟨k, by simpa [argmaxSet] using fun l => hk l (Finset.mem_univ l)⟩

theorem tieSet_nonempty {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ)
    (i : Fin m) : (tieSet c q π i).Nonempty := by
  classical
  obtain ⟨k, hk, hq⟩ := Finset.exists_max_image (argmaxSet c π i) q (argmaxSet_nonempty c π i)
  exact ⟨k, by simpa [tieSet] using ⟨hk, hq⟩⟩

/-- Best response (5) with tie-break (ii): among the maximizers of `π k - c i k`, the one with
the highest outcome `q`; any remaining tie (only possible when outcomes coincide) goes to the
least index. -/
noncomputable def br {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ)
    (i : Fin m) : Fin m :=
  (tieSet c q π i).min' (tieSet_nonempty c q π i)

/-- The strategic utility (7), regrouped by the initial feature value `i`. -/
noncomputable def u {m : ℕ} [NeZero m] (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (π : Fin m → ℝ) : ℝ :=
  ∑ i, p i * (q (br c q π i) - γ) * π (br c q π i)

/-- The non-strategic utility: (2) with the feature distribution `P(x)` itself (nobody moves). -/
def uNS {m : ℕ} (p q : Fin m → ℝ) (γ : ℝ) (π : Fin m → ℝ) : ℝ :=
  ∑ x, p x * (q x - γ) * π x

/-- Standing assumption (i), p. 4: moving to a feature value with an outcome at least as high
costs a positive amount. -/
def StandingI {m : ℕ} (q : Fin m → ℝ) (c : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j, i ≠ j → q i ≤ q j → 0 < c i j

/-- Outcome monotonic cost (p. 6), on distinct feature values, with free staying. -/
def OMCost {m : ℕ} (q : Fin m → ℝ) (c : Fin m → Fin m → ℝ) : Prop :=
  (∀ i, c i i = 0) ∧
  (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    ((q i < q j ∧ q j < q k) ↔ (c i j < c i k ∧ c j k < c i k))) ∧
  (∀ i j, i ≠ j → (q j < q i ↔ c i j = 0))

/-- A deterministic policy takes only the values `0` and `1`. -/
def IsDeterministic {m : ℕ} (π : Fin m → ℝ) : Prop :=
  ∀ x, π x = 0 ∨ π x = 1

end StrategicPolicy.StochasticOpt
