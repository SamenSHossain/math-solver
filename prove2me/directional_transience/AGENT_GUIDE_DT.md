# Guide for proof agents (Prove2Me workspace): velocity hemisphere reduction (DirectionalTransience)

## Environment
- Workspace `/root/prove2me_workspace`, Lean 4.33.1, Mathlib 0df444a. Run `export PATH="$HOME/.elan/bin:$PATH"` first.
- READ IN FULL FIRST: `Definitions/Def_VelocityHemisphere.lean` (namespace `OAI.DirectionalTransience`).
  - `Lattice d := Fin d → ℤ`, `Vector d := Fin d → ℝ`, and `Path d := ℕ → Lattice d` (product σ-algebra).
  - `annealedLaw ν : Measure (Path d)` is the map of `Kernel.trajMeasure` under `fun z n => (z n).2`.
  - `dot v ℓ := ∑ i, v i * ℓ i` and `realPosition x := fun i => (x i : ℝ)`.
  - `TransientPaths ℓ := {X | Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop}`.
  - `VelocityPaths v := {X | Tendsto (fun n : ℕ => fun i => (X n i : ℝ) / (n : ℝ)) atTop (𝓝 v)}`.
- TARGET: `Theorems/Thm_OAI_DirectionalTransience_positive_probability_transience_velocity_hemisphere.lean` (do not edit).
- CHILD THEOREMS you must use. They are open platform theorems, sorry stubs locally, already built; import them:
  - `Theorems.Thm_OAI_DirectionalTransience_ballistic_of_almost_sure_transience`:
    `ballistic_of_almost_sure_transience (hd : 2 ≤ d) (ν) [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ) (hℓ : dot ℓ ℓ = 1) (htrans : annealedLaw ν (TransientPaths ℓ) = 1) : ∃ v, 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1`.
  - `Theorems.Thm_OAI_DirectionalTransience_uniformElliptic_directional_zero_one`:
    `uniformElliptic_directional_zero_one (hd : 3 ≤ d) (ν) [IsProbabilityMeasure ν] (hue) (ℓ) (hℓ : ℓ ≠ 0) : annealedLaw ν (TransientPaths ℓ) = 0 ∨ annealedLaw ν (TransientPaths ℓ) = 1`.
- Type-check with `./check.sh Solutions/<file>.lean` (CHECK OK) and experiment with `lake env lean Solutions/Scratch_DT_*.lean`. NEVER run `lake build`.

## Solution file: `Solutions/Sol_OAI_DirectionalTransience_positive_probability_transience_velocity_hemisphere.lean`
```lean
import Mathlib
import Definitions.Def_VelocityHemisphere
import Theorems.Thm_OAI_DirectionalTransience_ballistic_of_almost_sure_transience
import Theorems.Thm_OAI_DirectionalTransience_uniformElliptic_directional_zero_one

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace OAI.DirectionalTransience.VH
open OAI.DirectionalTransience
... helper lemmas ...
end OAI.DirectionalTransience.VH

open OAI.DirectionalTransience in
theorem solution {d : ℕ} (hd : 3 ≤ d) ... (exact binders and conclusion of the target) := by ...
```
- `solution` is TOP-LEVEL and copies the target's binders and conclusion exactly.
- Check: `example : (type_of% @solution) = (type_of% @OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere) := rfl`,
  in a scratch copy that also imports the target's Theorems module.
- No sorry, admit, native_decide or axioms in your file. `#print axioms solution` WILL show `sorryAx`, coming only from the two child stubs;
  that is expected.

## Mathematics (elementary)
1. `annealedLaw ν` is a probability measure. `environmentLaw` is `Measure.infinitePi` of probability measures, `initialLaw` is a map, the
   `trajMeasure` of a probability measure with Markov kernels is a probability measure, and it is pushed forward by a measurable map. Any
   route to `annealedLaw ν Set.univ = 1` or `≤ 1` suffices.
2. `VelocityPaths v` is measurable (`measurableSet_tendsto`, from coordinates measurable in the product σ-algebra; the targets live in
   `Fin d → ℝ`). Uniqueness: `P(V_v) = 1 = P(V_w)` gives `P(V_v ∩ V_w) = 1`, so the intersection is nonempty, and limits are unique
   (`tendsto_nhds_unique`), so `v = w`.
3. Escape: if `0 < dot v u` then `V_v ⊆ T_u`. Indeed `dot (realPosition (X n)) u = n * dot (X n / n) u` for `n > 0`, and
   `dot (X n / n) u → dot v u > 0`; use `Tendsto.pos_mul_atTop`-type lemmas. Hence `P(T_u) ≥ P(V_v) = 1`, and `P(T_u) = 1` by
   `prob_le_one`.
4. Rescaling: for `r > 0`, `T_(ℓ/r) = T_ℓ` (`dot` is linear; `Tendsto.atTop_div_const`), and `dot v (ℓ/r) = dot v ℓ / r`. With
   `r = √(dot ℓ ℓ) > 0` for `ℓ ≠ 0`, the vector `u = ℓ/r` has `dot u u = 1`.
5. Main proof.
   - `P(T_ℓ) > 0` gives `P(T_ℓ) = 1` (zero–one child) and `P(T_u) = 1`.
   - The ballistic child gives `v` with `dot v u > 0` and `P(V_v) = 1`. So `dot v ℓ = r * dot v u > 0` and `v ≠ 0`.
   - Uniqueness gives the fourth conjunct.
   - For unit `u'`: `P(T_u') = 1 ↔ 0 < P(T_u')`. Use the zero–one child, since `u' ≠ 0` when `dot u' u' = 1`.
   - For unit `u'`: `0 < P(T_u') ↔ 0 < dot v u'`. (→) The zero–one child gives `P(T_u') = 1`, the ballistic child gives `w` with
     `dot w u' > 0` and `P(V_w) = 1`, and uniqueness gives `w = v`. (←) Escape.
   - Last conjunct: if `dot v u' ≤ 0`, then `P(T_u') = 0`. If not, `P(T_u') > 0`, so `dot v u' > 0` by the previous step, a
     contradiction.

## Return
A structured result: status OK / PARTIAL, file path, the exact `check.sh` tail, and a short proof description.
