# math-solver

Tooling for proving theorems on [Prove2Me](https://prove2.me) (Lean 4 + Mathlib) from a cloud session.

## Prove2Me setup

```bash
# one-time per machine; safe to re-run
P2M_API_KEY=p2m_... scripts/prove2me_setup.sh
```

The script clones the official [prove2me_workspace](https://github.com/prove2me/prove2me_workspace)
to `~/prove2me_workspace` (override with `P2M_WORKSPACE`), installs elan and Lean from GitHub
releases (the `*.lean-lang.org` hosts are blocked by the cloud egress policy), pins Mathlib to the
platform's default environment, downloads the prebuilt Mathlib cache, and runs the workspace smoke
test. If `P2M_API_KEY` is set it also stores the key in the workspace's gitignored
`credentials.json` and mints an access token.

The API key is a 30-day credential copied from the website (account menu, top right, **API key**).
It is never committed; pass it via the environment each session.

## Talking to the API

`scripts/p2m.py` is a dependency-free helper that keeps the 1-hour access token fresh:

```bash
scripts/p2m.py whoami
scripts/p2m.py get missions limit=5
scripts/p2m.py get "missions/<mission_id>/milestones"
scripts/p2m.py post rate '{"theorem_id": "<id>", "rating": 4}'
curl -H "Authorization: Bearer $(scripts/p2m.py token)" https://prove2.me/api/v1/me
```

The agent playbook lives in the workspace: `~/prove2me_workspace/SKILL.md` and `references/`.
Lean files go in the workspace's `Definitions/`, `Theorems/`, and `Solutions/` directories, and
`lake build Solutions` there verifies a solution locally before it is submitted.

## Proofs for the Ghadimi–Lan RSG mission

`prove2me/` keeps a copy of the Lean files produced for the mission *Stochastic First- and
Zeroth-Order Methods for Nonconvex Stochastic Programming 1* (Theorem 2.1 a), arXiv:1309.5549):

- `Solutions/Sol_*.lean`: the submitted (and server-accepted) proofs of milestones (2.8)–(2.12), the
  weighting identity, and the root reduction `theorem_2_1_a`.
- `Solutions/Infra_*.lean`: proofs of the two infrastructure lemmas published on the platform
  (`GhadimiLan.RSG.iterate_measurable`, `GhadimiLan.RSG.grad_sq_integrable`).
- `Theorems/`, `Definitions/`: local mirrors of the platform statements and definitions the proofs
  import (theorem bodies are `sorry` placeholders, as on the platform).
- `AGENT_GUIDE.md`, `check.sh`: the working conventions and the type-check helper used in the
  workspace (`lake env lean` against the pinned Mathlib).

To rebuild: run `scripts/prove2me_setup.sh`, copy these directories into `~/prove2me_workspace`,
`lake build` the `Definitions.*` and `Theorems.*` modules by name, then `./check.sh Solutions/<file>`.

## Proofs for the Uhlenbeck gauge-theory mission

`prove2me/uhlenbeck/` holds the Lean files for the mission *Uhlenbeck, Equations of Gauge Theory I:
Self-Dual Connections Minimize Yang-Mills* (Proposition 3.1.1, box version):

- `Solutions/`: server-accepted proofs of the root theorem `selfDual_absolute_minimizer` (a
  reduction), the two milestones `yangMills_ge_boundaryChernSimons` and
  `yangMills_eq_boundaryChernSimons_iff`, and the two published lemmas
  `curvature_isAntisymm_isSuNValued` and `boundaryChernSimons_eq_of_eq_on_boundary`.
- `Theorems/`, `Definitions/`: local mirrors of the platform statements and definitions.
- `AGENT_GUIDE_UHL.md`: the conventions used by the proof agents.

## Proofs for the Onsager reciprocal relations mission

`prove2me/onsager/` holds the Lean files for the mission *Onsager Reciprocal Relations: Symmetry of
Kinetic Coefficients*: the root reduction `onsager_reciprocal_relations`, all five milestones, and the
published lemma `integrable_norm_pow_mul_fluctuationWeight` (finite polynomial moments of the Gaussian
fluctuation weight), with local statement mirrors and the agent guide.

## Integer multiplication campaign links

`prove2me/intmul/` holds three reductions for the mission *Integer multiplication: κ =
0.00012612978530233 (Jain round eight)*: Jain round seven ⇐ round eight, community PR #62 ⇐ round
seven, and Jain round six ⇐ PR #62, each by monotonicity of `KappaBound` in κ. Together with the
existing community links they connect every milestone of the mission to its root.

## No-hair mission: Kerr–Newman solves Einstein–Maxwell

`prove2me/nohair/` holds the work on milestone `NoHair.kerrNewman_einsteinMaxwell` of the mission
*No-Hair Conjecture: Uniqueness of Stationary Kerr–Newman Black Holes*. The milestone is reduced to its
three conjuncts (`Sol_NoHair_kerrNewman_einsteinMaxwell.lean`, accepted as a sketch). Proved children:

- `kerrNewman_field_closed`: the Bianchi identity dF = 0, from smoothness of the potential and
  symmetry of second derivatives.
- `kerrNewman_maxwell`: the curved Maxwell equation, reduced to flat Maxwell using det g = −1, the
  explicit inverse metric, and alignment of the null vector k with F.
- `kerrNewman_flat_maxwell`: flat-space Maxwell for the Kerr–Newman potential, via ΔH = 0 and
  curl A = ∇ψ for the real and imaginary parts of Appell's potential.

The Einstein-equation child `kerrNewman_einstein` is still open. `ein_num.py` and `mx_num.py` are the
numerical sympy checks of the Einstein and Maxwell equations at a sample point. The `Thm_*.lean` files
are local statement mirrors.

## Robust four-row permanent inequality

`prove2me/fourrow/` holds a proof of `OAI.FourRow.robust_permanent`, accepted on Prove2Me. Laws on S₄
within total variation 1/25000 of uniform, with exactly uniform marginals, satisfy the permanent bound
with exponent p₀ = 2 − 1/2000. The argument follows OpenAI's preprint *A strict four-row permanent
inequality and permutation moments* (github.com/openai/math, Apache-2.0). The Lean proof was written
independently from a blueprint of that argument (`AGENT_GUIDE_FR.md`); the upstream repository has its
own formalization. `critical_exponent.py` numerically locates the critical exponent for the uniform law,
about 1.7448, where a permutation matrix becomes extremal.

## Disproof of the robust-VaR comonotonic risk-sharing theorem (as formalized)

`prove2me/robustvar/` holds an accepted disproof of `TailRiskSharing.RobustVaR.theorem6_robust_var_comonotonic`.
The formal definition of comonotonic allocations only asks each component to be comonotone with the
total loss X. For constant X this is vacuous, so the allocation (Z, −Z) is admissible. With two agents,
radius 1, level 3/4 and X = 0, it gives an inf-convolution of at most 0, while the claimed value is at
least 4/3. The paper's Theorem 6 uses pairwise comonotonic allocations and is not affected; the defect is
in the formal definition. The `Def_*.lean` files are the platform definitions the disproof builds on.

## C^r stability conjecture (Palis–Smale) mission

`prove2me/stability/` holds the work on the mission *C^r Stability Conjecture (Palis–Smale)*. Two new
lemmas are proved: structural stability implies Ω-stability (a conjugacy maps nonwandering sets onto
nonwandering sets), and when Ω(f) is hyperbolic every periodic point is hyperbolic. Accepted sketches
reduce Mañé's C¹ theorem to Palis's C¹ Ω-stability theorem, the Franks and periodic-density milestones to
Mañé's theorem, and the goal to Mañé's theorem (r = 1) plus a new child for r ≥ 2. The mission frontier is
now exactly Palis's theorem and the open case r ≥ 2.

## Rural hospitals theorem mission

`prove2me/rural/` holds a complete Lean proof of the rural hospitals theorem (Roth 1984/1986;
McVitie–Wilson 1970) for many-to-one markets with strict preferences, and its four milestones. The proof
is a direct counting argument, with no deferred acceptance. Doctors who strictly prefer one stable
matching sit at hospitals that are full in the other, and counting the doctors at those hospitals shows
nothing changes. Every other hospital keeps exactly the same doctors. The milestones follow from the
main theorem; the one-to-one cases do not need their capacity-one hypothesis.

## Computation under rapidly vanishing Navier–Stokes forcing (OpenAI comparator challenge)

`prove2me/alternating_ns/` holds a proof sketch of `OAI.AlternatingNS.alternating` and full proofs of five
of its six children. The theorem reduces to a core construction (`velocity_construction`, the
research content of OpenAI's manuscript, still open on the platform) and five general results, all
proved independently in Lean:
- `trajectory_flow`: particle trajectories exist globally and are unique (Picard–Lindelöf and Gronwall);
- `residual_regular`: the force inherits smoothness, compact support and rapid decay;
- `zero_pressure_solution`: zero-pressure Navier–Stokes and the energy class;
- `energy_uniqueness`: weak–strong uniqueness by the energy method;
- `force_compiler`: a computable compiler from velocity programs to force programs.
The five general results were written independently. The core construction is a port of OpenAI's own
formalization, published as eleven platform definitions (`port/Def_OAI_AlternatingFlow_Part01..11.lean`,
split only to fit the 300 s verification limit) and used by `Sol_OAI_AlternatingNS_velocity_construction.lean`;
the source is openai/math,
commit adc7f12, lean/OAI/MathematicalPhysics/AlternatingFlow, (c) OpenAI, Apache License 2.0. The ported
portions keep that license, and each part header lists the modifications: modules concatenated in order,
platform definitions used, force/uniqueness/assembly modules omitted, and small compatibility fixes.

## Smale's question: the homotopy type of Diff(S⁴)

`prove2me/smale_s4/` holds the work on the mission whose goal is the open question whether Diff(D⁴) is
path-connected. The goal is reduced (accepted sketch) to its classical isotopy form,
`diffDisk_four_smoothlyIsotopic_id` (still open), and to the proved lemma `continuous_of_smoothIsotopy`:
jointly smooth isotopies through diffeomorphisms of Dⁿ rel boundary are continuous paths in the platform's
C^∞ topology. The same lemma and the straight-line isotopy prove `diffDisk_one_pathConnected`, that
Diff(D¹ rel ∂) is path-connected.

## Exact quantum factoring over a fixed finite gate set (OpenAI comparator challenge)

`prove2me/quantum_factoring/` holds an accepted sketch of `OAI.ExactQuantumFactoring.exact_quantum_factoring`. Exact
success, a correct-output probability of exactly 1, is reduced to zero amplitude on wrong outputs:
- `outputState_normSq_sum` is proved independently: every circuit over the fixed 20-gate alphabet is unitary and
  preserves total probability;
- `zero_amplitude_core`, the construction of OpenAI's manuscript, is still open on the platform. A proof
  (`Sol_OAI_ExactQuantumFactoring_zero_amplitude_core.lean`) checks locally on top of a port of OpenAI's own
  formalization: 38 definition parts (`port/Def_OAI_QuantumFactoring_Part01..38.lean`), about 54,000 lines from 544
  modules. The source is openai/math, commit adc7f12, lean/OAI/Computability/QuantumFactoring, (c) OpenAI, Apache
  License 2.0. The ported portions keep that license, and each part header lists the modifications: modules
  concatenated in order, the platform definition `ExactQuantumFactoring` (identical to upstream Basic.lean) used,
  Main.lean omitted, and small compatibility edits for Lean 4.33.1 and Mathlib 0df444a.
- Only parts 1–17 are published. Server jobs recompile the uncached parts of the import chain, so from part 18 on
  even a probe that only imports the chain hits the 300 s limit. Finishing needs the platform's
  definitions-plus-theorem-nodes layout (references/upload_full_project.md).

## F_d versus F_{d+1}: fixed-depth separation of bounded-depth Frege

`prove2me/frege/` holds the proofs of the mission's first two milestones, both Proved:
- `depth_frege_sound`: every formula with an $F_d$-proof is a tautology. The proof uses De Morgan for `dual` and shows each
  rule preserves validity of sequents, by strong induction over proof lines.
- `depth_frege_complete`: every tautology of depth ≤ d has an $F_d$-proof. The proof is a cut-free proof search by
  strong induction on total sequent size; only subformulas occur, so all lines have depth ≤ d.
The remaining milestones (the exponential PHP lower bound and Krajíček's depth-dependent separation) and the goal are
still open.
