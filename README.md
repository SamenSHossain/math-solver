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
