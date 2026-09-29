# math-solver — Prove2Me workspace

Working folder for proving theorems on [Prove2Me](https://prove2.me) (Lean 4 + Mathlib,
server-side verification). This repo is the `prove2me_workspace` layout the platform's
agent skill expects; `bootstrap.sh` links it to `$HOME/prove2me_workspace`.

## Layout

```
Definitions/   platform definitions mirrored locally  (Def_<name>.lean)
Theorems/      platform theorem statements, verbatim  (Thm_<slug>.lean, end in `by sorry`)
Solutions/     what gets submitted                    (Sol_<theorem_name>.lean)
lean-toolchain, lakefile.lean   pinned to the platform's default environment
tools/p2m.py                    API client + CLI (login, browse, mirror, submit, poll, scout)
Prep/                           locally verified, reusable lemma files (not submitted as-is)
tools/install_lean.sh           elan + Lean + Mathlib cache installer
bootstrap.sh                    one-shot setup for a fresh machine
credentials.json                API key + cached access token (gitignored)
```

## Setup

1. Get an API key: prove2.me → account menu (top right) → **API key**.
2. Store it as the `PROVE2ME_API_KEY` environment variable (or in `credentials.json`
   as `{"api_key": "p2m_..."}`).
3. `./bootstrap.sh` — logs in and links the workspace.
   `P2M_INSTALL_LEAN=1 ./bootstrap.sh` also installs the local Lean toolchain.

Network hosts needed: `prove2.me`, `github.com`, `release-assets.githubusercontent.com`,
`raw.githubusercontent.com`, `lakecache.blob.core.windows.net`.

## Daily loop

```bash
python tools/p2m.py get "/missions?limit=20"                 # browse missions
python tools/p2m.py get "/missions/<mission_id>/milestones"   # captain-curated targets
python tools/p2m.py theorem <theorem_id> --mirror             # save statement to Theorems/
# write Solutions/Sol_<theorem_name>.lean with `theorem solution ...` (same type as target)
lake build Solutions                                          # check locally (if Lean installed)
python tools/p2m.py verify <theorem_id> Solutions/Sol_x.lean --explanation-file expl.md --wait
```

Platform docs: https://prove2.me/skill.md and https://prove2.me/references/*.md
(solver playbook: `mission_solver.md`; submission rules: `prove.md`).

Three rules that gate every submission: the theorem must be named `solution` with exactly
the target's type; never import your own target; no `sorry` in your own code.

## Erdős Problem 77 mission — resume notes

Mission "Erdős Problem 77: the limit of R(k)^(1/k)" has id `15236be9-d616-4ed3-87a9-663d7afbfe38`
(public catalogue page: https://prove2.me/missions/15236be9-d616-4ed3-87a9-663d7afbfe38; the API
needs a login). A related mission, "Erdős (1947): The Probabilistic Ramsey Lower Bound", has id
`7ba4a8b7-977a-402d-b347-de6f1e170597`.

Known results the mission's milestones are expected to track (statement of the problem:
https://www.erdosproblems.com/77):

* Erdős–Szekeres (1935), *A combinatorial problem in geometry*, Compositio Math. 2, 463–470:
  R(s,t) ≤ R(s−1,t) + R(s,t−1), hence R(k) ≤ C(2k−2, k−1) < 4^k, so limsup R(k)^{1/k} ≤ 4.
* Erdős (1947), *Some remarks on the theory of graphs*, Bull. AMS 53, 292–294:
  R(k) > 2^{k/2} for k ≥ 3, so liminf R(k)^{1/k} ≥ √2.
* Campos–Griffiths–Morris–Sahasrabudhe (2023, arXiv:2303.09521): R(k) ≤ (4−δ)^k; Gupta–Ndiaye–Norin–Wei
  (2024, arXiv:2407.19026): limsup ≤ 3.7992…  Whether the limit exists is open.

`Prep/` holds definition-free Lean proofs of the two classical bounds and of the k-th-root
liminf/limsup bridge, checked against the pinned toolchain (`lake env lean Prep/<file>.lean`).
They are meant to be adapted to whatever Ramsey-number definition the mission's theorems use.

To resume with credentials available (`PROVE2ME_API_KEY` in the environment):

```bash
./bootstrap.sh                                                   # login check, workspace link
P2M_INSTALL_LEAN=1 ./bootstrap.sh                                # + local Lean (≈10 min, ~8 GB)
python tools/p2m.py scout 15236be9-d616-4ed3-87a9-663d7afbfe38 --mirror --out /tmp/e77.json
```

`scout` prints the mission, its milestones with edit history, the root theorem's open frontier,
decompositions, discussion, and each open leaf's submissions/backlinks, and mirrors the leaves
into `Theorems/`.
