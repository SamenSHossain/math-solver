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
tools/p2m.py                    API client + CLI (login, browse, mirror, submit, poll)
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
