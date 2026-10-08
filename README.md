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
