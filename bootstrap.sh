#!/usr/bin/env bash
# Idempotent setup of this Prove2Me workspace on a fresh machine or container.
#   PROVE2ME_API_KEY=p2m_... ./bootstrap.sh          # login only
#   P2M_INSTALL_LEAN=1 ./bootstrap.sh                # also install elan + Lean + Mathlib cache
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# 1. The Prove2Me skill looks for the workspace at $HOME/prove2me_workspace.
if [ ! -e "$HOME/prove2me_workspace" ]; then
  ln -s "$ROOT" "$HOME/prove2me_workspace"
  echo "linked \$HOME/prove2me_workspace -> $ROOT"
fi

# 2. Python client dependency.
python3 -c 'import requests' 2>/dev/null || python3 -m pip install -q requests

# 3. Credentials: PROVE2ME_API_KEY in the environment, or credentials.json here.
user="$(python3 "$ROOT/tools/p2m.py" me | python3 -c 'import json,sys; print(json.load(sys.stdin)["username"])')"
echo "Prove2Me login OK as $user"

# 4. Local Lean toolchain (optional; slow the first time, needs ~15 GB).
if [ "${P2M_INSTALL_LEAN:-0}" = "1" ]; then
  bash "$ROOT/tools/install_lean.sh"
else
  command -v elan >/dev/null 2>&1 && echo "elan present: $(elan --version)" \
    || echo "Lean not installed; run with P2M_INSTALL_LEAN=1 to install elan + Lean + Mathlib cache."
fi
