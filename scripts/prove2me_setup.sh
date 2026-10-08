#!/usr/bin/env bash
# Idempotent Prove2Me setup for a fresh Linux x86_64 (cloud) session.
#
# What it does:
#   1. clone or update the prove2me_workspace repo at $P2M_WORKSPACE (default ~/prove2me_workspace)
#   2. install elan from its GitHub release (elan.lean-lang.org is often blocked by egress policy)
#   3. install the pinned Lean toolchain from GitHub releases (release.lean-lang.org is often blocked)
#   4. write lean-toolchain + lakefile.lean pinned to the platform's default environment
#   5. lake update  (clones Mathlib at the pinned commit and pulls the prebuilt .olean cache)
#   6. build Solutions/SmokeTest.lean to prove the local environment matches the server's
#   7. if $P2M_API_KEY is set, save it to credentials.json and exchange it for an access token
#
# Re-running is safe: every step checks for existing state first.
set -euo pipefail

WS="${P2M_WORKSPACE:-$HOME/prove2me_workspace}"
LEAN_VERSION="${P2M_LEAN_VERSION:-4.33.1}"
MATHLIB_REV="${P2M_MATHLIB_REV:-0df444a360eaa60ab8c11dca51a86af692955474}"
ELAN_DIR="${ELAN_HOME:-$HOME/.elan}"
TC_DIR="$ELAN_DIR/toolchains/leanprover--lean4---v${LEAN_VERSION}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

log() { printf '\n==> %s\n' "$*"; }

log "1/7 Prove2Me workspace at $WS"
if [ -d "$WS/.git" ]; then
  git -C "$WS" pull --ff-only --tags origin main
else
  git clone https://github.com/prove2me/prove2me_workspace "$WS"
fi

log "2/7 elan"
if [ ! -x "$ELAN_DIR/bin/elan" ]; then
  echo "Installing elan from GitHub releases (no default toolchain)."
  tmp="$(mktemp -d)"
  curl -sSL -o "$tmp/elan.tar.gz" \
    https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz
  tar xzf "$tmp/elan.tar.gz" -C "$tmp"
  "$tmp/elan-init" -y --no-modify-path --default-toolchain none
  rm -rf "$tmp"
fi
export PATH="$ELAN_DIR/bin:$PATH"
elan --version

log "3/7 Lean v$LEAN_VERSION"
if [ ! -x "$TC_DIR/bin/lean" ]; then
  echo "Downloading lean-${LEAN_VERSION}-linux.tar.zst from GitHub releases (~550 MB)."
  tmp="$(mktemp -d)"
  curl -sSL -o "$tmp/lean.tar.zst" \
    "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst"
  if command -v zstd >/dev/null 2>&1; then
    tar --use-compress-program=unzstd -xf "$tmp/lean.tar.zst" -C "$tmp"
  else
    echo "zstd binary missing; extracting with the Python 'zstandard' package."
    python3 -m pip install -q zstandard
    python3 - "$tmp/lean.tar.zst" "$tmp" <<'PY'
import sys, tarfile, zstandard
src, dst = sys.argv[1], sys.argv[2]
with open(src, "rb") as fh, zstandard.ZstdDecompressor().stream_reader(fh) as reader:
    with tarfile.open(fileobj=reader, mode="r|") as tar:
        tar.extractall(dst)
PY
  fi
  mkdir -p "$ELAN_DIR/toolchains"
  # elan recognises a toolchain by this directory name, so no `elan toolchain link` is needed.
  mv "$tmp/lean-${LEAN_VERSION}-linux" "$TC_DIR"
  rm -rf "$tmp"
fi
elan toolchain list

log "4/7 pinned project files"
cd "$WS"
printf 'leanprover/lean4:v%s\n' "$LEAN_VERSION" > lean-toolchain
cat > lakefile.lean <<LAKE
import Lake
open Lake DSL

package «prove2me» where
  leanOptions := #[⟨\`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "$MATHLIB_REV"

lean_lib «Definitions» where
lean_lib «Theorems» where
@[default_target]
lean_lib «Solutions» where
LAKE
lean --version
lake --version

log "5/7 Mathlib @ $MATHLIB_REV + prebuilt cache"
if [ "$(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null || true)" != "$MATHLIB_REV" ]; then
  echo "Resolving dependencies and downloading the Mathlib cache (several GB, a few minutes)."
  lake update
fi
lake exe cache get

log "6/7 smoke test"
lake build Solutions.SmokeTest

log "7/7 credentials"
if [ -n "${P2M_API_KEY:-}" ]; then
  python3 - "$WS/credentials.json" <<'PY'
import json, os, sys
path = sys.argv[1]
cred = {}
if os.path.exists(path):
    with open(path) as fh:
        cred = json.load(fh)
cred["api_key"] = os.environ["P2M_API_KEY"]
with open(path, "w") as fh:
    json.dump(cred, fh, indent=2)
os.chmod(path, 0o600)
print("saved API key to", path)
PY
fi
if [ -f "$WS/credentials.json" ]; then
  P2M_WORKSPACE="$WS" python3 "$SCRIPT_DIR/p2m.py" whoami
else
  echo "No credentials.json yet. Set P2M_API_KEY and re-run, or run: scripts/p2m.py login --api-key <key>"
fi

log "done — workspace: $WS"
