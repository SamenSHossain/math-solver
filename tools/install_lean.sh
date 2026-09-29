#!/usr/bin/env bash
# Install elan, the Lean toolchain pinned in ./lean-toolchain, and Mathlib with
# its prebuilt cache, so proofs can be checked locally before submission.
#
# Hosts used: github.com (git + release assets), release-assets.githubusercontent.com,
# lakecache.blob.core.windows.net (Mathlib cache). It does NOT need
# elan.lean-lang.org or release.lean-lang.org; if elan cannot reach those, the
# toolchain is fetched from GitHub releases and linked into elan.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ELAN_VERSION="${ELAN_VERSION:-v4.1.2}"
TOOLCHAIN="$(tr -d '[:space:]' < "$ROOT/lean-toolchain")"   # leanprover/lean4:v4.33.1
LEAN_TAG="${TOOLCHAIN##*:}"                                   # v4.33.1
TC_DIR="$HOME/.elan/toolchains/$(printf '%s' "$TOOLCHAIN" | sed 's#/#--#; s#:#---#')"
export PATH="$HOME/.elan/bin:$PATH"
CURL=(curl -sSfL --retry 6 --retry-all-errors --retry-delay 2)

echo ">>> Setting up local Lean verification: installing elan, $TOOLCHAIN, and the prebuilt Mathlib cache."

# 1. elan (toolchain manager), from GitHub releases
if ! command -v elan >/dev/null 2>&1; then
  tmp="$(mktemp -d)"
  "${CURL[@]}" "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-x86_64-unknown-linux-gnu.tar.gz" | tar -xz -C "$tmp"
  "$tmp/elan-init" -y --no-modify-path --default-toolchain none
  rm -rf "$tmp"
fi
echo "elan: $(elan --version)"

# 2. the pinned Lean toolchain: elan first, GitHub release tarball as fallback
if [ ! -x "$TC_DIR/bin/lean" ]; then
  if ! elan toolchain install "$TOOLCHAIN"; then
    echo ">>> elan could not download $TOOLCHAIN; fetching it from GitHub releases instead"
    rm -rf "$TC_DIR"; mkdir -p "$TC_DIR"; tmp="$(mktemp -d)"
    "${CURL[@]}" -o "$tmp/lean.tar.zst" "https://github.com/leanprover/lean4/releases/download/$LEAN_TAG/lean-${LEAN_TAG#v}-linux.tar.zst"
    if command -v zstd >/dev/null 2>&1; then
      zstd -dc "$tmp/lean.tar.zst" | tar -x -C "$TC_DIR" --strip-components=1
    else
      python3 -c 'import zstandard' 2>/dev/null || python3 -m pip install -q zstandard
      python3 - "$tmp/lean.tar.zst" "$TC_DIR" <<'PY'
import sys, tarfile, zstandard
src, dst = sys.argv[1], sys.argv[2]
with open(src, "rb") as f, zstandard.ZstdDecompressor().stream_reader(f) as r, tarfile.open(fileobj=r, mode="r|") as t:
    for m in t:
        parts = m.name.split("/", 1)
        if len(parts) < 2:
            continue
        m.name = parts[1]
        t.extract(m, dst)
PY
    fi
    rm -rf "$tmp"
  fi
fi
echo "lean: $("$TC_DIR/bin/lean" --version)"

# 3. Mathlib at the pinned revision + prebuilt .olean cache, then the smoke test
cd "$ROOT"
lake --version
if [ ! -d .lake/packages/mathlib ]; then lake update; fi
echo "mathlib rev: $(git -C .lake/packages/mathlib rev-parse HEAD)"
lake exe cache get
lake build Solutions.SmokeTest
echo ">>> Local Lean verification is ready."
