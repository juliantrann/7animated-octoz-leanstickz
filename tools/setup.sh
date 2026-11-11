#!/usr/bin/env bash
# Sets up everything the project builds on, from a checkout of this repository, each piece pinned (PLAN.md §7, G0):
#   Lean            leanprover/lean4:v4.34.0 (Zellic's statements, this project) and v4.35.0 (`lake comparator`,
#                   with the kernels con-leche, con-ron, nanoda), through elan
#   refs/zellic-x86 Zellic's model at commit 059a6a9 with patches/zellic-x86.patch (tools/zellic_patch.sh)
#   refs/lean4export at commit 076e8e5 (tag v4.34.0), built
#   upstream/7zip   7-Zip's sources at commit d3296e3 (tag 26.06), for the G0 rebuild that names functions
#   release/26.06   the author's release tarball and its 7zz, 7zzs, with the SHA-256 of pins/release-26.06.sha256
#                   (tools/fetch_release.sh)
#   refs/focal      the Ubuntu 20.04 toolchain 7zzs was built with (tools/fetch_focal.sh, pins/focal.sha256)
#   build/rebuild   7-Zip's objects compiled with it (tools/rebuild_focal.sh), for the names in CODEMAP.md
# A piece already there is checked against its pin, not fetched again. Downloads are data: the tarball and the .debs
# are checked before they are unpacked, and .debs are unpacked with dpkg-deb -x (no maintainer script runs).
# Needs: git, curl, elan, gcc, binutils (objdump, c++filt), python3, dpkg-deb, xz, strace, bwrap.
# Usage: tools/setup.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
for t in git curl elan gcc objdump c++filt python3 dpkg-deb xz strace bwrap; do
  command -v "$t" >/dev/null || { echo "missing: $t" >&2; exit 1; }
done

echo "== Lean toolchains"
elan toolchain install leanprover/lean4:v4.34.0 >/dev/null 2>&1 || true
elan toolchain install leanprover/lean4:v4.35.0 >/dev/null 2>&1 || true
elan toolchain list | grep -q 'v4.34.0' && elan toolchain list | grep -q 'v4.35.0'

# clone URL DIR COMMIT: DIR at COMMIT (cloned if absent; an existing DIR at another commit, as a cache made for an
# earlier pin holds, is moved to COMMIT if its work tree is clean, and is an error otherwise)
clone() {
  if [ ! -d "$2/.git" ]; then git clone -q "$1" "$2"; git -C "$2" checkout -q "$3"; fi
  if [ "$(git -C "$2" rev-parse HEAD)" != "$3" ] && [ -z "$(git -C "$2" status --porcelain)" ]; then
    git -C "$2" fetch -q --tags origin; git -C "$2" checkout -q "$3"
  fi
  [ "$(git -C "$2" rev-parse HEAD)" = "$3" ] || { echo "FAIL: $2 is not at $3" >&2; exit 1; }
  echo "ok: $2 at $3"
}

echo "== sources"
mkdir -p refs upstream
fresh=0; [ -d refs/zellic-x86/.git ] || fresh=1
clone https://github.com/Zellic/x86-formal-verification-research.git refs/zellic-x86 \
  059a6a9dc31a974b01b6aeebfa5c88f9dc37c3ac
if [ $fresh = 1 ]; then git -C refs/zellic-x86 checkout -q -b fv7z-g1; tools/zellic_patch.sh apply; fi
# in CI the copy may come from a cache made with an older patch: apply the current one afresh (never locally, where
# that would discard model changes not yet saved to the patch)
if [ "${CI:-}" = true ] && ! tools/zellic_patch.sh check 2>/dev/null; then tools/zellic_patch.sh reapply; fi
tools/zellic_patch.sh check
clone https://github.com/leanprover/lean4export refs/lean4export 076e8e57707e813375e8f9da8bf989799ace9680
[ -x refs/lean4export/.lake/build/bin/lean4export ] || (cd refs/lean4export && lake build >/dev/null)
clone https://github.com/ip7z/7zip.git upstream/7zip d3296e39e1f1f92c7b41c0c3848e65640428d42d

echo "== release 26.06"
tools/fetch_release.sh

echo "== Ubuntu 20.04 toolchain"
tools/fetch_focal.sh
echo "== GCC 9.4 rebuild of 7-Zip's objects (names for CODEMAP.md)"
# rebuilt when the objects there were compiled from another commit (build/rebuild/commit)
[ -s build/rebuild/7zip-objs.a ] && [ "$(cat build/rebuild/commit 2>/dev/null)" = d3296e39e1f1f92c7b41c0c3848e65640428d42d ] ||
  tools/rebuild_focal.sh
echo "setup done"
