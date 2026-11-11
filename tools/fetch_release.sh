#!/usr/bin/env bash
# The author's release the project verifies (PLAN.md, the header): release/26.06/7z2606-linux-x64.tar.xz from
# GitHub, and its 7zz and 7zzs, each with the SHA-256 of pins/release-26.06.sha256 (the tarball is checked before it
# is unpacked). A file already there is checked, not fetched again. Used by tools/setup.sh and the workflows.
# Usage: tools/fetch_release.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
V=26.06; R=release/$V; T=7z${V/./}-linux-x64.tar.xz; P="$root/pins/release-$V.sha256"
mkdir -p "$R"
[ -s "$R/$T" ] || curl -sfL -o "$R/$T" "https://github.com/ip7z/7zip/releases/download/$V/$T"
(cd "$R" && grep " $T\$" "$P" | sha256sum --quiet -c)
[ -s "$R/7zzs" ] && [ -s "$R/7zz" ] || tar -xJf "$R/$T" -C "$R" 7zz 7zzs
(cd "$R" && sha256sum --quiet -c "$P")
cp "$P" "$R/SHA256SUMS"
echo "ok: $R/7zz, $R/7zzs as pinned"
