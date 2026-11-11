#!/usr/bin/env bash
# The Ubuntu 20.04 (focal) toolchain 7zzs 26.06 was built with (`.comment`: GCC 9.4.0-1ubuntu1~20.04.2; glibc 2.31),
# unpacked without installing (dpkg-deb -x, no maintainer script runs) into refs/focal/root, for the G0 rebuild that
# names 7-Zip's functions (tools/rebuild_focal.sh). The runtime archives are also unpacked one per directory under
# refs/focal/x for tools/libmatch.py. Every .deb must have the SHA-256 pinned in pins/focal.sha256.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd); F="$root/refs/focal"; mkdir -p "$F/deb" "$F/root"
P=https://archive.ubuntu.com/ubuntu/pool/main
G=9.4.0-1ubuntu1~20.04.2; B=2.34-6ubuntu1.11
debs=(
  g/gcc-9/gcc-9_$G g/gcc-9/g++-9_$G g/gcc-9/cpp-9_$G g/gcc-9/gcc-9-base_$G g/gcc-9/libgcc-9-dev_$G
  g/gcc-9/libstdc++-9-dev_$G
  b/binutils/binutils_$B b/binutils/binutils-x86-64-linux-gnu_$B b/binutils/binutils-common_$B
  b/binutils/libbinutils_$B b/binutils/libctf0_$B b/binutils/libctf-nobfd0_$B
  g/glibc/libc6-dev_2.31-0ubuntu9.18 l/linux/linux-libc-dev_5.4.0-218.238
  i/isl/libisl22_0.22.1-1 m/mpclib3/libmpc3_1.1.0-1 m/mpfr4/libmpfr6_4.0.2-1 g/gmp/libgmp10_6.2.0+dfsg-4ubuntu0.1
)
for d in "${debs[@]}"; do
  f="${d##*/}_amd64.deb"
  [ -s "$F/deb/$f" ] || curl -sfL -o "$F/deb/$f" "$P/${d%/*}/$(printf %s "$f" | sed 's/+/%2b/g; s/~/%7e/g')"
done
# every package must have the SHA-256 pinned in pins/focal.sha256 before anything is unpacked
(cd "$F/deb" && sha256sum --quiet -c "$root/pins/focal.sha256")
cp "$root/pins/focal.sha256" "$F/SHA256SUMS"
for d in "${debs[@]}"; do dpkg-deb -x "$F/deb/${d##*/}_amd64.deb" "$F/root"; done
# the runtime archives for tools/libmatch.py, one directory per package
x() { rm -rf "$F/x/$2"; mkdir -p "$F/x/$2"; dpkg-deb -x "$F/deb/$1" "$F/x/$2"; }
x libc6-dev_2.31-0ubuntu9.18_amd64.deb libc6-dev-9.18
x "libgcc-9-dev_${G}_amd64.deb" libgcc-9-dev
x "libstdc++-9-dev_${G}_amd64.deb" libstdc++-9-dev
echo "unpacked $(ls "$F/deb" | wc -l) packages (SHA-256 as pinned) into $F/root and the runtime archives into $F/x"
