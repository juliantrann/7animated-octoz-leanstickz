#!/usr/bin/env bash
# G0 rebuild for naming (PLAN.md §8): compiles 7-Zip 26.06's objects of the 7zz/7zzs bundle (CPP/7zip/Bundles/Alone2,
# cmpl_gcc_x64.mak, USE_ASM=1) with the focal toolchain of tools/fetch_focal.sh, run in place (not installed) through
# `gcc`/`g++` wrappers first on PATH, so the makefiles see the names they test for. The assembly modules need asmc,
# which is not used here: make runs with -k and they are left out (they are named by their instructions, CODEMAP.md).
# Objects only, no link: tools/libmatch.py matches their functions against 7zzs. Output: build/rebuild/7zip-objs.a
# Not part of the trusted base: the names only help people and automation read the binary.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd); R="$root/refs/focal/root"; out="$root/build/rebuild"
rm -rf "$out"; mkdir -p "$out/bin"
for t in gcc:gcc-9 g++:g++-9; do
  cat > "$out/bin/${t%%:*}" <<W
#!/bin/sh
LD_LIBRARY_PATH="$R/usr/lib/x86_64-linux-gnu" exec "$R/usr/bin/${t#*:}" --sysroot="$R" -B"$R/usr/bin/" "\$@"
W
  chmod +x "$out/bin/${t%%:*}"
done
commit=d3296e39e1f1f92c7b41c0c3848e65640428d42d
git -C "$root/upstream/7zip" archive $commit | tar -x -C "$out" --one-top-level=src
cd "$out/src/CPP/7zip/Bundles/Alone2"
PATH="$out/bin:$PATH" make -k -j"$(nproc)" -f ../../cmpl_gcc_x64.mak > "$out/make.log" 2>&1 || true
objs=$(find b/g_x64 -name '*.o' | sort)
echo "$(echo "$objs" | wc -l) objects; failures: $(grep -c 'Error' "$out/make.log" || true) (see $out/make.log)"
ar rcs "$out/7zip-objs.a" $objs
echo $commit > "$out/commit"
