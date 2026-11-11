#!/usr/bin/env bash
# The project's changes to Zellic's model (PLAN.md §6, G1) are kept as one patch, patches/zellic-x86.patch, against
# the pinned commit; refs/zellic-x86 is that commit with the patch applied (tools/setup.sh). Every change in it is marked
# "FV_7zip G1" (or the stage that made it).
#   save   write refs/zellic-x86's changes (new files included) to the patch, after changing the model
#   apply  apply the patch to a clean checkout of the pinned commit (tools/setup.sh)
#   check  fail unless refs/zellic-x86 is the pinned commit with exactly the patch applied (tools/ci.sh)
#   reapply  discard refs/zellic-x86's changes (untracked files too, build outputs kept) and apply the patch again:
#            for a copy restored from a cache made with an older patch (CI); it destroys unsaved model changes
# Usage: tools/zellic_patch.sh save|apply|check|reapply
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd); Z="$root/refs/zellic-x86"; P="$root/patches/zellic-x86.patch"
PIN=059a6a9dc31a974b01b6aeebfa5c88f9dc37c3ac
diff_() { git -C "$Z" add --intent-to-add --all; git -C "$Z" diff --binary "$PIN"; }
case "${1:-}" in
  save) diff_ > "$P"; echo "saved $(grep -c '^diff --git' "$P") files' changes to $P" ;;
  apply)
    [ "$(git -C "$Z" rev-parse HEAD)" = "$PIN" ] || { echo "refs/zellic-x86 is not at $PIN" >&2; exit 1; }
    git -C "$Z" diff --quiet "$PIN" || { echo "refs/zellic-x86 has changes already" >&2; exit 1; }
    git -C "$Z" apply "$P"; echo "applied $P" ;;
  check)
    [ "$(git -C "$Z" rev-parse HEAD)" = "$PIN" ] || { echo "FAIL: refs/zellic-x86 HEAD is not $PIN" >&2; exit 1; }
    if diff_ | cmp -s - "$P"; then echo "ok: refs/zellic-x86 = $PIN + patches/zellic-x86.patch"
    else echo "FAIL: refs/zellic-x86 differs from $PIN + the patch (after changing the model: tools/zellic_patch.sh save)" >&2; exit 1; fi ;;
  reapply)
    git -C "$Z" reset -q --hard "$PIN"; git -C "$Z" clean -qfd; git -C "$Z" apply "$P"; echo "reapplied $P" ;;
  *) echo "usage: $0 save|apply|check|reapply" >&2; exit 2 ;;
esac
