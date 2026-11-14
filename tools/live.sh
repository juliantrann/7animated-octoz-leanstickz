#!/usr/bin/env bash
# Live status of a CI job while it runs (GitHub gives a job's log only once the job ends).
#   tools/live.sh start NAME LOG   in the background: a check run NAME on this commit, its output every 120 s:
#                                  the lean processes (age s, CPU s, RSS MB, module), memory, the tail of LOG
#   tools/live.sh stop NAME        marks the check run NAME completed (call from an `if: always()` step)
# Read it while the job runs:
#   gh api repos/OWNER/REPO/commits/SHA/check-runs -q '.check_runs[]|select(.name=="NAME")|.output.summary'
# Needs GH_TOKEN (the job's github.token with `checks: write`). Never fails the job.
set -u
cmd=${1:-}; name=${2:-live}; log=${3:-/dev/null}
idf=${RUNNER_TEMP:-/tmp}/live-$name.id
api() { gh api "$@" 2>/dev/null; }
case $cmd in
start)
  id=$(api -X POST "repos/$GITHUB_REPOSITORY/check-runs" -f name="$name" -f head_sha="$GITHUB_SHA" \
    -f status=in_progress -q .id) || exit 0
  [ -n "$id" ] || exit 0
  echo "$id" > "$idf"
  t0=$(date +%s)
  sleep 30; while :; do
    t=$(( $(date +%s) - t0 ))
    body=$( {
      echo "t = $t s, run $GITHUB_RUN_ID"
      echo '```'
      free -m | sed -n 2p
      ps -C lean -o etimes=,times=,rss=,args= |
        awk '{m=$NF; for(i=4;i<=NF;i++) if($i ~ /FV7z\//) m=$i; sub(/\.(setup\.json|lean)$/, "", m)
          printf "%6ds %6ds cpu %6d MB %s\n", $1, $2, $3/1024, m}'
      echo '---'
      tail -n 40 "$log" 2>/dev/null | cut -c1-200
      echo '```'
    } | head -c 60000 )
    api -X PATCH "repos/$GITHUB_REPOSITORY/check-runs/$id" -f "output[title]=t = $t s" \
      -f "output[summary]=$body" >/dev/null || true
    sleep 120
  done ;;
stop)
  [ -f "$idf" ] || exit 0
  api -X PATCH "repos/$GITHUB_REPOSITORY/check-runs/$(cat "$idf")" -f status=completed -f conclusion=neutral \
    >/dev/null || true ;;
esac
exit 0
