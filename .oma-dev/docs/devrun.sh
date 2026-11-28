#!/usr/bin/env bash
# devrun <worktree-dir> : wait for the cloud-dev run of the worktree's HEAD commit and print its errors.
# Exit 0 if the build passed with no sorry, 1 otherwise.
set -uo pipefail
DIR="${1:-.}"
REPO=FarzanAhmedHossain/open-math-agents
SHA=$(git -C "$DIR" rev-parse HEAD)
BR=$(git -C "$DIR" rev-parse --abbrev-ref HEAD)
ID=""
for i in $(seq 1 30); do
  ID=$(gh run list --repo "$REPO" --branch "$BR" --workflow cloud-dev --limit 10 --json databaseId,headSha \
        --jq ".[] | select(.headSha == \"$SHA\") | .databaseId" | head -1)
  [ -n "$ID" ] && break
  sleep 10
done
[ -n "$ID" ] || { echo "devrun: no cloud-dev run found for $SHA on $BR"; exit 2; }
echo "devrun: run $ID (https://github.com/$REPO/actions/runs/$ID)"
gh run watch "$ID" --repo "$REPO" --interval 30 > /dev/null 2>&1
OUT=$(mktemp -d)
gh run download "$ID" --repo "$REPO" -n build-log -D "$OUT" > /dev/null 2>&1 || { echo "devrun: no build log"; gh run view "$ID" --repo "$REPO" --log-failed | tail -40; exit 1; }
L="$OUT/build.log"
mkdir -p "$HOME/.oma-dev-logs"; cp "$L" "$HOME/.oma-dev-logs/$(echo "$BR" | tr / _).log" 2>/dev/null || true
E=$(grep -c 'error:' "$L" || true); S=$(grep -cE 'declaration uses .sorry.' "$L" || true)
echo "devrun: errors=$E sorries=$S $(grep '^exit=' "$L")"
grep -n -A 16 'error:' "$L" | head -400
grep -nE 'declaration uses .sorry.' "$L" | head -50
grep -q '^exit=0$' "$L" && [ "$S" = "0" ]
