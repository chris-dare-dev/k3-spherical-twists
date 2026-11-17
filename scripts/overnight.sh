#!/usr/bin/env bash
# Runs the tables of Ext groups for d = 2, 3, 3 with the special quadric, and 4, one surface after
# the other.  Light pairs: one process per surface, restarted after the pair in progress if it is
# killed at the memory limit.  The remaining pairs: one process per pair with its own time limit.
# Results go to results/; pairs that already have a result are not recomputed.
#   scripts/overnight.sh            (from the repository root)
# Environment: HEAVY_LIMIT seconds per heavy pair (default 3600), MEM memory limit per process
# (default 12G, applied with systemd-run when it is available), SURFACES (default "d2 d3 d3special d4").
set -u
cd "$(dirname "$0")/.."
mkdir -p results
HEAVY_LIMIT="${HEAVY_LIMIT:-3600}"
MEM="${MEM:-12G}"
SURFACES="${SURFACES:-d2 d3 d3special d4}"

run_limited() {   # run_limited SECONDS command...
    local secs="$1"; shift
    if command -v systemd-run >/dev/null 2>&1 && systemd-run --user --scope -q true 2>/dev/null; then
        timeout "$secs" systemd-run --user --scope -q -p MemoryMax="$MEM" -p MemorySwapMax=0 "$@"
    else
        timeout "$secs" "$@"
    fi
}

surface() {       # surface NAME D SPECIAL
    local name="$1" d="$2" special="$3"
    local light="results/ext-$name-light.txt"
    local code last
    while [ ! -e "$light.done" ]; do
        K3D="$d" K3SPECIAL="$special" K3TIER=light K3RESUME="$light" \
            run_limited 43200 M2 --script scripts/ext-table.m2 2>/dev/null | grep -v '^ --' >> "$light"
        code=${PIPESTATUS[0]}
        if [ "$code" -eq 0 ] || [ "$code" -eq 1 ]; then
            echo "exit $code" > "$light.done"
        else
            # killed or out of time: mark the pair that was in progress and go on with the next
            last="$(grep '^# start ' "$light" | tail -1 | sed 's/^# start //')"
            if [ -z "$last" ]; then echo "status $code before the first pair" > "$light.done"; break; fi
            # shellcheck disable=SC2086
            printf '%-14s%-14s%-18s (process ended with status %s, memory limit %s)\n' $last "killed" "$code" "$MEM" >> "$light"
        fi
    done
    K3D="$d" K3SPECIAL="$special" K3TIER=list M2 --script scripts/ext-table.m2 2>/dev/null \
        | grep -E '^[0-9]+ [0-9]+$' > "results/ext-$name-heavy.list"
    local i j out
    while read -r i j; do
        out="results/ext-$name-heavy-$i-$j.txt"
        [ -s "$out" ] && continue
        K3D="$d" K3SPECIAL="$special" K3PAIR="$i $j" \
            run_limited "$HEAVY_LIMIT" M2 --script scripts/ext-table.m2 2>/dev/null | grep -v '^ --' > "$out.part"
        code=${PIPESTATUS[0]}
        if [ "$code" -eq 124 ]; then
            echo "pair $i $j: no result within $HEAVY_LIMIT s" >> "$out.part"
        elif [ "$code" -ne 0 ] && [ "$code" -ne 1 ]; then
            echo "pair $i $j: killed, status $code, memory limit $MEM" >> "$out.part"
        fi
        mv "$out.part" "$out"
    done < "results/ext-$name-heavy.list"
}

for name in $SURFACES; do
    case "$name" in
        d2) surface d2 2 0 ;;
        d3) surface d3 3 0 ;;
        d3special) surface d3special 3 1 ;;
        d4) surface d4 4 0 ;;
    esac
done
echo "finished $(date -u +%Y-%m-%dT%H:%MZ)" > results/overnight.done
