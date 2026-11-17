#!/usr/bin/env bash
# Runs the tables of Ext groups for d = 2, 3, 3 with the special quadric, and 4.
# Light pairs: one process per surface.  The remaining pairs: one process per pair, each with its own
# time limit, a few at a time.  Results go to results/; a finished file is never recomputed.
#   scripts/overnight.sh            (from the repository root)
# Environment: HEAVY_LIMIT seconds per heavy pair (default 7200), JOBS parallel heavy pairs (default 4),
# MEM memory limit per process (default 10G, applied with systemd-run when it is available).
set -u
cd "$(dirname "$0")/.."
mkdir -p results
HEAVY_LIMIT="${HEAVY_LIMIT:-7200}"
JOBS="${JOBS:-4}"
MEM="${MEM:-10G}"

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
    if [ ! -s "$light.done" ]; then
        K3D="$d" K3SPECIAL="$special" K3TIER=light run_limited 43200 M2 --script scripts/ext-table.m2 > "$light" 2>&1
        echo "exit $?" > "$light.done"
    fi
    K3D="$d" K3SPECIAL="$special" K3TIER=list M2 --script scripts/ext-table.m2 2>/dev/null | grep -E '^[0-9]+ [0-9]+$' > "results/ext-$name-heavy.list"
    while read -r i j; do
        local out="results/ext-$name-heavy-$i-$j.txt"
        [ -s "$out" ] && continue
        while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do wait -n; done
        ( K3D="$d" K3SPECIAL="$special" K3PAIR="$i $j" run_limited "$HEAVY_LIMIT" M2 --script scripts/ext-table.m2 > "$out.part" 2>&1
          code=$?
          if [ "$code" -eq 124 ]; then echo "pair $i $j: no result within $HEAVY_LIMIT s" >> "$out.part"; fi
          mv "$out.part" "$out" ) &
    done < "results/ext-$name-heavy.list"
    wait
}

surface d2 2 0 &
surface d3 3 0 &
surface d3special 3 1 &
surface d4 4 0 &
wait
echo "finished $(date -u +%Y-%m-%dT%H:%MZ)" > results/overnight.done
