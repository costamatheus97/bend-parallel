#!/usr/bin/env bash
# bench/run.sh [-l lanes] [-r rounds] [driver ...]: builds the bench
# drivers (bench/scan.bend, histogram.bend, sort.bend by default) and runs
# them in interleaved rounds (round 1 on every lane, then round 2, ..),
# then prints the median ms per call of each line over the rounds.
#
# It only runs and prints: nothing is written to the repo, and nothing
# here is a recorded result. The numbers are only meaningful in a quiet
# window: no other heavy process on the CPU, and for the GPU lane nothing
# else on the GPU. Treat them as rough either way (IO.now has millisecond
# resolution; small sizes repeat the call to get above it, see lib.bend).
#
# Lanes (-l, comma-separated; default c1,c16):
#   c1, c16  $BEND builds a native binary; it runs on 1 and 16 threads
#   gpu      $BEND_HIP builds with its HIP lane; each `!` call runs on the
#            GPU. One GPU process at a time, each under timeout 300.
# Rounds: -r (default 3).
#
# Environment: BEND, BEND_HIP, CC and OUT as in run_tests.sh. The GPU lane
# needs whatever the HIP runtime wants in the environment (on WSL:
# HSA_ENABLE_DXG_DETECTION=1 and LD_LIBRARY_PATH to librocdxg).
#
# A line reads: lane, op (the -ref ops are ref.bend's sequential lists,
# timed on that lane's binary), d (2^d keys), b (fork depth), calls, the
# median ms per call, and the check (a hash that must agree across lanes).
set -u
cd "$(dirname "$0")"
LANES=c1,c16
ROUNDS=3
while [ $# -gt 0 ]; do
  case "$1" in
    -l) LANES=$2; shift 2 ;;
    -r) ROUNDS=$2; shift 2 ;;
    *) break ;;
  esac
done
DRIVERS=("$@")
[ ${#DRIVERS[@]} -eq 0 ] && DRIVERS=(scan histogram sort)
BEND=${BEND:-bend}
OUT=${OUT:-$(mktemp -d)}
mkdir -p "$OUT"
has() { case ",$LANES," in *",$1,"*) return 0 ;; esac; return 1; }
for d in "${DRIVERS[@]}"; do
  d=$(basename "$d" .bend)
  if has c1 || has c16; then
    $BEND "$d.bend" -o "$OUT/$d" >"$OUT/$d.build" 2>&1 || { echo "build failed: $OUT/$d.build"; exit 1; }
  fi
  if has gpu; then
    timeout 300 $BEND_HIP "$d.bend" -o "$OUT/$d.hip" >"$OUT/$d.hip.build" 2>&1 || { echo "GPU build failed: $OUT/$d.hip.build"; exit 1; }
  fi
done
raw=$OUT/raw.txt
: >"$raw"
for r in $(seq 1 "$ROUNDS"); do
  for d in "${DRIVERS[@]}"; do
    d=$(basename "$d" .bend)
    for lane in c1 c16 gpu; do
      has $lane || continue
      case $lane in
        c1) cmd=("$OUT/$d" --threads 1) ;;
        c16) cmd=("$OUT/$d" --threads 16) ;;
        gpu) cmd=(timeout 300 "$OUT/$d.hip") ;;
      esac
      "${cmd[@]}" >"$OUT/$d.$lane.$r" 2>"$OUT/$d.$lane.$r.err"
      rc=$?
      [ $rc -ne 0 ] && echo "round $r $d $lane: rc=$rc (see $OUT/$d.$lane.$r.err)"
      sed "s/^/$lane round=$r /" "$OUT/$d.$lane.$r" >>"$raw"
    done
  done
done
echo "# rough: medians of $ROUNDS interleaved rounds; raw lines in $raw"
python3 - "$raw" <<'EOF'
import re, sys, statistics
rows = {}
order = []
for line in open(sys.argv[1]):
    m = re.match(r'(\S+) round=\d+ (\S+) d=(\d+) b=(\d+) calls=(\d+) ms=(\d+) check=(\d+)', line)
    if not m:
        continue
    lane, op, d, b, calls, ms, check = m.groups()
    key = (op, int(d), int(b), lane)
    if key not in rows:
        order.append(key)
        rows[key] = ([], set(), int(calls))
    rows[key][0].append(int(ms) / int(calls))
    rows[key][1].add(check)
print(f"{'lane':5} {'op':9} {'d':>3} {'b':>3} {'calls':>6} {'ms/call':>10}  check")
for key in sorted(order, key=lambda k: (k[0], k[1], k[2], k[3])):
    op, d, b, lane = key
    ms, checks, calls = rows[key]
    check = checks.pop() if len(checks) == 1 else 'DIFFERS'
    print(f"{lane:5} {op:9} {d:>3} {b:>3} {calls:>6} {statistics.median(ms):>10.4f}  {check}")
EOF
