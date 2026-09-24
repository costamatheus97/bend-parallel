#!/usr/bin/env bash
# run_tests.sh [-l lanes] [test.bend ...]: runs every test (tests/*.bend
# by default) on each lane and compares its output with the #| lines at
# the end of the file.
#
# Lanes (-l, comma-separated; default check,js,c1,c16):
#   check    $BEND t.bend --check-only prints no error
#   js       $BEND builds t.js; bun runs it (sequential)
#   c1, c16  $BEND builds a native binary; it runs on 1 and 16 threads
#   check24  $BEND_HIP t.bend --check-only (the second compiler)
#   gpu      $BEND_HIP builds with its HIP lane; the binary runs its `!`
#            calls on the GPU, one process at a time, under timeout 300
#
# Environment:
#   BEND      the compiler for check, js, c1, c16 (default: bend), e.g.
#             "bun /path/to/bend/bend2/main.ts" for upstream 2.0.27
#   BEND_HIP  the compiler with a HIP lane, for check24 and gpu
#   CC        a clang >= 14 (>= 19 for a GPU build)
#   OUT       where binaries go (default: a fresh temp dir)
# A GPU run also needs whatever the HIP runtime wants in the environment
# (on WSL: HSA_ENABLE_DXG_DETECTION=1 and LD_LIBRARY_PATH to librocdxg).
set -u
cd "$(dirname "$0")"
LANES=check,js,c1,c16
if [ "${1:-}" = "-l" ]; then
  LANES=$2
  shift 2
fi
TESTS=("$@")
[ ${#TESTS[@]} -eq 0 ] && TESTS=(tests/*.bend)
BEND=${BEND:-bend}
OUT=${OUT:-$(mktemp -d)}
mkdir -p "$OUT"
export BUN_JSC_maxPerThreadStackUsage=33554432
has() { case ",$LANES," in *",$1,"*) return 0 ;; esac; return 1; }
pass=0
fail=0
report() { # lane test ok detail
  if [ "$3" = 1 ]; then
    pass=$((pass + 1))
    printf 'PASS %-8s %s\n' "$1" "$2"
  else
    fail=$((fail + 1))
    printf 'FAIL %-8s %s %s\n' "$1" "$2" "$4"
  fi
}
same() { # want-file got-file
  diff -q "$1" "$2" >/dev/null 2>&1 && echo 1 || echo 0
}
for t in "${TESTS[@]}"; do
  name=$(basename "$t" .bend)
  want=$OUT/$name.want
  grep '^#|' "$t" | sed 's/^#|//' >"$want"
  if has check; then
    out=$($BEND "$t" --check-only 2>&1)
    ok=1
    echo "$out" | grep -q '^Error' && ok=0
    report check "$name" $ok "$(echo "$out" | head -3)"
  fi
  if has check24; then
    out=$($BEND_HIP "$t" --check-only 2>&1)
    ok=1
    echo "$out" | grep -q '^Error' && ok=0
    report check24 "$name" $ok "$(echo "$out" | head -3)"
  fi
  if has js || has c1 || has c16; then
    if ! $BEND "$t" -o "$OUT/$name.js" -o "$OUT/$name" >"$OUT/$name.build" 2>&1; then
      for l in js c1 c16; do
        has $l && report $l "$name" 0 "(build failed: $OUT/$name.build)"
      done
    else
      if has js; then
        bun "$OUT/$name.js" >"$OUT/$name.js.got" 2>&1
        report js "$name" "$(same "$want" "$OUT/$name.js.got")" "($OUT/$name.js.got)"
      fi
      for n in 1 16; do
        if has c$n; then
          "$OUT/$name" --threads $n >"$OUT/$name.c$n.got" 2>&1
          report c$n "$name" "$(same "$want" "$OUT/$name.c$n.got")" "($OUT/$name.c$n.got)"
        fi
      done
    fi
  fi
  if has gpu; then
    if ! timeout 300 $BEND_HIP "$t" -o "$OUT/$name.hip" >"$OUT/$name.hip.build" 2>&1; then
      report gpu "$name" 0 "(build failed: $OUT/$name.hip.build)"
    else
      BEND_GPU_STATS=1 timeout 300 "$OUT/$name.hip" >"$OUT/$name.gpu.got" 2>"$OUT/$name.gpu.err"
      rc=$?
      turns=$(grep -o 'hip [0-9]* turns' "$OUT/$name.gpu.err" | head -1)
      ok=$(same "$want" "$OUT/$name.gpu.got")
      [ -z "$turns" ] && ok=0
      report gpu "$name" "$ok" "(rc=$rc ${turns:-no device turns}; $OUT/$name.gpu.got)"
    fi
  fi
done
echo "passed $pass, failed $fail (outputs in $OUT)"
[ $fail -eq 0 ]
