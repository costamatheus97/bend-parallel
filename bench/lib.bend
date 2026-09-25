# lib.bend: what the bench drivers share. Timing is IO.now (milliseconds)
# around a run of calls; each driver makes the timed work depend on the
# start time (x * 0 added to an argument), so it cannot run before it.
import Base
import ../tests/lib/check.bend as C

# The value of an (array, value) pair, as a[i] gives it.
def val(r: Array<U32> & U32) -> U32:
  (a, +x) = r
  x

# 0, computed from t, so that work fed with it waits for t.
def zero(+t: Nat) -> Nat:
  Nat.mul(t, 0n)

# One result line: op, lane-independent config, calls, total ms, check.
def line(op: String, +d: Nat, +b: Nat, +calls: Nat, +t0: Nat, +t1: Nat, +c: U32) -> String:
  op ++ " d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " calls=" ++ Nat.show(calls)
    ++ " ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " check=" ++ U32.show(c)

# How many calls to time at 2^d keys: 2^(20 - d), at least 1, so that a
# small size still runs for milliseconds.
def calls(+d: Nat) -> Nat:
  U32.to_nat(U32.shln(1, Nat.sub(20n, d)))

# The hash of a list that came with its array (tests/lib/check.bend's).
def hash(r: Array<U32> & List<&2, U32>) -> U32:
  (a, xs) = r
  C.hash(xs)
