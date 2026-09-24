# Scan edge cases, under `!`, against ref.bend: one entry (0, 7, the
# largest U32) at b 0 and 3; 1024 equal entries (1: the scan is 0, 1, ..;
# the largest U32: every sum wraps); 4096 largest entries at b 5; b far
# past log2 n; 16384 random entries at b 8 (the JS lane's stack holds the
# list reference's recursion up to about this size; 65536 overflows it).
# A line reads: the scan, the case, diff against the reference (plus 1 if
# the totals differ), the hash and the total. The hashes and totals come
# from tests/lib/expect.py.
import Base
import ../scan.bend as Scan
import ../ref.bend as Ref
import ./lib/check.bend as C

def par(+inc: Bool, +b: Nat, a: Array<U32>) -> Array<U32> & U32:
  match inc:
    case False{}:
      Scan.exclusive(b, a)
    case True{}:
      Scan.inclusive(b, a)

def refr(+inc: Bool, xs: List<&2, U32>) -> List<&2, U32> & U32:
  match inc:
    case False{}:
      Ref.exclusive(xs)
    case True{}:
      Ref.inclusive(xs)

def show.fin(+t: U32, want: List<&2, U32> & U32, r: Array<U32> & List<&2, U32>) -> String:
  (ws, +wt) = want
  (a, +got) = r
  "diff=" ++ Nat.show(Nat.add(C.diff(got, ws), C.one(U32.is_eq(t, wt)))) ++ " hash="
    ++ U32.show(C.hash(got)) ++ " total=" ++ U32.show(t)

def show(want: List<&2, U32> & U32, r: Array<U32> & U32) -> String:
  (a, +t) = r
  show.fin(t, want, C.to_list(a))

def name(b: Bool) -> String:
  match b:
    case False{}:
      "ex"
    case True{}:
      "in"

# 2^d entries of generator (kind, seed, m), at fork depth b.
def one_case(+inc: Bool, +d: Nat, +b: Nat, +kind: U32, +seed: U32, +m: U32) -> IO(Unit):
  IO.print(name(inc) ++ " d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " kind=" ++ U32.show(kind)
    ++ " m=" ++ U32.show(m) ++ " " ++ show(refr(inc, C.list(d, kind, seed, m)),
    par!(inc, b, C.fill(d, kind, seed, m))))

def both(+inc: Bool) -> IO(Unit):
  do IO<Unit>:
    Unit <- one_case(inc, 0n, 0n, 2, 0, 0)
    Unit <- one_case(inc, 0n, 3n, 2, 0, 7)
    Unit <- one_case(inc, 0n, 0n, 2, 0, 4294967295)
    Unit <- one_case(inc, 0n, 3n, 0, 5, 0)
    Unit <- one_case(inc, 10n, 4n, 2, 0, 1)
    Unit <- one_case(inc, 10n, 0n, 2, 0, 4294967295)
    Unit <- one_case(inc, 12n, 5n, 2, 0, 4294967295)
    Unit <- one_case(inc, 3n, 30n, 0, 9, 0)
    one_case(inc, 14n, 8n, 0, 16, 0)

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- both(False{})
    both(True{})

#|ex d=0 b=0 kind=2 m=0 diff=0 hash=0 total=0
#|ex d=0 b=3 kind=2 m=7 diff=0 hash=0 total=7
#|ex d=0 b=0 kind=2 m=4294967295 diff=0 hash=0 total=4294967295
#|ex d=0 b=3 kind=0 m=0 diff=0 hash=0 total=3693475633
#|ex d=10 b=4 kind=2 m=1 diff=0 hash=3101179904 total=1024
#|ex d=10 b=0 kind=2 m=4294967295 diff=0 hash=1153586176 total=4294966272
#|ex d=12 b=5 kind=2 m=4294967295 diff=0 hash=1208102912 total=4294963200
#|ex d=3 b=30 kind=0 m=0 diff=0 hash=2982198000 total=4012700955
#|ex d=14 b=8 kind=0 m=0 diff=0 hash=687737219 total=2270931363
#|in d=0 b=0 kind=2 m=0 diff=0 hash=0 total=0
#|in d=0 b=3 kind=2 m=7 diff=0 hash=7 total=7
#|in d=0 b=0 kind=2 m=4294967295 diff=0 hash=4294967295 total=4294967295
#|in d=0 b=3 kind=0 m=0 diff=0 hash=3693475633 total=3693475633
#|in d=10 b=4 kind=2 m=1 diff=0 hash=3284419584 total=1024
#|in d=10 b=0 kind=2 m=4294967295 diff=0 hash=2414864384 total=4294966272
#|in d=12 b=5 kind=2 m=4294967295 diff=0 hash=3721183232 total=4294963200
#|in d=3 b=30 kind=0 m=0 diff=0 hash=2801818347 total=4012700955
#|in d=14 b=8 kind=0 m=0 diff=0 hash=3356743472 total=2270931363
