# Exclusive and inclusive scans of random 32-bit entries (the sums wrap)
# at 2^d entries for d in {0, 1, 2, 5, 8, 11} and fork depths b in
# {0, 1, 3, 6, 12} (b past d is lowered to d), each run under `!` and
# compared with ref.bend's scan. A line reads: the scan, d, b, diff (the
# entries that differ from the reference, plus 1 if the totals differ),
# the hash of the parallel result and its total. The hashes and totals
# come from tests/lib/expect.py, not from Bend.
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

def one_case(+inc: Bool, +d: Nat, +b: Nat) -> IO(Unit):
  +seed = (U32.from_nat(d) * 1000 + U32.from_nat(b) : U32)
  IO.print(name(inc) ++ " d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " "
    ++ show(refr(inc, C.list(d, 0, seed, 0)), par!(inc, b, C.fill(d, 0, seed, 0))))

def bs(+inc: Bool, +d: Nat, xs: List<&2, Nat>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case b <> t:
      do IO<Unit>:
        Unit <- one_case(inc, d, b)
        bs(inc, d, t)

def ds(+inc: Bool, xs: List<&2, Nat>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case d <> t:
      do IO<Unit>:
        Unit <- bs(inc, d, [0n, 1n, 3n, 6n, 12n])
        ds(inc, t)

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- ds(False{}, [0n, 1n, 2n, 5n, 8n, 11n])
    ds(True{}, [0n, 1n, 2n, 5n, 8n, 11n])

#|ex d=0 b=0 diff=0 hash=0 total=3224134966
#|ex d=0 b=1 diff=0 hash=0 total=3424972597
#|ex d=0 b=3 diff=0 hash=0 total=3559226163
#|ex d=0 b=6 diff=0 hash=0 total=3626889520
#|ex d=0 b=12 diff=0 hash=0 total=4029631802
#|ex d=1 b=0 diff=0 hash=1094699484 total=1125878976
#|ex d=1 b=1 diff=0 hash=1295467487 total=1393232068
#|ex d=1 b=3 diff=0 hash=1429657561 total=1929980092
#|ex d=1 b=6 diff=0 hash=1497259482 total=3264977047
#|ex d=1 b=12 diff=0 hash=2964335909 total=571268064
#|ex d=2 b=0 diff=0 hash=4263069111 total=400048673
#|ex d=2 b=1 diff=0 hash=2211685357 total=1205358119
#|ex d=2 b=3 diff=0 hash=236710189 total=1742151203
#|ex d=2 b=6 diff=0 hash=325144455 total=2547343917
#|ex d=2 b=12 diff=0 hash=152210191 total=1465859612
#|ex d=5 b=0 diff=0 hash=1930348738 total=2211542667
#|ex d=5 b=1 diff=0 hash=4002917388 total=2044055345
#|ex d=5 b=3 diff=0 hash=3374069193 total=3000196686
#|ex d=5 b=6 diff=0 hash=2388458789 total=3301044677
#|ex d=5 b=12 diff=0 hash=4215676919 total=468309807
#|ex d=8 b=0 diff=0 hash=2198786242 total=2307936655
#|ex d=8 b=1 diff=0 hash=4076651501 total=3135466046
#|ex d=8 b=3 diff=0 hash=1747992986 total=1275712168
#|ex d=8 b=6 diff=0 hash=3361745222 total=1878666749
#|ex d=8 b=12 diff=0 hash=3640114791 total=1083157859
#|ex d=11 b=0 diff=0 hash=1333689540 total=3491059760
#|ex d=11 b=1 diff=0 hash=4291210179 total=2143723869
#|ex d=11 b=3 diff=0 hash=4082543392 total=3505498521
#|ex d=11 b=6 diff=0 hash=3576235583 total=3402371496
#|ex d=11 b=12 diff=0 hash=547777270 total=1469096271
#|in d=0 b=0 diff=0 hash=3224134966 total=3224134966
#|in d=0 b=1 diff=0 hash=3424972597 total=3424972597
#|in d=0 b=3 diff=0 hash=3559226163 total=3559226163
#|in d=0 b=6 diff=0 hash=3626889520 total=3626889520
#|in d=0 b=12 diff=0 hash=4029631802 total=4029631802
#|in d=1 b=0 diff=0 hash=719061468 total=1125878976
#|in d=1 b=1 diff=0 hash=3929562347 total=1393232068
#|in d=1 b=3 diff=0 hash=1468458677 total=1929980092
#|in d=1 b=6 diff=0 hash=650868013 total=3264977047
#|in d=1 b=12 diff=0 hash=3658770549 total=571268064
#|in d=2 b=0 diff=0 hash=2590372006 total=400048673
#|in d=2 b=1 diff=0 hash=3965851130 total=1205358119
#|in d=2 b=3 diff=0 hash=3069862718 total=1742151203
#|in d=2 b=6 diff=0 hash=1527425402 total=2547343917
#|in d=2 b=12 diff=0 hash=2090467907 total=1465859612
#|in d=5 b=0 diff=0 hash=3827037865 total=2211542667
#|in d=5 b=1 diff=0 hash=2081845117 total=2044055345
#|in d=5 b=3 diff=0 hash=1288662711 total=3000196686
#|in d=5 b=6 diff=0 hash=1579512400 total=3301044677
#|in d=5 b=12 diff=0 hash=725684200 total=468309807
#|in d=8 b=0 diff=0 hash=3121109421 total=2307936655
#|in d=8 b=1 diff=0 hash=1839862243 total=3135466046
#|in d=8 b=3 diff=0 hash=2960979922 total=1275712168
#|in d=8 b=6 diff=0 hash=2146611867 total=1878666749
#|in d=8 b=12 diff=0 hash=3605395796 total=1083157859
#|in d=11 b=0 diff=0 hash=1436401588 total=3491059760
#|in d=11 b=1 diff=0 hash=2142653838 total=2143723869
#|in d=11 b=3 diff=0 hash=1767889081 total=3505498521
#|in d=11 b=6 diff=0 hash=873859367 total=3402371496
#|in d=11 b=12 diff=0 hash=1575525209 total=1469096271
