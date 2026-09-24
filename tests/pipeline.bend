# A caller's own def that chains the package's calls: sort the keys,
# gather them into sorted order, then an inclusive scan of the sorted
# keys. The caller marks its def with `!` once (pipe!(..)) and every fork
# inside it, in all three modules, runs under that one bang (on the GPU
# lane: one device turn per line). Compared with ref.bend's inclusive
# scan of its sorted keys; the hashes and totals come from
# tests/lib/expect.py.
import Base
import ../scan.bend as Scan
import ../sort.bend as Sort
import ../ref.bend as Ref
import ./lib/check.bend as C

def pipe.scan(+b: Nat, m: Sort.Moved<U32>) -> Array<U32> & U32:
  match m:
    case Sort.Moved{pm, src, dst}:
      Scan.inclusive(b, dst)

def pipe.gather(+b: Nat, +d: Nat, r: Array<U32> & Sort.Bufs) -> Array<U32> & U32:
  (ks, bufs) = r
  Sort.Bufs{pm, cs, os, t} = bufs
  pipe.scan(b, Sort.gather(~U32, b, pm, ks, Array.new(U32, d, 0)))

# The running sums of the keys in sorted order.
def pipe(+b: Nat, +d: Nat, +k: U32, keys: Array<U32>) -> Array<U32> & U32:
  pipe.gather(b, d, Sort.by_key(b, k, keys, Sort.Bufs.new()))

def show.fin(+t: U32, want: List<&2, U32> & U32, r: Array<U32> & List<&2, U32>) -> String:
  (ws, +wt) = want
  (a, +got) = r
  "diff=" ++ Nat.show(Nat.add(C.diff(got, ws), C.one(U32.is_eq(t, wt)))) ++ " hash="
    ++ U32.show(C.hash(got)) ++ " total=" ++ U32.show(t)

def show(want: List<&2, U32> & U32, r: Array<U32> & U32) -> String:
  (a, +t) = r
  show.fin(t, want, C.to_list(a))

def one_case(+d: Nat, +b: Nat, +k: U32, +seed: U32) -> IO(Unit):
  IO.print("d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " k=" ++ U32.show(k) ++ " "
    ++ show(Ref.inclusive(Ref.sorted(k, C.list(d, 1, seed, k))), pipe!(b, d, k, C.fill(d, 1, seed, k))))

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- one_case(0n, 0n, 4, 1)
    Unit <- one_case(8n, 3n, 16, 2)
    Unit <- one_case(11n, 6n, 500, 3)
    one_case(13n, 9n, 64, 4)

#|d=0 b=0 k=4 diff=0 hash=1 total=1
#|d=8 b=3 k=16 diff=0 hash=865661102 total=2014
#|d=11 b=6 k=500 diff=0 hash=2416467285 total=513680
#|d=13 b=9 k=64 diff=0 hash=3466886537 total=257765
