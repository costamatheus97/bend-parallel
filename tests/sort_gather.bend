# Gathers by the sort's permutation, both under `!`: the keys themselves
# (the result must be ref.bend's sorted keys), an F32 payload holding each
# slot's index as a float (the result, read back as U32, must be perm),
# the keys again into a destination of the wrong size (replaced by a new
# array of the right one), and at another fork depth than the sort's. A
# line reads the case, diff against the reference and the hash of the
# result; the hashes come from tests/lib/expect.py.
import Base
import ../sort.bend as Sort
import ../ref.bend as Ref
import ./lib/check.bend as C

# The indices 0 .. n as F32.
def idx.go(+n: Nat, +j: U32, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      Array.set(F32, a, j, U32.to_f32(j))
    case 1n+p:
      idx.go(p, (j + 1 : U32), Array.set(F32, a, j, U32.to_f32(j)))

def idx(+d: Nat) -> Array<F32>:
  idx.go(U32.to_nat((U32.shln(1, d) - 1 : U32)), 0, Array.new(F32, d, 0.0))

# r holds the F32 array and its entry x at j: F32.to_u32(x) into out[j],
# then the n entries after j.
def back.go(+n: Nat, +j: U32, out: Array<U32>, r: Array<F32> & F32) -> Array<U32>:
  match n:
    case 0n:
      (a, +x) = r
      out[j] <- F32.to_u32(x)
    case 1n+p:
      (a, +x) = r
      +i = (j + 1 : U32)
      back.go(p, i, out[j] <- F32.to_u32(x), Array.get(F32, a, i))

# The F32 array's entries as U32s.
def back(+d: Nat, a: Array<F32>) -> Array<U32>:
  back.go(U32.to_nat((U32.shln(1, d) - 1 : U32)), 0, Array.new(U32, d, 0), Array.get(F32, a, 0))

def keys.fin(want: List<&2, U32>, r: Sort.Moved<U32>) -> String:
  match r:
    case Sort.Moved{pm, src, dst}:
      C.cmp(want, dst)

# The F32 gather's check, then the gather into a wrong-sized destination.
def g2(+d: Nat, +g: Nat, +k: U32, +xs: List<&2, U32>, ks: Array<U32>, r: Sort.Moved<F32>) -> IO(Unit):
  match r:
    case Sort.Moved{pm, src, dst}:
      do IO<Unit>:
        Unit <- IO.print("floats " ++ C.cmp(Ref.perm(k, xs), back(d, dst)))
        IO.print("resized " ++ keys.fin(Ref.sorted(k, xs), Sort.gather!(~U32, g, pm, ks, [7 : U32^0n])))

# The keys' gather's check, then the F32 gather.
def g1(+d: Nat, +g: Nat, +k: U32, +xs: List<&2, U32>, r: Sort.Moved<U32>) -> IO(Unit):
  match r:
    case Sort.Moved{pm, ks, dst}:
      do IO<Unit>:
        Unit <- IO.print("keys " ++ C.cmp(Ref.sorted(k, xs), dst))
        g2(d, g, k, xs, ks, Sort.gather!(~F32, g, pm, idx(d), Array.new(F32, d, 0.0)))

# The gathers at depth g, after the sort.
def gathers(+d: Nat, +g: Nat, +k: U32, +xs: List<&2, U32>, r: Array<U32> & Sort.Bufs) -> IO(Unit):
  (ks, bufs) = r
  Sort.Bufs{pm, cs, os, t} = bufs
  g1(d, g, k, xs, Sort.gather!(~U32, g, pm, ks, Array.new(U32, d, 0)))

def one_case(+d: Nat, +b: Nat, +g: Nat, +k: U32, +kind: U32, +seed: U32, +m: U32) -> IO(Unit):
  do IO<Unit>:
    Unit <- IO.print("d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " g=" ++ Nat.show(g) ++ " k="
      ++ U32.show(k) ++ " kind=" ++ U32.show(kind))
    gathers(d, g, k, C.list(d, kind, seed, m), Sort.by_key!(b, k, C.fill(d, kind, seed, m), Sort.Bufs.new()))

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- one_case(0n, 0n, 0n, 3, 1, 1, 3)
    Unit <- one_case(10n, 4n, 4n, 50, 1, 2, 50)
    Unit <- one_case(10n, 4n, 7n, 50, 1, 3, 50)
    Unit <- one_case(9n, 3n, 2n, 100, 0, 4, 0)
    one_case(12n, 8n, 12n, 4096, 1, 5, 4096)

#|d=0 b=0 g=0 k=3 kind=1
#|keys diff=0 hash=1
#|floats diff=0 hash=0
#|resized diff=0 hash=1
#|d=10 b=4 g=4 k=50 kind=1
#|keys diff=0 hash=806544396
#|floats diff=0 hash=622806352
#|resized diff=0 hash=806544396
#|d=10 b=4 g=7 k=50 kind=1
#|keys diff=0 hash=1409318709
#|floats diff=0 hash=16148384
#|resized diff=0 hash=1409318709
#|d=9 b=3 g=2 k=100 kind=0
#|keys diff=0 hash=3349807975
#|floats diff=0 hash=1162066944
#|resized diff=0 hash=3349807975
#|d=12 b=8 g=12 k=4096 kind=1
#|keys diff=0 hash=708722284
#|floats diff=0 hash=2816255264
#|resized diff=0 hash=708722284
