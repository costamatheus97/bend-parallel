# Bench: Hist.count of 2^d random keys into K = 256 buckets, fork depths b
# 0, 6 and 12, each call under `!` with buffers sized once outside it,
# against ref.bend's list histogram (sizes up to 2^14: it walks the K
# counts per key). Run it through bench/run.sh; it prints and records
# nothing. Numbers are only meaningful on a quiet machine (and a quiet GPU
# for the GPU lane).
import Base
import ../histogram.bend as Hist
import ../ref.bend as Ref
import ../tests/lib/check.bend as C
import ./lib.bend as L

# n calls with the same buffers; returns the keys and the buffers.
def reps(+n: Nat, +b: Nat, +k: U32, r: Array<U32> & Hist.Bufs) -> IO(Array<U32> & Hist.Bufs):
  match n:
    case 0n:
      IO.pure(Array<U32> & Hist.Bufs, r)
    case 1n+p:
      (keys, bufs) = r
      reps(p, b, k, Hist.count!(b, k, keys, bufs))

def check(r: Array<U32> & Hist.Bufs) -> U32:
  (keys, bufs) = r
  Hist.Bufs{counts, table} = bufs
  L.hash(C.to_list(counts))

def par(+d: Nat, +b: Nat) -> IO(Unit):
  +n = L.calls(d)
  do IO<Unit>:
    keys : Array<U32> <- IO.pure(Array<U32>, C.fill(d, 1, 7, 256))
    bufs : Hist.Bufs <- IO.pure(Hist.Bufs, Hist.Bufs.sized(b, 256, d))
    +t0 : Nat <- IO.now()
    r : Array<U32> & Hist.Bufs <- reps(n, Nat.add(b, L.zero(t0)), 256, (keys, bufs))
    +t1 : Nat <- IO.now()
    IO.print(L.line("hist", d, b, n, t0, t1, check(r)))

def seq(+d: Nat) -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, U32> <- IO.pure(List<&2, U32>, C.list(d, 1, 7, 256))
    +t0 : Nat <- IO.now()
    cs : List<&2, U32> <- IO.pure(List<&2, U32>, Ref.histogram((256 + U32.from_nat(L.zero(t0)) : U32), xs))
    +t1 : Nat <- IO.now()
    IO.print(L.line("hist-ref", d, 0n, 1n, t0, t1, C.hash(cs)))

def size(+d: Nat) -> IO(Unit):
  do IO<Unit>:
    Unit <- par(d, 0n)
    Unit <- par(d, 6n)
    par(d, 12n)

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- seq(10n)
    Unit <- seq(14n)
    Unit <- size(10n)
    Unit <- size(14n)
    Unit <- size(17n)
    Unit <- size(20n)
    size(22n)
