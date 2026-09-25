# Bench: Scan.exclusive at 2^d random U32s, fork depths b 0, 6 and 12,
# each call under `!`, against ref.bend's list scan (sizes up to 2^17).
# Run it through bench/run.sh; it prints and records nothing. Numbers are
# only meaningful on a quiet machine (and a quiet GPU for the GPU lane).
import Base
import ../scan.bend as Scan
import ../ref.bend as Ref
import ../tests/lib/check.bend as C
import ./lib.bend as L

# n calls, each on the last one's output; returns the last total.
def reps(+n: Nat, +b: Nat, r: Array<U32> & U32) -> IO(U32):
  match n:
    case 0n:
      (a, +t) = r
      IO.pure(U32, t)
    case 1n+p:
      (a, +t) = r
      reps(p, b, Scan.exclusive!(b, a))

def par(+d: Nat, +b: Nat) -> IO(Unit):
  +n = L.calls(d)
  do IO<Unit>:
    keys : Array<U32> <- IO.pure(Array<U32>, C.fill(d, 0, 7, 0))
    +t0 : Nat <- IO.now()
    c : U32 <- reps(n, Nat.add(b, L.zero(t0)), (keys, 0))
    t1 : Nat <- IO.now()
    IO.print(L.line("scan", d, b, n, t0, t1, c))

def seq(+d: Nat) -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, U32> <- IO.pure(List<&2, U32>, C.list(d, 0, 7, 0))
    +t0 : Nat <- IO.now()
    c : U32 <- IO.pure(U32, Ref.total(Ref.exclusive_from(xs, U32.from_nat(L.zero(t0)))))
    t1 : Nat <- IO.now()
    IO.print(L.line("scan-ref", d, 0n, 1n, t0, t1, c))

def size(+d: Nat) -> IO(Unit):
  do IO<Unit>:
    Unit <- par(d, 0n)
    Unit <- par(d, 6n)
    par(d, 12n)

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- seq(10n)
    Unit <- seq(14n)
    Unit <- seq(17n)
    Unit <- size(10n)
    Unit <- size(14n)
    Unit <- size(17n)
    Unit <- size(20n)
    size(22n)
