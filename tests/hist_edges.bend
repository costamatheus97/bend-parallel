# Histogram edge cases, under `!`, against ref.bend: one key (K 5 and 1);
# all keys equal; K = 1 with raw 32-bit keys (all clamp to bucket 0);
# K = n (256 buckets, 256 keys) at b 2 and 8; every key the largest U32
# (all clamp to K - 1); raw keys with K = 1000 (most clamp); K = 0 (one
# bucket). A line reads the case, diff and hash; the hashes come from
# tests/lib/expect.py.
import Base
import ../histogram.bend as Hist
import ../ref.bend as Ref
import ./lib/check.bend as C

def show(+d: Nat, +k: U32, +kind: U32, +seed: U32, +m: U32, r: Array<U32> & Hist.Bufs) -> String:
  (ks, bufs) = r
  Hist.Bufs{cs, t} = bufs
  C.cmp(C.pad(Ref.histogram(k, C.list(d, kind, seed, m)), C.width(k), 0), cs)

# 2^d keys of generator (kind, seed, m) into k buckets, at fork depth b.
def one_case(+d: Nat, +b: Nat, +k: U32, +kind: U32, +seed: U32, +m: U32) -> IO(Unit):
  IO.print("d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " k=" ++ U32.show(k) ++ " kind="
    ++ U32.show(kind) ++ " m=" ++ U32.show(m) ++ " counts "
    ++ show(d, k, kind, seed, m, Hist.count!(b, k, C.fill(d, kind, seed, m), Hist.Bufs.new())))

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- one_case(0n, 0n, 5, 1, 1, 5)
    Unit <- one_case(0n, 4n, 1, 0, 2, 0)
    Unit <- one_case(9n, 4n, 8, 2, 0, 3)
    Unit <- one_case(8n, 3n, 1, 0, 3, 0)
    Unit <- one_case(8n, 2n, 256, 1, 4, 256)
    Unit <- one_case(8n, 8n, 256, 1, 5, 256)
    Unit <- one_case(6n, 2n, 16, 2, 0, 4294967295)
    Unit <- one_case(10n, 5n, 1000, 0, 6, 0)
    Unit <- one_case(7n, 3n, 0, 1, 7, 9)
    one_case(14n, 10n, 100, 1, 8, 100)

#|d=0 b=0 k=5 kind=1 m=5 counts diff=0 hash=2345056881
#|d=0 b=4 k=1 kind=0 m=0 counts diff=0 hash=1
#|d=9 b=4 k=8 kind=2 m=3 counts diff=0 hash=3984163328
#|d=8 b=3 k=1 kind=0 m=0 counts diff=0 hash=256
#|d=8 b=2 k=256 kind=1 m=256 counts diff=0 hash=1048201410
#|d=8 b=8 k=256 kind=1 m=256 counts diff=0 hash=3556696022
#|d=6 b=2 k=16 kind=2 m=4294967295 counts diff=0 hash=64
#|d=10 b=5 k=1000 kind=0 m=0 counts diff=0 hash=3681682432
#|d=7 b=3 k=0 kind=1 m=9 counts diff=0 hash=128
#|d=14 b=10 k=100 kind=1 m=100 counts diff=0 hash=822549072
