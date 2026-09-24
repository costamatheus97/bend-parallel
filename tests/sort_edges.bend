# Sort edge cases, under `!`, against ref.bend (perm, counts, offsets): one
# key (K 5 and 1); all keys equal (perm is the identity); K = 1 with raw
# 32-bit keys; K = n (256 buckets, 256 keys) at b 2 and 8, and 4096
# keys that are a K = n shuffle-like spread; every key the largest U32 (all
# sort as K - 1, so perm is the identity); raw keys with K = 1000 (most
# clamp); K = 0 (one bucket). A line reads the case, then diff and hash
# for perm, counts and offs; the hashes come from tests/lib/expect.py.
import Base
import ../sort.bend as Sort
import ../ref.bend as Ref
import ./lib/check.bend as C

def show(+d: Nat, +k: U32, +kind: U32, +seed: U32, +m: U32, r: Array<U32> & Sort.Bufs) -> String:
  (ks, bufs) = r
  Sort.Bufs{pm, cs, os, t} = bufs
  +xs = C.list(d, kind, seed, m)
  +w = C.width(k)
  "perm " ++ C.cmp(Ref.perm(k, xs), pm) ++ " counts " ++ C.cmp(C.pad(Ref.histogram(k, xs), w, 0), cs)
    ++ " offs " ++ C.cmp(C.pad(Ref.offsets(k, xs), w, U32.shln(1, d)), os)

# 2^d keys of generator (kind, seed, m) into k buckets, at fork depth b.
def one_case(+d: Nat, +b: Nat, +k: U32, +kind: U32, +seed: U32, +m: U32) -> IO(Unit):
  IO.print("d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " k=" ++ U32.show(k) ++ " kind="
    ++ U32.show(kind) ++ " m=" ++ U32.show(m) ++ " "
    ++ show(d, k, kind, seed, m, Sort.by_key!(b, k, C.fill(d, kind, seed, m), Sort.Bufs.new())))

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- one_case(0n, 0n, 5, 1, 1, 5)
    Unit <- one_case(0n, 4n, 1, 0, 2, 0)
    Unit <- one_case(9n, 4n, 8, 2, 0, 3)
    Unit <- one_case(8n, 3n, 1, 0, 3, 0)
    Unit <- one_case(8n, 2n, 256, 1, 4, 256)
    Unit <- one_case(8n, 8n, 256, 1, 5, 256)
    Unit <- one_case(12n, 6n, 4096, 1, 11, 4096)
    Unit <- one_case(6n, 2n, 16, 2, 0, 4294967295)
    Unit <- one_case(10n, 5n, 1000, 0, 6, 0)
    one_case(7n, 3n, 0, 1, 7, 9)

#|d=0 b=0 k=5 kind=1 m=5 perm diff=0 hash=0 counts diff=0 hash=2345056881 offs diff=0 hash=3038898017
#|d=0 b=4 k=1 kind=0 m=0 perm diff=0 hash=0 counts diff=0 hash=1 offs diff=0 hash=0
#|d=9 b=4 k=8 kind=2 m=3 perm diff=0 hash=1162066944 counts diff=0 hash=3984163328 offs diff=0 hash=2846539776
#|d=8 b=3 k=1 kind=0 m=0 perm diff=0 hash=3109026816 counts diff=0 hash=256 offs diff=0 hash=0
#|d=8 b=2 k=256 kind=1 m=256 perm diff=0 hash=2720319168 counts diff=0 hash=1048201410 offs diff=0 hash=957148636
#|d=8 b=8 k=256 kind=1 m=256 perm diff=0 hash=1395632272 counts diff=0 hash=3556696022 offs diff=0 hash=2105406451
#|d=12 b=6 k=4096 kind=1 m=4096 perm diff=0 hash=2006174608 counts diff=0 hash=2319131652 offs diff=0 hash=1729905670
#|d=6 b=2 k=16 kind=2 m=4294967295 perm diff=0 hash=17251840 counts diff=0 hash=64 offs diff=0 hash=0
#|d=10 b=5 k=1000 kind=0 m=0 perm diff=0 hash=3101179904 counts diff=0 hash=3681682432 offs diff=0 hash=736165888
#|d=7 b=3 k=0 kind=1 m=9 perm diff=0 hash=1528536064 counts diff=0 hash=128 offs diff=0 hash=0
