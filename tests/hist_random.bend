# The histogram of random keys below K at 2^d keys for d in {0, 2, 7, 12},
# fork depths b in {0, 3, 8, 13} and K in {1, 3, 64, 1000}, each run
# under `!` and compared with ref.bend's histogram (padded with zeros to
# 2^ceil(log2 K) entries). A line reads d, b, k, diff and hash; the hashes
# come from tests/lib/expect.py.
import Base
import ../histogram.bend as Hist
import ../ref.bend as Ref
import ./lib/check.bend as C

def show(+d: Nat, +k: U32, +seed: U32, r: Array<U32> & Hist.Bufs) -> String:
  (ks, bufs) = r
  Hist.Bufs{cs, t} = bufs
  C.cmp(C.pad(Ref.histogram(k, C.list(d, 1, seed, k)), C.width(k), 0), cs)

def one_case(+d: Nat, +b: Nat, +k: U32) -> IO(Unit):
  +seed = (U32.from_nat(d) * 100 + U32.from_nat(b) * 10 + k : U32)
  IO.print("d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " k=" ++ U32.show(k) ++ " counts "
    ++ show(d, k, seed, Hist.count!(b, k, C.fill(d, 1, seed, k), Hist.Bufs.new())))

def ks(+d: Nat, +b: Nat, xs: List<&2, U32>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case k <> t:
      do IO<Unit>:
        Unit <- one_case(d, b, k)
        ks(d, b, t)

def bs(+d: Nat, xs: List<&2, Nat>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case b <> t:
      do IO<Unit>:
        Unit <- ks(d, b, [1, 3, 64, 1000])
        bs(d, t)

def ds(xs: List<&2, Nat>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case d <> t:
      do IO<Unit>:
        Unit <- bs(d, [0n, 3n, 8n, 13n])
        ds(t)

def main() -> IO(Unit):
  ds([0n, 2n, 7n, 12n])

#|d=0 b=0 k=1 counts diff=0 hash=1
#|d=0 b=0 k=3 counts diff=0 hash=3422824465
#|d=0 b=0 k=64 counts diff=0 hash=2345056881
#|d=0 b=0 k=1000 counts diff=0 hash=2712480913
#|d=0 b=3 k=1 counts diff=0 hash=1
#|d=0 b=3 k=3 counts diff=0 hash=2654435761
#|d=0 b=3 k=64 counts diff=0 hash=2371776049
#|d=0 b=3 k=1000 counts diff=0 hash=3366413713
#|d=0 b=8 k=1 counts diff=0 hash=1
#|d=0 b=8 k=3 counts diff=0 hash=2654435761
#|d=0 b=8 k=64 counts diff=0 hash=2677853329
#|d=0 b=8 k=1000 counts diff=0 hash=2292781665
#|d=0 b=13 k=1 counts diff=0 hash=1
#|d=0 b=13 k=3 counts diff=0 hash=2654435761
#|d=0 b=13 k=64 counts diff=0 hash=890965057
#|d=0 b=13 k=1000 counts diff=0 hash=3930221409
#|d=2 b=0 k=1 counts diff=0 hash=4
#|d=2 b=0 k=3 counts diff=0 hash=3277759840
#|d=2 b=0 k=64 counts diff=0 hash=1519017826
#|d=2 b=0 k=1000 counts diff=0 hash=2797071552
#|d=2 b=3 k=1 counts diff=0 hash=4
#|d=2 b=3 k=3 counts diff=0 hash=3319070338
#|d=2 b=3 k=64 counts diff=0 hash=175213536
#|d=2 b=3 k=1000 counts diff=0 hash=2169042672
#|d=2 b=8 k=1 counts diff=0 hash=4
#|d=2 b=8 k=3 counts diff=0 hash=1635576690
#|d=2 b=8 k=64 counts diff=0 hash=65041792
#|d=2 b=8 k=1000 counts diff=0 hash=107559472
#|d=2 b=13 k=1 counts diff=0 hash=4
#|d=2 b=13 k=3 counts diff=0 hash=1536777408
#|d=2 b=13 k=64 counts diff=0 hash=869048992
#|d=2 b=13 k=1000 counts diff=0 hash=1887444528
#|d=7 b=0 k=1 counts diff=0 hash=128
#|d=7 b=0 k=3 counts diff=0 hash=1675560702
#|d=7 b=0 k=64 counts diff=0 hash=3046550084
#|d=7 b=0 k=1000 counts diff=0 hash=3899994178
#|d=7 b=3 k=1 counts diff=0 hash=128
#|d=7 b=3 k=3 counts diff=0 hash=4159111118
#|d=7 b=3 k=64 counts diff=0 hash=689936630
#|d=7 b=3 k=1000 counts diff=0 hash=4199622400
#|d=7 b=8 k=1 counts diff=0 hash=128
#|d=7 b=8 k=3 counts diff=0 hash=3223344380
#|d=7 b=8 k=64 counts diff=0 hash=3220562598
#|d=7 b=8 k=1000 counts diff=0 hash=165731936
#|d=7 b=13 k=1 counts diff=0 hash=128
#|d=7 b=13 k=3 counts diff=0 hash=1110688514
#|d=7 b=13 k=64 counts diff=0 hash=2962123386
#|d=7 b=13 k=1000 counts diff=0 hash=3850374496
#|d=12 b=0 k=1 counts diff=0 hash=4096
#|d=12 b=0 k=3 counts diff=0 hash=4200443374
#|d=12 b=0 k=64 counts diff=0 hash=4059014764
#|d=12 b=0 k=1000 counts diff=0 hash=2400135342
#|d=12 b=3 k=1 counts diff=0 hash=4096
#|d=12 b=3 k=3 counts diff=0 hash=1498327730
#|d=12 b=3 k=64 counts diff=0 hash=2039205966
#|d=12 b=3 k=1000 counts diff=0 hash=3294180570
#|d=12 b=8 k=1 counts diff=0 hash=4096
#|d=12 b=8 k=3 counts diff=0 hash=2655361118
#|d=12 b=8 k=64 counts diff=0 hash=2384140112
#|d=12 b=8 k=1000 counts diff=0 hash=2584563548
#|d=12 b=13 k=1 counts diff=0 hash=4096
#|d=12 b=13 k=3 counts diff=0 hash=2419306062
#|d=12 b=13 k=64 counts diff=0 hash=3382012026
#|d=12 b=13 k=1000 counts diff=0 hash=844733366
