# The stable counting sort of random keys below K at 2^d keys for d in
# {0, 1, 3, 6, 10}, fork depths b in {0, 2, 5, 11} and K in {1, 2, 7,
# 256, 1000}, each run under `!` and compared with ref.bend's perm,
# histogram and offsets (counts padded with zeros and offsets with n to
# 2^ceil(log2 K) entries). A line reads d, b, k, then diff and hash for
# perm, counts and offs; the hashes come from tests/lib/expect.py.
import Base
import ../sort.bend as Sort
import ../ref.bend as Ref
import ./lib/check.bend as C

def show(+d: Nat, +k: U32, +seed: U32, r: Array<U32> & Sort.Bufs) -> String:
  (ks, bufs) = r
  Sort.Bufs{pm, cs, os, t} = bufs
  +xs = C.list(d, 1, seed, k)
  +w = C.width(k)
  "perm " ++ C.cmp(Ref.perm(k, xs), pm) ++ " counts " ++ C.cmp(C.pad(Ref.histogram(k, xs), w, 0), cs)
    ++ " offs " ++ C.cmp(C.pad(Ref.offsets(k, xs), w, U32.shln(1, d)), os)

def one_case(+d: Nat, +b: Nat, +k: U32) -> IO(Unit):
  +seed = (U32.from_nat(d) * 100 + U32.from_nat(b) * 10 + k : U32)
  IO.print("d=" ++ Nat.show(d) ++ " b=" ++ Nat.show(b) ++ " k=" ++ U32.show(k) ++ " "
    ++ show(d, k, seed, Sort.by_key!(b, k, C.fill(d, 1, seed, k), Sort.Bufs.new())))

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
        Unit <- ks(d, b, [1, 2, 7, 256, 1000])
        bs(d, t)

def ds(xs: List<&2, Nat>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case d <> t:
      do IO<Unit>:
        Unit <- bs(d, [0n, 2n, 5n, 11n])
        ds(t)

def main() -> IO(Unit):
  ds([0n, 1n, 3n, 6n, 10n])

#|d=0 b=0 k=1 perm diff=0 hash=0 counts diff=0 hash=1 offs diff=0 hash=0
#|d=0 b=0 k=2 perm diff=0 hash=0 counts diff=0 hash=2654435761 offs diff=0 hash=1
#|d=0 b=0 k=7 perm diff=0 hash=0 counts diff=0 hash=2654435761 offs diff=0 hash=1
#|d=0 b=0 k=256 perm diff=0 hash=0 counts diff=0 hash=3386024673 offs diff=0 hash=2283190000
#|d=0 b=0 k=1000 perm diff=0 hash=0 counts diff=0 hash=2712480913 offs diff=0 hash=1453293297
#|d=0 b=2 k=1 perm diff=0 hash=0 counts diff=0 hash=1 offs diff=0 hash=0
#|d=0 b=2 k=2 perm diff=0 hash=0 counts diff=0 hash=1 offs diff=0 hash=0
#|d=0 b=2 k=7 perm diff=0 hash=0 counts diff=0 hash=3422824465 offs diff=0 hash=1638879921
#|d=0 b=2 k=256 perm diff=0 hash=0 counts diff=0 hash=2024914129 offs diff=0 hash=3221713937
#|d=0 b=2 k=1000 perm diff=0 hash=0 counts diff=0 hash=2164345825 offs diff=0 hash=4221951856
#|d=0 b=5 k=1 perm diff=0 hash=0 counts diff=0 hash=1 offs diff=0 hash=0
#|d=0 b=5 k=2 perm diff=0 hash=0 counts diff=0 hash=1 offs diff=0 hash=0
#|d=0 b=5 k=7 perm diff=0 hash=0 counts diff=0 hash=1667543249 offs diff=0 hash=2284355089
#|d=0 b=5 k=256 perm diff=0 hash=0 counts diff=0 hash=3213384401 offs diff=0 hash=1207425809
#|d=0 b=5 k=1000 perm diff=0 hash=0 counts diff=0 hash=973864865 offs diff=0 hash=4131740752
#|d=0 b=11 k=1 perm diff=0 hash=0 counts diff=0 hash=1 offs diff=0 hash=0
#|d=0 b=11 k=2 perm diff=0 hash=0 counts diff=0 hash=2654435761 offs diff=0 hash=1
#|d=0 b=11 k=7 perm diff=0 hash=0 counts diff=0 hash=4293315681 offs diff=0 hash=2654435760
#|d=0 b=11 k=256 perm diff=0 hash=0 counts diff=0 hash=1537929361 offs diff=0 hash=4191170801
#|d=0 b=11 k=1000 perm diff=0 hash=0 counts diff=0 hash=2512968177 offs diff=0 hash=3514866977
#|d=1 b=0 k=1 perm diff=0 hash=1 counts diff=0 hash=2 offs diff=0 hash=0
#|d=1 b=0 k=2 perm diff=0 hash=2654435761 counts diff=0 hash=2654435760 offs diff=0 hash=1
#|d=1 b=0 k=7 perm diff=0 hash=2654435761 counts diff=0 hash=768388704 offs diff=0 hash=1638879922
#|d=1 b=0 k=256 perm diff=0 hash=1 counts diff=0 hash=1227213168 offs diff=0 hash=1303170401
#|d=1 b=0 k=1000 perm diff=0 hash=1 counts diff=0 hash=461809152 offs diff=0 hash=2066375106
#|d=1 b=2 k=1 perm diff=0 hash=1 counts diff=0 hash=2 offs diff=0 hash=0
#|d=1 b=2 k=2 perm diff=0 hash=1 counts diff=0 hash=2654435760 offs diff=0 hash=1
#|d=1 b=2 k=7 perm diff=0 hash=1 counts diff=0 hash=2462656784 offs diff=0 hash=4222798627
#|d=1 b=2 k=256 perm diff=0 hash=2654435761 counts diff=0 hash=594649744 offs diff=0 hash=413378801
#|d=1 b=2 k=1000 perm diff=0 hash=1 counts diff=0 hash=2364797040 offs diff=0 hash=1503805523
#|d=1 b=5 k=1 perm diff=0 hash=1 counts diff=0 hash=2 offs diff=0 hash=0
#|d=1 b=5 k=2 perm diff=0 hash=1 counts diff=0 hash=2654435760 offs diff=0 hash=1
#|d=1 b=5 k=7 perm diff=0 hash=2654435761 counts diff=0 hash=1669194864 offs diff=0 hash=1657727777
#|d=1 b=5 k=256 perm diff=0 hash=1 counts diff=0 hash=280825200 offs diff=0 hash=3432920659
#|d=1 b=5 k=1000 perm diff=0 hash=2654435761 counts diff=0 hash=3747534912 offs diff=0 hash=2129240450
#|d=1 b=11 k=1 perm diff=0 hash=1 counts diff=0 hash=2 offs diff=0 hash=0
#|d=1 b=11 k=2 perm diff=0 hash=1 counts diff=0 hash=1013904226 offs diff=0 hash=2
#|d=1 b=11 k=7 perm diff=0 hash=2654435761 counts diff=0 hash=1638879920 offs diff=0 hash=2654435763
#|d=1 b=11 k=256 perm diff=0 hash=2654435761 counts diff=0 hash=2869209440 offs diff=0 hash=3035940720
#|d=1 b=11 k=1000 perm diff=0 hash=1 counts diff=0 hash=3631220256 offs diff=0 hash=1713398482
#|d=3 b=0 k=1 perm diff=0 hash=4255098112 counts diff=0 hash=8 offs diff=0 hash=0
#|d=3 b=0 k=2 perm diff=0 hash=802046480 counts diff=0 hash=387276918 offs diff=0 hash=5
#|d=3 b=0 k=7 perm diff=0 hash=2849130848 counts diff=0 hash=1889342864 offs diff=0 hash=1313996027
#|d=3 b=0 k=256 perm diff=0 hash=2514445760 counts diff=0 hash=4131640976 offs diff=0 hash=3561718187
#|d=3 b=0 k=1000 perm diff=0 hash=656692144 counts diff=0 hash=724125872 offs diff=0 hash=1200349631
#|d=3 b=2 k=1 perm diff=0 hash=4255098112 counts diff=0 hash=8 offs diff=0 hash=0
#|d=3 b=2 k=2 perm diff=0 hash=2845428080 counts diff=0 hash=3668339990 offs diff=0 hash=3
#|d=3 b=2 k=7 perm diff=0 hash=491625696 counts diff=0 hash=623012736 offs diff=0 hash=2032665454
#|d=3 b=2 k=256 perm diff=0 hash=1305929552 counts diff=0 hash=2839660304 offs diff=0 hash=3797475417
#|d=3 b=2 k=1000 perm diff=0 hash=1080640784 counts diff=0 hash=1979059872 offs diff=0 hash=3497558848
#|d=3 b=5 k=1 perm diff=0 hash=4255098112 counts diff=0 hash=8 offs diff=0 hash=0
#|d=3 b=5 k=2 perm diff=0 hash=3650699712 counts diff=0 hash=2027808448 offs diff=0 hash=4
#|d=3 b=5 k=7 perm diff=0 hash=1611388368 counts diff=0 hash=2837303776 offs diff=0 hash=1770000926
#|d=3 b=5 k=256 perm diff=0 hash=582116912 counts diff=0 hash=1361618032 offs diff=0 hash=2472083003
#|d=3 b=5 k=1000 perm diff=0 hash=525834544 counts diff=0 hash=3334461360 offs diff=0 hash=3180181965
#|d=3 b=11 k=1 perm diff=0 hash=4255098112 counts diff=0 hash=8 offs diff=0 hash=0
#|d=3 b=11 k=2 perm diff=0 hash=3074207408 counts diff=0 hash=387276918 offs diff=0 hash=5
#|d=3 b=11 k=7 perm diff=0 hash=3846748640 counts diff=0 hash=226660240 offs diff=0 hash=3912437979
#|d=3 b=11 k=256 perm diff=0 hash=3585659824 counts diff=0 hash=2298474208 offs diff=0 hash=4000926662
#|d=3 b=11 k=1000 perm diff=0 hash=3569878672 counts diff=0 hash=1520283248 offs diff=0 hash=4051954341
#|d=6 b=0 k=1 perm diff=0 hash=17251840 counts diff=0 hash=64 offs diff=0 hash=0
#|d=6 b=0 k=2 perm diff=0 hash=1184095680 counts diff=0 hash=3964193070 offs diff=0 hash=29
#|d=6 b=0 k=7 perm diff=0 hash=491358800 counts diff=0 hash=921267424 offs diff=0 hash=648374572
#|d=6 b=0 k=256 perm diff=0 hash=1277990400 counts diff=0 hash=3042225776 offs diff=0 hash=2389749333
#|d=6 b=0 k=1000 perm diff=0 hash=3785142736 counts diff=0 hash=820848304 offs diff=0 hash=2886608587
#|d=6 b=2 k=1 perm diff=0 hash=17251840 counts diff=0 hash=64 offs diff=0 hash=0
#|d=6 b=2 k=2 perm diff=0 hash=3815177536 counts diff=0 hash=56502684 offs diff=0 hash=34
#|d=6 b=2 k=7 perm diff=0 hash=2891086768 counts diff=0 hash=1531198426 offs diff=0 hash=3627375877
#|d=6 b=2 k=256 perm diff=0 hash=917556640 counts diff=0 hash=1848969552 offs diff=0 hash=3695085237
#|d=6 b=2 k=1000 perm diff=0 hash=696527232 counts diff=0 hash=2383156210 offs diff=0 hash=1221560893
#|d=6 b=5 k=1 perm diff=0 hash=17251840 counts diff=0 hash=64 offs diff=0 hash=0
#|d=6 b=5 k=2 perm diff=0 hash=1446561296 counts diff=0 hash=3098215344 offs diff=0 hash=40
#|d=6 b=5 k=7 perm diff=0 hash=689723840 counts diff=0 hash=3284777986 offs diff=0 hash=116844140
#|d=6 b=5 k=256 perm diff=0 hash=2370047264 counts diff=0 hash=3750375456 offs diff=0 hash=2653873506
#|d=6 b=5 k=1000 perm diff=0 hash=1231040832 counts diff=0 hash=4227496432 offs diff=0 hash=459540481
#|d=6 b=11 k=1 perm diff=0 hash=17251840 counts diff=0 hash=64 offs diff=0 hash=0
#|d=6 b=11 k=2 perm diff=0 hash=3054824000 counts diff=0 hash=3337565696 offs diff=0 hash=32
#|d=6 b=11 k=7 perm diff=0 hash=1663590928 counts diff=0 hash=4291057810 offs diff=0 hash=3935858341
#|d=6 b=11 k=256 perm diff=0 hash=3727603488 counts diff=0 hash=1035232082 offs diff=0 hash=1023217941
#|d=6 b=11 k=1000 perm diff=0 hash=757173536 counts diff=0 hash=2868606480 offs diff=0 hash=4038965661
#|d=10 b=0 k=1 perm diff=0 hash=3101179904 counts diff=0 hash=1024 offs diff=0 hash=0
#|d=10 b=0 k=2 perm diff=0 hash=2851198416 counts diff=0 hash=2340144352 offs diff=0 hash=496
#|d=10 b=0 k=7 perm diff=0 hash=1401629712 counts diff=0 hash=3410827264 offs diff=0 hash=3869958295
#|d=10 b=0 k=256 perm diff=0 hash=2735320448 counts diff=0 hash=3486794112 offs diff=0 hash=3172223784
#|d=10 b=0 k=1000 perm diff=0 hash=128102816 counts diff=0 hash=2003536242 offs diff=0 hash=4219381173
#|d=10 b=2 k=1 perm diff=0 hash=3101179904 counts diff=0 hash=1024 offs diff=0 hash=0
#|d=10 b=2 k=2 perm diff=0 hash=1239884064 counts diff=0 hash=2100794992 offs diff=0 hash=504
#|d=10 b=2 k=7 perm diff=0 hash=3446654848 counts diff=0 hash=171797596 offs diff=0 hash=986211538
#|d=10 b=2 k=256 perm diff=0 hash=1174531072 counts diff=0 hash=3175878834 offs diff=0 hash=53368365
#|d=10 b=2 k=1000 perm diff=0 hash=4077065984 counts diff=0 hash=4032500104 offs diff=0 hash=1249842884
#|d=10 b=5 k=1 perm diff=0 hash=3101179904 counts diff=0 hash=1024 offs diff=0 hash=0
#|d=10 b=5 k=2 perm diff=0 hash=4057680896 counts diff=0 hash=2635997980 offs diff=0 hash=522
#|d=10 b=5 k=7 perm diff=0 hash=266691520 counts diff=0 hash=2761405358 offs diff=0 hash=2644777933
#|d=10 b=5 k=256 perm diff=0 hash=204987216 counts diff=0 hash=2800346438 offs diff=0 hash=2497496642
#|d=10 b=5 k=1000 perm diff=0 hash=2949230800 counts diff=0 hash=2663443106 offs diff=0 hash=3691673160
#|d=10 b=11 k=1 perm diff=0 hash=3101179904 counts diff=0 hash=1024 offs diff=0 hash=0
#|d=10 b=11 k=2 perm diff=0 hash=1017906272 counts diff=0 hash=2248721294 offs diff=0 hash=517
#|d=10 b=11 k=7 perm diff=0 hash=405336832 counts diff=0 hash=968463258 offs diff=0 hash=1669931358
#|d=10 b=11 k=256 perm diff=0 hash=49770976 counts diff=0 hash=252396516 offs diff=0 hash=806320594
#|d=10 b=11 k=1000 perm diff=0 hash=2442324560 counts diff=0 hash=2861791972 offs diff=0 hash=2873881780
