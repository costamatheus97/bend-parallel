# Buffers handed from call to call, each call under `!`: one Sort.Bufs
# goes through sorts that grow it (d 8, k 100 from empty), shrink the key
# count and K (d 10, k 7: the table is big enough and stays, the counts
# and offsets are replaced), grow K past it (k 1000) and go back; then a
# Sort.Bufs.sized one, and one Hist.Bufs through histograms the same way.
# Every result is compared with ref.bend. A line reads the call, then diff
# and hash per output; the hashes come from tests/lib/expect.py.
import Base
import ../sort.bend as Sort
import ../histogram.bend as Hist
import ../ref.bend as Ref
import ./lib/check.bend as C

type Cfg is Data:
  Cfg{d: Nat, b: Nat, k: U32}

def seed(+d: Nat, +b: Nat, +k: U32) -> U32:
  (U32.from_nat(d) * 100 + U32.from_nat(b) * 10 + k : U32)

def s.off(pm: Array<U32>, cs: Array<U32>, t: Array<U32>, +sp: String, +sc: String, r: Array<U32> & String) -> String & Sort.Bufs:
  (os, +so) = r
  ("perm " ++ sp ++ " counts " ++ sc ++ " offs " ++ so, Sort.Bufs{pm, cs, os, t})

def s.cnt(+d: Nat, +k: U32, +xs: List<&2, U32>, pm: Array<U32>, os: Array<U32>, t: Array<U32>, +sp: String, r: Array<U32> & String) -> String & Sort.Bufs:
  (cs, +sc) = r
  s.off(pm, cs, t, sp, sc, C.cmpk(C.pad(Ref.offsets(k, xs), C.width(k), U32.shln(1, d)), os))

def s.perm(+d: Nat, +k: U32, +xs: List<&2, U32>, cs: Array<U32>, os: Array<U32>, t: Array<U32>, r: Array<U32> & String) -> String & Sort.Bufs:
  (pm, +sp) = r
  s.cnt(d, k, xs, pm, os, t, sp, C.cmpk(C.pad(Ref.histogram(k, xs), C.width(k), 0), cs))

def s.fin(+d: Nat, +k: U32, r: Array<U32> & Sort.Bufs) -> String & Sort.Bufs:
  (ks, bufs) = r
  Sort.Bufs{pm, cs, os, t} = bufs
  +xs = C.list(d, 1, seed(d, 0n, k), k)
  s.perm(d, k, xs, cs, os, t, C.cmpk(Ref.perm(k, xs), pm))

# r holds the last line and the buffers: prints the line, then sorts with
# the buffers for each config left.
def sorts(cs: List<&2, Cfg>, r: String & Sort.Bufs) -> IO(Unit):
  match cs:
    case Nil{}:
      (line, bufs) = r
      IO.print(line)
    case Cfg{+d, +b, +k} <> t:
      (line, bufs) = r
      do IO<Unit>:
        Unit <- IO.print(line)
        sorts(t, s.fin(d, k, Sort.by_key!(b, k, C.fill(d, 1, seed(d, 0n, k), k), bufs)))

def h.cnt(t: Array<U32>, r: Array<U32> & String) -> String & Hist.Bufs:
  (cs, +sc) = r
  ("counts " ++ sc, Hist.Bufs{cs, t})

def h.fin(+d: Nat, +k: U32, r: Array<U32> & Hist.Bufs) -> String & Hist.Bufs:
  (ks, bufs) = r
  Hist.Bufs{cs, t} = bufs
  h.cnt(t, C.cmpk(C.pad(Ref.histogram(k, C.list(d, 1, seed(d, 0n, k), k)), C.width(k), 0), cs))

def hists(cs: List<&2, Cfg>, r: String & Hist.Bufs) -> IO(Unit):
  match cs:
    case Nil{}:
      (line, bufs) = r
      IO.print(line)
    case Cfg{+d, +b, +k} <> t:
      (line, bufs) = r
      do IO<Unit>:
        Unit <- IO.print(line)
        hists(t, h.fin(d, k, Hist.count!(b, k, C.fill(d, 1, seed(d, 0n, k), k), bufs)))

def cfgs() -> List<&2, Cfg>:
  [Cfg{8n, 3n, 100}, Cfg{10n, 5n, 7}, Cfg{6n, 2n, 1000}, Cfg{10n, 5n, 7}, Cfg{0n, 0n, 1}]

def sized() -> List<&2, Cfg>:
  [Cfg{9n, 4n, 300}, Cfg{9n, 4n, 300}]

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- sorts(cfgs(), ("sort from empty", Sort.Bufs.new()))
    Unit <- sorts(sized(), ("sort from sized", Sort.Bufs.sized(4n, 300, 9n)))
    Unit <- hists(cfgs(), ("hist from empty", Hist.Bufs.new()))
    hists(List.take(&2, Cfg, sized(), 1n), ("hist from sized", Hist.Bufs.sized(4n, 300, 9n)))

#|sort from empty
#|perm diff=0 hash=1050204576 counts diff=0 hash=1894825030 offs diff=0 hash=2896250036
#|perm diff=0 hash=1401629712 counts diff=0 hash=3410827264 offs diff=0 hash=3869958295
#|perm diff=0 hash=3785142736 counts diff=0 hash=820848304 offs diff=0 hash=2886608587
#|perm diff=0 hash=1401629712 counts diff=0 hash=3410827264 offs diff=0 hash=3869958295
#|perm diff=0 hash=0 counts diff=0 hash=1 offs diff=0 hash=0
#|sort from sized
#|perm diff=0 hash=3450877056 counts diff=0 hash=2037076630 offs diff=0 hash=3346812079
#|perm diff=0 hash=3450877056 counts diff=0 hash=2037076630 offs diff=0 hash=3346812079
#|hist from empty
#|counts diff=0 hash=1894825030
#|counts diff=0 hash=3410827264
#|counts diff=0 hash=820848304
#|counts diff=0 hash=3410827264
#|counts diff=0 hash=1
#|hist from sized
#|counts diff=0 hash=2037076630
