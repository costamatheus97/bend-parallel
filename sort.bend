# sort.bend: a parallel stable counting sort by U32 key, with no atomics,
# and a parallel gather to reorder payloads by its permutation.
#
#   import ./sort.bend as Sort
#   Sort.by_key(8n, 256, keys, Sort.Bufs.new())   # (keys, bufs)
#   Sort.Bufs{perm, counts, offs, table} = bufs
#   # perm[j]: the input index of the key the sort puts at j
#   # counts[c], offs[c]: bucket c's size and first slot
#   Sort.gather(~U32, 8n, perm, keys, [0 : U32^d])   # Moved{perm, keys, sorted}
#
# (As in scan.bend: take a call's result apart in a def's parameter.)
#
# k is the bucket count K (0 counts as 1), any U32; a key at or past K
# sorts as K - 1. The sort is stable: keys of one bucket keep their input
# order, so the result equals ref.bend's perm, offsets and histogram bit
# for bit, at every fork depth b. counts and offs hold 2^ceil(log2 K)
# entries: past K, counts are 0 and offs are n. A call under `!` runs its
# forks on the GPU.
#
# Bufs carries the buffers from call to call (the table of 2^b rows of
# 2^ceil(log2 K) counts, the counts, the offsets and the permutation). A
# call keeps a buffer that fits and allocates otherwise; under `!` an
# allocation fills on one lane, so size them once with Bufs.sized outside
# the `!` (see histogram.bend).
#
# Passes:
#   1. per block of keys, in parallel: the block's counts per bucket into
#      its row of the table (histogram.bend's pass 1);
#   2. per group of buckets, in parallel: each bucket's column sum into
#      counts and offs; then offs becomes its exclusive scan (scan.bend),
#      the buckets' first slots; then, per group of buckets again, each
#      table entry becomes its bucket's first slot plus the counts of the
#      rows above it: where the block's keys of that bucket start;
#   3. per block, in parallel: each key, in order, takes the next slot of
#      its bucket in the block's row, and perm[slot] becomes its index.
#
# Sharing: as in scan.bend, lanes share arrays through Base's @unsafe
# Array.fork and Array.join; no def here is @unsafe itself, and none may
# be evaluated in the checker (call them from an IO main).
import Base
import ./scan.bend as Scan
import ./histogram.bend as Hist

# Buffers
# -------

type Bufs is Type:
  Bufs{perm: Array<U32>, counts: Array<U32>, offs: Array<U32>, table: Array<U32>}

# Empty buffers: the first call allocates what it needs.
def Bufs.new() -> Bufs:
  Bufs{[0 : U32^0n], [0 : U32^0n], [0 : U32^0n], [0 : U32^0n]}

# Buffers for 2^lg keys at fork depth b and k buckets, allocated now.
def Bufs.sized(+b: Nat, +k: U32, +lg: Nat) -> Bufs:
  +kb = Hist.kbits(U32.max(k, 1))
  Bufs{Array.new(U32, lg, 0), Array.new(U32, kb, 0), Array.new(U32, kb, 0),
    Array.new(U32, Nat.add(Nat.min(b, lg), kb), 0)}

# Handles
# -------

type Three is Type:
  Three{a: Array<U32>, b: Array<U32>, c: Array<U32>}

def three.join(l: Three, r: Three) -> Three:
  Three{la, lb, lc} = l
  Three{ra, rb, rc} = r
  Three{Array.join(U32, la, ra), Array.join(U32, lb, rb), Array.join(U32, lc, rc)}

def three.rejoin(a2: Array<U32>, b2: Array<U32>, c2: Array<U32>, r: Three) -> Three:
  Three{a, b, c} = r
  Three{Array.join(U32, a, a2), Array.join(U32, b, b2), Array.join(U32, c, c2)}

# Pass 2a: column sums into counts and offs
# -----------------------------------------

def sum.put(+c: U32, cs: Array<U32>, os: Array<U32>, r: Array<U32> & U32) -> Three:
  (t, +v) = r
  Three{t, cs[c] <- v, os[c] <- v}

# Column c: its sum over the nb + 1 rows into cs[c] and os[c] when c < K,
# else 0 into both.
def sum.one(lt: Bool, +c: U32, +kb: Nat, +nb: Nat, p: Three) -> Three:
  match lt:
    case True{}:
      Three{t, cs, os} = p
      sum.put(c, cs, os, Hist.col.go(nb, c, U32.shln(1, kb), 0, t[c]))
    case False{}:
      Three{t, cs, os} = p
      Three{t, cs[c] <- 0, os[c] <- 0}

# Columns c to c + n.
def sum.go(+n: Nat, +c: U32, +k: U32, +kb: Nat, +nb: Nat, p: Three) -> Three:
  match n:
    case 0n:
      sum.one(U32.is_lt(c, k), c, kb, nb, p)
    case 1n+q:
      sum.go(q, (c + 1 : U32), k, kb, nb, sum.one(U32.is_lt(c, k), c, kb, nb, p))

# Pass 2a's forks: d levels down to groups of 2^w columns under group j,
# with two handles each to the table, the counts and the offsets. Group j
# reads only its columns of the table and writes only its own entries of
# counts and offs (j * 2^w to j * 2^w + 2^w - 1).
def sums(+d: Nat, +j: U32, +w: Nat, +k: U32, +kb: Nat, +nb: Nat, ft: Array<U32> & Array<U32>, fc: Array<U32> & Array<U32>, fo: Array<U32> & Array<U32>) -> Three:
  match d:
    case 0n:
      (t, t2) = ft
      (cs, cs2) = fc
      (os, os2) = fo
      three.rejoin(t2, cs2, os2, sum.go(U32.to_nat((U32.shln(1, w) - 1 : U32)), U32.shln(j, w), k, kb, nb, Three{t, cs, os}))
    case 1n+p:
      (t0, t1) = ft
      (c0, c1) = fc
      (o0, o1) = fo
      +i = (j * 2 : U32)
      l r = sums(p, i, w, k, kb, nb, Array.fork(U32, t0), Array.fork(U32, c0), Array.fork(U32, o0))
        sums(p, (i + 1 : U32), w, k, kb, nb, Array.fork(U32, t1), Array.fork(U32, c1), Array.fork(U32, o1))
      three.join(l, r)

# Pass 2c: each table entry becomes its block's first slot
# --------------------------------------------------------

# r holds the table and the entry x read at at: it becomes s, and the n
# entries after it (each step further on) follow, from s + x.
def base.go(+n: Nat, +at: U32, +step: U32, +s: U32, r: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      (t, +x) = r
      t[at] <- s
    case 1n+p:
      (t, +x) = r
      +q = (at + step : U32)
      base.go(p, q, step, (s + x : U32), (t[at] <- s)[q])

def base.at(+c: U32, +kb: Nat, +nb: Nat, t: Array<U32>, r: Array<U32> & U32) -> Hist.Two:
  (os, +s) = r
  Hist.Two{base.go(nb, c, U32.shln(1, kb), s, t[c]), os}

# Column c, when c < K: its entries from its first slot offs[c].
def base.one(lt: Bool, +c: U32, +kb: Nat, +nb: Nat, p: Hist.Two) -> Hist.Two:
  match lt:
    case True{}:
      Hist.Two{t, os} = p
      base.at(c, kb, nb, t, os[c])
    case False{}:
      p

# Columns c to c + n.
def base.cols(+n: Nat, +c: U32, +k: U32, +kb: Nat, +nb: Nat, p: Hist.Two) -> Hist.Two:
  match n:
    case 0n:
      base.one(U32.is_lt(c, k), c, kb, nb, p)
    case 1n+q:
      base.cols(q, (c + 1 : U32), k, kb, nb, base.one(U32.is_lt(c, k), c, kb, nb, p))

# Pass 2c's forks, shaped as pass 2a's, with two handles each to the table
# and the offsets. Group j reads only its own offsets and reads and
# writes only its columns of the table.
def bases(+d: Nat, +j: U32, +w: Nat, +k: U32, +kb: Nat, +nb: Nat, ft: Array<U32> & Array<U32>, fo: Array<U32> & Array<U32>) -> Hist.Two:
  match d:
    case 0n:
      (t, t2) = ft
      (os, os2) = fo
      Hist.two.rejoin(t2, os2, base.cols(U32.to_nat((U32.shln(1, w) - 1 : U32)), U32.shln(j, w), k, kb, nb, Hist.Two{t, os}))
    case 1n+p:
      (t0, t1) = ft
      (o0, o1) = fo
      +i = (j * 2 : U32)
      l r = bases(p, i, w, k, kb, nb, Array.fork(U32, t0), Array.fork(U32, o0))
        bases(p, (i + 1 : U32), w, k, kb, nb, Array.fork(U32, t1), Array.fork(U32, o1))
      Hist.two.join(l, r)

# Pass 3: scatter
# ---------------

def put.at(+j: U32, +slot: U32, pm: Array<U32>, r: Array<U32> & U32) -> Hist.Two:
  (t, +at) = r
  Hist.Two{t[slot] <- (at + 1 : U32), pm[at] <- j}

# Key j, whose bucket's next slot is t[slot]: perm[that slot] <- j, and
# the slot moves on.
def put.one(+j: U32, +slot: U32, p: Hist.Two) -> Hist.Two:
  Hist.Two{t, pm} = p
  put.at(j, slot, pm, t[slot])

def put.fin(ks: Array<U32>, p: Hist.Two) -> Three:
  Hist.Two{t, pm} = p
  Three{ks, t, pm}

# r holds the keys and the key x read at j: key j goes to the next slot
# of its bucket in the row at row, then the n keys after j. k1 is K - 1.
def put.go(+n: Nat, +j: U32, +row: U32, +k1: U32, p: Hist.Two, r: Array<U32> & U32) -> Three:
  match n:
    case 0n:
      (ks, +x) = r
      put.fin(ks, put.one(j, (row + U32.min(x, k1) : U32), p))
    case 1n+q:
      (ks, +x) = r
      +i = (j + 1 : U32)
      put.go(q, i, row, k1, put.one(j, (row + U32.min(x, k1) : U32), p), ks[i])

# Block i (2^e keys from i * 2^e, its row at i * 2^kb).
def puts.leaf(+i: U32, +e: Nat, +kb: Nat, +k: U32, ks: Array<U32>, t: Array<U32>, pm: Array<U32>) -> Three:
  +at = U32.shln(i, e)
  put.go(U32.to_nat((U32.shln(1, e) - 1 : U32)), at, U32.shln(i, kb), (k - 1 : U32), Hist.Two{t, pm}, ks[at])

# Pass 3's forks: d levels down to the blocks under block i, with two
# handles each to the keys, the table and perm. Block i reads only its
# keys, reads and writes only its row of the table, and writes perm only
# at the slots its row hands it: pass 2 gave each (block, bucket) pair its
# own run of slots, so no two lanes write one slot.
def puts(+d: Nat, +i: U32, +e: Nat, +kb: Nat, +k: U32, fk: Array<U32> & Array<U32>, ft: Array<U32> & Array<U32>, fp: Array<U32> & Array<U32>) -> Three:
  match d:
    case 0n:
      (ks, ks2) = fk
      (t, t2) = ft
      (pm, pm2) = fp
      three.rejoin(ks2, t2, pm2, puts.leaf(i, e, kb, k, ks, t, pm))
    case 1n+p:
      (k0, k1) = fk
      (t0, t1) = ft
      (p0, p1) = fp
      +j = (i * 2 : U32)
      l r = puts(p, j, e, kb, k, Array.fork(U32, k0), Array.fork(U32, t0), Array.fork(U32, p0))
        puts(p, (j + 1 : U32), e, kb, k, Array.fork(U32, k1), Array.fork(U32, t1), Array.fork(U32, p1))
      three.join(l, r)

# Driver
# ------

def run.fin(cs: Array<U32>, os: Array<U32>, r: Three) -> Array<U32> & Bufs:
  Three{ks, t, pm} = r
  (ks, Bufs{pm, cs, os, t})

# Pass 3.
def run.puts(+d: Nat, +e: Nat, +kb: Nat, +k: U32, ks: Array<U32>, pm: Array<U32>, cs: Array<U32>, r: Hist.Two) -> Array<U32> & Bufs:
  Hist.Two{t, os} = r
  run.fin(cs, os, puts(d, 0, e, kb, k, Array.fork(U32, ks), Array.fork(U32, t), Array.fork(U32, pm)))

# Pass 2c.
def run.bases(+d: Nat, +e: Nat, +kb: Nat, +k: U32, ks: Array<U32>, pm: Array<U32>, cs: Array<U32>, t: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Bufs:
  (os, +n) = r
  +g = Nat.min(d, kb)
  run.puts(d, e, kb, k, ks, pm, cs, bases(g, 0, Nat.sub(kb, g), k, kb,
    U32.to_nat((U32.shln(1, d) - 1 : U32)), Array.fork(U32, t), Array.fork(U32, os)))

# Pass 2b: offs becomes its exclusive scan.
def run.scan(+d: Nat, +e: Nat, +kb: Nat, +k: U32, ks: Array<U32>, pm: Array<U32>, r: Three) -> Array<U32> & Bufs:
  Three{t, cs, os} = r
  run.bases(d, e, kb, k, ks, pm, cs, t, Scan.exclusive(d, os))

# Pass 2a.
def run.sums(+d: Nat, +e: Nat, +kb: Nat, +k: U32, pm: Array<U32>, cs: Array<U32>, os: Array<U32>, r: Hist.Two) -> Array<U32> & Bufs:
  Hist.Two{ks, t} = r
  +g = Nat.min(d, kb)
  run.scan(d, e, kb, k, ks, pm, sums(g, 0, Nat.sub(kb, g), k, kb,
    U32.to_nat((U32.shln(1, d) - 1 : U32)), Array.fork(U32, t),
    Array.fork(U32, Hist.fit.eq(kb, Array.size(U32, cs))),
    Array.fork(U32, Hist.fit.eq(kb, Array.size(U32, os)))))

# Pass 1.
def run(+b: Nat, +k: U32, bufs: Bufs, r: Array<U32> & U32) -> Array<U32> & Bufs:
  Bufs{pm, cs, os, t} = bufs
  (ks, +n) = r
  +kk = U32.max(k, 1)
  +kb = Hist.kbits(kk)
  +lg = U32.log2(n)
  +d = Nat.min(b, lg)
  +e = Nat.sub(lg, d)
  run.sums(d, e, kb, kk, Hist.fit.eq(lg, Array.size(U32, pm)), cs, os, Hist.rows(d, 0, e, kb, kk,
    Array.fork(U32, ks), Array.fork(U32, Hist.fit.ge(Nat.add(d, kb), Array.size(U32, t)))))

# Gather
# ------

# A gather's arrays: the permutation, the source and the destination.
type Moved<-T: Data> is Type:
  Moved{perm: Array<U32>, src: Array<T>, dst: Array<T>}

type Sd<-T: Data> is Type:
  Sd{src: Array<T>, dst: Array<T>}

def gat.at(~T: Data, +j: U32, dst: Array<T>, r: Array<T> & T) -> Sd<T>:
  (src, v) = r
  Sd{src, Array.set(T, dst, j, v)}

# dst[j] <- src[x].
def gat.one(~T: Data, +j: U32, +x: U32, p: Sd<T>) -> Sd<T>:
  match p:
    case Sd{src, dst}:
      gat.at(~T, j, dst, Array.get(T, src, x))

def gat.fin(~T: Data, pm: Array<U32>, p: Sd<T>) -> Moved<T>:
  match p:
    case Sd{src, dst}:
      Moved{pm, src, dst}

# r holds perm and its entry x at j: dst[j] <- src[x], then the n entries
# after j.
def gat.go(~T: Data, +n: Nat, +j: U32, p: Sd<T>, r: Array<U32> & U32) -> Moved<T>:
  match n:
    case 0n:
      (pm, +x) = r
      gat.fin(~T, pm, gat.one(~T, j, x, p))
    case 1n+q:
      (pm, +x) = r
      +i = (j + 1 : U32)
      gat.go(~T, q, i, gat.one(~T, j, x, p), pm[i])

def moved.join(~T: Data, l: Moved<T>, r: Moved<T>) -> Moved<T>:
  match l r:
    case Moved{lp, ls, ld} Moved{rp, rs, rd}:
      Moved{Array.join(U32, lp, rp), Array.join(T, ls, rs), Array.join(T, ld, rd)}

def moved.rejoin(~T: Data, p2: Array<U32>, s2: Array<T>, d2: Array<T>, r: Moved<T>) -> Moved<T>:
  match r:
    case Moved{p, s, d}:
      Moved{Array.join(U32, p, p2), Array.join(T, s, s2), Array.join(T, d, d2)}

# The gather's forks: d levels down to blocks of 2^e slots under block i,
# with two handles each to perm, src and dst. Block i reads only its
# entries of perm, reads src anywhere (no lane writes src) and writes only
# its slots of dst.
def gats(~T: Data, +d: Nat, +i: U32, +e: Nat, fp: Array<U32> & Array<U32>, fs: Array<T> & Array<T>, fd: Array<T> & Array<T>) -> Moved<T>:
  match d:
    case 0n:
      (pm, pm2) = fp
      (src, src2) = fs
      (dst, dst2) = fd
      +at = U32.shln(i, e)
      moved.rejoin(~T, pm2, src2, dst2, gat.go(~T, U32.to_nat((U32.shln(1, e) - 1 : U32)), at,
        Sd{src, dst}, pm[at]))
    case 1n+p:
      (p0, p1) = fp
      (s0, s1) = fs
      (d0, d1) = fd
      +j = (i * 2 : U32)
      l r = gats(~T, p, j, e, Array.fork(U32, p0), Array.fork(T, s0), Array.fork(T, d0))
        gats(~T, p, (j + 1 : U32), e, Array.fork(U32, p1), Array.fork(T, s1), Array.fork(T, d1))
      moved.join(~T, l, r)

def gather.pick(~T: Data, ok: Bool, +lg: Nat, +v: T, src: Array<T>, dst: Array<T>) -> Sd<T>:
  match ok:
    case True{}:
      Sd{src, dst}
    case False{}:
      Sd{src, Array.new(T, lg, v)}

def gather.dst(~T: Data, ok: Bool, +lg: Nat, dst: Array<T>, r: Array<T> & T) -> Sd<T>:
  (src, v) = r
  gather.pick(~T, ok, lg, v, src, dst)

def gather.run(~T: Data, +b: Nat, +lg: Nat, pm: Array<U32>, p: Sd<T>) -> Moved<T>:
  match p:
    case Sd{src, dst}:
      +d = Nat.min(b, lg)
      gats(~T, d, 0, Nat.sub(lg, d), Array.fork(U32, pm), Array.fork(T, src), Array.fork(T, dst))

def gather.at(~T: Data, +b: Nat, src: Array<T>, r: Array<U32> & U32, s: Array<T> & U32) -> Moved<T>:
  (pm, +n) = r
  (dst, +m) = s
  +lg = U32.log2(n)
  gather.run(~T, b, lg, pm, gather.dst(~T, U32.is_eq(m, n), lg, dst, Array.get(T, src, 0)))

# API
# ---

# The stable counting sort of keys into k buckets at fork depth b. Returns
# the keys, unchanged, and the buffers: perm, counts and offs hold the
# result.
def by_key(+b: Nat, +k: U32, keys: Array<U32>, bufs: Bufs) -> Array<U32> & Bufs:
  run(b, k, bufs, Array.size(U32, keys))

# dst[j] <- src[perm[j]] for every slot j, at fork depth b: with by_key's
# perm, src in sorted order. src may be any size (indices wrap); dst is
# reused when it has perm's size, else replaced by a new array. Returns
# the three arrays.
def gather(~T: Data, +b: Nat, perm: Array<U32>, src: Array<T>, dst: Array<T>) -> Moved<T>:
  gather.at(~T, b, src, Array.size(U32, perm), Array.size(T, dst))
