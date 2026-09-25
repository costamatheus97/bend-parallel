# histogram.bend: a parallel histogram of U32 keys into K buckets, with no
# atomics.
#
#   import ./histogram.bend as Hist
#   Hist.count(8n, 256, keys, Hist.Bufs.new())   # (keys, bufs)
#   Hist.Bufs{counts, table} = bufs              # counts[c]: the keys in bucket c
#
# k is the bucket count K (0 counts as 1), any U32. A key at or past K
# counts as K - 1. counts holds 2^ceil(log2 K) entries: the K counts, then
# zeros. b is the fork depth, as in scan.bend: 2^b blocks of keys (b is
# lowered to log2 of the key count when larger), and every b gives the
# same counts. A call under `!` runs its forks on the GPU.
#
# Bufs carries the two buffers from call to call: the count table (2^b
# rows of 2^ceil(log2 K) entries, so 2^(b + ceil(log2 K)) U32s) and the
# counts. A call keeps a buffer that is big enough and allocates a new one
# otherwise. Array.new fills on one lane, which under `!` costs about 76 ms
# per million entries on the GPU we measured (see README), so size the
# buffers once with Bufs.sized outside the `!` and hand them back each
# call.
#
# Two passes:
#   1. per block of keys, in parallel: zero the block's row of the table,
#      then count its keys into it (the block owns its row);
#   2. per group of buckets, in parallel: a bucket's count is the sum of
#      its column over the rows (the group owns its counts).
# ref.bend's histogram is the sequential reference.
#
# Sharing: as in scan.bend, lanes share arrays through Base's @unsafe
# Array.fork and Array.join; no def here is @unsafe itself, and none may
# be evaluated in the checker (call them from an IO main).
import Base

# Buffers
# -------

type Bufs is Type:
  Bufs{counts: Array<U32>, table: Array<U32>}

# Empty buffers: the first call allocates what it needs.
def Bufs.new() -> Bufs:
  Bufs{[0 : U32^0n], [0 : U32^0n]}

def kbits.of(big: Bool, +k: U32) -> Nat:
  match big:
    case False{}:
      0n
    case True{}:
      1n+U32.log2((k - 1 : U32))

# ceil(log2 K), for K >= 1.
def kbits(+k: U32) -> Nat:
  kbits.of(U32.is_lt(1, k), k)

# Buffers for 2^lg keys at fork depth b and k buckets, allocated now.
def Bufs.sized(+b: Nat, +k: U32, +lg: Nat) -> Bufs:
  +kb = kbits(U32.max(k, 1))
  Bufs{Array.new(U32, kb, 0), Array.new(U32, Nat.add(Nat.min(b, lg), kb), 0)}

def fit.pick(ok: Bool, +d: Nat, t: Array<U32>) -> Array<U32>:
  match ok:
    case True{}:
      t
    case False{}:
      Array.new(U32, d, 0)

# t when it holds exactly 2^d entries, else a new one.
def fit.eq(+d: Nat, r: Array<U32> & U32) -> Array<U32>:
  (t, +n) = r
  fit.pick(U32.is_eq(n, U32.shln(1, d)), d, t)

# t when it holds at least 2^d entries, else a new one.
def fit.ge(+d: Nat, r: Array<U32> & U32) -> Array<U32>:
  (t, +n) = r
  fit.pick(U32.is_ge(n, U32.shln(1, d)), d, t)

# Handles
# -------

type Two is Type:
  Two{a: Array<U32>, b: Array<U32>}

def two.join(l: Two, r: Two) -> Two:
  Two{la, lb} = l
  Two{ra, rb} = r
  Two{Array.join(U32, la, ra), Array.join(U32, lb, rb)}

def two.rejoin(a2: Array<U32>, b2: Array<U32>, r: Two) -> Two:
  Two{a, b} = r
  Two{Array.join(U32, a, a2), Array.join(U32, b, b2)}

# Pass 1: rows
# ------------

# n + 1 zeros from at.
def zero.go(+n: Nat, +at: U32, t: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      t[at] <- 0
    case 1n+p:
      zero.go(p, (at + 1 : U32), t[at] <- 0)

def bump.at(+i: U32, r: Array<U32> & U32) -> Array<U32>:
  (t, +v) = r
  t[i] <- (v + 1 : U32)

# One more at t[i].
def bump(+i: U32, t: Array<U32>) -> Array<U32>:
  bump.at(i, t[i])

# r holds the keys and the key x read at j: one more in x's bucket of the
# row at row, then the same for the n keys after j. k1 is K - 1.
def count.go(+n: Nat, +j: U32, +row: U32, +k1: U32, t: Array<U32>, r: Array<U32> & U32) -> Two:
  match n:
    case 0n:
      (ks, +x) = r
      Two{ks, bump((row + U32.min(x, k1) : U32), t)}
    case 1n+p:
      (ks, +x) = r
      +q = (j + 1 : U32)
      count.go(p, q, row, k1, bump((row + U32.min(x, k1) : U32), t), ks[q])

# Block i (2^e keys from i * 2^e): its row, at i * 2^kb, zeroed, then its
# keys counted into it. k is K (at least 1).
def rows.leaf(+i: U32, +e: Nat, +kb: Nat, +k: U32, ks: Array<U32>, t: Array<U32>) -> Two:
  +row = U32.shln(i, kb)
  +at = U32.shln(i, e)
  count.go(U32.to_nat((U32.shln(1, e) - 1 : U32)), at, row, (k - 1 : U32),
    zero.go(U32.to_nat((k - 1 : U32)), row, t), ks[at])

# Pass 1's forks: d levels down to the blocks under block index i. fk and
# ft are two handles each to the keys and the table. Block i reads only
# its keys and reads and writes only its row (entries i * 2^kb to
# i * 2^kb + K - 1): no two lanes touch one slot.
def rows(+d: Nat, +i: U32, +e: Nat, +kb: Nat, +k: U32, fk: Array<U32> & Array<U32>, ft: Array<U32> & Array<U32>) -> Two:
  match d:
    case 0n:
      (ks, ks2) = fk
      (t, t2) = ft
      two.rejoin(ks2, t2, rows.leaf(i, e, kb, k, ks, t))
    case 1n+p:
      (k0, k1) = fk
      (t0, t1) = ft
      +j = (i * 2 : U32)
      l r = rows(p, j, e, kb, k, Array.fork(U32, k0), Array.fork(U32, t0))
        rows(p, (j + 1 : U32), e, kb, k, Array.fork(U32, k1), Array.fork(U32, t1))
      two.join(l, r)

# Pass 2: columns
# ---------------

# r holds the table and the entry x read at at: adds x and the n entries
# after it, each step further on, to s.
def col.go(+n: Nat, +at: U32, +step: U32, +s: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match n:
    case 0n:
      (t, +x) = r
      (t, (s + x : U32))
    case 1n+p:
      (t, +x) = r
      +q = (at + step : U32)
      col.go(p, q, step, (s + x : U32), t[q])

def col.put(+c: U32, cs: Array<U32>, r: Array<U32> & U32) -> Two:
  (t, +v) = r
  Two{t, cs[c] <- v}

# Column c's count into cs[c]: its sum over the nb + 1 rows when c < K,
# else 0.
def col.one(lt: Bool, +c: U32, +kb: Nat, +nb: Nat, p: Two) -> Two:
  match lt:
    case True{}:
      Two{t, cs} = p
      col.put(c, cs, col.go(nb, c, U32.shln(1, kb), 0, t[c]))
    case False{}:
      Two{t, cs} = p
      Two{t, cs[c] <- 0}

# Columns c to c + n.
def cols.go(+n: Nat, +c: U32, +k: U32, +kb: Nat, +nb: Nat, p: Two) -> Two:
  match n:
    case 0n:
      col.one(U32.is_lt(c, k), c, kb, nb, p)
    case 1n+q:
      cols.go(q, (c + 1 : U32), k, kb, nb, col.one(U32.is_lt(c, k), c, kb, nb, p))

# Pass 2's forks: d levels down to groups of 2^w columns under group index
# j. ft and fc are two handles each to the table and the counts. Group j
# reads only its columns of the table and writes only its counts (entries
# j * 2^w to j * 2^w + 2^w - 1): no two lanes write one slot.
def cols(+d: Nat, +j: U32, +w: Nat, +k: U32, +kb: Nat, +nb: Nat, ft: Array<U32> & Array<U32>, fc: Array<U32> & Array<U32>) -> Two:
  match d:
    case 0n:
      (t, t2) = ft
      (cs, cs2) = fc
      two.rejoin(t2, cs2, cols.go(U32.to_nat((U32.shln(1, w) - 1 : U32)), U32.shln(j, w), k, kb, nb, Two{t, cs}))
    case 1n+p:
      (t0, t1) = ft
      (c0, c1) = fc
      +i = (j * 2 : U32)
      l r = cols(p, i, w, k, kb, nb, Array.fork(U32, t0), Array.fork(U32, c0))
        cols(p, (i + 1 : U32), w, k, kb, nb, Array.fork(U32, t1), Array.fork(U32, c1))
      two.join(l, r)

# Driver
# ------

def count.fin(keys: Array<U32>, r: Two) -> Array<U32> & Bufs:
  Two{table, counts} = r
  (keys, Bufs{counts, table})

# Pass 2 over the 2^kb columns, 2^min(d, kb) groups.
def count.cols(+d: Nat, +k: U32, +kb: Nat, counts: Array<U32>, r: Two) -> Array<U32> & Bufs:
  Two{keys, table} = r
  +g = Nat.min(d, kb)
  count.fin(keys, cols(g, 0, Nat.sub(kb, g), k, kb, U32.to_nat((U32.shln(1, d) - 1 : U32)),
    Array.fork(U32, table), Array.fork(U32, fit.eq(kb, Array.size(U32, counts)))))

def count.at(+b: Nat, +k: U32, bufs: Bufs, r: Array<U32> & U32) -> Array<U32> & Bufs:
  Bufs{counts, table} = bufs
  (keys, +n) = r
  +kk = U32.max(k, 1)
  +kb = kbits(kk)
  +lg = U32.log2(n)
  +d = Nat.min(b, lg)
  count.cols(d, kk, kb, counts, rows(d, 0, Nat.sub(lg, d), kb, kk, Array.fork(U32, keys),
    Array.fork(U32, fit.ge(Nat.add(d, kb), Array.size(U32, table)))))

# API
# ---

# The histogram of keys into k buckets at fork depth b. Returns the keys,
# unchanged, and the buffers, whose counts field holds the counts.
def count(+b: Nat, +k: U32, keys: Array<U32>, bufs: Bufs) -> Array<U32> & Bufs:
  count.at(b, k, bufs, Array.size(U32, keys))
