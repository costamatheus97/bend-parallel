# ref.bend: the sequential references, over lists. Safe code only: every
# def here is checked for termination and none relies on Array.fork, so
# LAWS.bend states their laws and PROOF.bend proves them.
#
#   import ./ref.bend as Ref
#   Ref.exclusive(xs)          # (the exclusive prefix sums, the total)
#   Ref.inclusive(xs)          # (the inclusive prefix sums, the total)
#   Ref.histogram(k, keys)     # the K counts
#   Ref.perm(k, keys)          # the stable counting sort's source indices
#   Ref.offsets(k, keys)       # the K bucket starts
#
# The parallel defs (scan.bend, histogram.bend, sort.bend) must equal these
# bit for bit; the tests compare them at many sizes and fork depths. The
# lists are List<&2, U32> (reusable), as the laws read them more than once.
#
# Buckets. k is the bucket count K; K = 0 counts as 1. A key at or past K
# counts as K - 1 (clamped), in the parallel code too, so a bad key can
# neither write outside the tables nor make the two disagree.
#
# Cost. These are specs, not fast code: the scan and the histogram's
# walk are O(n) and O(n * K) (a list has no O(1) index), and perm peels
# one bucket at a time, O(n * K).
import Base

# Scan
# ----

# s + xs[0] + xs[1] + .., added left to right (wrapping at 2^32).
def sum_from(xs: List<&2, U32>, +s: U32) -> U32:
  match xs:
    case Nil{}:
      s
    case h <> t:
      sum_from(t, (s + h : U32))

def sum(xs: List<&2, U32>) -> U32:
  sum_from(xs, 0)

def items(r: List<&2, U32> & U32) -> List<&2, U32>:
  (ys, t) = r
  ys

def total(r: List<&2, U32> & U32) -> U32:
  (ys, t) = r
  t

def cons1(+s: U32, r: List<&2, U32> & U32) -> List<&2, U32> & U32:
  (ys, t) = r
  (s <> ys, t)

# Each entry becomes s plus the entries before it; beside the list, the
# running sum past the end.
def exclusive_from(xs: List<&2, U32>, +s: U32) -> List<&2, U32> & U32:
  match xs:
    case Nil{}:
      (Nil{}, s)
    case h <> t:
      cons1(s, exclusive_from(t, (s + h : U32)))

# Each entry becomes s plus the entries through it.
def inclusive_from(xs: List<&2, U32>, +s: U32) -> List<&2, U32> & U32:
  match xs:
    case Nil{}:
      (Nil{}, s)
    case h <> t:
      +u = (s + h : U32)
      cons1(u, inclusive_from(t, u))

def exclusive(xs: List<&2, U32>) -> List<&2, U32> & U32:
  exclusive_from(xs, 0)

def inclusive(xs: List<&2, U32>) -> List<&2, U32> & U32:
  inclusive_from(xs, 0)

# The entry at i, or d past the end.
def at(xs: List<&2, U32>, i: Nat, +d: U32) -> U32:
  match xs i:
    case Nil{} _:
      d
    case h <> t 0n:
      h
    case h <> t 1n+j:
      at(t, j, d)

# The first i entries.
def take(xs: List<&2, U32>, i: Nat) -> List<&2, U32>:
  match xs i:
    case _ 0n:
      Nil{}
    case Nil{} 1n+j:
      Nil{}
    case h <> t 1n+j:
      h <> take(t, j)

# Histogram
# ---------

def pick(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# K, the bucket count: k, or 1 when k is 0.
def buckets(+k: U32) -> Nat:
  +n = U32.to_nat(k)
  pick(Nat.is_lt(0n, n), n, 1n)

# The bucket of key x: x, or K - 1 when x >= K.
def bucket(+k: U32, +x: U32) -> Nat:
  +n = U32.to_nat(x)
  +kk = buckets(k)
  pick(Nat.is_lt(n, kk), n, Nat.sub(kk, 1n))

# n zeros.
def zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> zeros(p)

# One more at index i. Past the end it adds a cell holding 1, which the
# histogram never reaches (a bucket is below K) but which keeps "one bump
# adds one to the sum" true of every list.
def bump(cs: List<&2, U32>, i: Nat) -> List<&2, U32>:
  match cs i:
    case Nil{} _:
      [1]
    case h <> t 0n:
      U32.inc(h) <> t
    case h <> t 1n+j:
      h <> bump(t, j)

def hist_from(xs: List<&2, U32>, +k: U32, cs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      cs
    case h <> t:
      hist_from(t, k, bump(cs, bucket(k, h)))

# The K counts: counts[c] is how many keys fall in bucket c.
def histogram(+k: U32, xs: List<&2, U32>) -> List<&2, U32>:
  hist_from(xs, k, zeros(buckets(k)))

# The K bucket starts: the histogram's exclusive scan.
def offsets(+k: U32, xs: List<&2, U32>) -> List<&2, U32>:
  items(exclusive(histogram(k, xs)))

# Sort
# ----

# A key and its index in the input.
type Item is Data:
  Item{key: U32, idx: U32}

# The keys with their indices from i.
def index(xs: List<&2, U32>, +i: U32) -> List<&2, Item>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Item{h, i} <> index(t, (i + 1 : U32))

def rank(+k: U32, it: Item) -> Nat:
  match it:
    case Item{key, idx}:
      bucket(k, key)

def keep(+h: Item, r: List<&2, Item>, b: Bool) -> List<&2, Item>:
  match b:
    case True{}:
      h <> r
    case False{}:
      r

# The items in bucket c, in order.
def eqs(xs: List<&2, Item>, +k: U32, +c: Nat) -> List<&2, Item>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      keep(h, eqs(t, k, c), Nat.is_eq(rank(k, h), c))

# The items not in bucket c, in order.
def nes(xs: List<&2, Item>, +k: U32, +c: Nat) -> List<&2, Item>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      keep(h, nes(t, k, c), Bool.not(Nat.is_eq(rank(k, h), c)))

# Buckets c, c + 1, .. in turn, f of them, each in input order; what is
# left after the f-th goes last, in input order.
def peel(f: Nat, +xs: List<&2, Item>, +k: U32, +c: Nat) -> List<&2, Item>:
  match f:
    case 0n:
      xs
    case 1n+g:
      List.append(&2, Item, eqs(xs, k, c), peel(g, nes(xs, k, c), k, 1n+c))

# The stable counting sort of the items: buckets 0 .. K - 2 peeled, then
# the rest, which is bucket K - 1.
def sort_items(+k: U32, +xs: List<&2, Item>) -> List<&2, Item>:
  peel(Nat.sub(buckets(k), 1n), xs, k, 0n)

def idxs(xs: List<&2, Item>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Item{key, idx} <> t:
      idx <> idxs(t)

def keys_of(xs: List<&2, Item>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Item{key, idx} <> t:
      key <> keys_of(t)

# perm[j] is the input index of the key that the stable sort puts at j.
def perm(+k: U32, xs: List<&2, U32>) -> List<&2, U32>:
  idxs(sort_items(k, index(xs, 0)))

# The keys in sorted order.
def sorted(+k: U32, xs: List<&2, U32>) -> List<&2, U32>:
  keys_of(sort_items(k, index(xs, 0)))

# Vocabulary for the laws
# -----------------------

# b's 1, added to n.
def bump1(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# How many items of xs ~eq calls equal to y (hub: bend-lawful-stdlib).
def count(~eq: Item -> Item -> Bool, +y: Item, xs: List<&2, Item>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      bump1(eq(y, h), count(~eq, y, t))

# Every item's bucket is at least lo, and the buckets ascend.
def from(+k: U32, +lo: Nat, xs: List<&2, Item>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +h <> t:
      ({True{} == Nat.is_le(lo, rank(k, h)) : Bool} & from(k, rank(k, h), t))

# The items' buckets ascend.
def Sorted(+k: U32, xs: List<&2, Item>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +h <> t:
      from(k, rank(k, h), t)
