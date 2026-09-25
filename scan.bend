# scan.bend: parallel prefix sums over an Array<U32>, in place.
#
#   import ./scan.bend as Scan
#   Scan.exclusive(8n, a)   # (a, total): a[j] becomes a[0] + .. + a[j - 1]
#   Scan.inclusive(8n, a)   # (a, total): a[j] becomes a[0] + .. + a[j]
#
# A call's result is taken apart by a def's parameter (a def of yours
# taking r: Array<U32> & U32), not by a let or match on the call itself.
#
# Sums wrap at 2^32, as U32.add does. The first argument is the fork
# depth b: the array is cut into 2^b blocks of equal size (b is lowered to
# log2 of the size when larger). Every b gives the same bits; b only sets
# how many lanes share the work. A call under `!` (Scan.exclusive!(b, a),
# or a def of yours that calls it, marked with `!`) runs its forks on the
# GPU; without `!` they run on the CPU threads.
#
# Three passes, with no atomics:
#   1. per block, in parallel: the block's sum into s[i];
#   2. one lane: s becomes its exclusive scan (the blocks' bases) and the
#      total;
#   3. per block, in parallel: the block's scan from its base, in place.
# ref.bend's exclusive and inclusive are the sequential references; the
# tests check both passes against them bit for bit at many sizes and b.
#
# Sharing. The blocks' lanes read and write one array through handles
# from Array.fork (Base, @unsafe): two O(1) handles to one block, joined
# back by Array.join. No def here is @unsafe itself: the fork trees below
# recurse on their depth, which the checker verifies. But in Bend's theory
# Array.fork(a) is (a, a) and Array.join(a, b) is a, so the theory drops
# the writes made through the second handle: never evaluate these defs in
# the checker (a main that returns a value); call them from an IO main,
# which runs compiled. `bend` lists every def that relies on the fork.
import Base

# Loops (one lane)
# ----------------

# r holds the array and the entry x read at j: adds x and the n entries
# after it to s. Returns the array and the sum.
def sum.go(+n: Nat, +j: U32, +s: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match n:
    case 0n:
      (a, +x) = r
      (a, (s + x : U32))
    case 1n+p:
      (a, +x) = r
      +q = (j + 1 : U32)
      sum.go(p, q, (s + x : U32), a[q])

# r holds the array and the entry x read at j: a[j] becomes s, the sum
# before it, and so on for the n entries after it. Returns the array and
# the running sum past the last entry.
def ex.go(+n: Nat, +j: U32, +s: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match n:
    case 0n:
      (a, +x) = r
      (a[j] <- s, (s + x : U32))
    case 1n+p:
      (a, +x) = r
      +q = (j + 1 : U32)
      ex.go(p, q, (s + x : U32), (a[j] <- s)[q])

# As ex.go, but a[j] becomes the sum through it.
def in.go(+n: Nat, +j: U32, +s: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match n:
    case 0n:
      (a, +x) = r
      +t = (s + x : U32)
      (a[j] <- t, t)
    case 1n+p:
      (a, +x) = r
      +q = (j + 1 : U32)
      +t = (s + x : U32)
      in.go(p, q, t, (a[j] <- t)[q])

# The scan of the n + 1 entries from j, from base s.
def go(+inc: Bool, +n: Nat, +j: U32, +s: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match inc:
    case False{}:
      ex.go(n, j, s, r)
    case True{}:
      in.go(n, j, s, r)

# Handles
# -------

type Two is Type:
  Two{a: Array<U32>, s: Array<U32>}

def two.join(l: Two, r: Two) -> Two:
  Two{la, ls} = l
  Two{ra, rs} = r
  Two{Array.join(U32, la, ra), Array.join(U32, ls, rs)}

# A leaf's spare handles, joined back after its work.
def two.rejoin(a2: Array<U32>, s2: Array<U32>, r: Two) -> Two:
  Two{a, s} = r
  Two{Array.join(U32, a, a2), Array.join(U32, s, s2)}

# Pass 1
# ------

def sums.leaf.fin(+i: U32, s: Array<U32>, r: Array<U32> & U32) -> Two:
  (a, +v) = r
  Two{a, s[i] <- v}

# Block i (2^e entries): its sum into s[i].
def sums.leaf(+i: U32, +e: Nat, a: Array<U32>, s: Array<U32>) -> Two:
  +at = U32.shln(i, e)
  sums.leaf.fin(i, s, sum.go(U32.to_nat((U32.shln(1, e) - 1 : U32)), at, 0, a[at]))

# Pass 1's forks: d levels down to the leaves under leaf index i. fa and
# fs are two handles each to the data a and the sums s. Leaf i reads only
# its block of a and writes only s[i], so no two lanes touch one slot.
def sums(+d: Nat, +i: U32, +e: Nat, fa: Array<U32> & Array<U32>, fs: Array<U32> & Array<U32>) -> Two:
  match d:
    case 0n:
      (a, a2) = fa
      (s, s2) = fs
      two.rejoin(a2, s2, sums.leaf(i, e, a, s))
    case 1n+p:
      (a0, a1) = fa
      (s0, s1) = fs
      +j = (i * 2 : U32)
      l r = sums(p, j, e, Array.fork(U32, a0), Array.fork(U32, s0))
        sums(p, (j + 1 : U32), e, Array.fork(U32, a1), Array.fork(U32, s1))
      two.join(l, r)

# Pass 3
# ------

def puts.leaf.fin(s: Array<U32>, r: Array<U32> & U32) -> Two:
  (a, +t) = r
  Two{a, s}

def puts.leaf.at(+inc: Bool, +i: U32, +e: Nat, a: Array<U32>, r: Array<U32> & U32) -> Two:
  (s, +base) = r
  +at = U32.shln(i, e)
  puts.leaf.fin(s, go(inc, U32.to_nat((U32.shln(1, e) - 1 : U32)), at, base, a[at]))

# Block i: its scan in place, from its base s[i].
def puts.leaf(+inc: Bool, +i: U32, +e: Nat, a: Array<U32>, s: Array<U32>) -> Two:
  puts.leaf.at(inc, i, e, a, s[i])

# Pass 3's forks, shaped as pass 1's. Leaf i reads s[i] and reads and
# writes only its block of a: no two lanes touch one slot.
def puts(+inc: Bool, +d: Nat, +i: U32, +e: Nat, fa: Array<U32> & Array<U32>, fs: Array<U32> & Array<U32>) -> Two:
  match d:
    case 0n:
      (a, a2) = fa
      (s, s2) = fs
      two.rejoin(a2, s2, puts.leaf(inc, i, e, a, s))
    case 1n+p:
      (a0, a1) = fa
      (s0, s1) = fs
      +j = (i * 2 : U32)
      l r = puts(inc, p, j, e, Array.fork(U32, a0), Array.fork(U32, s0))
        puts(inc, p, (j + 1 : U32), e, Array.fork(U32, a1), Array.fork(U32, s1))
      two.join(l, r)

# Driver
# ------

def run.fin(r: Two, +total: U32) -> Array<U32> & U32:
  Two{a, s} = r
  (a, total)

# Pass 2 on one lane (2^d sums), then pass 3.
def run.mid(+inc: Bool, +d: Nat, +e: Nat, a: Array<U32>, r: Array<U32> & U32) -> Array<U32> & U32:
  (s, +total) = r
  run.fin(puts(inc, d, 0, e, Array.fork(U32, a), Array.fork(U32, s)), total)

def run.sums(+inc: Bool, +d: Nat, +e: Nat, r: Two) -> Array<U32> & U32:
  Two{a, s} = r
  run.mid(inc, d, e, a, ex.go(U32.to_nat((U32.shln(1, d) - 1 : U32)), 0, 0, s[0]))

def run(+inc: Bool, +b: Nat, r: Array<U32> & U32) -> Array<U32> & U32:
  (a, +n) = r
  +lg = U32.log2(n)
  +d = Nat.min(b, lg)
  +e = Nat.sub(lg, d)
  run.sums(inc, d, e, sums(d, 0, e, Array.fork(U32, a), Array.fork(U32, Array.new(U32, d, 0))))

# API
# ---

# a[j] becomes a[0] + .. + a[j - 1] (a[0] becomes 0); returns the array
# and the total, a[0] + .. + a[n - 1].
def exclusive(+b: Nat, a: Array<U32>) -> Array<U32> & U32:
  run(False{}, b, Array.size(U32, a))

# a[j] becomes a[0] + .. + a[j]; returns the array and the total.
def inclusive(+b: Nat, a: Array<U32>) -> Array<U32> & U32:
  run(True{}, b, Array.size(U32, a))
