# bend-parallel -- the laws of the sequential references (ref.bend).
#
# The parallel defs (scan.bend, histogram.bend, sort.bend) share arrays
# through Base's @unsafe Array.fork and Array.join, so the checker cannot
# relate them to these laws (in the theory a fork is two copies and a join
# drops the second copy's writes). The tests relate them instead: every
# test compares a parallel result with the reference, bit for bit, at many
# sizes and fork depths, on every lane.
#
# Proven in PROOF.bend: every law below.
import Base
import ./ref.bend as Ref

# Scan
# ----
# Each law is stated from any start s; Ref.exclusive(xs) and
# Ref.inclusive(xs) are the start 0.

# LAW: the exclusive scan's total is the sum
law exclusive_total:
  for xs: List<&2, U32>
  for +s: U32
  {Ref.total(Ref.exclusive_from(xs, s)) == Ref.sum_from(xs, s) : U32}

# LAW: the exclusive scan's entry i is the sum of the i entries before it
# (past the end, at reads the default, here the total)
law exclusive_prefix:
  for xs: List<&2, U32>
  for +s: U32
  for i: Nat
  {Ref.at(Ref.items(Ref.exclusive_from(xs, s)), i, Ref.sum_from(xs, s))
    == Ref.sum_from(Ref.take(xs, i), s) : U32}

# LAW: the inclusive scan's total is the sum
law inclusive_total:
  for xs: List<&2, U32>
  for +s: U32
  {Ref.total(Ref.inclusive_from(xs, s)) == Ref.sum_from(xs, s) : U32}

# LAW: the inclusive scan's entry i is the sum of the entries through i
law inclusive_prefix:
  for xs: List<&2, U32>
  for +s: U32
  for i: Nat
  {Ref.at(Ref.items(Ref.inclusive_from(xs, s)), i, Ref.sum_from(xs, s))
    == Ref.sum_from(Ref.take(xs, 1n+i), s) : U32}

# LAW: a scan keeps the length
law exclusive_length:
  for xs: List<&2, U32>
  for +s: U32
  {List.length(&2, U32, Ref.items(Ref.exclusive_from(xs, s))) == List.length(&2, U32, xs) : Nat}

law inclusive_length:
  for xs: List<&2, U32>
  for +s: U32
  {List.length(&2, U32, Ref.items(Ref.inclusive_from(xs, s))) == List.length(&2, U32, xs) : Nat}

# Histogram
# ---------

# LAW: the counts add up to the number of keys (mod 2^32, as U32s do)
# LAW: the counts add up to the number of keys (mod 2^32, as U32s do)
law histogram_total:
  for +k: U32
  for +xs: List<&2, U32>
  {Ref.sum(Ref.histogram(k, xs)) == U32.from_nat(List.length(&2, U32, xs)) : U32}
