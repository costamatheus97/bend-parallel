# check.bend: the tests' inputs and comparisons. Inputs come from a
# xorshift32 generator that tests/lib/expect.py mirrors, so every #| line
# is computed independently of Bend.
import Base

# xorshift32 (13, 17, 5).
def prng(+x: U32) -> U32:
  +a = U32.xor(x, U32.shln(x, 13n))
  +b = U32.xor(a, U32.shrn(a, 17n))
  U32.xor(b, U32.shln(b, 5n))

# Entry j of stream seed: prng(prng((j + 1) * 2654435761 + seed)).
def at(+seed: U32, +j: U32) -> U32:
  prng(prng(((j + 1) * 2654435761 + seed : U32)))

def gen.of(raw: Bool, md: Bool, +seed: U32, +m: U32, +j: U32) -> U32:
  match raw md:
    case True{} _:
      at(seed, j)
    case False{} True{}:
      U32.mod(at(seed, j), m)
    case False{} False{}:
      m

# kind 0: at(seed, j); kind 1: at(seed, j) % m; kind 2: m (every entry).
def gen(+kind: U32, +seed: U32, +m: U32, +j: U32) -> U32:
  gen.of(U32.is_eq(kind, 0), U32.is_eq(kind, 1), seed, m, j)

def fill.go(+n: Nat, +j: U32, +kind: U32, +seed: U32, +m: U32, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a[j] <- gen(kind, seed, m, j)
    case 1n+p:
      fill.go(p, (j + 1 : U32), kind, seed, m, a[j] <- gen(kind, seed, m, j))

# 2^d entries of generator (kind, seed, m).
def fill(+d: Nat, +kind: U32, +seed: U32, +m: U32) -> Array<U32>:
  fill.go(U32.to_nat((U32.shln(1, d) - 1 : U32)), 0, kind, seed, m, Array.new(U32, d, 0))

# The same entries as a list.
def list.go(n: Nat, +kind: U32, +seed: U32, +m: U32, +j: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      gen(kind, seed, m, j) <> list.go(p, kind, seed, m, (j + 1 : U32))

def list(+d: Nat, +kind: U32, +seed: U32, +m: U32) -> List<&2, U32>:
  list.go(U32.to_nat(U32.shln(1, d)), kind, seed, m, 0)

# r holds the array and its entry x at n: x, then the entries below n,
# consed onto acc.
def to_list.go(+n: Nat, acc: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  match n:
    case 0n:
      (a, +x) = r
      (a, x <> acc)
    case 1n+p:
      (a, +x) = r
      to_list.go(p, x <> acc, a[U32.from_nat(p)])

def to_list.at(r: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  (a, +n) = r
  to_list.go(U32.to_nat((n - 1 : U32)), Nil{}, a[(n - 1 : U32)])

# The array (handed back) and its entries as a list, in index order.
def to_list(a: Array<U32>) -> Array<U32> & List<&2, U32>:
  to_list.at(Array.size(U32, a))

def one(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

# The positions where xs and ys differ, plus the length difference.
def diff(xs: List<&2, U32>, ys: List<&2, U32>) -> Nat:
  match xs ys:
    case Nil{} Nil{}:
      0n
    case Nil{} h <> t:
      List.length(&2, U32, ys)
    case h <> t Nil{}:
      List.length(&2, U32, xs)
    case x <> xt y <> yt:
      Nat.add(one(U32.is_eq(x, y)), diff(xt, yt))

# h = (h * 2654435761) ^ x over the list, from 0.
def hash.go(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case x <> t:
      hash.go(t, U32.xor((h * 2654435761 : U32), x))

def hash(xs: List<&2, U32>) -> U32:
  hash.go(xs, 0)

# "diff=D hash=H" for got against want.
def verdict(+got: List<&2, U32>, want: List<&2, U32>) -> String:
  "diff=" ++ Nat.show(diff(got, want)) ++ " hash=" ++ U32.show(hash(got))

def cmp.fin(want: List<&2, U32>, r: Array<U32> & List<&2, U32>) -> String:
  (a, +got) = r
  verdict(got, want)

# "diff=D hash=H" for the array a against want (a is dropped).
def cmp(want: List<&2, U32>, a: Array<U32>) -> String:
  cmp.fin(want, to_list(a))

# xs, then v until the list holds n entries.
def pad(xs: List<&2, U32>, n: Nat, +v: U32) -> List<&2, U32>:
  match xs n:
    case Nil{} 0n:
      Nil{}
    case Nil{} 1n+p:
      v <> pad(Nil{}, p, v)
    case h <> t 0n:
      h <> t
    case h <> t 1n+p:
      h <> pad(t, p, v)

def width.bits(big: Bool, +k: U32) -> Nat:
  match big:
    case False{}:
      0n
    case True{}:
      1n+U32.log2((k - 1 : U32))

# 2^ceil(log2 K) with K = max(k, 1), as a Nat.
def width(+k: U32) -> Nat:
  U32.to_nat(U32.shln(1, width.bits(U32.is_lt(1, k), k)))

def cmpk.fin(want: List<&2, U32>, r: Array<U32> & List<&2, U32>) -> Array<U32> & String:
  (a, +got) = r
  (a, verdict(got, want))

# As cmp, but hands the array back.
def cmpk(want: List<&2, U32>, a: Array<U32>) -> Array<U32> & String:
  cmpk.fin(want, to_list(a))
