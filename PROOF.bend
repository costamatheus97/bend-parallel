# bend-parallel -- the proofs of LAWS.bend.
#
# Scan: inductions on the list, where cons1 moves the head out of the
# pair. Histogram: U32 addition is proven to step like Nat addition (bit by
# bit, over Word(32n)), then one bump adds one to the sum. Sort: counts
# split over each peeled bucket and the rest; the order rests on the bucket
# bound (a clamped key's bucket is at most K - 1); stability on bucket c of
# a peel being bucket c of its input.
import Base
import ./ref.bend as Ref
import ./LAWS.bend as Laws

# Pairs
# -----

def total_cons1(+s: U32, r: List<&2, U32> & U32) -> {Ref.total(r) == Ref.total(Ref.cons1(s, r)) : U32}:
  match r:
    case (ys, t):
      {==}

def items_cons1(+s: U32, r: List<&2, U32> & U32) -> {s <> Ref.items(r) == Ref.items(Ref.cons1(s, r)) : List<&2, U32>}:
  match r:
    case (ys, t):
      {==}

# Scan
# ----

def take_zero(xs: List<&2, U32>) -> {Nil{} == Ref.take(xs, 0n) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def Laws.exclusive_total(xs, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %total_cons1(s, Ref.exclusive_from(t, (s + h : U32))) : {_ == Ref.sum_from(t, (s + h : U32)) : U32}
      Laws.exclusive_total(t, (s + h : U32))

def Laws.exclusive_prefix(xs, s, i):
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case +h <> +t 0n:
      %items_cons1(s, Ref.exclusive_from(t, (s + h : U32))) : {Ref.at(_, 0n, Ref.sum_from(t, (s + h : U32))) == s : U32}
      {==}
    case +h <> +t 1n+j:
      %items_cons1(s, Ref.exclusive_from(t, (s + h : U32))) : {Ref.at(_, 1n+j, Ref.sum_from(t, (s + h : U32))) == Ref.sum_from(Ref.take(t, j), (s + h : U32)) : U32}
      Laws.exclusive_prefix(t, (s + h : U32), j)

def Laws.inclusive_total(xs, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %total_cons1((s + h : U32), Ref.inclusive_from(t, (s + h : U32))) : {_ == Ref.sum_from(t, (s + h : U32)) : U32}
      Laws.inclusive_total(t, (s + h : U32))

def Laws.inclusive_prefix(xs, s, i):
  match xs i:
    case Nil{} _:
      {==}
    case +h <> +t 0n:
      %items_cons1((s + h : U32), Ref.inclusive_from(t, (s + h : U32))) : {Ref.at(_, 0n, Ref.sum_from(t, (s + h : U32))) == Ref.sum_from(Ref.take(t, 0n), (s + h : U32)) : U32}
      %take_zero(t) : {(s + h : U32) == Ref.sum_from(_, (s + h : U32)) : U32}
      {==}
    case +h <> +t 1n+j:
      %items_cons1((s + h : U32), Ref.inclusive_from(t, (s + h : U32))) : {Ref.at(_, 1n+j, Ref.sum_from(t, (s + h : U32))) == Ref.sum_from(Ref.take(t, 1n+j), (s + h : U32)) : U32}
      Laws.inclusive_prefix(t, (s + h : U32), j)

def Laws.exclusive_length(xs, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %items_cons1(s, Ref.exclusive_from(t, (s + h : U32))) : {List.length(&2, U32, _) == 1n+List.length(&2, U32, t) : Nat}
      %Laws.exclusive_length(t, (s + h : U32)) : {1n+List.length(&2, U32, Ref.items(Ref.exclusive_from(t, (s + h : U32)))) == 1n+_ : Nat}
      {==}

def Laws.inclusive_length(xs, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %items_cons1((s + h : U32), Ref.inclusive_from(t, (s + h : U32))) : {List.length(&2, U32, _) == 1n+List.length(&2, U32, t) : Nat}
      %Laws.inclusive_length(t, (s + h : U32)) : {1n+List.length(&2, U32, Ref.items(Ref.inclusive_from(t, (s + h : U32)))) == 1n+_ : Nat}
      {==}

# U32 addition, bit by bit
# ------------------------

# Carrying one into an add is adding one to the sum.
def adc_carry(+n: Nat, +a: Word(n), +b: Word(n))
  -> {Word.adc(n, a, b, False{}, True{}) == Word.inc(n, Word.adc(n, a, b, False{}, False{})) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          %adc_carry(p, at, bt) : {WCon{False{}, Word.adc(p, at, bt, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt}:
          %adc_carry(p, at, bt) : {WCon{False{}, Word.adc(p, at, bt, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt}:
          {==}

# Adding one to an operand adds one to the sum.
def adc_inc(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool)
  -> {Word.adc(n, Word.inc(n, a), b, False{}, c) == Word.inc(n, Word.adc(n, a, b, False{}, c)) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          %adc_carry(p, at, bt) : {WCon{False{}, Word.adc(p, at, bt, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          %adc_carry(p, at, bt) : {WCon{False{}, Word.adc(p, at, bt, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          %adc_inc(p, at, bt, False{}) : {WCon{False{}, Word.adc(p, Word.inc(p, at), bt, False{}, False{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          %Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_carry(p, at, bt)) : {WCon{True{}, Word.adc(p, Word.inc(p, at), bt, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          %adc_inc(p, at, bt, False{}) : {WCon{True{}, Word.adc(p, Word.inc(p, at), bt, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          %Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_carry(p, at, bt)) : {WCon{True{}, Word.adc(p, Word.inc(p, at), bt, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          %adc_inc(p, at, bt, False{}) : {WCon{True{}, Word.adc(p, Word.inc(p, at), bt, False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          %adc_inc(p, at, bt, True{}) : {WCon{False{}, Word.adc(p, Word.inc(p, at), bt, False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}

# Adding zero changes nothing.
def adc_zero(+n: Nat, +a: Word(n)) -> {a == Word.adc(n, a, Word.zero(n), False{}, False{}) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, +at}:
          %adc_zero(p, at) : {WCon{False{}, at} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at}:
          %adc_zero(p, at) : {WCon{True{}, at} == WCon{True{}, _} : Word(1n+p)}
          {==}

def add_inc_l(+a: U32, +b: U32) -> {U32.add(U32.inc(a), b) == U32.inc(U32.add(a, b)) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %adc_inc(32n, x, y, False{}) : {U32{Word.adc(32n, Word.inc(32n, x), y, False{}, False{})} == U32{_} : U32}
      {==}

def add_inc_r(+a: U32, +b: U32) -> {U32.add(a, U32.inc(b)) == U32.inc(U32.add(a, b)) : U32}:
  %U32.add_comm(b, a) : {U32.add(a, U32.inc(b)) == U32.inc(_) : U32}
  %add_inc_l(b, a) : {U32.add(a, U32.inc(b)) == _ : U32}
  U32.add_comm(a, U32.inc(b))

def add_zero(+a: U32) -> {a == U32.add(a, 0) : U32}:
  match a:
    case U32{+x}:
      %adc_zero(32n, x) : {U32{x} == U32{_} : U32}
      {==}

# Histogram
# ---------

# A sum from s + 1 is one more than the sum from s.
def sum_from_inc(xs: List<&2, U32>, +s: U32) -> {Ref.sum_from(xs, U32.inc(s)) == U32.inc(Ref.sum_from(xs, s)) : U32}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(U32, U32.add(U32.inc(s), h), U32.inc(U32.add(s, h)), add_inc_l(s, h)) : {Ref.sum_from(t, _) == U32.inc(Ref.sum_from(t, U32.add(s, h))) : U32}
      sum_from_inc(t, U32.add(s, h))

# Zeros add nothing.
def zeros_sum(n: Nat, +s: U32) -> {Ref.sum_from(Ref.zeros(n), s) == s : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(s) : {Ref.sum_from(Ref.zeros(p), _) == s : U32}
      zeros_sum(p, s)

# One bump adds one to the sum, wherever it lands.
def bump_sum(cs: List<&2, U32>, i: Nat, +s: U32) -> {Ref.sum_from(Ref.bump(cs, i), s) == U32.inc(Ref.sum_from(cs, s)) : U32}:
  match cs i:
    case Nil{} _:
      %Equal.sym(U32, U32.add(s, U32.inc(0)), U32.inc(U32.add(s, 0)), add_inc_r(s, 0)) : {_ == U32.inc(s) : U32}
      %add_zero(s) : {U32.inc(_) == U32.inc(s) : U32}
      {==}
    case +h <> +t 0n:
      %Equal.sym(U32, U32.add(s, U32.inc(h)), U32.inc(U32.add(s, h)), add_inc_r(s, h)) : {Ref.sum_from(t, _) == U32.inc(Ref.sum_from(t, U32.add(s, h))) : U32}
      sum_from_inc(t, U32.add(s, h))
    case +h <> +t 1n+j:
      bump_sum(t, j, U32.add(s, h))

# Counting xs into cs adds the number of keys to cs's sum.
def hist_sum(xs: List<&2, U32>, +k: U32, +cs: List<&2, U32>, +s: U32)
  -> {Ref.sum_from(Ref.hist_from(xs, k, cs), s)
    == U32.add(Ref.sum_from(cs, s), U32.from_nat(List.length(&2, U32, xs))) : U32}:
  match xs:
    case Nil{}:
      add_zero(Ref.sum_from(cs, s))
    case +h <> +t:
      +c = Ref.sum_from(cs, s)
      +m = U32.from_nat(List.length(&2, U32, t))
      +b = Ref.bump(cs, Ref.bucket(k, h))
      %Equal.sym(U32, U32.add(c, U32.inc(m)), U32.inc(U32.add(c, m)), add_inc_r(c, m)) : {Ref.sum_from(Ref.hist_from(t, k, b), s) == _ : U32}
      %add_inc_l(c, m) : {Ref.sum_from(Ref.hist_from(t, k, b), s) == _ : U32}
      %bump_sum(cs, Ref.bucket(k, h), s) : {Ref.sum_from(Ref.hist_from(t, k, b), s) == U32.add(_, m) : U32}
      hist_sum(t, k, b, s)

def Laws.histogram_total(k, xs):
  +z = Ref.zeros(Ref.buckets(k))
  +f = U32.from_nat(List.length(&2, U32, xs))
  +l = Ref.sum_from(Ref.hist_from(xs, k, z), 0)
  %Equal.sym(U32, f, U32.add(f, 0), add_zero(f)) : {l == _ : U32}
  %U32.add_comm(0, f) : {l == _ : U32}
  %zeros_sum(Ref.buckets(k), 0) : {l == U32.add(_, f) : U32}
  hist_sum(xs, k, z, 0)

# Nat
# ---

def nat_add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nat_add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def nat_add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nat_add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# Sort: counts
# ------------

def bump1_add_l(e: Bool, +a: Nat, +b: Nat) -> {Ref.bump1(e, Nat.add(a, b)) == Nat.add(Ref.bump1(e, a), b) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def bump1_add_r(e: Bool, +a: Nat, +b: Nat) -> {Ref.bump1(e, Nat.add(a, b)) == Nat.add(a, Ref.bump1(e, b)) : Nat}:
  match e:
    case True{}:
      nat_add_succ(a, b)
    case False{}:
      {==}

def count_append(~eq: Ref.Item -> Ref.Item -> Bool, +y: Ref.Item, xs: List<&2, Ref.Item>, +ys: List<&2, Ref.Item>)
  -> {Ref.count(~eq, y, List.append(&2, Ref.Item, xs, ys)) == Nat.add(Ref.count(~eq, y, xs), Ref.count(~eq, y, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +e = eq(y, h)
      %bump1_add_l(e, Ref.count(~eq, y, t), Ref.count(~eq, y, ys)) : {Ref.bump1(e, Ref.count(~eq, y, List.append(&2, Ref.Item, t, ys))) == _ : Nat}
      %count_append(~eq, y, t, ys) : {Ref.bump1(e, Ref.count(~eq, y, List.append(&2, Ref.Item, t, ys))) == Ref.bump1(e, _) : Nat}
      {==}

# One item, kept on one side of the split and dropped on the other.
def split_one(~eq: Ref.Item -> Ref.Item -> Bool, +y: Ref.Item, +h: Ref.Item, +a: List<&2, Ref.Item>, +b: List<&2, Ref.Item>, s: Bool)
  -> {Nat.add(Ref.count(~eq, y, Ref.keep(h, a, s)), Ref.count(~eq, y, Ref.keep(h, b, Bool.not(s))))
    == Ref.bump1(eq(y, h), Nat.add(Ref.count(~eq, y, a), Ref.count(~eq, y, b))) : Nat}:
  match s:
    case True{}:
      +e = eq(y, h)
      %bump1_add_l(e, Ref.count(~eq, y, a), Ref.count(~eq, y, b)) : {_ == Ref.bump1(e, Nat.add(Ref.count(~eq, y, a), Ref.count(~eq, y, b))) : Nat}
      {==}
    case False{}:
      +e = eq(y, h)
      %bump1_add_r(e, Ref.count(~eq, y, a), Ref.count(~eq, y, b)) : {_ == Ref.bump1(e, Nat.add(Ref.count(~eq, y, a), Ref.count(~eq, y, b))) : Nat}
      {==}

# Splitting into bucket c and the rest keeps every count.
def partition(~eq: Ref.Item -> Ref.Item -> Bool, +y: Ref.Item, xs: List<&2, Ref.Item>, +k: U32, +c: Nat)
  -> {Nat.add(Ref.count(~eq, y, Ref.eqs(xs, k, c)), Ref.count(~eq, y, Ref.nes(xs, k, c))) == Ref.count(~eq, y, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +s = Nat.is_eq(Ref.rank(k, h), c)
      +l = Nat.add(Ref.count(~eq, y, Ref.keep(h, Ref.eqs(t, k, c), s)), Ref.count(~eq, y, Ref.keep(h, Ref.nes(t, k, c), Bool.not(s))))
      %partition(~eq, y, t, k, c) : {l == Ref.bump1(eq(y, h), _) : Nat}
      split_one(~eq, y, h, Ref.eqs(t, k, c), Ref.nes(t, k, c), s)

def peel_count(~eq: Ref.Item -> Ref.Item -> Bool, +y: Ref.Item, +f: Nat, +xs: List<&2, Ref.Item>, +k: U32, +c: Nat)
  -> {Ref.count(~eq, y, Ref.peel(f, xs, k, c)) == Ref.count(~eq, y, xs) : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      +e = Ref.eqs(xs, k, c)
      +n = Ref.nes(xs, k, c)
      +l = Ref.count(~eq, y, List.append(&2, Ref.Item, e, Ref.peel(g, n, k, 1n+c)))
      %partition(~eq, y, xs, k, c) : {l == _ : Nat}
      %peel_count(~eq, y, g, n, k, 1n+c) : {l == Nat.add(Ref.count(~eq, y, e), _) : Nat}
      count_append(~eq, y, e, Ref.peel(g, n, k, 1n+c))

def Laws.sort_count(eq, y, k, xs):
  peel_count(~eq, y, Nat.sub(Ref.buckets(k), 1n), xs, k, 0n)

# Sort: order
# -----------
# The bucket bound (a clamped key's bucket is at most K - 1) makes what
# peel leaves after the last bucket one bucket, so the whole output
# ascends. Rng(k, lo, hi, xs): every item's bucket is in lo .. hi.

# A type picked by a Bool: a rewrite through it refutes True{} == False{}.
def BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def le_zero(n: Nat) -> {True{} == Nat.is_le(0n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_refl(n: Nat) -> {True{} == Nat.is_le(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_succ(n: Nat) -> {True{} == Nat.is_le(n, 1n+n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_succ(p)

def le_trans(a: Nat, b: Nat, c: Nat, ab: {True{} == Nat.is_le(a, b) : Bool}, bc: {True{} == Nat.is_le(b, c) : Bool})
  -> {True{} == Nat.is_le(a, c) : Bool}:
  match a b c:
    case 0n _ _:
      le_zero(c)
    case 1n+p 0n _:
      %ab : BD(_, Unit, {True{} == Nat.is_le(1n+p, c) : Bool})
      Unit{}
    case 1n+p 1n+q 0n:
      %bc : BD(_, Unit, {True{} == Nat.is_le(1n+p, 0n) : Bool})
      Unit{}
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

def eq_le_l(r: Nat, c: Nat, e: {True{} == Nat.is_eq(r, c) : Bool}) -> {True{} == Nat.is_le(c, r) : Bool}:
  match r c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %e : BD(_, Unit, {True{} == Nat.is_le(1n+q, 0n) : Bool})
      Unit{}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      eq_le_l(p, q, e)

def eq_le_r(r: Nat, c: Nat, e: {True{} == Nat.is_eq(r, c) : Bool}) -> {True{} == Nat.is_le(r, c) : Bool}:
  match r c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      %e : BD(_, Unit, {True{} == Nat.is_le(1n+p, 0n) : Bool})
      Unit{}
    case 1n+p 1n+q:
      eq_le_r(p, q, e)

# c <= r and r != c: c + 1 <= r.
def le_ne_succ(c: Nat, r: Nat, le: {True{} == Nat.is_le(c, r) : Bool}, ne: {False{} == Nat.is_eq(r, c) : Bool})
  -> {True{} == Nat.is_le(1n+c, r) : Bool}:
  match c r:
    case 0n 0n:
      %ne : BD(_, {True{} == Nat.is_le(1n, 0n) : Bool}, Unit)
      Unit{}
    case 0n 1n+q:
      le_zero(q)
    case 1n+p 0n:
      %le : BD(_, Unit, {True{} == Nat.is_le(2n+p, 0n) : Bool})
      Unit{}
    case 1n+p 1n+q:
      le_ne_succ(p, q, le, ne)

def sub_zero(n: Nat) -> {n == Nat.sub(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# n < m: n + 1 <= m.
def lt_le_succ(n: Nat, m: Nat, lt: {True{} == Nat.is_lt(n, m) : Bool}) -> {True{} == Nat.is_le(1n+n, m) : Bool}:
  match n m:
    case 0n 0n:
      %lt : BD(_, Unit, {True{} == Nat.is_le(1n, 0n) : Bool})
      Unit{}
    case 0n 1n+q:
      le_zero(q)
    case 1n+p 0n:
      %lt : BD(_, Unit, {True{} == Nat.is_le(2n+p, 0n) : Bool})
      Unit{}
    case 1n+p 1n+q:
      lt_le_succ(p, q, lt)

# n < m: n <= m - 1.
def lt_le_pred(n: Nat, +m: Nat, lt: {True{} == Nat.is_lt(n, m) : Bool}) -> {True{} == Nat.is_le(n, Nat.sub(m, 1n)) : Bool}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      le_zero(Nat.sub(q, 0n))
    case 1n+p 0n:
      %lt : BD(_, Unit, {True{} == Nat.is_le(1n+p, 0n) : Bool})
      Unit{}
    case 1n+p 1n+q:
      %sub_zero(q) : {True{} == Nat.is_le(1n+p, _) : Bool}
      lt_le_succ(p, q, lt)

def pick_le(b: Bool, +n: Nat, +m: Nat, e: {b == Nat.is_lt(n, m) : Bool})
  -> {True{} == Nat.is_le(Ref.pick(b, n, Nat.sub(m, 1n)), Nat.sub(m, 1n)) : Bool}:
  match b:
    case True{}:
      lt_le_pred(n, m, e)
    case False{}:
      le_refl(Nat.sub(m, 1n))

# The bucket bound: every item's bucket is at most K - 1.
def rank_le(+k: U32, it: Ref.Item) -> {True{} == Nat.is_le(Ref.rank(k, it), Nat.sub(Ref.buckets(k), 1n)) : Bool}:
  match it:
    case Ref.Item{+key, idx}:
      +n = U32.to_nat(key)
      +m = Ref.buckets(k)
      pick_le(Nat.is_lt(n, m), n, m, {==})

def Rng(+k: U32, +lo: Nat, +hi: Nat, xs: List<&2, Ref.Item>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +h <> t:
      {True{} == Nat.is_le(lo, Ref.rank(k, h)) : Bool} & {True{} == Nat.is_le(Ref.rank(k, h), hi) : Bool} & Rng(k, lo, hi, t)

def rng_cast(+k: U32, +lo: Nat, -a: Nat, -b: Nat, -xs: List<&2, Ref.Item>, e: {a == b : Nat}, r: Rng(k, lo, b, xs)) -> Rng(k, lo, a, xs):
  %Equal.sym(Nat, a, b, e) : Rng(k, lo, _, xs)
  r

def rng_all(+k: U32, xs: List<&2, Ref.Item>) -> Rng(k, 0n, Nat.sub(Ref.buckets(k), 1n), xs):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> t:
      (le_zero(Ref.rank(k, h)), rank_le(k, h), rng_all(k, t))

def eqs_one(b: Bool, +h: Ref.Item, +k: U32, +c: Nat, -a: List<&2, Ref.Item>, e: {b == Nat.is_eq(Ref.rank(k, h), c) : Bool},
  e2: {b == Nat.is_eq(Ref.rank(k, h), c) : Bool}, r: Rng(k, c, c, a)) -> Rng(k, c, c, Ref.keep(h, a, b)):
  match b:
    case True{}:
      (eq_le_l(Ref.rank(k, h), c, e), eq_le_r(Ref.rank(k, h), c, e2), r)
    case False{}:
      r

# Bucket c's items are all in bucket c.
def eqs_rng(xs: List<&2, Ref.Item>, +k: U32, +c: Nat) -> Rng(k, c, c, Ref.eqs(xs, k, c)):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      eqs_one(Nat.is_eq(Ref.rank(k, h), c), h, k, c, Ref.eqs(t, k, c), {==}, {==}, eqs_rng(t, k, c))

def nes_one(b: Bool, +h: Ref.Item, +k: U32, +c: Nat, +hi: Nat, -a: List<&2, Ref.Item>, e: {b == Nat.is_eq(Ref.rank(k, h), c) : Bool},
  l: {True{} == Nat.is_le(c, Ref.rank(k, h)) : Bool}, u: {True{} == Nat.is_le(Ref.rank(k, h), hi) : Bool}, r: Rng(k, 1n+c, hi, a))
  -> Rng(k, 1n+c, hi, Ref.keep(h, a, Bool.not(b))):
  match b:
    case True{}:
      r
    case False{}:
      (le_ne_succ(c, Ref.rank(k, h), l, e), u, r)

# The items past bucket c are past it.
def nes_rng(xs: List<&2, Ref.Item>, +k: U32, +c: Nat, +hi: Nat, r: Rng(k, c, hi, xs)) -> Rng(k, 1n+c, hi, Ref.nes(xs, k, c)):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (l, u, rt) = r
      nes_one(Nat.is_eq(Ref.rank(k, h), c), h, k, c, hi, Ref.nes(t, k, c), {==}, l, u, nes_rng(t, k, c, hi, rt))

def from_weaken(xs: List<&2, Ref.Item>, +k: U32, +lo: Nat, +c: Nat, l: {True{} == Nat.is_le(lo, c) : Bool}, r: Ref.from(k, c, xs))
  -> Ref.from(k, lo, xs):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> t:
      (a, b) = r
      (le_trans(lo, c, Ref.rank(k, h), l, a), b)

# One bucket's items, all of them c, then items that ascend from c.
def from_append(xs: List<&2, Ref.Item>, +ys: List<&2, Ref.Item>, +k: U32, +lo: Nat, +c: Nat, r: Rng(k, c, c, xs),
  l: {True{} == Nat.is_le(lo, c) : Bool}, f: Ref.from(k, c, ys)) -> Ref.from(k, lo, List.append(&2, Ref.Item, xs, ys)):
  match xs:
    case Nil{}:
      from_weaken(ys, k, lo, c, l, f)
    case +h <> +t:
      (a, u, rt) = r
      (le_trans(lo, c, Ref.rank(k, h), l, a), from_append(t, ys, k, Ref.rank(k, h), c, rt, u, f))

# Items all in bucket c ascend.
def rng_from(xs: List<&2, Ref.Item>, +k: U32, +c: Nat, +lo: Nat, r: Rng(k, c, c, xs), l: {True{} == Nat.is_le(lo, c) : Bool})
  -> Ref.from(k, lo, xs):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (a, u, rt) = r
      (le_trans(lo, c, Ref.rank(k, h), l, a), rng_from(t, k, c, Ref.rank(k, h), rt, u))

# Peeling items in buckets c .. c + f ascends from c.
def peel_from(+f: Nat, +xs: List<&2, Ref.Item>, +k: U32, +c: Nat, +lo: Nat, r: Rng(k, c, Nat.add(c, f), xs), l: {True{} == Nat.is_le(lo, c) : Bool})
  -> Ref.from(k, lo, Ref.peel(f, xs, k, c)):
  match f:
    case 0n:
      rng_from(xs, k, c, lo, rng_cast(k, c, c, Nat.add(c, 0n), xs, nat_add_zero(c), r), l)
    case 1n+g:
      +n = Ref.nes(xs, k, c)
      from_append(Ref.eqs(xs, k, c), Ref.peel(g, n, k, 1n+c), k, lo, c, eqs_rng(xs, k, c), l,
        peel_from(g, n, k, 1n+c, c, rng_cast(k, 1n+c, 1n+Nat.add(c, g), Nat.add(c, 1n+g), n, nat_add_succ(c, g),
          nes_rng(xs, k, c, Nat.add(c, 1n+g), r)), le_succ(c)))

def from_sorted(xs: List<&2, Ref.Item>, +k: U32, +lo: Nat, r: Ref.from(k, lo, xs)) -> Ref.Sorted(k, xs):
  match xs:
    case Nil{}:
      Unit{}
    case +h <> t:
      (a, b) = r
      b

def Laws.sort_sorted(k, xs):
  from_sorted(Ref.sort_items(k, xs), k, 0n,
    peel_from(Nat.sub(Ref.buckets(k), 1n), xs, k, 0n, 0n, rng_all(k, xs), {==}))

# Sort: stability
# ---------------
# Bucket c of a peel is bucket c of its input: the bucket peeled first
# holds bucket c only when it is c, and the rest holds the rest of c.

def keep_append(+h: Ref.Item, x: List<&2, Ref.Item>, y: List<&2, Ref.Item>, s: Bool)
  -> {Ref.keep(h, List.append(&2, Ref.Item, x, y), s) == List.append(&2, Ref.Item, Ref.keep(h, x, s), y) : List<&2, Ref.Item>}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

def eqs_append(xs: List<&2, Ref.Item>, +ys: List<&2, Ref.Item>, +k: U32, +c: Nat)
  -> {Ref.eqs(List.append(&2, Ref.Item, xs, ys), k, c) == List.append(&2, Ref.Item, Ref.eqs(xs, k, c), Ref.eqs(ys, k, c)) : List<&2, Ref.Item>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +s = Nat.is_eq(Ref.rank(k, h), c)
      +l = Ref.keep(h, Ref.eqs(List.append(&2, Ref.Item, t, ys), k, c), s)
      %keep_append(h, Ref.eqs(t, k, c), Ref.eqs(ys, k, c), s) : {l == _ : List<&2, Ref.Item>}
      %eqs_append(t, ys, k, c) : {l == Ref.keep(h, _, s) : List<&2, Ref.Item>}
      {==}

def eq_of_is_eq(a: Nat, b: Nat, e: {True{} == Nat.is_eq(a, b) : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %e : BD(_, Unit, {0n == 1n+q : Nat})
      Unit{}
    case 1n+p 0n:
      %e : BD(_, Unit, {1n+p == 0n : Nat})
      Unit{}
    case 1n+p 1n+q:
      %eq_of_is_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# r is c and not c0: c is not c0.
def ne_of(r: Nat, c: Nat, -c0: Nat, e: {True{} == Nat.is_eq(r, c) : Bool}, e0: {False{} == Nat.is_eq(r, c0) : Bool})
  -> {False{} == Nat.is_eq(c, c0) : Bool}:
  %eq_of_is_eq(r, c, e) : {False{} == Nat.is_eq(_, c0) : Bool}
  e0

def is_eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      is_eq_comm(p, q)

def none_one(s: Bool, +h: Ref.Item, +k: U32, +c0: Nat, +c: Nat, -a: List<&2, Ref.Item>, +ne: {False{} == Nat.is_eq(c, c0) : Bool},
  e: {s == Nat.is_eq(Ref.rank(k, h), c0) : Bool}, r: {Nil{} == Ref.eqs(a, k, c) : List<&2, Ref.Item>})
  -> {Nil{} == Ref.eqs(Ref.keep(h, a, s), k, c) : List<&2, Ref.Item>}:
  match s:
    case True{}:
      %Equal.sym(Nat, Ref.rank(k, h), c0, eq_of_is_eq(Ref.rank(k, h), c0, e)) : {Nil{} == Ref.keep(h, Ref.eqs(a, k, c), Nat.is_eq(_, c)) : List<&2, Ref.Item>}
      %is_eq_comm(c, c0) : {Nil{} == Ref.keep(h, Ref.eqs(a, k, c), _) : List<&2, Ref.Item>}
      %ne : {Nil{} == Ref.keep(h, Ref.eqs(a, k, c), _) : List<&2, Ref.Item>}
      r
    case False{}:
      r

# Bucket c of bucket c0 is empty when c is not c0.
def eqs_eqs_ne(xs: List<&2, Ref.Item>, +k: U32, +c0: Nat, +c: Nat, +ne: {False{} == Nat.is_eq(c, c0) : Bool})
  -> {Nil{} == Ref.eqs(Ref.eqs(xs, k, c0), k, c) : List<&2, Ref.Item>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      none_one(Nat.is_eq(Ref.rank(k, h), c0), h, k, c0, c, Ref.eqs(t, k, c0), ne, {==}, eqs_eqs_ne(t, k, c0, c, ne))

def merge_s(s: Bool, +h: Ref.Item, +t: List<&2, Ref.Item>, +k: U32, +c0: Nat, +c: Nat,
  e0: {False{} == Nat.is_eq(Ref.rank(k, h), c0) : Bool}, e: {s == Nat.is_eq(Ref.rank(k, h), c) : Bool},
  ih: {List.append(&2, Ref.Item, Ref.eqs(Ref.eqs(t, k, c0), k, c), Ref.eqs(Ref.nes(t, k, c0), k, c)) == Ref.eqs(t, k, c) : List<&2, Ref.Item>})
  -> {List.append(&2, Ref.Item, Ref.eqs(Ref.eqs(t, k, c0), k, c), Ref.keep(h, Ref.eqs(Ref.nes(t, k, c0), k, c), s))
    == Ref.keep(h, Ref.eqs(t, k, c), s) : List<&2, Ref.Item>}:
  match s:
    case False{}:
      ih
    case True{}:
      +x = Ref.eqs(Ref.eqs(t, k, c0), k, c)
      +y = Ref.eqs(Ref.nes(t, k, c0), k, c)
      %ih : {List.append(&2, Ref.Item, x, h <> y) == h <> _ : List<&2, Ref.Item>}
      %eqs_eqs_ne(t, k, c0, c, ne_of(Ref.rank(k, h), c, c0, e, e0)) : {List.append(&2, Ref.Item, _, h <> y) == h <> List.append(&2, Ref.Item, _, y) : List<&2, Ref.Item>}
      {==}

def merge_s0(s0: Bool, +h: Ref.Item, +t: List<&2, Ref.Item>, +k: U32, +c0: Nat, +c: Nat,
  e0: {s0 == Nat.is_eq(Ref.rank(k, h), c0) : Bool},
  ih: {List.append(&2, Ref.Item, Ref.eqs(Ref.eqs(t, k, c0), k, c), Ref.eqs(Ref.nes(t, k, c0), k, c)) == Ref.eqs(t, k, c) : List<&2, Ref.Item>})
  -> {List.append(&2, Ref.Item, Ref.eqs(Ref.keep(h, Ref.eqs(t, k, c0), s0), k, c), Ref.eqs(Ref.keep(h, Ref.nes(t, k, c0), Bool.not(s0)), k, c))
    == Ref.keep(h, Ref.eqs(t, k, c), Nat.is_eq(Ref.rank(k, h), c)) : List<&2, Ref.Item>}:
  match s0:
    case True{}:
      +s = Nat.is_eq(Ref.rank(k, h), c)
      +x = Ref.eqs(Ref.eqs(t, k, c0), k, c)
      +y = Ref.eqs(Ref.nes(t, k, c0), k, c)
      %keep_append(h, x, y, s) : {_ == Ref.keep(h, Ref.eqs(t, k, c), s) : List<&2, Ref.Item>}
      %ih : {Ref.keep(h, List.append(&2, Ref.Item, x, y), s) == Ref.keep(h, _, s) : List<&2, Ref.Item>}
      {==}
    case False{}:
      merge_s(Nat.is_eq(Ref.rank(k, h), c), h, t, k, c0, c, e0, {==}, ih)

# Bucket c of bucket c0, then bucket c of the rest, is bucket c.
def merge(xs: List<&2, Ref.Item>, +k: U32, +c0: Nat, +c: Nat)
  -> {List.append(&2, Ref.Item, Ref.eqs(Ref.eqs(xs, k, c0), k, c), Ref.eqs(Ref.nes(xs, k, c0), k, c)) == Ref.eqs(xs, k, c) : List<&2, Ref.Item>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      merge_s0(Nat.is_eq(Ref.rank(k, h), c0), h, t, k, c0, c, {==}, merge(t, k, c0, c))

def peel_stable(+f: Nat, +xs: List<&2, Ref.Item>, +k: U32, +c0: Nat, +c: Nat)
  -> {Ref.eqs(Ref.peel(f, xs, k, c0), k, c) == Ref.eqs(xs, k, c) : List<&2, Ref.Item>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      +e = Ref.eqs(xs, k, c0)
      +n = Ref.nes(xs, k, c0)
      %merge(xs, k, c0, c) : {Ref.eqs(List.append(&2, Ref.Item, e, Ref.peel(g, n, k, 1n+c0)), k, c) == _ : List<&2, Ref.Item>}
      %peel_stable(g, n, k, 1n+c0, c) : {Ref.eqs(List.append(&2, Ref.Item, e, Ref.peel(g, n, k, 1n+c0)), k, c) == List.append(&2, Ref.Item, Ref.eqs(e, k, c), _) : List<&2, Ref.Item>}
      eqs_append(e, Ref.peel(g, n, k, 1n+c0), k, c)

def Laws.sort_stable(k, xs, c):
  peel_stable(Nat.sub(Ref.buckets(k), 1n), xs, k, 0n, c)
