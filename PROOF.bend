# bend-parallel -- the proofs of LAWS.bend.
#
# Scan: inductions on the list, where cons1 moves the head out of the
# pair. Histogram: U32 addition is proven to step like Nat addition (bit by
# bit, over Word(32n)), then one bump adds one to the sum.
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
