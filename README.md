# bend-parallel

Parallel prefix sums, histograms and a stable counting sort over flat
`Array<U32>`s, for Bend 2. The same code runs on the CPU threads and, when
called under `!`, on the GPU.

This is a community package. It is not part of Bend and is not maintained
by the Bend authors. BendHub name: `bend-parallel` (not yet published).

- `scan.bend`: exclusive and inclusive prefix sums, in place, with the total.
- `histogram.bend`: counts of U32 keys in K buckets.
- `sort.bend`: a stable counting sort by key that returns the permutation,
  per-bucket counts and bucket offsets, plus a parallel gather that applies
  the permutation to a payload of any element type.
- `ref.bend`: sequential references over lists. The parallel code is tested
  against them bit for bit, and `LAWS.bend` / `PROOF.bend` prove their laws.

None of it uses atomics. Every parallel pass cuts its array into 2^b
blocks. Each block owns its slots and writes per-block count tables, so
the result is deterministic and is the same for every fork depth `b`,
thread count and lane.

## Import

Once published:

```
import bend-parallel@0.1.0.0/scan.bend as Scan
import bend-parallel@0.1.0.0/histogram.bend as Hist
import bend-parallel@0.1.0.0/sort.bend as Sort
```

For now, from a checkout: `import ./bend-parallel/sort.bend as Sort`.
Versioned `name@version/...` imports need Bend 2.0.27 or later.

## API

`b: Nat` is always the fork depth. The work is cut into 2^b blocks, and `b`
is lowered to log2 of the size when it is larger. `b = 0` is one block on
one lane. Which `b` is fastest depends on the size and the lane;
`bench/run.sh` measures b = 0, 6 and 12 on your machine.

### Scan

```
Scan.exclusive(b: Nat, a: Array<U32>) -> Array<U32> & U32   # a[j] <- a[0] + .. + a[j-1]
Scan.inclusive(b: Nat, a: Array<U32>) -> Array<U32> & U32   # a[j] <- a[0] + .. + a[j]
```

Both run in place and return the array and the total. Sums wrap at 2^32,
as `U32.add` does. See the example below for a complete program.

There are three passes:

1. Each block computes its own sum, in parallel.
2. One lane scans the 2^b block sums.
3. Each block scans itself from its base, in parallel.

### Histogram

```
Hist.count(b: Nat, k: U32, keys: Array<U32>, bufs: Hist.Bufs) -> Array<U32> & Hist.Bufs
Hist.Bufs{counts: Array<U32>, table: Array<U32>}
Hist.Bufs.new() -> Hist.Bufs                    # empty: the first call allocates
Hist.Bufs.sized(b: Nat, k: U32, lg: Nat) -> Hist.Bufs   # sized for 2^lg keys now
```

`k` is the bucket count K. A K of 0 counts as 1. A key at or past K is
counted in bucket K - 1 (clamped), so a bad key can never write out of
bounds. `counts` holds 2^ceil(log2 K) entries: the K counts, then zeros.
The keys come back unchanged.

There are two passes:

1. Each block counts its keys into its own row of the table (2^b rows of
   2^ceil(log2 K) counts).
2. Each group of buckets sums its columns.

### Sort

```
Sort.by_key(b: Nat, k: U32, keys: Array<U32>, bufs: Sort.Bufs) -> Array<U32> & Sort.Bufs
Sort.Bufs{perm, counts, offs, table: Array<U32>}
Sort.Bufs.new() / Sort.Bufs.sized(b, k, lg)
Sort.gather(~T: Data, b: Nat, perm: Array<U32>, src: Array<T>, dst: Array<T>) -> Sort.Moved<T>
Sort.Moved{perm: Array<U32>, src: Array<T>, dst: Array<T>}
```

`by_key` is a stable counting sort into K buckets, with keys clamped as in
the histogram:

- `perm[j]` is the input index of the key that lands at slot j. Keys of
  one bucket keep their input order.
- `counts[c]` is bucket c's size, and `offs[c]` is its first slot. Past K,
  counts are 0 and offs are n.

The keys come back unchanged. To move keys or payloads into sorted order,
gather them: `dst[j] <- src[perm[j]]`. `dst` is reused when it has perm's
size and is replaced otherwise.

`gather` is a template. The call names the element type (`~U32`, `~F32`,
a `Data` type of yours), because the compiler needs a closed element type
for an Array.

### Buffers

`Bufs` carries the tables from call to call. A call keeps a buffer that is
big enough and allocates a new one otherwise. `Array.new` fills memory on
one lane, and under `!` that fill runs on the GPU. So size the buffers once
with `Bufs.sized` outside the `!` and hand the same `Bufs` back each call
(see `tests/sort_bufs.bend`).

## Example

With `./bend-parallel/...` imports in place of the versioned ones (until
the package is published), this program checks on both compilers. Built
with 2.0.27, it prints 9 (the total), 2 (the keys in bucket 3) and 1 (the
smallest key).

```
import Base
import bend-parallel@0.1.0.0/scan.bend as Scan
import bend-parallel@0.1.0.0/histogram.bend as Hist
import bend-parallel@0.1.0.0/sort.bend as Sort

# Four keys: 3, 1, 3, 2 (a is re-bound by each write).
def keys() -> Array<U32>:
  a = [0 : U32^2n]
  a[0] <- 3
  a[1] <- 1
  a[2] <- 3
  a[3] <- 2

# A call returns a pair or a record: a def's parameter takes it apart
# (a match or a let may not take apart a call's result directly).
def total(r: Array<U32> & U32) -> U32:
  (a, +t) = r
  t

def val(r: Array<U32> & U32) -> U32:
  (a, +x) = r
  x

def count3(r: Array<U32> & Hist.Bufs) -> U32:
  (keys, bufs) = r
  Hist.Bufs{counts, table} = bufs
  val(counts[3])

def first(m: Sort.Moved<U32>) -> U32:
  Sort.Moved{perm, src, dst} = m
  val(dst[0])

def sort.gather(+b: Nat, r: Array<U32> & Sort.Bufs) -> Sort.Moved<U32>:
  (keys, bufs) = r
  Sort.Bufs{perm, counts, offs, table} = bufs
  Sort.gather(~U32, b, perm, keys, [0 : U32^2n])

# The keys in sorted order: sort, then gather.
def sort(+b: Nat, +k: U32, keys: Array<U32>) -> Sort.Moved<U32>:
  sort.gather(b, Sort.by_key(b, k, keys, Sort.Bufs.new()))

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- IO.print(U32.show(total(Scan.exclusive!(8n, keys()))))
    Unit <- IO.print(U32.show(count3(Hist.count!(8n, 4, keys(), Hist.Bufs.new()))))
    IO.print(U32.show(first(sort!(8n, 4, keys()))))
```

Each call returns a pair or a record. A def's parameter takes it apart,
because a `match` or a destructuring let may not take apart a call's result
directly (the checker asks for "its own def"). Arrays are built by writes,
since there is no array literal.

## Calling under `!`

A call runs its forks on the CPU threads. Marked with `!`, the call runs
them on the GPU when the program is built with a GPU lane:

- Mark one call directly: `Scan.exclusive!(b, a)`.
- Or mark a def of your own once: `pipe!(b, d, k, keys)` in
  `tests/pipeline.bend` sorts, gathers and scans under a single bang.

Without a GPU lane, the `!` forks run on the CPU threads. The results are
the same bits either way.

## Unsafe code

No def in this package is `@unsafe` itself. The lanes of a pass share one
array through Base's `Array.fork` and `Array.join`, which are `@unsafe`:

- `Array.fork` hands out two O(1) handles to the same memory, and
  `Array.join` merges them back.
- Every pass writes disjoint slots from each handle, so no two lanes write
  the same slot.
- The fork trees recurse on their depth, which the checker verifies.

Two consequences:

- `bend` prints a verdict listing every def that relies on unsafe or
  foreign code, transitively. Your own callers of these functions will show
  up in that list. This is expected.
- The theory cannot see shared memory. In Bend's theory, `Array.fork(a)` is
  `(a, a)` and `Array.join(a, b)` is `a`, so the checker's evaluation drops
  the writes made through the second handle. Never evaluate these functions
  in the checker, for example from a `main` that returns a value. Call them
  from an `IO` main, which runs compiled. The tests all do.

Because the checker cannot relate the parallel code to its laws, the
parallel code is tied to the proven references by tests instead (next
section).

## Laws and proofs

`LAWS.bend` states the laws of the sequential references in `ref.bend`.
`PROOF.bend` proves every one of them. It prints `All terms check.` on
Bend 2.0.27 and on 2.0.24.

- Scan:
  - `exclusive_total` and `inclusive_total`: the total is the sum.
  - `exclusive_prefix`: entry i is the sum of the entries before it.
  - `inclusive_prefix`: entry i is the sum of the entries through it.
  - `exclusive_length` and `inclusive_length`: a scan keeps the length.
- Histogram:
  - `histogram_total`: the counts add up to the number of keys (as a U32).
    This is proven over U32's bit-level definition.
- Sort, over the (key, input index) items that `perm` reads:
  - `sort_count`: every item appears as often in the output as in the
    input, for any equality, so the output is a permutation.
  - `sort_sorted`: the output ascends by bucket. This rests on the clamp:
    a key's bucket is at most K - 1.
  - `sort_stable`: bucket c of the output is bucket c of the input, in
    order.

Tested only, not proven:

- The parallel code equals the references bit for bit.
- The histogram has exactly K entries.

## Tests

```
BEND="bend" ./run_tests.sh                        # check, proof, js, c1, c16
BEND_HIP="..." ./run_tests.sh -l check24,proof24,gpu
```

Each `tests/*.bend` ends in `#|` lines holding its expected output. Those
lines come from `tests/lib/expect.py`, an independent Python model of the
three primitives that shares the xorshift input generator. Every test also
compares the parallel result with `ref.bend`.

The tests cover:

- n = 1, all keys equal, K = 1, K = n (4096), random keys and the largest
  U32 keys;
- fork depths from 0 to far past log2 n;
- `Bufs` reuse across growing and shrinking sizes;
- a gather of an F32 payload;
- a three-primitive pipeline under one `!`.

The lanes are:

| lane             | what                                                                           |
| ---------------- | ------------------------------------------------------------------------------ |
| check            | `bend t.bend --check-only` (upstream 2.0.27)                                   |
| proof            | `bend PROOF.bend` prints `All terms check.`                                    |
| js               | the JS build under bun (sequential)                                            |
| c1, c16          | the native build on 1 and 16 threads                                           |
| check24, proof24 | the same checks with a 2.0.24-based compiler                                   |
| gpu              | the HIP build (a 2.0.24-based fork with a HIP lane): every `!` call on the GPU |

All 9 tests pass on every lane. The GPU runs covered 4 to 100 device turns
per test, one per `!` call.

The JS lane is sequential, and the list references recurse deeply.
`run_tests.sh` raises bun's stack (`BUN_JSC_maxPerThreadStackUsage`), and
even then the largest JS-checked list is 2^14 entries.

## Benchmark

```
BEND="bend" CC=clang bench/run.sh                 # c1 and c16, 3 rounds
BEND_HIP="..." bench/run.sh -l c1,c16,gpu -r 3
```

There is one driver per primitive:

- `bench/scan.bend`, `bench/histogram.bend` and `bench/sort.bend` run
  2^10 to 2^22 keys at b = 0, 6 and 12;
- each call is under `!`, and small sizes repeat the call so that a run
  lasts milliseconds;
- the ref.bend list version runs at the small sizes.

`run.sh` runs the lanes in interleaved rounds and prints the median ms per
call, with a check hash that must agree across lanes. It only prints and
records nothing. The numbers are rough, since `IO.now` has millisecond
resolution. They mean something only in a quiet window: nothing else
heavy on the CPU, and nothing else on the GPU for the GPU lane.

No numbers are published here yet, because none were taken in a quiet
window. Expect the parallel versions to lose to `b = 0` on small inputs,
where fork, join and GPU turn overheads dominate. Unrecorded smoke runs
on the CPU lanes showed this at 2^10 to 2^14 keys.

## Sizes that are not a power of two

Bend arrays are power-of-two blocks, so n is always 2^d. To handle another
length, pad it up to the next power of two:

- scan: pad with 0. The sums and the total are unchanged.
- histogram and sort: pad with K - 1, or any key at or past K. The padding
  lands in the last bucket, so subtract the pad count from `counts[K-1]`.
  In the sort, the padding comes last: stable, and last in bucket K - 1.
  Drop the tail of `perm`.

## Limitations

- Keys are U32 and the only payload path is `gather`. There is no
  key/value sort in one pass, and no radix sort over keys wider than
  log2 K bits (run `by_key` per digit with `gather` for that).
- Memory:
  - the table is 2^(b + ceil(log2 K)) words, so a large K times a large b
    grows fast;
  - K is rounded up to a power of two for the counts.
- Pass 2 of the scan runs on one lane over 2^b block sums.
- The references in `ref.bend` are specs, not fast code. The sort and
  histogram references are O(n * K).
- Allocation under `!` fills on one lane (see Buffers).
- The package targets Bend 2.0.27 and also checks and runs on 2.0.24. The
  code uses no syntax that differs between the two. Things that 2.0.27 has
  and this package avoids:
  - `def f?()` as sugar for `@unsafe`;
  - versioned `name@version/` imports;
  - the stricter rule against dots in module file names.

## License

TODO: not chosen yet. There is no LICENSE file. Note that Bend 2.0.27's
guide says a package published without a LICENSE is treated as MIT-0, so
choose one before publishing.
