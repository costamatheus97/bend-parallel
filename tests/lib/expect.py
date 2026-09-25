#!/usr/bin/env python3
"""The tests' expected lines, computed without Bend.

    python3 tests/lib/expect.py scan_random     # prints the #| lines

Mirrors tests/lib/check.bend's inputs (xorshift32 streams) and computes
each test's results from plain definitions: prefix sums, counts per
bucket (keys at or past K clamp to K - 1) and a stable counting sort."""
import sys

M = 0xFFFFFFFF


def prng(x):
    x &= M
    a = (x ^ (x << 13)) & M
    b = a ^ (a >> 17)
    return (b ^ (b << 5)) & M


def at(seed, j):
    return prng(prng(((j + 1) * 2654435761 + seed) & M))


def gen(kind, seed, m, j):
    if kind == 0:
        return at(seed, j)
    if kind == 1:
        return at(seed, j) % m if m else at(seed, j)
    return m


def fill(d, kind, seed, m):
    return [gen(kind, seed, m, j) for j in range(1 << d)]


def hsh(xs):
    h = 0
    for x in xs:
        h = ((h * 2654435761) & M) ^ x
    return h


def exclusive(xs):
    out, s = [], 0
    for x in xs:
        out.append(s)
        s = (s + x) & M
    return out, s


def inclusive(xs):
    out, s = [], 0
    for x in xs:
        s = (s + x) & M
        out.append(s)
    return out, s


def bucket(k, x):
    kk = max(k, 1)
    return min(x, kk - 1)


def counts(k, xs):
    kk = max(k, 1)
    cs = [0] * kk
    for x in xs:
        cs[bucket(k, x)] += 1
    return cs


def perm(k, xs):
    # stable: by bucket, then by input index
    return sorted(range(len(xs)), key=lambda j: (bucket(k, xs[j]), j))


def pow2(k):
    kk, p = max(k, 1), 1
    while p < kk:
        p *= 2
    return p


def full_counts(k, xs):
    cs = counts(k, xs)
    return cs + [0] * (pow2(k) - len(cs))


def full_offs(k, xs):
    return exclusive(full_counts(k, xs))[0]


# Per test: the expected lines.

def scan_random():
    out = []
    for name, f in (("ex", exclusive), ("in", inclusive)):
        for d in (0, 1, 2, 5, 8, 11):
            for b in (0, 1, 3, 6, 12):
                seed = (d * 1000 + b) & M
                ys, t = f(fill(d, 0, seed, 0))
                out.append(f"{name} d={d} b={b} diff=0 hash={hsh(ys)} total={t}")
    return out


def sort_random():
    out = []
    for d in (0, 1, 3, 6, 10):
        for b in (0, 2, 5, 11):
            for k in (1, 2, 7, 256, 1000):
                seed = (d * 100 + b * 10 + k) & M
                xs = fill(d, 1, seed, k)
                out.append(f"d={d} b={b} k={k} perm diff=0 hash={hsh(perm(k, xs))}"
                           f" counts diff=0 hash={hsh(full_counts(k, xs))}"
                           f" offs diff=0 hash={hsh(full_offs(k, xs))}")
    return out


def scan_edges():
    cases = [(0, 0, 2, 0, 0), (0, 3, 2, 0, 7), (0, 0, 2, 0, M), (0, 3, 0, 5, 0),
             (10, 4, 2, 0, 1), (10, 0, 2, 0, M), (12, 5, 2, 0, M), (3, 30, 0, 9, 0),
             (14, 8, 0, 16, 0), (12, 12, 0, 17, 0), (14, 13, 0, 18, 0)]
    out = []
    for name, f in (("ex", exclusive), ("in", inclusive)):
        for d, b, kind, seed, m in cases:
            ys, t = f(fill(d, kind, seed, m))
            out.append(f"{name} d={d} b={b} kind={kind} m={m} diff=0 hash={hsh(ys)} total={t}")
    return out


def hist_random():
    out = []
    for d in (0, 2, 7, 12):
        for b in (0, 3, 8, 13):
            for k in (1, 3, 64, 1000):
                seed = (d * 100 + b * 10 + k) & M
                xs = fill(d, 1, seed, k)
                out.append(f"d={d} b={b} k={k} counts diff=0 hash={hsh(full_counts(k, xs))}")
    return out


HIST_EDGES = [(0, 0, 5, 1, 1, 5), (0, 4, 1, 0, 2, 0), (9, 4, 8, 2, 0, 3), (8, 3, 1, 0, 3, 0),
              (8, 2, 256, 1, 4, 256), (8, 8, 256, 1, 5, 256), (6, 2, 16, 2, 0, M),
              (10, 5, 1000, 0, 6, 0), (7, 3, 0, 1, 7, 9), (14, 10, 100, 1, 8, 100),
              (13, 13, 300, 1, 9, 300), (12, 12, 1, 0, 10, 0)]


def hist_edges():
    out = []
    for d, b, k, kind, seed, m in HIST_EDGES:
        xs = fill(d, kind, seed, m)
        out.append(f"d={d} b={b} k={k} kind={kind} m={m} counts diff=0 hash={hsh(full_counts(k, xs))}")
    return out


SORT_EDGES = [(0, 0, 5, 1, 1, 5), (0, 4, 1, 0, 2, 0), (9, 4, 8, 2, 0, 3), (8, 3, 1, 0, 3, 0),
              (8, 2, 256, 1, 4, 256), (8, 8, 256, 1, 5, 256), (12, 6, 4096, 1, 11, 4096),
              (6, 2, 16, 2, 0, M), (10, 5, 1000, 0, 6, 0), (7, 3, 0, 1, 7, 9),
              (12, 12, 1000, 1, 12, 1000), (13, 13, 300, 1, 13, 300), (12, 12, 1, 0, 14, 0)]


def sort_line(d, k, xs):
    return (f"perm diff=0 hash={hsh(perm(k, xs))} counts diff=0 hash={hsh(full_counts(k, xs))}"
            f" offs diff=0 hash={hsh(full_offs(k, xs))}")


def sort_edges():
    out = []
    for d, b, k, kind, seed, m in SORT_EDGES:
        xs = fill(d, kind, seed, m)
        out.append(f"d={d} b={b} k={k} kind={kind} m={m} " + sort_line(d, k, xs))
    return out


def sort_gather():
    out = []
    for d, b, g, k, kind, seed, m in [(0, 0, 0, 3, 1, 1, 3), (10, 4, 4, 50, 1, 2, 50),
                                      (10, 4, 7, 50, 1, 3, 50), (9, 3, 2, 100, 0, 4, 0),
                                      (12, 8, 12, 4096, 1, 5, 4096)]:
        xs = fill(d, kind, seed, m)
        p = perm(k, xs)
        keys = [xs[j] for j in p]
        out.append(f"d={d} b={b} g={g} k={k} kind={kind}")
        out.append(f"keys diff=0 hash={hsh(keys)}")
        out.append(f"floats diff=0 hash={hsh(p)}")
        out.append(f"resized diff=0 hash={hsh(keys)}")
    return out


def sort_bufs():
    cfgs = [(8, 3, 100), (10, 5, 7), (6, 2, 1000), (10, 5, 7), (0, 0, 1)]
    out = []

    def keys(d, k):
        return fill(d, 1, (d * 100 + k) & M, k)

    for head, cs in (("sort from empty", cfgs), ("sort from sized", [(9, 4, 300)] * 2)):
        out.append(head)
        for d, b, k in cs:
            xs = keys(d, k)
            out.append(f"perm diff=0 hash={hsh(perm(k, xs))} counts diff=0 hash={hsh(full_counts(k, xs))}"
                       f" offs diff=0 hash={hsh(full_offs(k, xs))}")
    for head, cs in (("hist from empty", cfgs), ("hist from sized", [(9, 4, 300)])):
        out.append(head)
        for d, b, k in cs:
            out.append(f"counts diff=0 hash={hsh(full_counts(k, keys(d, k)))}")
    return out


def pipeline():
    out = []
    for d, b, k, seed in [(0, 0, 4, 1), (8, 3, 16, 2), (11, 6, 500, 3), (13, 9, 64, 4)]:
        xs = fill(d, 1, seed, k)
        ys, t = inclusive([xs[j] for j in perm(k, xs)])
        out.append(f"d={d} b={b} k={k} diff=0 hash={hsh(ys)} total={t}")
    return out


TESTS = {name: fn for name, fn in globals().items() if callable(fn)
         and name.split("_")[0] in ("scan", "hist", "sort", "pipeline")}

def stamp(path):
    """Replace the #| lines at the end of the test file at path."""
    name = path.rsplit("/", 1)[-1][:-len(".bend")]
    src = open(path).read().rstrip("\n").split("\n")
    while src and src[-1].startswith("#|"):
        src.pop()
    while src and src[-1] == "":
        src.pop()
    lines = src + [""] + ["#|" + line for line in TESTS[name]()]
    open(path, "w").write("\n".join(lines) + "\n")


if __name__ == "__main__":
    if sys.argv[1] == "--write":
        for path in sys.argv[2:]:
            stamp(path)
    else:
        for line in TESTS[sys.argv[1]]():
            print("#|" + line)
