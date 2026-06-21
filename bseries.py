#!/usr/bin/env python3
"""
bseries.py — a B-series / Butcher-group toolkit built on the rooted-tree Hopf algebra.

What it does, in exact rational arithmetic:
  * enumerate rooted trees and their invariants  (order |t|, density gamma, symmetry sigma, alpha);
  * the **admissible-cut coproduct**  Delta(t)  of the Connes-Kreimer / Butcher Hopf algebra;
  * the **antipode**  S(t)  (the inverse method), by the convolution recursion;
  * Runge-Kutta **order conditions**  Phi(t) = 1/gamma(t)  and the leading **error coefficients**;
  * the **modified equation** of a method (backward error analysis) via the convolution logarithm
    log_*, i.e. the Eulerian idempotent.

Why it is more than an order-condition checker: the coproduct and antipode are the very operations
machine-checked in the two companion papers, and `--selftest` re-verifies the formalized theorems
numerically:
  * Delta on small trees matches the textbook values;
  * the antipode axiom  m (S (x) id) Delta = eta . eps  holds  (the Hopf-algebra theorem of paper I);
  * log_*(explicit Euler) gives the classical modified field  f - (h/2) f'f + ...  (paper II's
    Eulerian idempotent log_* in action).

Companion papers (this repository):
  I.  How a Tree Remembers Its Cuts   — DOI 10.5281/zenodo.20762280
  II. How a Tree Forgets Its Order     — DOI 10.5281/zenodo.20774821

Dependency-free (Python 3.9+, standard library only).  Apache-2.0.
"""
from __future__ import annotations
from fractions import Fraction
from functools import lru_cache
from collections import Counter, defaultdict
from itertools import product
import math
import argparse

# ---------------------------------------------------------------------------
# Rooted trees.  A tree is a canonical tuple of child trees; the node • is ().
# A forest is a canonical (sorted) tuple of trees; the empty forest is ().
# (No clash: a tree-• is (), but as a forest element it is wrapped, e.g. ((),).)
# ---------------------------------------------------------------------------
Tree = tuple
Forest = tuple

LEAF: Tree = ()


@lru_cache(maxsize=None)
def order(t: Tree) -> int:
    return 1 + sum(order(c) for c in t)


@lru_cache(maxsize=None)
def gamma(t: Tree) -> int:
    g = order(t)
    for c in t:
        g *= gamma(c)
    return g


@lru_cache(maxsize=None)
def sigma(t: Tree) -> int:
    s = 1
    for sub, m in Counter(t).items():
        s *= math.factorial(m) * sigma(sub) ** m
    return s


def alpha(t: Tree) -> int:
    """Number of monotonic labelings: |t|! / (sigma(t) gamma(t))."""
    return math.factorial(order(t)) // (sigma(t) * gamma(t))


def render(t: Tree) -> str:
    if t == LEAF:
        return "•"
    return "[" + "".join(render(c) for c in t) + "]"


def render_forest(f: Forest) -> str:
    if f == ():
        return "1"
    return "".join(render(t) for t in f)


@lru_cache(maxsize=None)
def trees_of_order(n: int) -> tuple:
    if n == 1:
        return ((),)
    avail = []
    for k in range(1, n):
        avail.extend(trees_of_order(k))
    avail.sort(key=lambda t: (order(t), t))
    seen, res = set(), []
    for children in _child_multisets(tuple(avail), n - 1):
        t = tuple(sorted(children))
        if t not in seen:
            seen.add(t)
            res.append(t)
    return tuple(sorted(res))


def _child_multisets(avail: tuple, target: int):
    def rec(start, remaining):
        if remaining == 0:
            yield ()
            return
        for i in range(start, len(avail)):
            o = order(avail[i])
            if o > remaining:
                break
            for rest in rec(i, remaining - o):
                yield (avail[i],) + rest
    yield from rec(0, target)


def all_trees(max_order: int) -> list[Tree]:
    out = []
    for n in range(1, max_order + 1):
        out.extend(trees_of_order(n))
    return out


# ---------------------------------------------------------------------------
# The admissible-cut coproduct (Connes-Kreimer).  Delta(t) = t(x)1 + sum P^c (x) R^c,
# pruned forest on the left, trunk (root component) on the right; the empty cut gives 1(x)t.
# Returned as a list of (left_forest, right_forest).
# ---------------------------------------------------------------------------
def _label(t: Tree, nxt=[0]):
    """Build a labelled tree: (id, [child labelled trees])."""
    me = nxt[0]
    nxt[0] += 1
    return (me, [_label(c, nxt) for c in t])


def _subtree_to_canon(node) -> Tree:
    _id, ch = node
    return tuple(sorted(_subtree_to_canon(c) for c in ch))


@lru_cache(maxsize=None)
def coproduct(t: Tree) -> tuple:
    """Full coproduct of a tree, as a tuple of (left_forest, right_forest) terms."""
    nxt = [0]
    root = _label(t, nxt)
    nodes = {}

    def index(n):
        nodes[n[0]] = n
        for c in n[1]:
            index(c)
    index(root)
    children = {i: [c[0] for c in n[1]] for i, n in nodes.items()}
    parent = {}
    for i, n in nodes.items():
        for c in n[1]:
            parent[c[0]] = i
    root_id = root[0]

    # trunk S = root-containing, parent-closed subset of node ids -> one admissible cut.
    # ids are assigned in DFS pre-order, so a parent's id is always < its children's:
    # sorted(all_ids) is a topological order, and each node's parent is decided before it.
    all_ids = sorted(nodes)

    def gen_trunks():
        topo = all_ids  # already sorted; topo[0] == root_id

        def rec(idx, S):
            if idx == len(topo):
                yield S
                return
            nid = topo[idx]
            p = parent.get(nid)
            if p in S:                       # parent included -> may include or exclude this node
                yield from rec(idx + 1, S | frozenset({nid}))
                yield from rec(idx + 1, S)
            else:                            # parent excluded -> must exclude
                yield from rec(idx + 1, S)
        return list(rec(1, frozenset({root_id})))

    terms = []
    # explicit t (x) 1
    terms.append(((t,), ()))
    for S in gen_trunks():
        # trunk tree induced on S
        def build(nid, allowed):
            return tuple(sorted(build(c, allowed) for c in children[nid] if c in allowed))
        trunk = build(root_id, S)
        # pruned forest: components hanging off S (nodes whose parent in S but node not in S)
        pruned = []
        for i in all_ids:
            if i not in S and parent.get(i) in S:
                pruned.append(build_sub(i, S, children))
        pruned_forest = tuple(sorted(pruned))
        terms.append((pruned_forest, (trunk,)))
    return tuple(terms)


def build_sub(nid, trunk_set, children):
    """Canonical tree of the component rooted at nid, excluding trunk nodes."""
    return tuple(sorted(build_sub(c, trunk_set, children)
                        for c in children[nid] if c not in trunk_set))


# ---------------------------------------------------------------------------
# The free commutative algebra on trees: an element is a dict {forest: Fraction}.
# ---------------------------------------------------------------------------
def el_zero():
    return {}


def el_add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, Fraction(0)) + v
        if out[k] == 0:
            del out[k]
    return out


def el_scale(a, s):
    s = Fraction(s)
    if s == 0:
        return {}
    return {k: v * s for k, v in a.items()}


def el_mul(a, b):
    out = {}
    for fa, va in a.items():
        for fb, vb in b.items():
            f = tuple(sorted(fa + fb))
            out[f] = out.get(f, Fraction(0)) + va * vb
            if out[f] == 0:
                del out[f]
    return out


def el_str(a) -> str:
    if not a:
        return "0"
    parts = []
    for f, v in sorted(a.items(), key=lambda kv: (sum(order(t) for t in kv[0]), kv[0])):
        parts.append(f"{v}*{render_forest(f)}")
    return " + ".join(parts)


# ---------------------------------------------------------------------------
# The antipode, by the recursion  S(t) = -t - sum_{proper cuts} S(P) . R.
# ---------------------------------------------------------------------------
@lru_cache(maxsize=None)
def antipode(t: Tree):
    res = {(t,): Fraction(-1)}                       # the -t term
    for (P, R) in coproduct(t):
        if R == () or P == ():                       # skip t(x)1 and 1(x)t
            continue
        SP = antipode_forest(P)
        res = el_add(res, el_scale(el_mul(SP, {R: Fraction(1)}), -1))
    return res


def antipode_forest(f: Forest):
    out = {(): Fraction(1)}                           # S(1) = 1
    for t in f:
        out = el_mul(out, antipode(t))
    return out


def convolution_S_id(t: Tree):
    """m (S (x) id) Delta (t) — must be 0 for nonempty t (the antipode axiom)."""
    res = el_zero()
    for (P, R) in coproduct(t):
        SP = antipode_forest(P)
        Rel = {(): Fraction(1)} if R == () else {R: Fraction(1)}
        res = el_add(res, el_mul(SP, Rel))
    return res


# ---------------------------------------------------------------------------
# Runge-Kutta elementary weights and order conditions.
# ---------------------------------------------------------------------------
def phi_vec(t: Tree, A):
    s = len(A)
    if t == LEAF:
        return [Fraction(1)] * s
    cv = [phi_vec(c, A) for c in t]
    out = []
    for i in range(s):
        p = Fraction(1)
        for v in cv:
            p *= sum(A[i][j] * v[j] for j in range(s))
        out.append(p)
    return out


def phi(t: Tree, A, b):
    pv = phi_vec(t, A)
    return sum(b[i] * pv[i] for i in range(len(b)))


def check_order(A, b, max_order=6):
    rows, order_ok = [], {}
    for n in range(1, max_order + 1):
        ok_n = True
        for t in trees_of_order(n):
            val = phi(t, A, b)
            tgt = Fraction(1, gamma(t))
            ok = val == tgt
            rows.append((t, n, val, tgt, ok))
            ok_n = ok_n and ok
        order_ok[n] = ok_n
    p = 0
    for n in range(1, max_order + 1):
        if order_ok[n]:
            p = n
        else:
            break
    return p, rows


def error_coefficients(A, b, p):
    """Leading truncation-error coefficients: Phi(t) - 1/gamma(t) for trees of order p+1."""
    out = []
    for t in trees_of_order(p + 1):
        out.append((t, phi(t, A, b) - Fraction(1, gamma(t))))
    return out


def is_explicit(A) -> bool:
    s = len(A)
    return all(A[i][j] == 0 for i in range(s) for j in range(i, s))


def stability_poly(A, b):
    """Exact coefficients [r0, r1, ...] of the stability function R(z) = sum_k r_k z^k for an
    EXPLICIT method (A strictly lower-triangular): R(z) = 1 + sum_{k>=1} (b . A^{k-1} 1) z^k.
    For an order-p method R agrees with exp(z) through z^p (e.g. RK4 -> [1,1,1/2,1/6,1/24])."""
    if not is_explicit(A):
        raise ValueError("stability_poly: implicit methods (R rational) not supported here")
    s = len(A)
    ones = [Fraction(1)] * s
    coeffs = [Fraction(1)]            # r0 = R(0) = 1
    vec = ones[:]                     # A^0 . 1
    for _k in range(1, s + 1):
        coeffs.append(sum(b[i] * vec[i] for i in range(s)))
        vec = [sum(A[i][j] * vec[j] for j in range(s)) for i in range(s)]
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs


def convergence_data(A, b, Ns=(1, 2, 4, 8, 16, 32, 64, 128, 256)):
    """Empirical convergence on the scalar test problem y'=y, y(0)=1, t in [0,1] (exact value e).
    For a linear problem one step multiplies by R(h), so y_N = R(h)^N.  Returns [(h, error), ...]."""
    coeffs = [float(c) for c in stability_poly(A, b)]

    def R(h):
        return sum(c * h ** k for k, c in enumerate(coeffs))
    out = []
    for N in Ns:
        h = 1.0 / N
        out.append((h, abs(R(h) ** N - math.e)))
    return out


def empirical_order(A, b) -> float:
    """Least-squares slope of log(error) vs log(h) over the finest steps -> the observed order."""
    data = [(h, e) for (h, e) in convergence_data(A, b) if e > 0]
    data = data[-5:]
    xs = [math.log(h) for h, _ in data]
    ys = [math.log(e) for _, e in data]
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return num / den if den else 0.0


# ---------------------------------------------------------------------------
# Functionals on the Hopf algebra, convolution, and the modified equation (log_*).
# A functional is a dict {forest: Fraction}; the method character `a` is multiplicative.
# ---------------------------------------------------------------------------
@lru_cache(maxsize=None)
def coproduct_forest(f: Forest) -> tuple:
    """Delta on a forest = product of the tree coproducts (Delta is an algebra hom)."""
    if f == ():
        return (((), ()),)
    terms = [((), ())]
    for t in f:
        ct = coproduct(t)
        new = []
        for (L, R) in terms:
            for (Lt, Rt) in ct:
                new.append((tuple(sorted(L + Lt)), tuple(sorted(R + Rt))))
        terms = new
    return tuple(terms)


def all_forests(max_order: int) -> list[Forest]:
    """All forests with total order <= max_order (including the empty forest)."""
    pool = tuple(all_trees(max_order))
    res = [()]
    def rec(start, remaining, acc):
        for i in range(start, len(pool)):
            o = order(pool[i])
            if o > remaining:
                continue
            res.append(tuple(sorted(acc + (pool[i],))))
            rec(i, remaining - o, acc + (pool[i],))
    rec(0, max_order, ())
    # dedupe
    return sorted(set(res), key=lambda f: (sum(order(t) for t in f), f))


def counit_functional(max_order):
    return {(): Fraction(1)}


def char_from_method(coeff_on_tree, max_order):
    """Build the multiplicative functional a with a(t)=coeff_on_tree(t), a(1)=1."""
    a = {}
    for f in all_forests(max_order):
        v = Fraction(1)
        for t in f:
            v *= coeff_on_tree(t)
        a[f] = v
    return a


def convolve(phi_f, psi_f, max_order):
    out = {}
    for x in all_forests(max_order):
        s = Fraction(0)
        for (L, R) in coproduct_forest(x):
            s += phi_f.get(L, Fraction(0)) * psi_f.get(R, Fraction(0))
        if s != 0:
            out[x] = s
    return out


def log_star(a_char, max_order):
    """Convolution logarithm  log_*(a) = sum_{k>=1} (-1)^{k+1}/k (a-e)^{*k},
    finite because (a-e) vanishes on the empty forest (per-degree nilpotent)."""
    e = counit_functional(max_order)
    d = el_add(a_char, el_scale(e, -1))          # a - e  (vanishes on 1)
    res = el_zero()
    powk = {(): Fraction(0)}                      # placeholder; build (a-e)^{*k}
    powk = dict(d)                                # (a-e)^{*1}
    k = 1
    while powk:
        res = el_add(res, el_scale(powk, Fraction((-1) ** (k + 1), 1) / k))
        if k >= max_order:
            break
        powk = convolve(powk, d, max_order)
        k += 1
    return res


def modified_equation(coeff_on_tree, max_order=4):
    """Coefficients b(t) = log_*(a)(t) of the modified vector field of a method with
    B-series character a (a(t)=coeff_on_tree(t)). b(•)=1; e.g. explicit Euler -> b([•])=-1/2."""
    a = char_from_method(coeff_on_tree, max_order)
    L = log_star(a, max_order)
    return {t: L.get((t,), Fraction(0)) for t in all_trees(max_order)}


# Method B-series characters (a(t) = Phi(t) for an RK method; a is multiplicative).
def rk_character_coeff(A, b):
    return lambda t: phi(t, A, b)


# ---------------------------------------------------------------------------
# A small library of classic explicit methods.
# ---------------------------------------------------------------------------
def methods():
    F = Fraction
    def T(A, bb):
        return ([[F(x) for x in row] for row in A], [F(x) for x in bb])
    M = {}
    M["euler"] = (*T([[0]], [1]), 1)
    M["midpoint"] = (*T([[0, 0], [F(1, 2), 0]], [0, 1]), 2)
    M["heun"] = (*T([[0, 0], [1, 0]], [F(1, 2), F(1, 2)]), 2)
    M["ralston2"] = (*T([[0, 0], [F(2, 3), 0]], [F(1, 4), F(3, 4)]), 2)
    M["rk4"] = (*T([[0, 0, 0, 0], [F(1, 2), 0, 0, 0], [0, F(1, 2), 0, 0], [0, 0, 1, 0]],
                   [F(1, 6), F(1, 3), F(1, 3), F(1, 6)]), 4)
    M["rk4_broken"] = (*T([[0, 0, 0, 0], [F(1, 2), 0, 0, 0], [0, F(1, 2), 0, 0], [0, 0, 1, 0]],
                          [F(1, 6), F(1, 3), F(1, 3), F(1, 7)]), 0)
    return M


# ---------------------------------------------------------------------------
# Reports.
# ---------------------------------------------------------------------------
def report_order(name, A, b, max_order=6):
    p, rows = check_order(A, b, max_order)
    print(f"\n=== {name}: attained order = {p} ===")
    print(f"{'tree':<10}{'|t|':>4}{'Phi':>12}{'1/gamma':>12}   ok")
    for t, n, val, tgt, ok in rows:
        if n <= p + 1:
            print(f"{render(t):<10}{n:>4}{str(val):>12}{str(tgt):>12}   {'.' if ok else 'X'}")
    errs = error_coefficients(A, b, p)
    print(f"leading error coefficients (order {p+1}):  "
          + ",  ".join(f"{render(t)}:{c}" for t, c in errs if c != 0) or "  (none)")
    return p


def report_modified(name, A, b, max_order=4):
    coeff = rk_character_coeff(A, b)
    mod = modified_equation(coeff, max_order)
    print(f"\n=== {name}: modified-equation coefficients  b(t) = log_*(method)(t) ===")
    print("  (modified field  f~ = sum_t (h^{|t|-1}/sigma(t)) b(t) F(t);  b(•)=1 recovers f)")
    for t in all_trees(max_order):
        c = mod[t]
        if c != 0:
            print(f"  {render(t):<10} |t|={order(t)}  b(t) = {c}")


# ---------------------------------------------------------------------------
# Self-test: re-verify the formalized theorems numerically.
# ---------------------------------------------------------------------------
def selftest():
    # tree counts = OEIS A000081
    counts = [len(trees_of_order(n)) for n in range(1, 9)]
    assert counts == [1, 1, 2, 4, 9, 20, 48, 115], counts

    leaf, l2, l3 = (), ((),), (((),),)
    cherry = ((), ())
    assert gamma(l2) == 2 and gamma(l3) == 6 and gamma(cherry) == 3
    assert render(l3) == "[[•]]" and render(cherry) == "[••]"

    # coproduct matches the textbook / formalized values
    def coprod_str(t):
        terms = []
        for (L, R) in coproduct(t):
            terms.append(f"{render_forest(L)}(x){render_forest(R)}")
        return sorted(terms)
    assert coprod_str(leaf) == sorted(["•(x)1", "1(x)•"]), coprod_str(leaf)
    assert coprod_str(l2) == sorted(["[•](x)1", "1(x)[•]", "•(x)•"]), coprod_str(l2)
    assert coprod_str(l3) == sorted(["[[•]](x)1", "1(x)[[•]]", "•(x)[•]", "[•](x)•"]), coprod_str(l3)
    # cherry is symmetric: the cut •(x)[•] occurs twice (prune either leaf) -> coefficient 2
    assert coprod_str(cherry) == sorted(["[••](x)1", "1(x)[••]", "•(x)[•]", "•(x)[•]", "••(x)•"]), coprod_str(cherry)

    # antipode values (commutative algebra)
    assert antipode(leaf) == {(leaf,): Fraction(-1)}                     # S(•) = -•
    assert antipode(l2) == {((), ()): Fraction(1), (l2,): Fraction(-1)}  # S([•]) = •• - [•]

    # THE antipode axiom (paper I's HopfAlgebra theorem):  m(S(x)id)Delta(t) = 0  for nonempty t
    for n in range(1, 7):
        for t in trees_of_order(n):
            assert convolution_S_id(t) == {}, (render(t), el_str(convolution_S_id(t)))

    # order: classic methods hit their known order
    for name, (A, b, exp) in methods().items():
        p, _ = check_order(A, b, max_order=6)
        assert p == exp, (name, p, exp)

    # modified equation (paper II's log_* = Eulerian idempotent):
    #   explicit Euler  y1 = y0 + h f  has character a(•)=1, a(t)=0 else; its modified field is
    #   f~ = f - (h/2) f'f + ...   i.e.  b(•)=1,  b([•])=-1/2.
    euler_coeff = lambda t: Fraction(1) if t == leaf else Fraction(0)
    mod = modified_equation(euler_coeff, max_order=4)
    assert mod[leaf] == 1, mod[leaf]
    assert mod[l2] == Fraction(-1, 2), mod[l2]

    # a consistency cross-check: the modified field of an order-p method has b(t)=0 for 1<|t|<=p
    A, b, _ = methods()["rk4"]
    modrk = modified_equation(rk_character_coeff(A, b), max_order=4)
    for t in all_trees(4):
        if 2 <= order(t) <= 4:
            assert modrk[t] == 0, (render(t), modrk[t])

    # stability function (exact) and empirical convergence order
    assert stability_poly(*methods()["rk4"][:2]) == [Fraction(1), Fraction(1),
        Fraction(1, 2), Fraction(1, 6), Fraction(1, 24)]
    for nm, exp in [("euler", 1), ("midpoint", 2), ("heun", 2), ("rk4", 4)]:
        A, b, _ = methods()[nm]
        assert abs(empirical_order(A, b) - exp) < 0.1, (nm, empirical_order(A, b))

    print("selftest OK")
    print("  - rooted-tree counts = A000081:", {n: counts[n - 1] for n in range(1, 9)})
    print("  - stability function R = exp truncation; empirical convergence order matches (e.g. RK4 ~ 4)")
    print("  - coproduct values match the formalized Delta")
    print("  - antipode axiom  m(S(x)id)Delta = eta.eps  holds for all trees up to order 6  (paper I)")
    print("  - classic RK methods attain their known order")
    print("  - log_*(Euler) = modified field  f - (h/2)f'f + ...   (paper II, Eulerian idempotent)")
    print("  - order-4 method has trivial modified field up to order 4")


def main():
    ap = argparse.ArgumentParser(description="B-series / Butcher-group toolkit on the rooted-tree Hopf algebra.")
    ap.add_argument("method", nargs="?", default="all",
                    help="euler|midpoint|heun|ralston2|rk4|rk4_broken|all")
    ap.add_argument("--order", type=int, default=6, help="max tree order for order conditions")
    ap.add_argument("--modified", action="store_true", help="also show the modified-equation coefficients")
    ap.add_argument("--hopf", action="store_true", help="demo the coproduct and antipode on small trees")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        selftest()
        return
    if a.hopf:
        for t in [(), ((),), (((),),), ((), ())]:
            terms = " + ".join(f"{render_forest(L)}(x){render_forest(R)}" for (L, R) in coproduct(t))
            print(f"Delta({render(t)}) = {terms}")
            print(f"   S({render(t)}) = {el_str(antipode(t))}")
        return
    M = methods()
    names = list(M) if a.method == "all" else [a.method]
    for nm in names:
        A, b, _ = M[nm]
        p = report_order(nm, A, b, a.order)
        if a.modified:
            report_modified(nm, A, b, max_order=min(4, a.order))


if __name__ == "__main__":
    main()
