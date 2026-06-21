# Certified Runge–Kutta Order Conditions over Rooted Trees — in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20787666.svg)](https://doi.org/10.5281/zenodo.20787666)

A machine-checked formalization in **Lean 4 / Mathlib** of the **Butcher order conditions** of
Runge–Kutta methods, on the rooted-tree (Butcher / Connes–Kreimer) substrate. Every headline result is
**`sorry`-free**: `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` — no
`native_decide`, no ad-hoc axioms.

To the best of our knowledge (a focused search of the Lean/Mathlib, Isabelle/HOL **Archive of Formal
Proofs**, and Coq/Rocq ecosystems, June 2026) the **Runge–Kutta order conditions had not previously been
formalized in any proof assistant**; the only prior machine-checked RK work (Boldo *et al.*, Coq)
certifies floating-point round-off of Euler/RK2 on linear systems — an orthogonal layer.

## The headline

> **Take a Runge–Kutta tableau `(A,b)` and a rooted tree `t`.** The method has order `p` exactly when an
> *elementary weight* `Φ(t)(A,b)` equals `1/γ(t)` for every tree with at most `p` nodes (Butcher's
> theorem). That is an *infinite* family of conditions; a **keystone** turns it into one finite,
> decidable catalogue check, discharged here from Euler up to Gauss–Legendre **order 6**.

| Lean name | Statement |
|---|---|
| `satisfiesOrderConditions_iff` | keystone: "order `p`" ⟺ a finite catalogue check (sound + complete) |
| `rk4_order4` / `rk4_not_ord5` | classical RK4 attains order 4 — and *not* 5 (order pinned exactly) |
| `dp_order5` | Dormand–Prince DOPRI5 (the `ode45` / SciPy `RK45` default) attains order 5 |
| `gauss_order4` | Gauss–Legendre s=3 attains order 4, coefficients in ℚ(√15) (via `norm_num`) |
| `gauss_order6` | Gauss–Legendre s=3 attains **order 6**, via the integer ring ℤ[√15] + `decide` |
| `orderCond_node_perm` | `Φ` is invariant under permuting a node's children (planar ⇒ abstract) |

The order-6 certificate is the methodological core. Over ℚ the kernel cannot reduce the `Nat.gcd` inside
`Rat` normalization, so `decide` stalls and symbolic `norm_num` on the large order-6 trees exhausts
memory (~20 GB). The fix is to change the *representation*: clearing denominators (scale by `D = 360`)
moves the tableau into the **integer** ring `ℤ[√15]`, so the order condition becomes the integer identity
`γ(t)·Φ(D·A,D·b,t) = D^|t|`, which the kernel's GMP `Int` arithmetic decides outright — fast, negligible
memory, axiom-free. The whole 65-tree order-6 certificate compiles in ~1 s.

## The paper

**What Order a Method Knows: certified Runge–Kutta order conditions over rooted trees, machine-checked
in Lean 4** — English ([`runge-kutta-order-conditions-lean.pdf`](runge-kutta-order-conditions-lean.pdf))
and Spanish ([`runge-kutta-order-conditions-lean-es.pdf`](runge-kutta-order-conditions-lean-es.pdf)).
DOI `10.5281/zenodo.20787666`.

This is the **applied payoff** of the rooted-tree Hopf-algebra series ([How a Tree Remembers Its
Cuts](https://doi.org/10.5281/zenodo.20762280), [How a Tree Forgets Its
Order](https://doi.org/10.5281/zenodo.20774821)): the elementary weight `Φ` is a *character* of that
Hopf algebra, and a method has order `p` iff that character agrees with the exact flow's,
`t ↦ 1/γ(t)`, on trees of order ≤ `p`.

## What this is, and what it is not

The mathematics is **classical throughout** (Butcher 1963; Foissy 2002); the contribution is the
**formalization**. Specifically:

- We certify the **algebraic** order conditions `γ(t)·Φ(t)=1`, *not* Butcher's analytic theorem that
  they are equivalent to a local error `O(h^{p+1})`.
- Trees are **planar** (ordered children); the bridge to the abstract conditions is the one-lemma
  symmetrization `orderCond_node_perm`, not a formalization of Foissy's full Hopf morphism.
- The Hopf-algebraic framing is **contextual**: the certificates use only the trees, `order`, `γ`, `Φ`
  and permutation invariance; coproduct/antipode/Butcher-group/pre-Lie live in the companion.
- "First in a proof assistant" is a **focused search result, not a theorem**; pointers to anything
  missed are welcome.

## Independent cross-checks

The engine's `#eval` values were cross-checked, before the theorems were proved, against two independent
oracles: [`bseries.py`](bseries.py) (the elementary-weight recursion over ℚ, in Python) and
[`validate_order_conditions.sage`](validate_order_conditions.sage) (a brute-force index summation — a
genuinely different algorithm — over ℚ, ℚ(√3), ℚ(√15); it confirms Gauss s=3 holds orders 1–6 and fails
all 48 order-7 conditions, i.e. exactly order 6).

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain`
(`leanprover/lean4:v4.30.0-rc2`); Mathlib is pinned in `lakefile.lean` (rev `701fb6e9c3`).

```bash
lake exe cache get      # prebuilt Mathlib oleans (recommended)
lake build ButcherOrder
```

Verify the axiom footprint:

```lean
import ButcherOrder
#print axioms Butcher.gauss_order6   -- propext, Classical.choice, Quot.sound
```

`ButcherOrder.lean` is self-contained.

## References — the two worlds this joins

One Hopf algebra of rooted trees governs two very different subjects. In **numerical analysis** it is
the Butcher group of Runge–Kutta methods, and its characters are the order conditions certified in this
repository. In **quantum field theory** it is the Connes–Kreimer algebra whose coproduct organizes the
subtraction of subdivergences in BPHZ renormalization. Brouder made the dictionary explicit: a
Runge–Kutta step and a renormalized Feynman amplitude are computed by the *same* algebra on the *same*
trees. This development is the machine-checked numerical-analysis end of that bridge — and its companion
([How a Tree Remembers Its Cuts](https://doi.org/10.5281/zenodo.20762280)) is the Hopf-algebra end.

- **Numerical analysis.** J. C. Butcher, *Coefficients for the study of Runge–Kutta integration
  processes*, J. Austral. Math. Soc. **3** (1963) 185,
  [10.1017/s1446788700027932](https://doi.org/10.1017/s1446788700027932); E. Hairer, C. Lubich,
  G. Wanner, *Geometric Numerical Integration*, Springer (2006),
  [10.1007/3-540-30666-8](https://doi.org/10.1007/3-540-30666-8).
- **QFT & the Hopf algebra.** A. Connes, D. Kreimer, *Hopf algebras, renormalization and noncommutative
  geometry*, Comm. Math. Phys. **199** (1998) 203,
  [10.1007/s002200050499](https://doi.org/10.1007/s002200050499); L. Foissy, *Les algèbres de Hopf des
  arbres enracinés décorés, I*, Bull. Sci. Math. **126** (2002) 193,
  [10.1016/s0007-4497(02)01108-9](https://doi.org/10.1016/s0007-4497(02)01108-9).
- **The bridge.** C. Brouder, *Runge–Kutta methods and renormalization*, Eur. Phys. J. C **12** (2000)
  521, [10.1007/s100529900235](https://doi.org/10.1007/s100529900235).

## Citing

```bibtex
@misc{Marin2026RKorderLean,
  author = {Mar\'in, Carles},
  title  = {What Order a Method Knows: Certified Runge--Kutta Order Conditions over Rooted Trees, Machine-Checked in Lean 4},
  year   = {2026},
  doi    = {10.5281/zenodo.20787666},
  note   = {\url{https://github.com/karlesmarin/runge-kutta-order-conditions-lean}}
}
```

## Author and license

**Carles Marín** (independent researcher, `karlesmarin@gmail.com`). A large language model was used as a
coding assistant; every statement was independently verified by the Lean kernel, and all mathematics and
claims are the author's responsibility.

Licensed under the **Apache License 2.0** — see [`LICENSE`](LICENSE).
