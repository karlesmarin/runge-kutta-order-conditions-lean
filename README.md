# Certified Runge–Kutta order conditions in Lean 4

Machine-checked Butcher order conditions for Runge–Kutta methods, on the rooted-tree
(Butcher / Connes–Kreimer) substrate. All headline theorems are `sorry`-free and depend only on the
three standard axioms of classical Lean/Mathlib (`propext`, `Classical.choice`, `Quot.sound`) — no
`native_decide`, no ad-hoc axioms.

> Companion paper: **"What Order a Method Knows: certified Runge–Kutta order conditions over rooted
> trees, machine-checked in Lean 4"** (Carles Marín, 2026).
> Paper PDFs: `runge-kutta-order-conditions-lean.pdf` (EN), `…-es.pdf` (ES).
> Zenodo: **DOI [10.5281/zenodo.20787666](https://doi.org/10.5281/zenodo.20787666)** (draft; resolves on publication).

## What is verified

A method has order *p* iff, for every rooted tree *t* with ≤ *p* nodes, the Butcher elementary weight
Φ(*t*)(A,b) equals 1/γ(*t*). `ButcherOrder.lean` builds a small computable engine (`order`, `gamma`,
`Phi`), proves a keystone reducing the infinite family of conditions to a finite, decidable catalogue
check, and discharges it for:

| Theorem | Method | order | coeff. ring / tactic |
|---|---|---|---|
| `rk4_order4`   | classical RK4        | 4 | ℚ / `norm_num` |
| `dp_order5`    | Dormand–Prince DOPRI5 | 5 | ℚ / `norm_num` |
| `gauss_order4` | Gauss–Legendre s=3   | 4 | ℚ(√15) via `Q15` / `norm_num` |
| `gauss_order6` | Gauss–Legendre s=3   | 6 | ℤ[√15] via `Z15` / `decide` |

plus negative certificates (`rk4_not_ord5`, `heun_not_ord3`) that pin the order exactly, and the
symmetrization lemma `orderCond_node_perm` (planar ⇒ abstract).

The order-6 Gauss certificate uses the *integer*-`decide` trick: clearing denominators (scale by
D = 360) moves the tableau into ℤ[√15], so the order condition becomes the integer identity
γ(t)·Φ(D·A, D·b, t) = D^|t|, which the kernel's GMP `Int` arithmetic decides directly.

## Build

```sh
# Lean toolchain is pinned in lean-toolchain (leanprover/lean4:v4.30.0-rc2)
lake exe cache get      # fetch the matching Mathlib oleans
lake build              # builds ButcherOrder
```

To re-check the axiom footprint, the file ends with `#print axioms` for each headline theorem; each
reports `[propext, Classical.choice, Quot.sound]`.

## Independent cross-checks

The engine's `#eval` values were cross-checked, before the theorems were proved, against two
independent oracles:
- `bseries.py` — the elementary-weight recursion over ℚ (Python).
- `validate_order_conditions.sage` — a brute-force index summation (a genuinely different algorithm)
  over ℚ, ℚ(√3) and ℚ(√15); confirms Gauss s=3 holds orders 1–6 and fails all 48 order-7 conditions
  (exactly order 6). Run via `docker run --rm -v "$PWD:/work" sagemath/sagemath sage /work/validate_order_conditions.sage`.

## Series

This is the applied payoff of the rooted-tree Hopf-algebra formalization:
- **Paper I** — "How a Tree Remembers Its Cuts" (the Connes–Kreimer–Foissy Hopf algebra). Zenodo
  10.5281/zenodo.20762280.
- **Paper II** — "How a Tree Forgets Its Order" (Eulerian idempotent / backward error). Zenodo
  10.5281/zenodo.20774821.

The elementary weight Φ is a *character* of that Hopf algebra; order *p* ⟺ Φ and the exact flow
(t ↦ 1/γ(t)) agree on trees of order ≤ *p*.

## References — the two worlds this joins

One Hopf algebra of rooted trees governs two very different subjects. In **numerical analysis** it is
the Butcher group of Runge–Kutta methods, and its characters are the order conditions certified in this
repository. In **quantum field theory** it is the Connes–Kreimer algebra whose coproduct organizes the
subtraction of subdivergences in BPHZ renormalization. Brouder made the dictionary explicit: a
Runge–Kutta step and a renormalized Feynman amplitude are computed by the *same* algebra on the *same*
trees. This development is the machine-checked numerical-analysis end of that bridge — and its companion
([How a Tree Remembers Its Cuts](https://doi.org/10.5281/zenodo.20762280)) is the Hopf-algebra end.

**Numerical analysis (the order theory).**
- J. C. Butcher, *Coefficients for the study of Runge–Kutta integration processes*, J. Austral. Math.
  Soc. **3** (1963) 185. DOI [10.1017/s1446788700027932](https://doi.org/10.1017/s1446788700027932).
- E. Hairer, C. Lubich, G. Wanner, *Geometric Numerical Integration*, Springer (2006). DOI
  [10.1007/3-540-30666-8](https://doi.org/10.1007/3-540-30666-8).

**Quantum field theory & the Hopf algebra (the other shore).**
- A. Connes, D. Kreimer, *Hopf algebras, renormalization and noncommutative geometry*, Comm. Math.
  Phys. **199** (1998) 203. DOI [10.1007/s002200050499](https://doi.org/10.1007/s002200050499).
- L. Foissy, *Les algèbres de Hopf des arbres enracinés décorés, I*, Bull. Sci. Math. **126** (2002)
  193. DOI [10.1016/s0007-4497(02)01108-9](https://doi.org/10.1016/s0007-4497(02)01108-9) — the planar
  (noncommutative) algebra formalized in the companion.

**The bridge.**
- C. Brouder, *Runge–Kutta methods and renormalization*, Eur. Phys. J. C **12** (2000) 521. DOI
  [10.1007/s100529900235](https://doi.org/10.1007/s100529900235) — the explicit dictionary between the
  two worlds.

## License & citation

Code: Apache-2.0. Paper PDFs: CC-BY-4.0. See `CITATION.cff`.

A large language model was used as a coding assistant; every statement was independently checked by the
Lean kernel, and all mathematical decisions and claims are the author's.
