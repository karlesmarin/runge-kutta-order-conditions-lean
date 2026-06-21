import Lake
open Lake DSL

package «runge-kutta-order-conditions-lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Pinned to the exact Mathlib revision the development was built against
-- (Lean toolchain: see `lean-toolchain`). Run `lake exe cache get` before `lake build`.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "701fb6e9c3b9285968b375d19886bfc5ca134840"

@[default_target]
lean_lib «ButcherOrder» where
  -- Certified Runge–Kutta order conditions: order, gamma, the Butcher elementary weight Phi,
  -- the order-budget catalogue keystone, and the certificates (RK4, DOPRI5, Gauss s=3 orders 4 & 6).
