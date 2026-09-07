/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Bivariate

/-!
# Hasse vanishing and bivariate root multiplicity

The coefficient formulation of symbolic interpolation uses all shifted coefficients below a
given total degree. This module connects it to the existing root-multiplicity value. Nonzeroness
is explicit because that value uses `none` for the zero polynomial, not an infinite multiplicity.
-/

namespace Polynomial.Bivariate

variable {R : Type} [CommRing R] [DecidableEq R]

/-- For a nonzero polynomial, a lower bound on root multiplicity is equivalent to vanishing of
all Hasse coefficients below that total order. The X order precedes the Y order. -/
theorem le_rootMultiplicity_iff_of_ne_zero (Q : Polynomial (Polynomial R)) (hQ : Q ≠ 0)
    (x y : R) (m : ℕ) :
    (some m : Option ℕ) ≤ rootMultiplicity Q x y ↔
      ∀ r s, r + s < m → ((shift Q x y).coeff s).coeff r = 0 := by
  have hne := rootMultiplicity₀_ne_none (shift Q x y) (shift_ne_zero Q x y hQ)
  have hiff := rootMultiplicity₀_ge_iff (shift Q x y) m
  change (some m : Option ℕ) ≤ rootMultiplicity₀ (shift Q x y) ↔ _
  cases heq : rootMultiplicity₀ (shift Q x y) with
  | none => exact (hne heq).elim
  | some d =>
    rw [heq] at hiff
    simpa only [Option.some_le_some, Option.mem_def, Option.some.injEq,
      forall_eq, forall_eq', coeff] using hiff.symm

end Polynomial.Bivariate
