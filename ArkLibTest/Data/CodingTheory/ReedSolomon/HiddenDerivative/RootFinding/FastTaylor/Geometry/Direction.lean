/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Geometry.Direction

/-! Computed top parts, rejected early grid points, and the zero-parameter edge. -/

namespace DirectionTests
open CPoly CPoly.CMvPolynomial
open ReedSolomon.HiddenDerivative.FastTaylor.Geometry.Direction

/-- Search genuinely skips vanishing points and retains the top monomials only. -/
def run : IO Unit := do
  let p : CMvPolynomial 2 ℚ := 2 * X 0 ^ 2 + X 0 * X 1 + X 1 + 7
  unless homogeneousPart 2 p == 2 * X 0 ^ 2 + X 0 * X 1 do
    throw (IO.userError "homogeneous filter retained a lower-degree term")
  let some (v, m, inv) := chooseFor? p [0, 1, 2] |
    throw (IO.userError "nonzero top part failed direction search")
  unless decide (v = ![1, 0]) && decide (m * inv = 1 ∧ inv * m = 1) do
    throw (IO.userError "direction search failed to skip the first vanishing row")
  unless (chooseFor? (0 : CMvPolynomial 2 ℚ) [0, 1, 2]).isNone do
    throw (IO.userError "zero polynomial selected a nonvanishing direction")
  unless (chooseFor? p [0]).isNone do
    throw (IO.userError "vanishing short grid unexpectedly succeeded")
  let some (v₀, _, _) := chooseFor? (X 0 ^ 2 : CMvPolynomial 1 ℚ) [0, 2] |
    throw (IO.userError "zero-parameter direction search failed")
  unless v₀ 0 == 2 do
    throw (IO.userError "zero-parameter search chose a vanishing direction")

end DirectionTests
