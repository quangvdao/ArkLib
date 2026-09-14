/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection

/-!
# Checked projection clients

The fixtures cover a line, a cusp, a curve needing a nonzero shear, and rejected zero,
constant and repeated equations. Cusp success asserts a finite separable projection,
not that the cusp ring is normal.
-/

open CompPoly CPoly Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection

private def y : CMvPolynomial 2 ℚ := CMvPolynomial.X 0
private def z : CMvPolynomial 2 ℚ := CMvPolynomial.X 1

/-- A downstream client obtains a nonzero denominator without an extra certificate. -/
example (Q : CMvPolynomial 2 ℚ) (c : Candidate ℚ) (h : search 3 Q = some c) :
    c.discriminant ≠ 0 := (search_sound 3 Q c h).1.discriminant_ne_zero

/-- The inverse is also usable by downstream clients. -/
example (Q : CMvPolynomial 2 ℚ) : shearHom (-2) (shearHom 2 Q) = Q :=
  shear_inverse 2 Q

/-- Runtime assertions exercise the actual stored polynomial and gcd algorithms. -/
def commonCenterProjectionStandaloneMain : IO Unit := do
  for Q in [z - y, z ^ 2 - y ^ 3, y * z - 1] do
    unless (search 3 Q).isSome do
      throw (IO.userError "regular projection unexpectedly failed")
  for Q in [(0 : CMvPolynomial 2 ℚ), 1, (z - y) ^ 2] do
    if (search 2 Q).isSome then
      throw (IO.userError "degenerate or repeated equation incorrectly accepted")
  if (trySlope 0 (y * z - 1)).isSome then
    throw (IO.userError "nonconstant leading coefficient incorrectly accepted")
  unless shearHom (-2) (shearHom 2 (z ^ 2 - y ^ 3)) == z ^ 2 - y ^ 3 do
    throw (IO.userError "stored inverse shear failed")
  let some cusp := trySlope 0 (z ^ 2 - y ^ 3)
    | throw (IO.userError "cusp projection failed")
  unless cusp.discriminant == CPolynomial.X ^ 3 do
    throw (IO.userError "cusp discriminant normalization failed")
  IO.println "checked shear, line/cusp/hyperbola, and rejection fixtures: passed"

#print axioms shear_inverse
#print axioms derivativeCoprime_sound
#print axioms trySlope_sound
#print axioms search_sound
#print axioms search_success_iff
