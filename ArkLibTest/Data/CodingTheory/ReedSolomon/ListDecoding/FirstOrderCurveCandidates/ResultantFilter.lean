/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ResultantFilter
import Mathlib.Data.ZMod.Basic

/-! Executed lowest-coefficient regressions, including partial universality at a crossing. -/

open CompPoly ReedSolomon.ListDecoding.FirstOrderCurveCandidates

private abbrev E := ZMod 3

private def u : CPolynomial E := CPolynomial.X

private def v : CPolynomial (CPolynomial E) := CPolynomial.X

/-- `v(v-u)` has two components crossing at the origin. -/
private def crossing : CPolynomial (CPolynomial E) :=
  v ^ 2 - CPolynomial.C u * v

-- Zero on the whole curve gives the constant filter.
example : (residualFilter? crossing 0 == some (1 : CPolynomial E)) = true := by decide +kernel

-- The residual `v` is universal on only one component: its filter is `u`, not one.
example : (residualFilter? crossing v == some u) = true := by decide +kernel

-- A nonzero constant residual has no detecting parameter roots.
example : (residualFilter? crossing 1 == some (1 : CPolynomial E)) = true := by decide +kernel

-- A zero intermediate coefficient does not terminate the increasing coefficient scan.
example : (lowestCoefficient? (v ^ 2) == some (1 : CPolynomial E)) = true := by decide +kernel
