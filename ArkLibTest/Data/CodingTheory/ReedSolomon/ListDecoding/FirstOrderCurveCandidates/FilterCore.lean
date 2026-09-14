/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.FilterCore

/-! Executed traces of coefficient scans, distinct-position thresholding, and one radical. -/

open CompPoly ReedSolomon.ListDecoding.FirstOrderCurveCandidates

private abbrev E := ZMod 3

private def u : CPolynomial E := CPolynomial.X

private def v : CPolynomial (CPolynomial E) := CPolynomial.X

private def parameter : CPolynomial (CPolynomial E) := CPolynomial.C u

-- This reduced curve has a ramified fiber above u=0.
private def ramified : CPolynomial (CPolynomial E) := v ^ 2 - parameter

private def checkTrace (out : Option (FilterCore.Trace E))
    (rows : List (CPolynomial E)) (H : CPolynomial E) (base : Option (CPolynomial E)) :
    Bool :=
  match out with
  | none => false
  | some trace => trace.coefficients == rows && trace.thresholdPolynomial == H && trace.base == base

-- Multiplicity two at one position cannot meet the two-position threshold.
example : checkTrace (FilterCore.run 3 id 3 2 ramified [parameter, 1, 1])
    [u ^ 2, 1, 1] 1 none = true := by decide +kernel

-- Two positions qualify: the trace retains H=u², then radicalizes once to G=u.
example : checkTrace (FilterCore.run 3 id 3 2 ramified [parameter, parameter, 1])
    [u ^ 2, u ^ 2, 1] (u ^ 2) (some u) = true := by decide +kernel

-- Whole-curve universality contributes one, preserving all original row positions.
example : checkTrace (FilterCore.run 3 id 3 2 ramified [0, parameter, 1])
    [1, u ^ 2, 1] 1 none = true := by decide +kernel
