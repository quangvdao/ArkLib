/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentFilter
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.FilterCore
import Mathlib.Data.ZMod.Basic

open CompPoly ReedSolomon.ListDecoding.FirstOrderCurveCandidates

private abbrev E := ZMod 2
private def u : CPolynomial E := CPolynomial.X
private def v : CPolynomial (CPolynomial E) := CPolynomial.X
private def q : CPolynomial (CPolynomial E) := (v - CPolynomial.C u) ^ 2
private noncomputable def σ : CPolynomial E →+* E :=
  (Polynomial.eval₂RingHom (RingHom.id E) 1).comp CPolynomial.toPolyRingHom

-- A universal simple factor meets a nonuniversal double factor in characteristic two.
example : residualFilter? (v * q) v = some (u ^ 2) := by decide +kernel

private theorem generic_coprime : IsCoprime (q.toPoly.map σ) (v.toPoly.map σ) := by
  refine ⟨1, 2 - Polynomial.X, ?_⟩
  have hq : q.toPoly.map σ = (Polynomial.X - 1) ^ 2 := by
    simp [q, v, u, σ, CPolynomial.toPoly_pow, CPolynomial.toPoly_sub,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly, CPolynomial.toPolyRingHom_apply]
  have hv : v.toPoly.map σ = Polynomial.X := by simp [v, CPolynomial.X_toPoly]
  rw [hq, hv]
  ring

-- Invoke the semantic bridge at the intersection, where the specialized quotient is nonreduced.
example : (u ^ 2).toPoly.eval₂ (RingHom.id E) 0 = 0 := by
  apply residualFilter?_vanishes_of_nonuniversal_point σ (RingHom.id E) 0 0
    v q v (by decide +kernel) (by decide +kernel) (dvd_refl _) generic_coprime
    _ _ (u ^ 2) (by decide +kernel)
  · simp [q, v, u, CPolynomial.toPoly_pow, CPolynomial.toPoly_sub,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly, CPolynomial.toPolyRingHom_apply]
  · simp [v, CPolynomial.X_toPoly]

-- Position one remains position one even when position zero is wholly universal.
example : ∃ c, ([1, u ^ 2] : List (CPolynomial E))[1]? = some c ∧
    residualFilter? (v * q) v = some c := by
  exact FilterCore.coefficients?_getElem? (v * q) [0, v] [1, u ^ 2]
    (by decide +kernel) 1 v rfl

#print axioms residualFilter?_factorization
#print axioms residualFilter?_vanishes_of_scan_point
#print axioms FilterCore.coefficients?_getElem?
