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

-- At the crossing, the generic first index is one; its specialization gains one order
-- exactly at parameter zero. This uses the scan/order theorem rather than an output oracle.
private theorem crossing_order (a : E) :
    Polynomial.X ^ 2 ∣ (characteristicPolynomial crossing v).toPoly.map
      ((Polynomial.eval₂RingHom (RingHom.id E) a).comp CPolynomial.toPolyRingHom) ↔ a = 0 := by
  obtain ⟨j, _, hn, _, hbefore, hiff⟩ :=
    residualFilter?_specialization_iff (RingHom.id E) a crossing v u (by decide +kernel)
  have hz : (characteristicPolynomial crossing v).coeff 0 = 0 := by decide +kernel
  have h1 : (characteristicPolynomial crossing v).coeff 1 ≠ 0 := by decide +kernel
  have hj0 : j ≠ 0 := by
    intro hj
    exact hn (hj ▸ hz)
  have hj1 : j ≤ 1 := by
    by_contra hj
    exact h1 (hbefore 1 (by omega))
  have hj : j = 1 := by omega
  subst j
  simpa only [u, CPolynomial.X_toPoly, Polynomial.eval₂_X] using hiff

example : Polynomial.X ^ 2 ∣ (characteristicPolynomial crossing v).toPoly.map
    ((Polynomial.eval₂RingHom (RingHom.id E) 0).comp CPolynomial.toPolyRingHom) :=
  (crossing_order 0).mpr rfl

example : ¬Polynomial.X ^ 2 ∣ (characteristicPolynomial crossing v).toPoly.map
    ((Polynomial.eval₂RingHom (RingHom.id E) 1).comp CPolynomial.toPolyRingHom) :=
  (crossing_order 1).not.mpr one_ne_zero

-- A double infinitesimal fiber retains its multiplicity and the sign of `W - g`.
example : characteristicPolynomial (v ^ 2) (v + 1) = v ^ 2 + v + 1 := by decide +kernel

-- The Sylvester bridge requires only monicity, including for this nonreduced fiber.
example :
    (characteristicPolynomial (v ^ 2) (v + 1)).toPoly =
      Polynomial.resultant ((v ^ 2).toPoly.map Polynomial.C)
        (Polynomial.C Polynomial.X - (v + 1).toPoly.map Polynomial.C) := by
  apply characteristicPolynomial_eq_resultant
  decide +kernel

namespace OddSign

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def w : CPolynomial (CPolynomial (ZMod 5)) := CPolynomial.X

-- Odd width distinguishes `W - g` from `g - W` in odd characteristic.
example : characteristicPolynomial (w ^ 3) (w + 1) =
    w ^ 3 + 2 * w ^ 2 + 3 * w + 4 := by decide +kernel

-- The rank-zero quotient has determinant one, including at the zero residual.
example : characteristicPolynomial (E := ZMod 5) 1 0 = 1 :=
  by decide +kernel

example : characteristicPolynomial (w ^ 3) 0 = w ^ 3 := by decide +kernel

end OddSign
