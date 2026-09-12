/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Global.Residual
import Mathlib.Algebra.Field.ZMod

/-! Nonlinear residual tests allowing nilpotents and a vanishing characteristic pivot. -/

namespace RingResidualTests

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.FastTaylor.Global

private noncomputable def equation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  X (some 1) - X (some 0) ^ 2

/-- A square-zero constant solves the nonlinear equation in a nonreduced target.
The actual residual yields the literal common numerator at the later index two. -/
example {A : Type*} [CommRing A] (f : ℚ →+* A) (e : A) (he : e ^ 2 = 0) :
    eval₂ f (fun i : Fin 2 => (Polynomial.C e).coeff i.val)
      (commonTaylorNumerator 0 (equation ℚ) 3 (2 : Fin 3)) = 0 := by
  have hz : ringResidual f 0 (Polynomial.C e) (equation ℚ) = 0 := by
    simp [ringResidual, equation, ← map_pow, he]
  have hb : ∀ l < 3, 1 < l → (l.choose 1 : ℚ) ≠ 0 := by
    intro l hl hr
    have heq : l = 2 := by omega
    subst l
    norm_num
  simpa using commonTaylorNumerator_of_ringResidual f 0 (Polynomial.C e) (equation ℚ) 3
    hb (by intro l _ _; simp [hz]) (2 : Fin 3)

/-- The affine law itself remains true when characteristic kills the binomial slope. -/
example (Y : Polynomial (ZMod 2)) :
    (ringResidual (RingHom.id (ZMod 2)) 0 Y (equation (ZMod 2))).coeff 1 =
      eval₂ (RingHom.id (ZMod 2)) (fun i : Fin 2 => Y.coeff i.val)
        ((optionEquivLeft (ZMod 2) (Fin 2)
          (universalTaylorResidual 2 0 (equation (ZMod 2)))).coeff 1) := by
  simpa [show (2 : ZMod 2) = 0 by decide] using coeff_ringResidual_affine (RingHom.id (ZMod 2)) 0 Y
    (equation (ZMod 2)) 2 (by omega)

end RingResidualTests
