/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.TaylorReconstruction.ClearedCoefficients
import ArkLib.Data.MvPolynomial.BoxAlgebra

/-! Executed denominator clearing and a nonreduced-ring recurrence client. -/

namespace ClearedCoefficientsTests

open CPoly CPoly.BoxAlgebra CPoly.TaylorReconstruction.ClearedCoefficients

private abbrev A := Carrier 2 2 ℤ
private def e : A := eps 0 + eps 1

/-- The recurrence bridge works without treating the target ring as a field. -/
example {B : Type*} [CommRing B] (f : ℚ →+* B) (s : B) :
    -f (2⁻¹) * MvPolynomial.clearedSubstitution f s
      (fun _ : Fin 1 => s * (f 2 * s)) (fun _ => 1) 1 (MvPolynomial.X 0) =
      s ^ 2 * (-1) := by
  apply cleared_recurrence_step f s _ (fun _ : Fin 1 => f 2 * s) _ 1 _ 2 (by norm_num) (-1)
  · intro i
    simp
  · intro m hm
    have he : m = Finsupp.single 0 1 := by
      simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hm
    subst m
    simp [Finsupp.weight_apply]
  · simp

/-- Check actual separant powers, mixed terms, cleared products, and agreement factoring. -/
def run : IO Unit := do
  let s := 1 + e
  let c : Fin 2 → A := ![1 + eps 0, 2 + eps 1]
  let packet := clear s c
  unless packet.1 == 1 + 4 * e + 6 * e ^ 2 do
    throw (IO.userError "denominator did not compute the separant fourth power")
  unless packet.1.val.coeff #m[1, 1] == 12 do
    throw (IO.userError "clearing lost a mixed nilpotent coefficient")
  unless packet.2 0 == packet.1 * c 0 && packet.2 1 == packet.1 * c 1 do
    throw (IO.userError "cleared coefficients are not the computed products")
  unless packet.2 0 + packet.2 1 * 3 - 5 * packet.1 ==
      packet.1 * (c 0 + c 1 * 3 - 5) do
    throw (IO.userError "cleared agreement identity failed")
  unless (clear s (Fin.elim0 : Fin 0 → A)).1 == 1 do
    throw (IO.userError "zero-width clearing has the wrong denominator")

end ClearedCoefficientsTests
