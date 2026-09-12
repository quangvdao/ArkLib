/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedAdapter
import Mathlib.Algebra.Field.ZMod

/-! Focused checks for the supplied-field zeroth-order composition boundary. -/

namespace SuppliedAdapterTests

open CompPoly Polynomial ReedSolomon ReedSolomon.ListDecoding
open ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
open ReedSolomon.ListDecoding.ZerothOrderDecoder
open ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedAdapter

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def cmpZMod5 : ZMod 5 → ZMod 5 → Ordering := fun a b => compare a.val b.val

private instance : Std.TransCmp cmpZMod5 where
  eq_swap := by
    intro a b
    exact Std.OrientedCmp.eq_swap (cmp := compare) (a := a.val) (b := b.val)
  isLE_trans := by
    intro a b c hab hbc
    exact Std.TransCmp.isLE_trans (cmp := compare) hab hbc

private instance : Std.LawfulEqCmp cmpZMod5 where
  eq_of_compare := by
    intro a b hab
    apply ZMod.val_injective
    exact Std.LawfulEqCmp.eq_of_compare (cmp := compare) hab

private def storedEquation : CBivariate (ZMod 5) :=
  (CPolynomial.X : CBivariate (ZMod 5)) +
    CPolynomial.C (CPolynomial.X : CPolynomial (ZMod 5))

private def domain : Fin 4 ↪ ZMod 5 where
  toFun i := i.val
  inj' := by
    intro i j h
    apply Fin.ext
    simpa [ZMod.val_natCast_of_lt (by omega : (i : ℕ) < 5),
      ZMod.val_natCast_of_lt (by omega : (j : ℕ) < 5)] using congrArg ZMod.val h

/-- The constant exactness client does not require a normalization package. -/
example :
    ∃ output,
      run? cmpZMod5 (RingHom.id (ZMod 5)) domain ![1, 2, 1, 1] 1 3 none = some output ∧
        ExactOutput domain ![1, 2, 1, 1] 1 3 output :=
  run?_one_exact cmpZMod5 (RingHom.id (ZMod 5)) domain ![1, 2, 1, 1] 3 (by omega) none

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- Exercise literal stored-fiber conversion and the frequency-first dispatch. -/
def run : IO Unit := do
  check "regular equation fiber conversion failed" <|
    sectionPolynomial (regularEquation ({
      original := storedEquation
      support := storedEquation
      discarded := 1
      regular := storedEquation
      obstruction := 1
    } : NormalizationData (ZMod 5))) 2 == CPolynomial.X + CPolynomial.C 2
  check "k=1 did not bypass absent normalization" <|
    SuppliedAdapter.run? cmpZMod5 (RingHom.id (ZMod 5)) domain ![1, 2, 1, 1]
      1 3 none == some [[1]]

#print axioms sectionPolynomial_regularEquation
#print axioms goodCenter_regularEquation
#print axioms CheckedInput.run?_exact
#print axioms run?_one_exact

end SuppliedAdapterTests
