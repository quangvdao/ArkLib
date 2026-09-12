/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.RegularFiber
import Mathlib.Algebra.Field.ZMod

/-! Generic field acceptance and characteristic-two ordinary lifting beyond the characteristic. -/

namespace RegularFiberTests

open CPoly CompPoly ReedSolomon ReedSolomon.ListDecoding
open ReedSolomon.ListDecoding.ZerothOrderDecoder

/-- The executable exactness adapter requires no field enumeration or characteristic instance. -/
example {E F : Type*} [Field E] [BEq E] [LawfulBEq E]
    [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (Q : CMvPolynomial 2 E) (center : E)
    (hg : goodCenter Q center = true)
    (hq : ∀ P : Polynomial F, P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P.map base]
        (fromCMvPolynomial Q) = 0) :
    ∃ output, RegularFiber.run? base domain received k A Q center = some output ∧
      ExactOutput domain received k A output :=
  RegularFiber.run?_exact base domain received k A hAk Q center hg hq

private def x : CMvPolynomial 2 (ZMod 2) := CMvPolynomial.X 0
private def y : CMvPolynomial 2 (ZMod 2) := CMvPolynomial.X 1
private def domain : Fin 2 ↪ ZMod 2 where
  toFun i := i.val
  inj' := by decide

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- Exercise the actual unrestricted-characteristic producer and recovery, including unit fiber. -/
def run : IO Unit := do
  let equation := y ^ 2 + y + x
  check "binary nonlinear center rejected" (goodCenter equation 0)
  match RegularFiber.representations? equation 0 6 with
  | some [rep] =>
    check "regular binary fiber not normalized directly" <|
      rep.modulus == CPolynomial.X ^ 2 + CPolynomial.X
    -- Stored vectors are descending: theta+X+X²+X⁴ has [0,1,0,1,1,theta].
    check "binary precision six branch zero incorrect" <|
      rep.coefficients.map (CPolynomial.eval 0) == [0, 1, 0, 1, 1, 0]
    check "binary precision six branch one incorrect" <|
      rep.coefficients.map (CPolynomial.eval 1) == [0, 1, 0, 1, 1, 1]
  | _ => throw (IO.userError "binary precision six producer failed")
  check "binary ordinary agreement recovery failed" <|
    RegularFiber.run? (RingHom.id (ZMod 2)) domain ![0, 1] 2 2 (y + x) 0 == some [[1, 0]]
  check "binary high precision empty agreement list failed" <|
    RegularFiber.run? (RingHom.id (ZMod 2)) domain ![0, 1] 6 6 equation 0 == some []
  check "singular fiber failure lost" <|
    (RegularFiber.representations? (y ^ 2) 0 6).isNone
  check "zero fiber failure lost" <|
    (RegularFiber.representations? (0 : CMvPolynomial 2 (ZMod 2)) 0 6).isNone
  check "unit fiber was not a successful empty list" <|
    RegularFiber.run? (RingHom.id (ZMod 2)) domain ![0, 1] 2 2
      (1 : CMvPolynomial 2 (ZMod 2)) 0 == some []

end RegularFiberTests
