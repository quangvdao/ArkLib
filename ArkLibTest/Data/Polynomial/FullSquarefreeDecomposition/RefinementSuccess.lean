/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.RefinementSuccess
import Mathlib.Algebra.Field.ZMod

/-! Compile-time client for weighted tagged routing reconstruction. -/

namespace FullSquarefreeRefinementSuccessTests

open CompPoly CPolynomial
open FullSquarefreeDecomposition
open FullSquarefreeDecomposition.Driver
open CPolynomial.BatchRemainder

example {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    factorProduct ((routeTagged M D t pieces).map fun z => (z.1, z.2.2)) =
      factorProduct pieces :=
  routeTagged_factorProduct_exact M D t pieces hm

example {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : ℕ) (M : MulContext F) (D : ModContext F)
    (strata recursive : List (ℕ × CPolynomial F))
    (hstrataMonic : ∀ z ∈ strata, z.2.monic)
    (hstrataSquarefree : Squarefree ((strata.map Prod.snd).prod).toPoly)
    (hrecursiveMonic : ∀ z ∈ recursive, z.2.monic) :
    ∃ factors, refineFactors p M D strata recursive = some factors :=
  refineFactors_succeeds p M D strata recursive hstrataMonic
    hstrataSquarefree hrecursiveMonic

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

/-- Exercise mixed intersections together with residue-only and recursive-only leaves. -/
def run : IO Unit := do
  let x : CPolynomial F := X
  let M := MulContext.naive (R := F)
  let D := ModContext.naive (R := F)
  let strata :=
    [(1, x * (x - 1) * (x - 6)), (2, (x - 2) * (x - 3))]
  let recursive :=
    [(1, x * (x - 2) * (x - 4)), (2, (x - 1) * (x - 3) * (x - 5))]
  let some factors := refineFactors 7 M D strata recursive
    | throw (IO.userError "refinement unexpectedly failed")
  for z in [(8, x), (15, x - 1), (9, x - 2), (16, x - 3),
      (1, x - 6), (7, x - 4), (14, x - 5)] do
    unless factors.contains z do
      throw (IO.userError s!"refinement lost labelled factor {z.1}")
  unless factorProduct factors =
      factorProduct strata * factorProduct recursive ^ 7 do
    throw (IO.userError "refinement failed weighted reconstruction")

end FullSquarefreeRefinementSuccessTests
