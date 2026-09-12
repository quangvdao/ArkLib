/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.RefinementSuccess

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

end FullSquarefreeRefinementSuccessTests
