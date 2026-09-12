/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Driver
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.NormSieve.MultiplicitySupport

/-!
# Bridge from labelled decomposition to the Hasse norm-sieve specification

The fast labelled driver and the existing Hasse-derivative implementation compute squarefree
polynomials with the same geometric roots. This file keeps the application dependency out of the
generic recursive driver.
-/

@[expose] public section

namespace CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver

open Polynomial.FunctionFieldAlgorithms
open ReedSolomon.ListDecoding.NormSieve

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]

/-- On every successful actual decomposition, threshold extraction is root-equivalent to the
existing Hasse-derivative multiplicity support over every coefficient-field extension. -/
theorem thresholdProduct_eval₂_eq_zero_iff_retainedMultiplicitySupport
    (p threshold : ℕ) [Fact p.Prime] [CharP F p] (hthreshold : 0 < threshold)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (out : Output F)
    (hout : decompose p inverse M D f = .ok out) :
    (thresholdProduct M threshold out).toPoly.eval₂ phi x = 0 ↔
      (retainedMultiplicitySupport p threshold f).toPoly.eval₂ phi x = 0 := by
  have hf := decompose_input_ne_zero p inverse M D f out hout
  rw [thresholdProduct_eval₂_eq_zero_iff_le_rootMultiplicity
      phi x p inverse M D threshold hthreshold f out hout,
    eval₂_retainedMultiplicitySupport_eq_zero_iff_le_rootMultiplicity
      p threshold phi x hf hthreshold]

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
