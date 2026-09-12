/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.NormSieveBridge

/-! Compile-time client for the labelled-decomposition/Hasse threshold bridge. -/

namespace FullSquarefreeNormSieveBridgeTests

open CompPoly CPolynomial Polynomial.FunctionFieldAlgorithms
open FullSquarefreeDecomposition.Driver
open ReedSolomon.ListDecoding.NormSieve

example {F K : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    [Field K] (p threshold : ℕ) [Fact p.Prime] [CharP F p]
    (hthreshold : 0 < threshold) (phi : F →+* K) (x : K)
    (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (out : Output F)
    (hout : decompose p inverse M D f = .ok out) :
    (thresholdProduct M threshold out).toPoly.eval₂ phi x = 0 ↔
      (retainedMultiplicitySupport p threshold f).toPoly.eval₂ phi x = 0 :=
  thresholdProduct_eval₂_eq_zero_iff_retainedMultiplicitySupport
    p threshold hthreshold phi x inverse M D f out hout

end FullSquarefreeNormSieveBridgeTests
