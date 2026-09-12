/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Degree

/-! Compile-time clients for threshold-product degree bounds. -/

namespace FullSquarefreeDegreeTests

open CompPoly CPolynomial FullSquarefreeDecomposition.Driver

example {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (threshold : ℕ)
    (f : CPolynomial F) (out : Output F)
    (hout : decompose p inverse M D f = .ok out) :
    threshold * (thresholdProduct M threshold out).natDegree ≤ f.natDegree :=
  thresholdProduct_degree_le p inverse M D threshold f out hout

example (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : ModContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (threshold : ℕ)
    (f : CPolynomial (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (out : Output (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (hout : decomposeSupplied p modulus M D f = .ok out) :
    threshold * (thresholdProduct M threshold out).natDegree ≤ f.natDegree :=
  decomposeSupplied_thresholdProduct_degree_le
    p modulus M D threshold f out hout

end FullSquarefreeDegreeTests
