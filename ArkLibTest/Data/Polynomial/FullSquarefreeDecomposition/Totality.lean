/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Totality

/-! Compile-time clients for unconditional full squarefree decomposition success. -/

namespace FullSquarefreeTotalityTests

open CompPoly CPolynomial FullSquarefreeDecomposition.Driver

example {F : Type*} [Field F] [BEq F] [LawfulBEq F] [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (hf : f ≠ 0) :
    ∃ out, decompose p inverse M D f = .ok out :=
  decompose_succeeds p inverse hinverse M D f hf

example (p : ℕ) [Fact p.Prime]
    (M : MulContext (ZMod p)) (D : ModContext (ZMod p))
    (f : CPolynomial (ZMod p)) (hf : f ≠ 0) :
    ∃ out, decomposePrime p M D f = .ok out :=
  decomposePrime_succeeds p M D f hf

example {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F) :
    decompose p inverse M D (0 : CPolynomial F) = .error .zeroInput :=
  decompose_zero p inverse M D

end FullSquarefreeTotalityTests
