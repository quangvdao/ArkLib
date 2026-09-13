/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Success

/-! Compile-time clients for residue exhaustion and checked stratum division. -/

namespace FullSquarefreeSuccessTests

open CompPoly CPolynomial Polynomial.FunctionFieldAlgorithms
open FullSquarefreeDecomposition
open FullSquarefreeDecomposition.Driver

example {F : Type*} [Field F] [BEq F] [LawfulBEq F] [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : run p f = some out) :
    out.residual = 1 :=
  residue_run_residual_eq_one p f hf out hout

example {F : Type*} [Field F] [BEq F] [LawfulBEq F] [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (M : MulContext F) (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : run p f = some out) :
    ∃ repeated, exactDivide f (weightedProduct M (pruneTagged out.strata)) =
      some repeated :=
  residue_run_exactDivide_exists p M f hf out hout

example {F : Type*} [Field F] [BEq F] [LawfulBEq F] [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (M : MulContext F) (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : run p f = some out) (repeated : CPolynomial F)
    (hdivide : exactDivide f (weightedProduct M (pruneTagged out.strata)) =
      some repeated) :
    repeated.derivative = 0 :=
  residue_run_repeated_derivative_eq_zero p M f hf out hout repeated hdivide

example {F : Type*} [Field F] [BEq F] [LawfulBEq F] [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (M : MulContext F) (f : CPolynomial F) (hf : f.monic) :
    ∃ out, prepare p inverse M f = .ok out :=
  prepare_succeeds p inverse M f hf

example {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (M : MulContext F) (f : CPolynomial F) (out : Preparation F)
    (hf : f.monic) (hfunit : f ≠ 1) (hout : prepare p inverse M f = .ok out) :
    out.contracted.natDegree < f.natDegree :=
  prepare_contracted_natDegree_lt p inverse hinverse M f out hf hfunit hout

end FullSquarefreeSuccessTests
