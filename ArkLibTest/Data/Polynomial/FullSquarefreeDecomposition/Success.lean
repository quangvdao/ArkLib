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

end FullSquarefreeSuccessTests
