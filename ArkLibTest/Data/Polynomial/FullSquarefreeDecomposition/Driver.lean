/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Driver
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! Execute mixed integer multiplicities, repeated contraction and actual-label thresholding. -/
namespace FullSquarefreeDriverTests
open CompPoly CPolynomial FullSquarefreeDecomposition.Driver
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

/-- Mixed `1,2,p,p+2,p²` multiplicities require two recursive inverse-Frobenius levels. -/
def run : IO Unit := do
  let x : CPolynomial F := X
  let M := MulContext.naive (R := F)
  let D := ModContext.naive (R := F)
  let f := C (3 : F) * x * (x - 1) ^ 2 * (x - 2) ^ 5 * (x - 3) ^ 7 * (x - 4) ^ 25
  let .ok out := decomposePrime 5 M D f
    | throw (IO.userError "mixed recursive decomposition failed")
  unless out.scalar == 3 do
    throw (IO.userError "decomposition lost the scalar unit")
  unless out.factors.length == 5 do
    throw (IO.userError "decomposition failed to group exact integer labels")
  for z in [(1, x), (2, x - 1), (5, x - 2), (7, x - 3), (25, x - 4)] do
    unless out.factors.contains z do
      throw (IO.userError s!"missing or incorrect multiplicity {z.1}")
  unless C out.scalar * factorProduct out.factors == f do
    throw (IO.userError "weighted decomposition does not reconstruct the input")
  unless out.stages.map Stage.inputDegree == [40, 7, 1] &&
      out.stages.map Stage.contractedDegree == [7, 1, 0] do
    throw (IO.userError "recursive driver did not execute the expected Frobenius contractions")
  unless thresholdProduct M 5 out == (x - 2) * (x - 3) * (x - 4) do
    throw (IO.userError "multiplicity-five threshold lost characteristic-divisible roots")
  unless thresholdProduct M 6 out == (x - 3) * (x - 4) do
    throw (IO.userError "threshold used residues instead of full integer labels")
  unless thresholdProduct M 26 out == 1 do
    throw (IO.userError "empty threshold support is not one")
  let .ok constant := decomposePrime 5 M D (C (3 : F))
    | throw (IO.userError "nonzero constant decomposition failed")
  unless constant.scalar == 3 && constant.factors.isEmpty && constant.stages.isEmpty do
    throw (IO.userError "constant policy lost its scalar or introduced factors")
  match decomposePrime 5 M D (0 : CPolynomial F) with
  | .error .zeroInput => pure ()
  | _ => throw (IO.userError "zero input did not receive the explicit zero policy")
  -- `X² + 2` has no F5 root. Its labelled factor therefore checks that the residue
  -- and refinement stages do not classify only roots visible in the base field.
  let quadratic := x ^ 2 + C (2 : F)
  let extensionOnly := quadratic ^ 3 * (x - 1) ^ 5
  let .ok extensionOut := decomposePrime 5 M D extensionOnly
    | throw (IO.userError "extension-only factor decomposition failed")
  unless extensionOut.factors.contains (3, quadratic) &&
      extensionOut.factors.contains (5, x - 1) do
    throw (IO.userError "extension-only roots lost their integer multiplicity")

namespace BinaryExtension

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private abbrev Base := ZMod 2

/-- `X² + X + 1` supplies the concrete polynomial-basis presentation of F4. -/
private abbrev modulus : CPolynomial Base := X ^ 2 + X + C 1

private instance : Fact modulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [modulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  convert Polynomial.monic_X_pow_add (n := 2)
    (p := Polynomial.X + Polynomial.C (1 : Base))
    (by rw [Polynomial.degree_X_add_C]; decide) using 1
  ring⟩

private theorem modulus_degree : modulus.natDegree = 2 := by
  rw [CPolynomial.natDegree_toPoly]
  simp only [modulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  simpa using (Polynomial.natDegree_quadratic (R := Base)
    (a := 1) (b := 1) (c := 1) one_ne_zero)

private theorem modulus_irreducible : Irreducible modulus.toPoly := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro a ha
    have hroot := (Polynomial.mem_roots' (p := modulus.toPoly)).mp ha
    have heval : a ^ 2 + a + 1 = 0 := by
      simpa [modulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
        CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.IsRoot] using hroot.2
    have haval : a = (a.val : Base) := (ZMod.natCast_zmod_val a).symm
    have halt := a.val_lt
    interval_cases h : a.val
    all_goals rw [haval] at heval
    case «0» => exact (show (0 : Base) ^ 2 + 0 + 1 ≠ 0 by decide) heval
    case «1» => exact (show (1 : Base) ^ 2 + 1 + 1 ≠ 0 by decide) heval
  · rw [← CPolynomial.natDegree_toPoly]
    rw [modulus_degree]
  · rw [← CPolynomial.natDegree_toPoly]
    rw [modulus_degree]
    decide

private instance : Fact (Irreducible modulus.toPoly) := ⟨modulus_irreducible⟩

open ArkLib.FiniteField.ExplicitConstruction
private abbrev F4 := Carrier modulus

/-- The supplied F4 path takes two derivative-zero contractions and its inverse Frobenius
changes the polynomial-basis generator. -/
def run : IO Unit := do
  let x : CPolynomial F4 := X
  let theta : F4 := frobeniusTheta 2 modulus
  unless inverseFrobenius 2 modulus theta != theta do
    throw (IO.userError "F4 inverse Frobenius unexpectedly acted as the identity")
  let f := (x - C theta) ^ 4 * (x - C (theta + 1)) ^ 3
  let M := MulContext.naive (R := F4)
  let D := ModContext.naive (R := F4)
  let .ok out := decomposeSupplied 2 modulus M D f
    | throw (IO.userError "supplied F4 decomposition failed")
  unless out.factors.contains (4, x - C theta) &&
      out.factors.contains (3, x - C (theta + 1)) do
    throw (IO.userError "supplied F4 labels do not match integer multiplicities")
  unless out.stages.map Stage.inputDegree == [7, 3, 1] &&
      out.stages.map Stage.contractedDegree == [3, 1, 0] do
    throw (IO.userError "supplied F4 path skipped a Frobenius recursion level")

end BinaryExtension

end FullSquarefreeDriverTests
