/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.CharacteristicSafeRadical

/-! Executed saturation states distinguish this recursion from a multiplicity decomposition. -/

open CompPoly CPolynomial CharacteristicSafeRadical

private abbrev F := ZMod 2

private def x : CPolynomial F := CPolynomial.X

private def mixed : CPolynomial F := x ^ 3 * (x + 1) ^ 2

-- The derivative-zero branch preserves its residual and contracts it through Frobenius.
example : (saturate (x ^ 4)).common = x ^ 4 := by decide +kernel
example : (saturate (x ^ 4)).visible = 1 := by decide +kernel
example : (saturate (x ^ 4)).poweredRemainder = 1 := by decide +kernel
example : (saturate (x ^ 4)).residual = x ^ 4 := by decide +kernel
example : FullSquarefreeDecomposition.contractWith 2 id (x ^ 4) = x ^ 2 := by decide +kernel
example : radical 2 id (x ^ 4) = x := by decide +kernel

-- Three visible copies of x are removed together; the even multiplicity is contracted.
example : (saturate mixed).visible = x := by decide +kernel
example : (saturate mixed).removed = x ^ 3 := by decide +kernel
example : (saturate mixed).residual = (x + 1) ^ 2 := by decide +kernel
example : radical 2 id mixed = x * (x + 1) := by decide +kernel

-- Constant input and a constant residual do not depend on inverse-Frobenius values.
example : radical 2 (fun _ : F => 0) (1 : CPolynomial F) = 1 := by decide +kernel
example : radical 2 (fun _ : F => 0) x = x := by decide +kernel
