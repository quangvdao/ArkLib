/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.UniformFirstOrder

/-!
# Checks for the uniform first-order certificate

These examples exercise the smallest admissible block-code parameters.  The first reaches the
shifted height-851 constructor at `k = 2`; the second checks that the public theorem also covers
the constant-message edge `k = 1` without exposing a numerical premise.
-/

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode

example :
    firstOrderCurveShiftedRowSlotBound (max (2 - 1) 2) 3 12 4 22 3 1 851 <
      firstOrderCurveShiftedHeightSlotCount (max (2 - 1) 2) 3 12 4 22 1 851 := by
  exact (uniformFirstOrder_parameters 3 2 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2.2.2

example {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 2 ↪ F) (received : Fin 2 → F)
    (hchar : ringChar F = 0 ∨ 22 < ringChar F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received 1 2) ∧
      list.card ≤ 13623 * 2 := by
  exact exists_uniformFirstOrder_list 2 1 2 domain received
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using hchar)

/-- The elementary `k = 1` branch retains one exceptional set and equality of the complete
agreement set, with the same public quadratic budget. -/
example {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 2 ↪ F) (f g : Fin 2 → F)
    (hchar : ringChar F = 0 ∨ 22 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 571487759 * (2 : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 1 →
        2 ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) 1 z P := by
  exact exists_uniformFirstOrder_lineMCA 2 1 2 domain f g
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using hchar)

/-- The public affine-family corollary keeps the quadratic exceptional budget and incurs only the
dimension-independent `|F| - 1` denominator. -/
example {F : Type} [Field F] [Fintype F]
    (n k A s : ℕ) (domain : Fin n ↪ F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : ringChar F = 0 ∨ max n 22 < ringChar F)
    (hs : 1 ≤ s) (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineSpaceGenerator F s) (code domain k) radius ≤
      ENNReal.ofReal
        (571487759 * (n : ℝ) ^ 2 / ((Fintype.card F : ℝ) - 1)) := by
  exact mcaError_affineSpace_uniformFirstOrder_le n k A s domain
    hn hk hAn hgap hchar hs radius hthreshold

end ReedSolomon
