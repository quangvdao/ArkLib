/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.CurveProfile

/-!
# LambdaVM first-order interpolation certificates

This module checks the interpolation data behind the largest equality-table row of
`lambda-beyond.json`.  It covers the initial domain of size `65536`, all eight binary-fold
domains, and the original-tuple line certificate used after undoing the DEEP quotient.

Each profile records the script's exact values of `n`, `k`, `A`, `m`, `M`, `mu`, equation
height, support dimension, local rank bound, and column-degree sum. The line verification checks

```text
firstOrderCurveShiftedRowSlotBound (k - 1) A m M mu n 1 h
  < firstOrderCurveShiftedHeightSlotCount (k - 1) A m M mu 1 h.
```

This is the coefficient surplus for the actual canonical enumeration of all monomials
`X^x Y₀^a Y₁^b` in the finite first-order support. The constructor therefore
produces a primitive symbolic interpolant whose specialization is nonzero and sound over every
extension field and every later affine-line challenge.

## Profiles

The initial row uses batching degree 17 and height 20169.  The eight fold rows have batching
degree one and heights 1180, 1154, 1130, 1041, 969, 749, 619, and 358.  The original-tuple row
has `k = 32769` and height 1191.

The initial row is checked both as an affine line and as an actual degree-17 polynomial curve.
The remaining rows expose their affine-line certificates.
-/

open PolynomialDifferential Polynomial

namespace ArkLibExamples.ReedSolomon.LambdaVMInterpolation

open CurveProfile
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicWeightedSupportInterpolation

noncomputable section

universe u v

/-! ## Initial powers row -/

/-- Initial powers row: `n = 65536`, `k = 32768`, and `A = 45910`. -/
def initial : LineProfile where
  n := 65536
  k := 32768
  agreement := 45910
  multiplicity := 22
  firstDerivativeCap := 6
  totalJetCap := 30
  batchingDegree := 17
  supportDimension := 92454740
  localRank := 1400
  columnY₀Weight := 835652580
  height := 20169
  heightSlots := 1863976453220

/-- Lean recomputes the initial support dimension, rank, height slots, and strict surplus. -/
theorem initial_verified : initial.Verification := by
  constructor <;> decide

/-- A primitive, universally specialization-sound affine-line certificate for the initial row.

The result certifies the line interpolation input to the powers argument; it does not supply the
separate degree-17 powers transfer.
-/
theorem exists_initial_symbolicCertificate {F : Type u} [Field F]
    (centers : Fin initial.n ↪ F) (f g : Fin initial.n → F) :
    Nonempty (initial.SymbolicCertificate.{u, v} centers f g) :=
  initial_verified.exists_symbolicCertificate centers f g

/-- Lean checks the initial row's shifted degree-17 source and compressed-row surplus. -/
theorem initial_curveVerified : initial.CurveVerification := by decide

/-- The initial LambdaVM row constructs its full degree-17 polynomial-curve certificate. -/
theorem exists_initial_curveCertificate {F : Type u} [Field F]
    (centers : Fin initial.n ↪ F) (w : Fin initial.n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ initial.batchingDegree) :
    Nonempty (FirstOrderCurveCertificate initial.D initial.agreement initial.multiplicity
      initial.firstDerivativeCap initial.totalJetCap initial.k initial.height centers w
      initial.columns) :=
  initial_curveVerified.exists_certificate centers w hw

/-! ## Binary-fold rows -/

/-- The eight binary-fold rows, in decreasing domain order from `32768` to `256`. -/
def folds : Fin 8 → LineProfile := ![
  { n := 32768, k := 16384, agreement := 22955, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 46229260, localRank := 1400, columnY₀Weight := 417858140,
    height := 1180, heightSlots := 54178897920 },
  { n := 16384, k := 8192, agreement := 11478, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 23118676, localRank := 1400, columnY₀Weight := 208990180,
    height := 1154, heightSlots := 26493080600 },
  { n := 8192, k := 4096, agreement := 5739, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 11561228, localRank := 1400, columnY₀Weight := 104526940,
    height := 1130, heightSlots := 12971221928 },
  { n := 4096, k := 2048, agreement := 2870, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 5784660, localRank := 1400, columnY₀Weight := 52324580,
    height := 1041, heightSlots := 5975291140 },
  { n := 2048, k := 1024, agreement := 1435, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 2894220, localRank := 1400, columnY₀Weight := 26194140,
    height := 969, heightSlots := 2781199260 },
  { n := 1024, k := 512, agreement := 718, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 1451156, localRank := 1400, columnY₀Weight := 13158180,
    height := 749, heightSlots := 1075208820 },
  { n := 512, k := 256, agreement := 359, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 727468, localRank := 1400, columnY₀Weight := 6610940,
    height := 619, heightSlots := 444419220 },
  { n := 256, k := 128, agreement := 180, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 367780, localRank := 1400, columnY₀Weight := 3366580,
    height := 358, heightSlots := 128666440 }
]

/-- Every binary-fold row has its claimed actual support dimension, rank, height count, and
strict coefficient surplus. -/
theorem folds_verified : ∀ i, (folds i).Verification := by
  intro i
  fin_cases i <;> constructor <;> decide

/-- Each binary-fold row produces its actual complete-support symbolic line certificate. -/
theorem exists_fold_symbolicCertificate {F : Type u} [Field F] (i : Fin 8)
    (centers : Fin (folds i).n ↪ F) (f g : Fin (folds i).n → F) :
    Nonempty ((folds i).SymbolicCertificate.{u, v} centers f g) :=
  (folds_verified i).exists_symbolicCertificate centers f g

/-! ## Original-tuple line row -/

/-- Line row for the original tuple after restoring the constant removed by the DEEP quotient. -/
def originalTuple : LineProfile where
  n := 65536
  k := 32769
  agreement := 45910
  multiplicity := 22
  firstDerivativeCap := 6
  totalJetCap := 30
  batchingDegree := 1
  supportDimension := 92451520
  localRank := 1400
  columnY₀Weight := 835596090
  height := 1191
  heightSlots := 109366615750

/-- Lean recomputes the original-tuple support dimension, rank, height slots, and surplus. -/
theorem originalTuple_verified : originalTuple.Verification := by
  constructor <;> decide

/-- The original-tuple row produces an actual complete-support symbolic line certificate. -/
theorem exists_originalTuple_symbolicCertificate {F : Type u} [Field F]
    (centers : Fin originalTuple.n ↪ F) (f g : Fin originalTuple.n → F) :
    Nonempty (originalTuple.SymbolicCertificate.{u, v} centers f g) :=
  originalTuple_verified.exists_symbolicCertificate centers f g

end

end ArkLibExamples.ReedSolomon.LambdaVMInterpolation
