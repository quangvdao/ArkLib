/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.CurveProfile

/-!
# ZisK first-order interpolation certificates

This module checks every interpolation profile in `goldilocks-beyond-poseidon.json`: the initial
Poseidon2 powers row and the five folding rows on domains of sizes `65536`, `8192`, `1024`, `128`,
and `32`.

For each row, Lean evaluates the exact finite first-order support cardinality, the certified local
rank bound, and the executable column-height double sum.  It proves

```text
n * certifiedEnlargedRankBound 1 m M 0 * (h + 1)
  < firstOrderHeightSlotCount (k - 1) A m M mu h.
```

The generic full-support constructor turns this numerical surplus into a primitive symbolic
interpolant over `F[Z]`.  Its specialization remains nonzero over every extension field, and every
degree-`< k` polynomial agreeing with the specialized received line at `A` positions satisfies
the resulting differential equation.

The JSON batching degrees 181, 7, 7, 7, 7, and 3 are retained as profile metadata.  The theorem
proved here is the underlying affine-line interpolation certificate at each recorded height.  It
does not assert the separate polynomial-curve or powers-batching transfer for degrees above one.
-/

open PolynomialDifferential

namespace ArkLibExamples.ReedSolomon.ZisKInterpolation

open CurveProfile
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicBandInterpolation

noncomputable section

universe u v

/-! ## Initial powers row -/

/-- Initial Poseidon2 profile on the domain of size `524288`. -/
def initial : LineProfile where
  n := 524288
  k := 131072
  agreement := 260512
  multiplicity := 9
  firstDerivativeCap := 3
  totalJetCap := 17
  batchingDegree := 181
  supportDimension := 75053054
  localRank := 140
  columnY₀Weight := 388950086
  height := 42596
  heightSlots := 3196645991152

/-- Lean recomputes the initial support dimension, rank, height slots, and strict surplus. -/
theorem initial_verified : initial.Verification := by
  constructor <;> decide

/-- A primitive, universally specialization-sound affine-line certificate for the initial row.

This is the line certificate beneath the degree-181 powers profile; it does not prove powers
transfer.
-/
theorem exists_initial_symbolicCertificate {F : Type u} [Field F]
    (centers : Fin initial.n ↪ F) (f g : Fin initial.n → F) :
    Nonempty (initial.SymbolicCertificate.{u, v} centers f g) :=
  initial_verified.exists_symbolicCertificate centers f g

/-! ## Folding rows -/

/-- The five folding rows in decreasing domain order. -/
def folds : Fin 5 → LineProfile := ![
  { n := 65536, k := 16384, agreement := 32564, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 7,
    supportDimension := 9382246, localRank := 140, columnY₀Weight := 48624814,
    height := 1642, heightSlots := 15366405364 },
  { n := 8192, k := 2048, agreement := 4071, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 7,
    supportDimension := 1173692, localRank := 140, columnY₀Weight := 6086468,
    height := 1589, heightSlots := 1860083812 },
  { n := 1024, k := 256, agreement := 509, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 7,
    supportDimension := 147400, localRank := 140, columnY₀Weight := 767440,
    height := 1329, heightSlots := 195274560 },
  { n := 128, k := 32, agreement := 64, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 7,
    supportDimension := 19262, localRank := 140, columnY₀Weight := 103718,
    height := 541, heightSlots := 10336286 },
  { n := 32, k := 8, agreement := 16, multiplicity := 9,
    firstDerivativeCap := 3, totalJetCap := 17, batchingDegree := 3,
    supportDimension := 5342, localRank := 140, columnY₀Weight := 31118,
    height := 108, heightSlots := 551160 }
]

/-- Every folding row has its claimed actual dimension, rank, height count, and strict surplus. -/
theorem folds_verified : ∀ i, (folds i).Verification := by
  intro i
  fin_cases i <;> constructor <;> decide

/-- Every folding row produces an actual primitive and specialization-sound symbolic line
certificate.  The recorded batching degrees identify the script rows but require a separate
transfer theorem. -/
theorem exists_fold_symbolicCertificate {F : Type u} [Field F] (i : Fin 5)
    (centers : Fin (folds i).n ↪ F) (f g : Fin (folds i).n → F) :
    Nonempty ((folds i).SymbolicCertificate.{u, v} centers f g) :=
  (folds_verified i).exists_symbolicCertificate centers f g

end

end ArkLibExamples.ReedSolomon.ZisKInterpolation
