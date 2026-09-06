/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate

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

open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicBandInterpolation

noncomputable section

universe u v

/-- One first-order line-interpolation row copied from `goldilocks-beyond-poseidon.json`. -/
structure LineProfile where
  n : ℕ
  k : ℕ
  agreement : ℕ
  multiplicity : ℕ
  firstDerivativeCap : ℕ
  totalJetCap : ℕ
  batchingDegree : ℕ
  supportDimension : ℕ
  localRank : ℕ
  columnY₀Weight : ℕ
  height : ℕ
  heightSlots : ℕ
  deriving DecidableEq, Repr

namespace LineProfile

/-- The exact candidate-degree weight used by the finite first-order support. -/
def D (p : LineProfile) : ℕ := p.k - 1

/-- The support dimension recomputed from the finite monomial constraints. -/
def computedDimension (p : LineProfile) : ℕ :=
  firstOrderDimensionCount p.D p.agreement p.multiplicity p.firstDerivativeCap p.totalJetCap

/-- The certified rank contribution of one received position. -/
def computedLocalRank (p : LineProfile) : ℕ :=
  certifiedEnlargedRankBound 1 p.multiplicity p.firstDerivativeCap 0

/-- The executable count of polynomial coefficient slots at the recorded height. -/
def computedHeightSlots (p : LineProfile) : ℕ :=
  firstOrderHeightSlotCount p.D p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap p.height

/-- Exact arithmetic connecting a pinned row to the actual finite first-order support and
certificate constructor. -/
structure Verification (p : LineProfile) : Prop where
  D_gt_one : 1 < p.D
  budget_pos : 0 < p.multiplicity * p.agreement
  degree_le : p.k ≤ p.D + 1
  cap_le_height : p.totalJetCap ≤ p.height
  dimension_eq : p.computedDimension = p.supportDimension
  localRank_eq : p.computedLocalRank = p.localRank
  heightSlots_eq : p.computedHeightSlots = p.heightSlots
  columnWeight_eq : p.heightSlots + p.columnY₀Weight = p.supportDimension * (p.height + 1)
  heightSurplus : p.n * p.computedLocalRank * (p.height + 1) < p.computedHeightSlots

/-- The recorded `N` is the cardinality of the actual constrained monomial support. -/
theorem Verification.support_card_eq {p : LineProfile} (hp : p.Verification) :
    (firstOrderExponents p.D p.agreement p.multiplicity p.firstDerivativeCap
      p.totalJetCap).card = p.supportDimension := by
  rw [card_firstOrderExponents_eq_dimensionCount (Nat.zero_lt_of_lt hp.D_gt_one)]
  simpa [computedDimension] using hp.dimension_eq

/-- The recorded column-degree sum is the actual sum of `Y₀` exponents over the support. -/
theorem Verification.columnY₀Weight_eq {p : LineProfile} (hp : p.Verification) :
    p.columnY₀Weight = firstOrderY₀Weight p.D p.agreement p.multiplicity
      p.firstDerivativeCap p.totalJetCap := by
  have hrectangle := firstOrderColumnSlotCount_add_y₀Weight
    (D := p.D) (A := p.agreement) (m := p.multiplicity)
    (M := p.firstDerivativeCap) (μ := p.totalJetCap) (h := p.height) hp.cap_le_height
  have hslots : firstOrderHeightSlotCount p.D p.agreement p.multiplicity
      p.firstDerivativeCap p.totalJetCap p.height = p.heightSlots := by
    simpa [computedHeightSlots] using hp.heightSlots_eq
  rw [firstOrderColumnSlotCount_eq_heightSlotCount (Nat.zero_lt_of_lt hp.D_gt_one),
    hslots, hp.support_card_eq] at hrectangle
  exact Nat.add_left_cancel (hp.columnWeight_eq.trans hrectangle.symm)

/-- The canonical enumeration of the complete finite support. -/
abbrev columns (p : LineProfile) :=
  firstOrderColumns (D := p.D) (A := p.agreement) (m := p.multiplicity)
    (M := p.firstDerivativeCap) (μ := p.totalJetCap)

/-- The actual symbolic-certificate type belonging to a pinned row. -/
abbrev SymbolicCertificate {F : Type u} [Field F] (p : LineProfile)
    (centers : Fin p.n ↪ F) (f g : Fin p.n → F) :=
  FirstOrderSymbolicCertificate.{u, v} p.D p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap p.k p.height centers f g p.columns

/-- A verified row produces a primitive certificate whose line specializations are uniformly
nonzero and sound. -/
theorem Verification.exists_symbolicCertificate {F : Type u} [Field F] {p : LineProfile}
    (hp : p.Verification) (centers : Fin p.n ↪ F) (f g : Fin p.n → F) :
    Nonempty (p.SymbolicCertificate.{u, v} centers f g) := by
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    hp.D_gt_one hp.budget_pos hp.degree_le centers f g hp.heightSurplus

end LineProfile

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
