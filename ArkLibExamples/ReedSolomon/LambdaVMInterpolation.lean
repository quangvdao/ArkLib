/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate

/-!
# LambdaVM first-order interpolation certificates

This module checks the interpolation data behind the largest equality-table row of
`lambda-beyond.json`.  It covers the initial domain of size `65536`, all eight binary-fold
domains, and the original-tuple line certificate used after undoing the DEEP quotient.

Each profile records the script's exact values of `n`, `k`, `A`, `m`, `M`, `mu`, equation
height, support dimension, local rank bound, and column-degree sum.  The verification theorem
then recomputes, inside Lean,

```text
N = firstOrderDimensionCount (k - 1) A m M mu,
r = certifiedEnlargedRankBound 1 m M 0,
n * r * (h + 1) < firstOrderHeightSlotCount (k - 1) A m M mu h.
```

The last strict inequality is the coefficient surplus for the actual canonical enumeration of
all monomials `X^x Y₀^a Y₁^b` in the finite first-order support.  The generic constructor therefore
produces a primitive symbolic interpolant whose specialization is nonzero and sound over every
extension field and every later affine-line challenge.

## Profiles

The initial row uses batching degree 17 and height 20169.  The eight fold rows have batching
degree one and heights 1180, 1154, 1130, 1041, 969, 749, 619, and 358.  The original-tuple row
has `k = 32769` and height 1191.

The batching degree is recorded to identify the source JSON row.  The certificate constructed
here is the underlying affine-line interpolation certificate.  In particular, the initial
degree-17 entry does not establish a powers-batching transfer theorem.
-/

open PolynomialDifferential

namespace ArkLibExamples.ReedSolomon.LambdaVMInterpolation

open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicBandInterpolation

noncomputable section

universe u v

/-- One first-order line-interpolation row copied from `lambda-beyond.json`. -/
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

/-- The weight assigned to `Y₀`; candidates have degree strictly below `k`. -/
def D (p : LineProfile) : ℕ := p.k - 1

/-- The support dimension recomputed from the exact finite first-order monomial set. -/
def computedDimension (p : LineProfile) : ℕ :=
  firstOrderDimensionCount p.D p.agreement p.multiplicity p.firstDerivativeCap p.totalJetCap

/-- The local first-order constraint-rank bound used at each received position. -/
def computedLocalRank (p : LineProfile) : ℕ :=
  certifiedEnlargedRankBound 1 p.multiplicity p.firstDerivativeCap 0

/-- The executable count of coefficient slots at the recorded equation height. -/
def computedHeightSlots (p : LineProfile) : ℕ :=
  firstOrderHeightSlotCount p.D p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap p.height

/-- Kernel-checked facts needed to turn a script row into a finite symbolic certificate.

The two equalities expose the actual support dimension and actual rank expression.  The slot
equality exposes the executable double sum, while `heightSurplus` is exactly the hypothesis of
the full-support certificate constructor.  The rectangular equality independently checks the
script's recorded sum of column `Y₀`-degrees.
-/
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

/-- The script's column-degree sum is the actual sum of `Y₀` exponents over the support. -/
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

/-- The canonical full-support source columns for this profile. -/
abbrev columns (p : LineProfile) :=
  firstOrderColumns (D := p.D) (A := p.agreement) (m := p.multiplicity)
    (M := p.firstDerivativeCap) (μ := p.totalJetCap)

/-- The concrete certificate type produced from a verified profile. -/
abbrev SymbolicCertificate {F : Type u} [Field F] (p : LineProfile)
    (centers : Fin p.n ↪ F) (f g : Fin p.n → F) :=
  FirstOrderSymbolicCertificate.{u, v} p.D p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap p.k p.height centers f g p.columns

/-- Every verified profile constructs an actual primitive and specialization-sound symbolic
certificate on the complete finite support. -/
theorem Verification.exists_symbolicCertificate {F : Type u} [Field F] {p : LineProfile}
    (hp : p.Verification) (centers : Fin p.n ↪ F) (f g : Fin p.n → F) :
    Nonempty (p.SymbolicCertificate.{u, v} centers f g) := by
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    hp.D_gt_one hp.budget_pos hp.degree_le centers f g hp.heightSurplus

end LineProfile

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
