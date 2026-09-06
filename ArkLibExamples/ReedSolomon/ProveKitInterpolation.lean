/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate

/-!
# ProveKit parameters instantiate the actual interpolation theorem

The arithmetic in `ProveKit` checks the consequences of supplied list and exceptional
counts. Here we derive the underlying interpolation certificates from ArkLib's mathematics.
For both rows, the exact monomial count exceeds the number of independent local
constraints. The chosen challenge heights also pass the column-sensitive coefficient test.

## Reading the statements

Both codes have `n = 1048576`, `k = 262144`, and `D = k-1`. Their agreement thresholds
are below the finite Johnson threshold, as checked in `ProveKit`. The multiplicity,
derivative cap, and total jet cap differ between the two interpolation supports.

The dimension and height sums below are definitions already proved equal to the actual
support counts. The rank budget is already proved to bound the actual constraint map.
Consequently the interpolation existence conclusions hold for every field and received
word with these parameters; they do not assume a successful external certificate.

The original envelope rank suffices for these profiles. The sharper cutoff-sensitive
rank formula could improve other choices but is unnecessary to validate these supports.
Interpolation is the algebraic input to list counting and MCA, not either conclusion alone.
-/

open PolynomialDifferential
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

set_option maxRecDepth 4096

/-- Exact number of allowed monomials in the BN254 profile's support. -/
theorem bn254_interpolation_dimension :
    firstOrderDimensionCount 262143 492831 384 168 688 = 9056412854060 := by decide

/-- The certified envelope rank at one received point in the BN254 profile. -/
theorem bn254_interpolation_rank : certifiedEnlargedRankBound 1 384 168 0 = 8635900 := by
  decide

/-- Exact support count for the revised cubic Goldilocks row. -/
theorem goldilocksCubic113_interpolation_dimension :
    firstOrderDimensionCount 262143 508263 16 7 30 = 828594536 := by decide

/-- Coarse local rank expression recorded alongside the revised shifted-rank profile. -/
theorem goldilocksCubic113_interpolation_rank :
    certifiedEnlargedRankBound 1 16 7 0 = 780 := by decide

/-- Historical 115-query support retained until its semantic clients migrate to the shifted
finite constructor. -/
theorem goldilocksCubic_interpolation_dimension :
    firstOrderDimensionCount 262143 512754 13 5 24 = 433269050 := by decide

/-- The certified envelope rank at one received point in the cubic Goldilocks profile. -/
theorem goldilocksCubic_interpolation_rank : certifiedEnlargedRankBound 1 13 5 0 = 406 := by
  decide

/-- The BN254 profile has more coefficients than independent global constraints. -/
theorem bn254_interpolation_surplus :
    1048576 * certifiedEnlargedRankBound 1 384 168 0 <
      firstOrderDimensionCount 262143 492831 384 168 688 := by
  rw [bn254_interpolation_dimension, bn254_interpolation_rank]
  norm_num

/-- The cubic Goldilocks profile has a strict global interpolation surplus. -/
theorem goldilocksCubic_interpolation_surplus :
    1048576 * certifiedEnlargedRankBound 1 13 5 0 <
      firstOrderDimensionCount 262143 512754 13 5 24 := by
  rw [goldilocksCubic_interpolation_dimension, goldilocksCubic_interpolation_rank]
  norm_num

/-- Height 1905902 passes the actual column-sensitive scalar coefficient test. -/
theorem bn254_interpolation_height :
    1048576 * certifiedEnlargedRankBound 1 384 168 0 * (1905902 + 1) <
      firstOrderHeightSlotCount 262143 492831 384 168 688 1905902 := by
  rw [bn254_interpolation_rank]
  decide

/-- Height 423 passes the historical column test. The revised height 339 requires the shifted
row-profile constructor, whose translated-kernel bridge is a separate prerequisite. -/
theorem goldilocksCubic_interpolation_height :
    1048576 * certifiedEnlargedRankBound 1 13 5 0 * (423 + 1) <
      firstOrderHeightSlotCount 262143 512754 13 5 24 423 := by
  rw [goldilocksCubic_interpolation_rank]
  decide

/-- At the BN254 profile's parameters, every received word has a nonzero supported
interpolant satisfying all actual local constraints, over an arbitrary field. -/
theorem bn254_exists_interpolant {F : Type*} [Field F]
    (centers received : Fin 1048576 → F) :
    ∃ Q : DifferentialPolynomial F 1, Q ≠ 0 ∧
      Q ∈ firstOrderSpace F 262143 492831 384 168 688 ∧
      ∀ i, SatisfiesLocalConstraints 384 (centers i) (received i) Q := by
  apply exists_nonzero_firstOrder_interpolant_of_dimensionCount
    (by norm_num : 1 < 262143) centers received
  simpa only [Fintype.card_fin] using bn254_interpolation_surplus

/-- The cubic Goldilocks profile likewise instantiates the genuine interpolation theorem. -/
theorem goldilocksCubic_exists_interpolant {F : Type*} [Field F]
    (centers received : Fin 1048576 → F) :
    ∃ Q : DifferentialPolynomial F 1, Q ≠ 0 ∧
      Q ∈ firstOrderSpace F 262143 512754 13 5 24 ∧
      ∀ i, SatisfiesLocalConstraints 13 (centers i) (received i) Q := by
  apply exists_nonzero_firstOrder_interpolant_of_dimensionCount
    (by norm_num : 1 < 262143) centers received
  simpa only [Fintype.card_fin] using goldilocksCubic_interpolation_surplus

/-- The full primitive symbolic certificate at the BN254 profile's parameters.
One polynomial works for every challenge and every close candidate over every field extension. -/
theorem bn254_exists_symbolicCertificate {F : Type*} [Field F]
    (centers : Fin 1048576 ↪ F) (f g : Fin 1048576 → F) :
    Nonempty (FirstOrderSymbolicCertificate 262143 492831 384 168 688 262144 1905902
      centers f g (SymbolicBandInterpolation.firstOrderColumns
        (D := 262143) (A := 492831) (m := 384) (M := 168) (μ := 688))) := by
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (by norm_num) (by norm_num) (by norm_num) centers f g bn254_interpolation_height

/-- The cubic Goldilocks profile also yields a full primitive specialization-sound certificate. -/
theorem goldilocksCubic_exists_symbolicCertificate {F : Type*} [Field F]
    (centers : Fin 1048576 ↪ F) (f g : Fin 1048576 → F) :
    Nonempty (FirstOrderSymbolicCertificate 262143 512754 13 5 24 262144 423
      centers f g (SymbolicBandInterpolation.firstOrderColumns
        (D := 262143) (A := 512754) (m := 13) (M := 5) (μ := 24))) := by
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (by norm_num) (by norm_num) (by norm_num) centers f g goldilocksCubic_interpolation_height

end ArkLibExamples.ReedSolomon.ProveKit
