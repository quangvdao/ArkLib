/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.Line
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.AffineCapacity
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.PowerBatching


/-!
# Mutual correlated agreement at every Reed–Solomon rate

This module is the public entry point for the three capacity-level mutual correlated
agreement interfaces proved in this development. For every positive capacity gap, their
constants are chosen before the field, code, received words, and challenges.

## Affine lines

`HasCapacityLineAgreement` states exact full-set agreement for a received line
`f + z * g`. The theorem `exists_capacity_lineAgreement` supplies a field-independent
exceptional-set bound of the form `C * n ^ (d + 1)`.

## Affine families

`HasCapacityAffineAgreement` extends the line conclusion to a constant word and any
positive number of independently sampled directions. The theorem
`exists_capacity_affineAgreement` gives an exceptional-density bound independent of the
affine dimension. `exists_capacity_mcaError` states the corresponding canonical MCA error
bounds, while `exists_capacity_affineAgreement_and_mcaError` provides both conclusions with
one shared choice of constants.

## Power batching

`HasCapacityPowerBatchingAgreement` treats the correlated polynomial curve
`w₀ + z * w₁ + ... + z ^ ℓ * wℓ`. The theorem
`exists_capacity_powerBatchingAgreement` gives an exceptional-set bound
`ℓ * C * n ^ (d + 1)` for `0 < ℓ`. The characteristic assumption is independent of `ℓ`,
and outside the exceptional set the candidate polynomial has exact full power agreement
with low-degree constituent polynomials.

The affine-family and power-batching interfaces are distinct: affine directions use
independent parameters, whereas power batching correlates all coefficients through powers
of one challenge.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Theorem 1.2 and Sections 8–11.
-/
