/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Symbolic

/-!
# A finite first-order symbolic certificate from executable counts

This module removes the remaining choice of source columns from first-order symbolic
interpolation. It uses the canonical enumeration of every monomial

```text
X^x Y₀^a Y₁^b,  b ≤ M,  a + b ≤ μ,
                    x + D a + (D - 1) b < m A
```

and rewrites its column-sensitive coefficient count as the executable nested sum
`firstOrderHeightSlotCount D A m M μ h`.

## Reading the statements

The main theorem takes only the mathematical parameters, an embedding of the `n`
evaluation centers, the two received words defining `f + Zg`, and the strict numeric
inequality

```text
n * certifiedEnlargedRankBound 1 m M 0 * (h + 1)
  < firstOrderHeightSlotCount D A m M μ h.
```

There is no caller-supplied matrix rank, column family, or support-membership proof.
The result contains one primitive polynomial `Q` over `F[Z]`, chosen before any extension
field, challenge, agreement set, or candidate polynomial. Every candidate of degree below
`k` that agrees with `f + zg` at at least `A` positions satisfies the specialized
differential identity.

The second theorem chooses a canonical height automatically when the ordinary support
dimension exceeds the certified total rank budget. This condition is convenient for
existence proofs; the explicit-height theorem is the direct interface for concrete
parameter checking.

## Proof route and scope

The support equivalence transports the sum of `h + 1 - a` over the canonical columns to
the executable height-slot count. The selected-column constructor then supplies the
actual symbolic rank bound, primitive kernel, finite-support bounds, local constraints,
and extension-field soundness.

These theorems construct the interpolation equation and prove its agreement implication.
They do not count solutions of that equation or establish a final list-size or
correlated-agreement bound.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Section 6.1.3, Proposition 6.3 (finite first-order
  certificate).
-/

open PolynomialDifferential
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicBandInterpolation

noncomputable section

variable {F : Type*} [Field F]

/-- The coefficient-slot sum over the canonical column enumeration is the executable
first-order height count. -/
theorem sum_firstOrderColumns_height_eq_heightSlotCount
    {D A m M μ h : ℕ} (hD : 0 < D) :
    (Finset.univ.sum fun j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) ↦
      h + 1 -
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).y₀) =
        firstOrderHeightSlotCount D A m M μ h := by
  let e := Fintype.equivFin ↑(firstOrderExponents D A m M μ)
  calc
    (Finset.univ.sum fun j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) ↦
        h + 1 -
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).y₀) =
        Finset.univ.sum fun u : ↑(firstOrderExponents D A m M μ) ↦
          h + 1 - u.1 (some 0) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      simp [firstOrderColumns, e, SourceColumn.ofExponent]
    _ = firstOrderColumnSlotCount D A m M μ h := by
      rw [firstOrderColumnSlotCount, Finset.univ_eq_attach]
      exact Finset.sum_attach (firstOrderExponents D A m M μ)
        (fun u ↦ (h + 1 - u (some 0) : ℕ))
    _ = firstOrderHeightSlotCount D A m M μ h :=
      firstOrderColumnSlotCount_eq_heightSlotCount hD

/-- An executable column-height inequality constructs the complete finite first-order
symbolic certificate. All rank and column-eligibility facts are discharged internally. -/
theorem exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    {D A m M μ k h n : ℕ}
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (f g : Fin n → F)
    (hheight : n * certifiedEnlargedRankBound 1 m M 0 * (h + 1) <
      firstOrderHeightSlotCount D A m M μ h) :
    Nonempty (FirstOrderSymbolicCertificate (F := F) D A m M μ k h centers f g
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) := by
  apply exists_firstOrder_symbolic_certificate_of_column_height
    hD hbudget hkD centers f g
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))
      firstOrderColumns_injective firstOrderColumns_eligible
  rw [sum_firstOrderColumns_height_eq_heightSlotCount (by omega : 0 < D)]
  exact hheight

/-- If the complete first-order support has dimension above the certified total rank,
the canonical height supplies a symbolic certificate without a separate height inequality. -/
theorem exists_finite_firstOrder_symbolic_certificate
    {D A m M μ k n : ℕ}
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (f g : Fin n → F)
    (hdim : n * certifiedEnlargedRankBound 1 m M 0 <
      (firstOrderExponents D A m M μ).card) :
    Nonempty (FirstOrderSymbolicCertificate (F := F) D A m M μ k
      (firstOrderCertificateHeight D A m M μ
        (n * certifiedEnlargedRankBound 1 m M 0)) centers f g
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) := by
  apply exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    hD hbudget hkD centers f g
  exact firstOrder_rowTotal_mul_height_lt_heightSlotCount
    (by omega : 0 < D) hdim

end

end ReedSolomon.HiddenDerivative
