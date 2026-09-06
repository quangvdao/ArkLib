/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ColumnHeight

/-!
# A symbolic certificate on the finite first-order support

Fix a received affine line `f + Zg`. This module constructs one differential polynomial
over `F[Z]` whose local interpolation constraints hold identically in `Z`. The source
columns may be any distinct selection from the finite first-order support

```text
X^x Y₀^a Y₁^b,  b ≤ M,  a + b ≤ μ,
                    x + D a + (D - 1) b < m A.
```

Column `j` has challenge degree at most its `Y₀` exponent `a_j`. At a target height `h`,
it therefore contributes `h + 1 - a_j` scalar unknowns. The strict surplus

```text
n * certifiedEnlargedRankBound 1 m M 0 * (h + 1)
  < ∑ j, (h + 1 - a_j)
```

produces a primitive polynomial kernel vector. The resulting `Q` has coefficient height
at most `h`, stays nonzero after every challenge specialization over every extension
field, and satisfies all actual local constraints.

## Reading the statement

* `D`, `A`, `m`, `M`, and `μ` define the displayed finite support. The cap `M` applies
  to `Y₁`, while `μ` caps the total exponent of `Y₀` and `Y₁`.
* `columns` is an arbitrary injective list of eligible source monomials. A later counting
  theorem may take it to enumerate the full support, but fullness is not assumed here.
* `centers` is an embedding, so the chosen agreement positions have distinct evaluation
  points. The interpolant depends only on `centers`, `f`, and `g`, and is chosen before
  the extension field, challenge, agreement set, or candidate polynomial.
* `hD` supplies both `1 < D` for the first-order rank theorem and the exact-support
  embedding. `hbudget` and `hkD` close the global multiplicity argument for candidates
  of degree below `k`.

## Proof route and scope

The first-order symbolic-rank theorem bounds the rank of the actual constraint matrix
over `F(Z)`. The column-height kernel theorem then constructs and primitively normalizes
its polynomial kernel vector. Eligibility places the assembled polynomial in the finite
first-order space. After any scalar extension and challenge specialization, support can
only shrink, so this space embeds in the exact interpolation space. Mapping the local
constraints and applying the distinct-root multiplicity theorem proves the final
differential identity.

This is an interpolation and root-count certificate. It does not enumerate the full
support, bound the number of polynomial solutions to the differential equation, or by
itself prove a list-decoding or correlated-agreement theorem.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], finite first-order symbolic interpolation.
-/

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation

noncomputable section

variable {F : Type*} [Field F]

/-- A primitive first-order symbolic interpolant and its uniform soundness property.

`primitiveCoefficients` is primitivity of the finite coefficient vector used to assemble
`Q`. Together with injectivity of `columns`, it implies the recorded nonvanishing after
every extension-field challenge specialization. -/
structure FirstOrderSymbolicCertificate {n N : ℕ} (D A m M μ k h : ℕ)
    (centers : Fin n ↪ F) (f g : Fin n → F) (columns : Fin N → SourceColumn 1) where
  coefficients : Fin N → F[X]
  Q : DifferentialPolynomial F[X] 1
  eq_interpolant : Q = interpolant columns coefficients
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  challengeDegree_le : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h
  support : Q ∈ firstOrderSpace F[X] D A m M μ
  firstJetDegree_le : ∀ u ∈ Q.support, firstJetExponent u ≤ M
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ μ
  localConstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
    (receivedLine (f i) (g i)) Q
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Distinct source columns preserve the coefficient height of the kernel vector. -/
theorem coeff_interpolant_natDegree_le {N h : ℕ}
    (columns : Fin N → SourceColumn 1) (hcolumns : Function.Injective columns)
    (v : Fin N → F[X]) (hv : ∀ j, (v j).natDegree ≤ h) :
    ∀ u, (MvPolynomial.coeff u (interpolant columns v)).natDegree ≤ h := by
  classical
  intro u
  by_cases hu : u ∈ Set.range (fun j ↦ (columns j).exponent)
  · obtain ⟨j, rfl⟩ := hu
    rw [coeff_interpolant columns hcolumns v j]
    exact hv j
  · have hcoeff : MvPolynomial.coeff u (interpolant columns v) = 0 := by
      rw [interpolant, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [MvPolynomial.coeff_monomial]
      split
      · rename_i heq
        exact (hu ⟨j, heq⟩).elim
      · rfl
    simp [hcoeff]

/-- Assembling eligible source columns preserves the finite first-order support. -/
theorem interpolant_mem_firstOrderSpace {D A m M μ N : ℕ}
    (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ)
    (v : Fin N → F[X]) :
    interpolant columns v ∈ firstOrderSpace F[X] D A m M μ := by
  rw [interpolant]
  apply Submodule.sum_mem
  intro j _
  rw [mem_firstOrderSpace_iff]
  intro u hu
  have hueq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hu
  exact hueq ▸ heligible j

/-- The column-sensitive numerical surplus constructs a primitive symbolic certificate on
any distinct collection of eligible first-order columns. No matrix-rank hypothesis is left
to the caller, and the single returned `Q` works simultaneously for every later extension
field, challenge, and sufficiently agreeing degree-`< k` polynomial. -/
theorem exists_firstOrder_symbolic_certificate_of_column_height
    {D A m M μ k h n N : ℕ}
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (f g : Fin n → F)
    (columns : Fin N → SourceColumn 1) (hcolumns : Function.Injective columns)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ)
    (hheight : n * certifiedEnlargedRankBound 1 m M 0 * (h + 1) <
      ∑ j, (h + 1 - (columns j).y₀)) :
    Nonempty (FirstOrderSymbolicCertificate (F := F) D A m M μ k h centers f g columns) := by
  have hrank := firstOrder_symbolic_matrix_rank_le hD
    (fun i ↦ centers i) f g columns heligible
  obtain ⟨v, _hv, _hkernel, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    exists_symbolic_received_line_interpolant_of_column_height
      m (certifiedEnlargedRankBound 1 m M 0) h (fun i ↦ centers i) f g columns
        hcolumns hrank hheight
  let Q : DifferentialPolynomial F[X] 1 := interpolant columns v
  have hQsupport : Q ∈ firstOrderSpace F[X] D A m M μ := by
    exact interpolant_mem_firstOrderSpace columns heligible v
  have hfirstJet : ∀ u ∈ Q.support, firstJetExponent u ≤ M := by
    intro u hu
    exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQsupport u hu)).1
  have htotalJet : ∀ u ∈ Q.support, totalJetDegree u ≤ μ := by
    intro u hu
    exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQsupport u hu)).2.1
  refine ⟨⟨v, Q, rfl, hprimitive, ?_, hQsupport, hfirstJet, htotalJet,
    hconstraints, ?_⟩⟩
  · exact coeff_interpolant_natDegree_le columns hcolumns v hvdegree
  · intro E _ ι z
    refine ⟨hnonzero ι z, ?_⟩
    intro indices P hPdegree hcard hagreements
    let φ := Polynomial.eval₂RingHom ι z
    have hQexact : Q ∈ exactInterpolationSpace F[X] D A 1 m M 0 hD :=
      firstOrderSpace_le_exactInterpolationSpace hD hQsupport
    have hQmapped : MvPolynomial.map φ Q ∈
        exactInterpolationSpace E D A 1 m M 0 hD := by
      rw [mem_exactInterpolationSpace_iff]
      intro u hu
      have huQ : u ∈ Q.support := MvPolynomial.support_map_subset φ Q hu
      exact mem_exactInterpolationSpace_iff.mp hQexact u huQ
    have hconstraintsE : ∀ i, SatisfiesLocalConstraints m (ι (centers i))
        (ι (f i) + z * ι (g i)) (MvPolynomial.map φ Q) := by
      intro i
      have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (centers i))
        (receivedLine (f i) (g i)) Q (hconstraints i)
      change SatisfiesLocalConstraints m
        (Polynomial.eval₂ ι z (Polynomial.C (centers i)))
        (Polynomial.eval₂ ι z (receivedLine (f i) (g i)))
        (MvPolynomial.map φ Q) at hi
      simpa only [Polynomial.eval₂_C, receivedLine, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_X] using hi
    have hPnat : P.natDegree ≤ D := by
      by_cases hPzero : P = 0
      · simp [hPzero]
      · have hlt : P.natDegree < k :=
          (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hPdegree
        omega
    have hcenters : Set.InjOn (fun i ↦ ι (centers i))
        (indices : Set (Fin n)) := by
      intro i _ j _ hij
      exact centers.injective (ι.injective hij)
    exact differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
      hbudget hD (fun i ↦ ι (centers i))
        (fun i ↦ ι (f i) + z * ι (g i)) indices hQmapped hconstraintsE
          P hPnat hcenters hcard hagreements

end

end ReedSolomon.HiddenDerivative
