/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.TaylorReconstruction.ClearedCoefficients
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Chart

/-!
# Literal Taylor numerators over nonreduced target rings

A coefficient sequence satisfying the universal affine residual recurrence has the
paper's actual cleared numerators after any ring-homomorphic substitution. This is
an identity in the target ring, not an equality only at field-valued points. The
runtime solver must separately establish the stated initial values and recurrence.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.Global

open MvPolynomial PolynomialDifferential
open CPoly.TaylorReconstruction.ClearedCoefficients

variable {F A : Type*} [Field F] [CommRing A] {r : ℕ}

/-- The actual literal numerator recurrence agrees with any ring-valued coefficient
sequence solving the universal affine residual equations. No separant cancellation is needed. -/
theorem map_rationalTaylorNumerator_of_recurrence
    (center : F) (Q : DifferentialPolynomial F r)
    (φ : MvPolynomial (Fin (r + 1)) F →+* A) (c : ℕ → A) (K : ℕ)
    (hinit : ∀ l < K, ∀ hl : l < r + 1, c l = φ (X ⟨l, hl⟩))
    (hbin : ∀ l < K, r < l → (l.choose r : F) ≠ 0)
    (hres : ∀ l < K, r < l →
      eval₂ (φ.comp C) (fun i : Fin l => c i.val)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
        ((φ.comp C) (l.choose r : F) * c l) * φ (initialJetSeparant center Q) = 0) :
    ∀ l < K, φ (rationalTaylorNumerator center Q l) =
      φ (initialJetSeparant center Q) ^ (2 * (l - r) - 1) * c l := by
  apply cleared_sequence (φ.comp C) (φ (initialJetSeparant center Q))
    (fun l => φ (rationalTaylorNumerator center Q l)) c
    (fun l => 2 * (l - r) - 1) (fun l => 2 * (l - r) - 2)
    (fun l => (optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
    (fun l => (l.choose r : F)) (r + 1) K
  · intro l hl hi
    refine ⟨by omega, ?_⟩
    rw [rationalTaylorNumerator, dif_pos hi]
    exact (hinit l hl hi).symm
  · intro l hl hi
    have hrl : r < l := by omega
    have hh : 0 < l - r := by omega
    have hlr : r + (l - r) = l := by omega
    refine ⟨by omega, hbin l hl hrl, ?_, ?_, hres l hl hrl⟩
    · have hb := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := r) (h := l - r) hh center Q
      rwa [hlr] at hb
    · rw [rationalTaylorNumerator, dif_neg (by omega), map_mul, map_neg]
      rw [ringHom_clearedSubstitution]
      rfl

/-- Padding literal numerators to a sufficient common exponent gives the exact
cleared coefficient identity over any commutative target ring. -/
theorem map_commonTaylorNumerator_of_recurrence
    (center : F) (Q : DifferentialPolynomial F r)
    (φ : MvPolynomial (Fin (r + 1)) F →+* A) (c : ℕ → A) (K tau : ℕ)
    (htau : TaylorExponentSufficient r K tau)
    (hinit : ∀ l < K, ∀ hl : l < r + 1, c l = φ (X ⟨l, hl⟩))
    (hbin : ∀ l < K, r < l → (l.choose r : F) ≠ 0)
    (hres : ∀ l < K, r < l →
      eval₂ (φ.comp C) (fun i : Fin l => c i.val)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
        ((φ.comp C) (l.choose r : F) * c l) * φ (initialJetSeparant center Q) = 0)
    (j : Fin K) :
    φ (commonTaylorNumerator center Q K j tau) =
      φ (initialJetSeparant center Q) ^ tau * c j.val := by
  rw [commonTaylorNumerator, map_mul, map_pow]
  exact pad_cleared_identity _ _ _ _ _ (htau j)
    (map_rationalTaylorNumerator_of_recurrence center Q φ c K hinit hbin hres j.val j.isLt)

/-- The paper's common exponent `2*K` specializes the ring-valued clearing theorem. -/
theorem map_commonTaylorNumerator_two_mul
    (center : F) (Q : DifferentialPolynomial F r)
    (φ : MvPolynomial (Fin (r + 1)) F →+* A) (c : ℕ → A) (K : ℕ)
    (hinit : ∀ l < K, ∀ hl : l < r + 1, c l = φ (X ⟨l, hl⟩))
    (hbin : ∀ l < K, r < l → (l.choose r : F) ≠ 0)
    (hres : ∀ l < K, r < l →
      eval₂ (φ.comp C) (fun i : Fin l => c i.val)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)) +
        ((φ.comp C) (l.choose r : F) * c l) * φ (initialJetSeparant center Q) = 0)
    (j : Fin K) :
    φ (commonTaylorNumerator center Q K j) =
      φ (initialJetSeparant center Q) ^ (2 * K) * c j.val :=
  map_commonTaylorNumerator_of_recurrence center Q φ c K (2 * K)
    (taylorExponentSufficient_two_mul r K) hinit hbin hres j

end ReedSolomon.HiddenDerivative.FastTaylor.Global
