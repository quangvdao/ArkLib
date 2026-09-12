/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ConfluentAlgebra.Structure
public import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution

/-!
# Execute Taylor denominator clearing in a stored monic quotient

The supplied series coefficients are multiplied by the computed separant power.
Every operation uses the quotient's stored canonical reduction. These algebraic
identities do not assert that arbitrary input coefficients solve a differential equation.
-/

@[expose] public section

namespace CPoly.TaylorReconstruction.ClearedCoefficients

variable {A : Type*} [CommRing A]

/-- Compute the common Taylor denominator by exponentiation in the coefficient algebra. -/
def denominator (k : ℕ) (separant : A) : A := separant ^ (2 * k)

/-- Multiply each local Taylor coefficient by the computed common denominator. -/
def numerators {k : ℕ} (separant : A) (coefficients : Fin k → A) : Fin k → A :=
  let common := denominator k separant
  fun j => common * coefficients j

/-- The runtime packet contains exactly one computed denominator and `k` cleared coefficients. -/
def clear {k : ℕ} (separant : A) (coefficients : Fin k → A) : A × (Fin k → A) :=
  let common := denominator k separant
  (common, fun j => common * coefficients j)

/-- Each executed numerator satisfies the exact cleared coefficient equation. -/
theorem cleared_identity {k : ℕ} (separant : A) (coefficients : Fin k → A) (j : Fin k) :
    (clear separant coefficients).1 * coefficients j = (clear separant coefficients).2 j := rfl

/-- Clearing commutes with every coefficient-algebra specialization. -/
theorem map_clear {B : Type*} [CommRing B] (f : A →+* B) {k : ℕ}
    (separant : A) (coefficients : Fin k → A) :
    (f (clear separant coefficients).1, fun j => f ((clear separant coefficients).2 j)) =
      clear (f separant) (fun j => f (coefficients j)) := by
  apply Prod.ext
  · exact map_pow f separant (2 * k)
  · funext j
    exact (map_mul f (separant ^ (2 * k)) (coefficients j)).trans
      (congrArg (fun b => b * f (coefficients j)) (map_pow f separant (2 * k)))

/-- The cleared agreement residual is the denominator times the original message residual. -/
theorem agreement_identity {k : ℕ} (separant : A) (coefficients : Fin k → A)
    (offset received : A) :
    (∑ j : Fin k, (clear separant coefficients).2 j * offset ^ j.val) -
      received * (clear separant coefficients).1 =
      (clear separant coefficients).1 *
        ((∑ j : Fin k, coefficients j * offset ^ j.val) - received) := by
  simp only [clear, mul_sub, Finset.mul_sum, mul_assoc]
  rw [mul_comm received]

/-- Scaled numerator identities clear a substitution over any commutative ring.
No cancellation of the separant or field-valued point argument is used. -/
theorem clearedSubstitution_scaled {F τ : Type*} [CommSemiring F]
    (f : F →+* A) (s : A) (n c : τ → A) (d : τ → ℕ) (H : ℕ)
    (Q : MvPolynomial τ F) (hn : ∀ i, n i = s ^ d i * c i)
    (hQ : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H) :
    MvPolynomial.clearedSubstitution f s n d H Q =
      s ^ H * MvPolynomial.eval₂ f c Q := by
  classical
  rw [MvPolynomial.clearedSubstitution, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [hn, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  have hw : (∑ i ∈ m.support, d i * m i) = Finsupp.weight d m := by
    simp [Finsupp.weight_apply, Finsupp.sum, Nat.mul_comm]
  rw [hw]
  have hs : s ^ Finsupp.weight d m * s ^ (H - Finsupp.weight d m) = s ^ H := by
    rw [← pow_add]
    congr 1
    have := hQ m hm
    omega
  calc
    _ = f (MvPolynomial.coeff m Q) * (∏ i ∈ m.support, c i ^ m i) *
        (s ^ Finsupp.weight d m * s ^ (H - Finsupp.weight d m)) := by ring
    _ = _ := by rw [hs]; ring

/-- One literal numerator-recurrence step agrees with a coefficient solving its affine residual.
Only the scalar pivot is inverted, in the source field; the target may be nonreduced. -/
theorem cleared_recurrence_step {F τ : Type*} [Field F]
    (f : F →+* A) (s : A) (n c : τ → A) (d : τ → ℕ) (H : ℕ)
    (Q : MvPolynomial τ F) (beta : F) (hbeta : beta ≠ 0) (next : A)
    (hn : ∀ i, n i = s ^ d i * c i)
    (hQ : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hres : MvPolynomial.eval₂ f c Q + (f beta * next) * s = 0) :
    -f beta⁻¹ * MvPolynomial.clearedSubstitution f s n d H Q = s ^ (H + 1) * next := by
  rw [clearedSubstitution_scaled f s n c d H Q hn hQ]
  have he : MvPolynomial.eval₂ f c Q = -(f beta * next * s) :=
    eq_neg_of_add_eq_zero_left hres
  rw [he, pow_succ]
  have hb : f beta⁻¹ * f beta = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hbeta, map_one]
  calc
    _ = (f beta⁻¹ * f beta) * (s ^ H * s * next) := by ring
    _ = _ := by rw [hb, one_mul]

/-- Strong induction turns the literal numerator recurrence into cleared coefficient identities.
The source polynomials and scalar pivots are proof data; this does not replace the
runtime solver. -/
theorem cleared_sequence {F : Type*} [Field F] (f : F →+* A) (s : A)
    (n c : ℕ → A) (d H : ℕ → ℕ) (Q : (l : ℕ) → MvPolynomial (Fin l) F)
    (beta : ℕ → F) (initial K : ℕ)
    (hinit : ∀ l < K, l < initial → d l = 0 ∧ n l = c l)
    (hstep : ∀ l < K, initial ≤ l →
      d l = H l + 1 ∧ beta l ≠ 0 ∧
      (∀ m ∈ (Q l).support, Finsupp.weight (fun i : Fin l => d i.val) m ≤ H l) ∧
      n l = -f (beta l)⁻¹ * MvPolynomial.clearedSubstitution f s
        (fun i : Fin l => n i.val) (fun i => d i.val) (H l) (Q l) ∧
      MvPolynomial.eval₂ f (fun i : Fin l => c i.val) (Q l) +
        (f (beta l) * c l) * s = 0) :
    ∀ l < K, n l = s ^ d l * c l := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro hl
    by_cases hi : l < initial
    · obtain ⟨hd, hn⟩ := hinit l hl hi
      simp [hd, hn]
    · obtain ⟨hd, hb, hQ, hn, hr⟩ := hstep l hl (Nat.le_of_not_gt hi)
      rw [hn, hd]
      exact cleared_recurrence_step f s _ _ _ _ _ _ hb _
        (fun i => ih i.val i.isLt (i.isLt.trans hl)) hQ hr

/-- Padding a proved literal numerator to a sufficient common exponent preserves clearing. -/
theorem pad_cleared_identity (s n c : A) (d tau : ℕ) (hd : d ≤ tau)
    (hn : n = s ^ d * c) : n * s ^ (tau - d) = s ^ tau * c := by
  rw [hn]
  calc
    _ = (s ^ d * s ^ (tau - d)) * c := by ring
    _ = s ^ tau * c := by rw [← pow_add, Nat.add_sub_of_le hd]

open CompPoly ArkLib.ConfluentAlgebra

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
variable (h : CPolynomial R) [Fact h.monic]

/-- Denominator exponentiation returns the strict last-variable normal-form bound. -/
theorem denominator_degree_lt (k : ℕ) (separant : Representative h) :
    (denominator k separant).val.toPoly.degree < h.toPoly.degree :=
  degree_representative_lt h Fact.out _

/-- Every cleared coefficient retains the strict last-variable normal-form bound. -/
theorem numerator_degree_lt {k : ℕ} (separant : Representative h)
    (coefficients : Fin k → Representative h) (j : Fin k) :
    (numerators separant coefficients j).val.toPoly.degree < h.toPoly.degree :=
  degree_representative_lt h Fact.out _

/-- The computed denominator is the canonical remainder of the actual separant power. -/
theorem denominator_val (k : ℕ) (separant : Representative h) :
    (denominator k separant).val = (separant.val ^ (2 * k)).modByMonic h := rfl

/-- Each computed numerator is the canonical remainder of the cleared product. -/
theorem numerator_val {k : ℕ} (separant : Representative h)
    (coefficients : Fin k → Representative h) (j : Fin k) :
    (numerators separant coefficients j).val =
      ((denominator k separant).val * (coefficients j).val).modByMonic h := rfl

end CPoly.TaylorReconstruction.ClearedCoefficients
