/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.TaylorChart.PointRecognition
import ArkLib.ToMathlib.AlgebraicGeometry.AffineGraphPullback


/-!
# Recognizing prime components of the symbolic source chart

Flattening the retained challenge commutes with point evaluation. A positive-dimensional
regular prime component containing high-coefficient cuts and a common sample lies on an
actual base-field pair graph. Restriction to that graph preserves every ideal equation
and keeps the separant nonzero.
-/

open PolynomialDifferential


noncomputable section

namespace MvPolynomial

variable {E σ : Type*} [Field E]

/-- Evaluating after separating the challenge coordinate is evaluation of the original
joint polynomial. -/
theorem aeval_map_optionEquivRight (x : Option σ → E)
    (p : MvPolynomial (Option σ) E) :
    aeval (fun j ↦ x (some j))
      (MvPolynomial.map (Polynomial.evalRingHom (x none)) (optionEquivRight E σ p)) =
        aeval x p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1
      cases i <;> simp

/-- Evaluating a flattened symbolic polynomial specializes its challenge coefficient first. -/
theorem aeval_optionEquivRight_symm (x : Option σ → E)
    (p : MvPolynomial σ (Polynomial E)) :
    aeval x ((optionEquivRight E σ).symm p) =
      aeval (fun j ↦ x (some j))
        (MvPolynomial.map (Polynomial.evalRingHom (x none)) p) := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (aeval_map_optionEquivRight x ((optionEquivRight E σ).symm p)).symm

end MvPolynomial

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K r : ℕ}

/-- The initial differential equation in joint source coordinates. -/
def symbolicSourceInitialEquation (center : E) (Q : DifferentialPolynomial E[X] r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm (initialJetEquationOver (Polynomial.C center) Q)

/-- The separant viewed as a polynomial in challenge and initial jets. -/
def symbolicSourceSeparant (center : E) (Q : DifferentialPolynomial E[X] r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm (initialJetSeparantOver (Polynomial.C center) Q)

/-- One high-coefficient numerator in joint source coordinates. -/
def symbolicSourceNumerator (center : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (l : Fin K) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm
    (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l)

/-- One received-line agreement cut in joint source coordinates. -/
def symbolicSourceAgreement (center : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (alpha f g : E) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K (Polynomial.C alpha)
      (Polynomial.C f + Polynomial.X * Polynomial.C g))

/-- The cleared identity identifying one reconstructed coefficient with an affine pair. -/
def symbolicSourceReconstructionError (center : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (P₀ P₁ : E[X]) (l : Fin K) : MvPolynomial (Option (Fin (r + 1))) E :=
  symbolicSourceNumerator center Q K l - symbolicSourceSeparant center Q ^ (2 * K) *
    (MvPolynomial.C ((Polynomial.taylor center P₀).coeff l.val) +
      MvPolynomial.X none * MvPolynomial.C ((Polynomial.taylor center P₁).coeff l.val))

/-- Actual prime components supported on a common sample lie on a base-field pair graph.
Every polynomial in the component ideal restricts to zero and the restricted separant
is nonzero. The component hypotheses concern explicit symbolic cuts. -/
theorem exists_graphLine_pair_of_symbolic_prime_sample
    [IsAlgClosed E] (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hs : symbolicSourceSeparant center Q ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree)
    (hinit : symbolicSourceInitialEquation center Q ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val → symbolicSourceNumerator center Q K l ∈ P)
    (hcuts : ∀ i ∈ sample,
      symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i)) ∈ P) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      (∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
        x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) (x none)) ∧
      (∀ p ∈ P,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) p = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota))
        (symbolicSourceInitialEquation center Q) = 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceNumerator center Q K l) = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (symbolicSourceSeparant center Q) ≠ 0 ∧
      ∀ l : Fin K,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceReconstructionError center Q K (P₀.map iota) (P₁.map iota) l) = 0 := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hrecognize⟩ :=
    exists_graphLine_pair_of_symbolic_sample domain f g sample hsample iota center Q hK
  have hpoint (x : Option (Fin (r + 1)) → E)
      (hx : x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q)) :=
    hrecognize (x none) (fun j ↦ x (some j))
      (by simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm] using hx.2)
      (fun l hl ↦ by
        have hz := hx.1 _ (hhigh l hl)
        simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm] using hz)
      (fun i hi ↦ by
        have hz := hx.1 _ (hcuts i hi)
        simpa only [symbolicSourceAgreement, aeval_optionEquivRight_symm] using hz)
  have hgraph : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (x none) := by
    intro x hx
    have hjet := (hpoint x hx).2.1
    funext j
    cases j with
    | none => rfl
    | some j => exact congrFun hjet j
  obtain ⟨hvanish, hsep⟩ := graphPullback_vanishes_of_principalOpen hP hs hd
    (polynomialJet (d := r) center (P₀.map iota))
    (polynomialJet (d := r) center (P₁.map iota)) hgraph
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hgraph, hvanish, hvanish _ hinit,
    (fun l hl ↦ hvanish _ (hhigh l hl)), hsep, ?_⟩
  intro l
  have hinfinite : (principalOpenZeroLocus P (symbolicSourceSeparant center Q)).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  apply affineGraphPullback_eq_zero_of_infinite _ _ hinfinite hgraph
  intro x hx
  have hcoeff := (hpoint x hx).2.2 l
  have hlinear : (Polynomial.taylor center
      (P₀.map iota + Polynomial.C (x none) * P₁.map iota)).coeff l.val =
        (Polynomial.taylor center (P₀.map iota)).coeff l.val +
          x none * (Polynomial.taylor center (P₁.map iota)).coeff l.val := by
    rw [← Polynomial.smul_eq_C_mul, map_add, map_smul]
    simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]
  simp only [symbolicSourceReconstructionError, map_sub, map_mul, map_pow, map_add,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    symbolicSourceNumerator, symbolicSourceSeparant, aeval_optionEquivRight_symm]
  rw [hcoeff, hlinear, sub_self]

end ReedSolomon
