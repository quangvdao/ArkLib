/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Validity
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.LinearCombination
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ConcreteEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.ComputableChart
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.ConfluentSample
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Geometry.Monic
public import ArkLib.Data.MvPolynomial.TaylorReconstruction.GlobalNormalForm
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Global.Residual
public import ArkLib.Data.Polynomial.TruncatedSeries.Basic
public import ArkLib.Data.Polynomial.ConfluentAlgebra.FundamentalMatrix
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative
public import CompPoly.Multivariate.MvPolyEquiv.Eval

/-!
# Algebraic correctness of the one-chart Taylor constructor

The nonlinear remainder lies in the square of the displacement ideal over any
commutative coefficient ring. In particular the proof applies to the stored
nonreduced confluent algebra, without field cancellation in that algebra.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.Nonlinear

open MvPolynomial

variable {E A σ : Type*} [CommRing E] [CommRing A] [Fintype σ]

/-- The first-order part of polynomial substitution along a vector of displacements. -/
noncomputable def linearTerm (f : E →+* A) (u d : σ → A) (P : MvPolynomial σ E) : A :=
  ∑ i, eval₂ f u (pderiv i P) * d i

/-- The linear term of a constant polynomial vanishes. -/
@[simp] theorem linearTerm_C (f : E →+* A) (u d : σ → A) (c : E) :
    linearTerm f u d (C c) = 0 := by simp [linearTerm]

/-- Linearization is additive in the polynomial. -/
@[simp] theorem linearTerm_add (f : E →+* A) (u d : σ → A) (P Q : MvPolynomial σ E) :
    linearTerm f u d (P + Q) = linearTerm f u d P + linearTerm f u d Q := by
  simp [linearTerm, add_mul, Finset.sum_add_distrib]

/-- Multiplication by a coordinate obeys the polynomial product rule. -/
theorem linearTerm_mul_X (f : E →+* A) (u d : σ → A) (P : MvPolynomial σ E) (i : σ) :
    linearTerm f u d (P * X i) = linearTerm f u d P * u i + eval₂ f u P * d i := by
  classical
  simp only [linearTerm, pderiv_mul, eval₂_add, eval₂_mul, eval₂_X,
    add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [pderiv_X, Pi.single_apply, apply_ite]

/-- Displacements in an ideal put every linear term in that same ideal. -/
theorem linearTerm_mem (f : E →+* A) (u d : σ → A) (I : Ideal A)
    (hd : ∀ i, d i ∈ I) (P : MvPolynomial σ E) : linearTerm f u d P ∈ I := by
  apply I.sum_mem
  intro i _
  exact I.mul_mem_left _ (hd i)

/-- The actual nonlinear substitution error belongs to the square of the displacement ideal. -/
theorem remainder_mem_square (f : E →+* A) (u d : σ → A) (I : Ideal A)
    (hd : ∀ i, d i ∈ I) (P : MvPolynomial σ E) :
    eval₂ f (fun i => u i + d i) P - eval₂ f u P - linearTerm f u d P ∈ I ^ 2 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    simp only [eval₂_add, linearTerm_add]
    convert (I ^ 2).add_mem hP hQ using 1
    · ring
  | mul_X P i hP =>
    rw [eval₂_mul, eval₂_mul, eval₂_X, eval₂_X, linearTerm_mul_X]
    have hprod : linearTerm f u d P * d i ∈ I ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (linearTerm_mem f u d I hd P) (hd i)
    convert (I ^ 2).add_mem ((I ^ 2).mul_mem_right (u i + d i) hP) hprod using 1
    · ring

open CompPoly CPoly CPoly.CMvPolynomial ArkLib.TruncatedSeries

variable [BEq A] [LawfulBEq A] [Nontrivial A]

/-- Stored coefficient vanishing is membership in the principal series-power ideal. -/
theorem order_iff_mem_span (m : ℕ) (p : CPolynomial A) :
    Order m p ↔ p ∈ Ideal.span {(CPolynomial.X : CPolynomial A) ^ m} := by
  rw [order_iff_X_pow_dvd, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨CPolynomial.ringEquiv.symm q, ?_⟩
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    have hr : (CPolynomial.ringEquiv.symm q).toPoly = q := by
      rw [← CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply]
    rw [hr]
    exact hq
  · rintro ⟨q, rfl⟩
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact dvd_mul_right _ _

variable [BEq E] [LawfulBEq E]

/-- The actual stored multivariate substitution has quadratic nonlinear error in series order. -/
theorem stored_remainder_order {n : ℕ} (f : E →+* CPolynomial A)
    (u d : Fin n → CPolynomial A) (m : ℕ) (hd : ∀ i, Order m (d i))
    (T : CMvPolynomial n E) :
    Order (2 * m)
      (CMvPolynomial.eval₂ f (fun i => u i + d i) T - CMvPolynomial.eval₂ f u T -
        ∑ i, CMvPolynomial.eval₂ f u (CMvPolynomial.partialDerivative i T) * d i) := by
  have he := remainder_mem_square f u d
    (Ideal.span {(CPolynomial.X : CPolynomial A) ^ m})
    (fun i => (order_iff_mem_span m (d i)).mp (hd i)) (fromCMvPolynomial T)
  rw [Ideal.span_singleton_pow, ← pow_mul, Nat.mul_comm m 2] at he
  rw [order_iff_mem_span]
  simpa only [linearTerm, CPoly.eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_partialDerivative] using he

omit [Nontrivial A] in
/-- A correction of order `m+r` has every Hasse jet of order at least `m`.
This bound is valid at every finite storage cap and uses no scalar inverses. -/
theorem hasse_order_of_correction (k m r j : ℕ) (hjr : j ≤ r)
    (delta : CPolynomial A) (hd : Order (m + r) delta) :
    Order m (hasse k j delta) := by
  intro i hi
  have hz := hd (i + j) (by omega)
  simp only [CPolynomial.coeff_zero] at hz ⊢
  simp [coeff_hasse, hz]

omit [Fintype σ] [BEq E] [LawfulBEq E] in
/-- Polynomial evaluation preserves coefficient precision over the nonreduced target ring. -/
theorem eval_lowEq (f : E →+* CPolynomial A) (u v : σ → CPolynomial A)
    (k : ℕ) (huv : ∀ i, LowEq k (u i) (v i)) (T : MvPolynomial σ E) :
    LowEq k (MvPolynomial.eval₂ f u T) (MvPolynomial.eval₂ f v T) := by
  induction T using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂_C] using LowEq.refl k (f c)
  | add P Q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X P i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (huv i)

omit [BEq E] [LawfulBEq E] in
/-- The congruence theorem applies to the actual stored multivariate evaluator. -/
theorem stored_eval_lowEq {n : ℕ} (f : E →+* CPolynomial A)
    (u v : Fin n → CPolynomial A) (k : ℕ) (huv : ∀ i, LowEq k (u i) (v i))
    (T : CMvPolynomial n E) : LowEq k (CMvPolynomial.eval₂ f u T) (CMvPolynomial.eval₂ f v T) := by
  simpa only [CPoly.eval₂_equiv] using eval_lowEq f u v k huv (fromCMvPolynomial T)

omit [BEq E] [LawfulBEq E] in
/-- Hasse differentiation is additive for every storage cap. -/
theorem hasse_add (k j : ℕ) (Y δ : CPolynomial A) :
    hasse k j (Y + δ) = hasse k j Y + hasse k j δ := by
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  simp only [← CPolynomial.coeff_toPoly]
  by_cases hi : i < k <;> simp [coeff_hasse, hi, CPolynomial.coeff_add, mul_add]

omit [Nontrivial A] [BEq E] [LawfulBEq E] in
/-- Hasse differentiation loses exactly its order in a coefficient congruence. -/
theorem hasse_lowEq (cap j k : ℕ) {Y W : CPolynomial A} (h : LowEq k Y W) :
    LowEq (k - j) (hasse cap j Y) (hasse cap j W) := by
  intro i hi
  simp only [coeff_hasse]
  by_cases hic : i < cap
  · rw [if_pos hic, if_pos hic, h (i + j) (by omega)]
  · rw [if_neg hic, if_neg hic]

/-- Linearized cancellation plus the quadratic remainder proves the nonlinear precision gain. -/
theorem stored_newton_order {n : ℕ} (f : E →+* CPolynomial A)
    (u d : Fin n → CPolynomial A) (m q : ℕ) (hd : ∀ i, Order m (d i))
    (T : CMvPolynomial n E)
    (hlin : Order q (CMvPolynomial.eval₂ f u T +
      ∑ i, CMvPolynomial.eval₂ f u (CMvPolynomial.partialDerivative i T) * d i)) :
    Order (min q (2 * m)) (CMvPolynomial.eval₂ f (fun i => u i + d i) T) := by
  have hrem := stored_remainder_order f u d m hd T
  have he := (hrem.mono (Nat.min_le_right _ _)).add (hlin.mono (Nat.min_le_left _ _))
  convert he using 1
  ring

end ReedSolomon.HiddenDerivative.FastTaylor.Nonlinear

namespace ReedSolomon.HiddenDerivative.FastTaylor.Companion

open CompPoly ArkLib.TruncatedSeries

variable {E A : Type*} [Field E] [CommRing A] [BEq A] [LawfulBEq A]

omit [BEq A] [LawfulBEq A] in
/-- Companion derivative rows identify each coordinate with the corresponding Hasse jet.
The range `i+j<k` explicitly accounts for the loss of one coefficient per derivative. -/
theorem coefficient_eq_hasse (p k r : ℕ) [CharP E p] (base : E →+* A)
    (hk : k ≤ p) (hr : r ≤ k) (x : ℕ → CPolynomial A)
    (hrows : ∀ j, j + 1 < r → ∀ i, i < k - 1 →
      (i + 1 : A) * (x j).coeff (i + 1) = (j + 1 : A) * (x (j + 1)).coeff i) :
    ∀ j, j < r → ∀ i, i + j < k →
      (x j).coeff i = ((i + j).choose j : A) * (x 0).coeff (i + j) := by
  intro j
  induction j with
  | zero => intro _ i _; simp
  | succ j ih =>
    intro hj i hi
    have hunit : IsUnit (j + 1 : A) :=
      isUnit_iff_exists_inv.mpr ⟨base ((j + 1 : E)⁻¹),
        by simpa only [Nat.cast_add, Nat.cast_one] using
          integration_scalar_unit p k (j + 1) base hk (by omega) (by omega)⟩
    apply hunit.mul_left_cancel
    have hrow := (hrows j hj i (by omega)).symm
    rw [ih (by omega) (i + 1) (by omega)] at hrow
    have hcomb : (j + 1 : A) * ((i + (j + 1)).choose (j + 1) : A) =
        (i + 1 : A) * ((i + 1 + j).choose j : A) := by
      have hc := Nat.choose_succ_right_eq (i + (j + 1)) j
      have he : i + (j + 1) - j = i + 1 := by omega
      rw [he] at hc
      have hi' : i + (j + 1) = i + 1 + j := by omega
      rw [hi'] at hc
      have hn : (j + 1) * (i + (j + 1)).choose (j + 1) =
          (i + 1) * (i + 1 + j).choose j := by simpa [hi', Nat.mul_comm] using hc
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        congrArg (fun n : ℕ => (n : A)) hn
    calc
      (j + 1 : A) * (x (j + 1)).coeff i =
          (i + 1 : A) * (((i + 1 + j).choose j : A) * (x 0).coeff (i + 1 + j)) := hrow
      _ = (j + 1 : A) * (((i + (j + 1)).choose (j + 1) : A) *
          (x 0).coeff (i + (j + 1))) := by
        rw [← mul_assoc, ← hcomb, mul_assoc]
        rw [show i + 1 + j = i + (j + 1) by omega]

/-- The zero-initial companion solution gains the differential order in its first coordinate.
Only coefficient indices below the storage cap are inverted; larger indices vanish by storage. -/
theorem correction_order (p k r m : ℕ) [CharP E p] (base : E →+* A)
    (hk : k ≤ p) (hrk : r ≤ k) (hr : 0 < r) (x : ℕ → CPolynomial A)
    (hrows : ∀ j, j + 1 < r → ∀ i, i < k - 1 →
      (i + 1 : A) * (x j).coeff (i + 1) = (j + 1 : A) * (x (j + 1)).coeff i)
    (horder : ∀ j, j < r → Order (min k (m + 1)) (x j))
    (hdegree : (x 0).toPoly.degree < k) : Order (m + r) (x 0) := by
  intro i hi
  simp only [CPolynomial.coeff_zero]
  by_cases hik : i < k
  · let j := min i (r - 1)
    have hjr : j < r := by dsimp [j]; omega
    have hji : j ≤ i := Nat.min_le_left _ _
    have hij : i - j + j = i := Nat.sub_add_cancel hji
    have ht : i - j < min k (m + 1) := by dsimp [j]; omega
    have hz := horder j hjr (i - j) ht
    simp only [CPolynomial.coeff_zero] at hz
    have he := coefficient_eq_hasse p k r base hk hrk x hrows j hjr (i - j) (by omega)
    rw [hij, hz] at he
    have hp : 0 < p := (Nat.zero_le i).trans_lt (hik.trans_le hk)
    have hbin : (i.choose j : E) ≠ 0 :=
      Polynomial.natCast_choose_ne_zero_of_lt_charP
        (CharP.char_prime_of_ne_zero E hp.ne') (hik.trans_le hk) hji
    have hu : IsUnit (i.choose j : A) := by
      simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hbin).map base
    apply hu.mul_left_cancel
    simpa only [mul_zero] using he.symm
  · rw [CPolynomial.coeff_toPoly]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    apply hdegree.trans_le
    exact_mod_cast (Nat.le_of_not_gt hik)

open ArkLib.ConfluentAlgebra

variable [Nontrivial A]

/-- Read the computed companion solution as a sequence, with zero outside the system dimension. -/
def coordinates (k r : ℕ) (base : E →+* A) (V U : CPolynomial A)
    (a : Fin (r + 1) → CPolynomial A) (hr : 0 < r) : ℕ → CPolynomial A :=
  fun j => if hj : j < r then
    FundamentalMatrix.companionSolution k r base V U a ⟨j, hj⟩ ⟨0, hr⟩ else 0

/-- The stored companion coordinates satisfy the coefficient form of the derivative chain. -/
theorem coordinates_rows (p k r : ℕ) [CharP E p] (base : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) (V U : CPolynomial A)
    (a : Fin (r + 1) → CPolynomial A) (hr : 0 < r) :
    ∀ j, j + 1 < r → ∀ i, i < k - 1 →
      (i + 1 : A) * (coordinates k r base V U a hr j).coeff (i + 1) =
        (j + 1 : A) * (coordinates k r base V U a hr (j + 1)).coeff i := by
  intro j hj i hi
  have he := FundamentalMatrix.companionSolution_row p k r base hk0 hk V U a
    ⟨j, by omega⟩ hj ⟨0, hr⟩ i hi
  simpa only [coordinates, dif_pos (show j < r by omega), dif_pos hj,
    CPolynomial.coeff_derivative, CPolynomial.coeff_C_mul, Nat.cast_add,
    Nat.cast_one, mul_comm] using he

/-- Actual system coordinates are Hasse jets through the precision surviving `j` derivatives. -/
theorem coordinates_hasse (p k r : ℕ) [CharP E p] (base : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) (hrk : r ≤ k) (V U : CPolynomial A)
    (a : Fin (r + 1) → CPolynomial A) (hr : 0 < r) (j : Fin r) :
    LowEq (k - j.val) (coordinates k r base V U a hr j.val)
      (hasse k j.val (coordinates k r base V U a hr 0)) := by
  intro i hi
  have he := coefficient_eq_hasse p k r base hk hrk (coordinates k r base V U a hr)
    (coordinates_rows p k r base hk0 hk V U a hr) j.val j.isLt i (by omega)
  rw [coeff_hasse, if_pos (by omega)]
  exact he

/-- The computed scalar correction has order `m+r`, including every clipped storage boundary. -/
theorem coordinates_correction_order (p k r m : ℕ) [CharP E p] (base : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) (hrk : r ≤ k) (V U : CPolynomial A)
    (a : Fin (r + 1) → CPolynomial A) (hr : 0 < r) (hU : Order m U) :
    Order (m + r) (coordinates k r base V U a hr 0) := by
  apply correction_order p k r m base hk hrk hr (coordinates k r base V U a hr)
    (coordinates_rows p k r base hk0 hk V U a hr)
  · intro j hj
    simp only [coordinates, dif_pos hj]
    exact FundamentalMatrix.companionSolution_order k r m base V U a hU _ _
  · simp only [coordinates, dif_pos hr]
    exact FundamentalMatrix.companionSolution_degree k r base V U a _ _

/-- Differentiating a Hasse coordinate gives the next coordinate with its natural scalar. -/
theorem derivative_hasse (k j : ℕ) (Y : CPolynomial A) :
    LowEq (k - (j + 1)) (hasse k j Y).derivative
      (CPolynomial.C (j + 1 : A) * hasse k (j + 1) Y) := by
  intro i hi
  simp only [CPolynomial.coeff_derivative, CPolynomial.coeff_C_mul, coeff_hasse,
    if_pos (show i + 1 < k by omega), if_pos (show i < k by omega)]
  have hc := Nat.choose_succ_right_eq (i + (j + 1)) j
  have he : i + (j + 1) - j = i + 1 := by omega
  rw [he] at hc
  have hn : (j + 1) * (i + (j + 1)).choose (j + 1) =
      (i + 1) * (i + 1 + j).choose j := by
    simpa [show i + (j + 1) = i + 1 + j by omega, Nat.mul_comm] using hc
  have hcast := congrArg (fun n : ℕ => (n : A)) hn
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
  rw [show i + 1 + j = i + (j + 1) by omega] at *
  simp only [Nat.cast_add, Nat.cast_one]
  linear_combination -(Y.coeff (i + (j + 1))) * hcast

/-- The computed last coordinate differentiates to the highest Hasse correction. -/
theorem coordinates_last_derivative (p k r : ℕ) [CharP E p] (base : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) (hrk : r ≤ k) (V U : CPolynomial A)
    (a : Fin (r + 1) → CPolynomial A) (hr : 0 < r) :
    LowEq (k - r) (coordinates k r base V U a hr (r - 1)).derivative
      (CPolynomial.C (r : A) * hasse k r (coordinates k r base V U a hr 0)) := by
  have hx := (coordinates_hasse p k r base hk0 hk hrk V U a hr
    ⟨r - 1, by omega⟩).rawDerivative
  have he : k - (r - 1) - 1 = k - r := by omega
  rw [he] at hx
  have hy := derivative_hasse k (r - 1) (coordinates k r base V U a hr 0)
  have hc : ((r - 1 : ℕ) : A) + 1 = (r : A) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : A)) (show r - 1 + 1 = r by omega)
  rw [show r - 1 + 1 = r by omega, hc] at hy
  exact hx.trans hy

/-- The executed companion system solves the scalar linearized equation at precision `k-r`. -/
theorem coordinates_linearized (p k r : ℕ) [CharP E p] (base : E →+* A)
    (hk0 : 0 < k) (hk : k ≤ p) (hrk : r < k) (V U : CPolynomial A)
    (a : Fin (r + 1) → CPolynomial A) (hr : 0 < r)
    (hinv : LowEq k (V * a (Fin.last r)) 1) :
    Order (k - r) (U + ∑ j, a j * hasse k j.val (coordinates k r base V U a hr 0)) := by
  let δ := coordinates k r base V U a hr 0
  let low := ∑ j : Fin r, a j.castSucc * hasse k j.val δ
  have hsum : LowEq (k - r)
      (∑ j : Fin r, a j.castSucc * coordinates k r base V U a hr j.val) low := by
    apply LowEq.sum
    intro j _
    exact (LowEq.refl _ _).mul
      ((coordinates_hasse p k r base hk0 hk hrk.le V U a hr j).mono (by omega))
  have hd := coordinates_last_derivative p k r base hk0 hk hrk.le V U a hr
  have hrow := (FundamentalMatrix.companionSolution_last p k r base hk0 hk hr V U a).mono
    (show k - r ≤ k - 1 by omega)
  have hrow' : LowEq (k - r)
      (CPolynomial.C (r : A) * hasse k r δ + CPolynomial.C (r : A) * V * low)
      (-CPolynomial.C (r : A) * V * U) := by
    apply (hd.add ((LowEq.refl _ _).mul hsum)).symm.trans
    simpa only [coordinates, dif_pos (show r - 1 < r by omega),
      dif_pos (Fin.isLt _)] using hrow
  let π := project (A := A) (k - r)
  have he := (project_eq_iff (k - r) _ _).mpr hrow'
  have hv := (project_eq_iff (k - r) _ _).mpr (hinv.mono (by omega))
  change π _ = π _ at he hv
  simp only [map_add, map_mul, map_neg] at he
  simp only [map_mul, map_one] at hv
  have hunit : IsUnit (π (CPolynomial.C (r : A))) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨π (CPolynomial.C (base ((r : E)⁻¹))), ?_⟩
    have hz : CPolynomial.C (r : A) * CPolynomial.C (base ((r : E)⁻¹)) = 1 := by
      apply CPolynomial.toPoly_injective
      rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly, CPolynomial.C_toPoly,
        ← Polynomial.C_mul, integration_scalar_unit p k r base hk hr hrk,
        Polynomial.C_1, CPolynomial.toPoly_one]
    rw [← map_mul, hz, map_one]
  have he' : π (hasse k r δ) + π V * π low = -(π V * π U) := by
    apply hunit.mul_left_cancel
    simpa only [mul_add, mul_assoc, mul_neg, neg_mul] using he
  have hscalar : π U + π low + π (a (Fin.last r)) * π (hasse k r δ) = 0 := by
    have hmul := congrArg (fun z => π (a (Fin.last r)) * z) he'
    have hv' : π (a (Fin.last r)) * π V = 1 := by rw [mul_comm]; exact hv
    rw [mul_add, ← mul_assoc _ (π V), hv', one_mul, mul_neg,
      ← mul_assoc _ (π V), hv', one_mul] at hmul
    linear_combination hmul
  apply (project_eq_zero_iff (k - r) _).mp
  change π _ = 0
  rw [Fin.sum_univ_castSucc]
  simp only [map_add, map_mul, Fin.val_last]
  simpa only [add_assoc, low, δ, Fin.val_castSucc] using hscalar

end ReedSolomon.HiddenDerivative.FastTaylor.Companion

namespace ReedSolomon.HiddenDerivative.FastTaylor.Lifting

open CompPoly CPoly ArkLib.TruncatedSeries ArkLib.ConfluentAlgebra
open SeriesNewton

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]
variable {r N : ℕ} [Fact (0 < N)]
variable (h : CPolynomial (BoxAlgebra.Carrier r N E))
variable [Fact h.monic] [Fact (0 < h.toPoly.degree)]

/-- Evaluation on stored jets preserves precisely the precision left after differentiation. -/
theorem jetEval_lowEq (cap k d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    {Y W : CPolynomial (Representative h)} (he : LowEq k Y W) :
    LowEq (k - d) (jetEval h cap d c T Y) (jetEval h cap d c T W) := by
  apply Nonlinear.stored_eval_lowEq
  intro i
  dsimp only [jetPoint]
  split_ifs with hi
  · exact LowEq.refl _ _
  · exact (Nonlinear.hasse_lowEq cap (i.val - 1) k he).mono (by omega)

/-- Changing storage caps preserves all evaluation coefficients below both caps. -/
theorem jetEval_cap_lowEq (k l q d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) (hqk : q ≤ k) (hql : q ≤ l) :
    LowEq q (jetEval h k d c T Y) (jetEval h l d c T Y) := by
  apply Nonlinear.stored_eval_lowEq
  intro i j hj
  dsimp only [jetPoint]
  split_ifs
  · rfl
  · simp only [coeff_hasse, if_pos (show j < k by omega), if_pos (show j < l by omega)]

/-- A positive-order correction returned by the program has both the required order and
linearized cancellation; its inverse and system solution are computed internally. -/
theorem correction_positive (p k d m : ℕ) [CharP E p] (c : E)
    (T : CMvPolynomial (d + 2) E) (Y δ : CPolynomial (Representative h))
    (hd : 0 < d) (hdk : d < k) (hk : k ≤ p) (hres : Order m (jetEval h k d c T Y))
    (hδ : FundamentalMatrix.nonlinearCorrection? h k d c T Y = some δ) :
    Order (m + d) δ ∧ Order (k - d)
      (jetEval h k d c T Y + ∑ j, jetPartial h k d c T Y j * hasse k j.val δ) := by
  obtain ⟨V, hV, he⟩ := Option.map_eq_some_iff.mp hδ
  rw [dif_pos hd] at he
  subst δ
  have hc : Companion.coordinates k d (scalarHom h) V (jetEval h k d c T Y)
      (jetPartial h k d c T Y) hd 0 =
      FundamentalMatrix.companionSolution k d (scalarHom h) V (jetEval h k d c T Y)
        (jetPartial h k d c T Y) ⟨0, hd⟩ ⟨0, hd⟩ := by
    simp only [Companion.coordinates, dif_pos hd]
  rw [← hc]
  refine ⟨Companion.coordinates_correction_order p k d m (scalarHom h) (by omega) hk
    hdk.le V _ _ hd hres, ?_⟩
  apply Companion.coordinates_linearized p k d (scalarHom h) (by omega) hk hdk V _ _ hd
  simpa only [mul_comm, Fin.last] using inverseSeries?_sound h k _ V hV

/-- The jet displacement contains no independent-variable correction. -/
def displacement (k d : ℕ) (δ : CPolynomial (Representative h)) :
    Fin (d + 2) → CPolynomial (Representative h) :=
  fun i => if i.val = 0 then 0 else hasse k (i.val - 1) δ

/-- Stored jet substitution commutes with adding the scalar correction. -/
theorem jetPoint_add (k d : ℕ) (c : E) (Y δ : CPolynomial (Representative h)) :
    jetPoint h k d c (Y + δ) = fun i => jetPoint h k d c Y i + displacement h k d δ i := by
  funext i
  simp only [jetPoint, displacement]
  split_ifs
  · exact (add_zero _).symm
  · exact Nonlinear.hasse_add k (i.val - 1) Y δ

/-- The multivariate linear term is exactly the sum over the dependent Hasse coordinates. -/
theorem linearTerm_jet (k d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    (Y δ : CPolynomial (Representative h)) :
    (∑ i, CMvPolynomial.eval₂ (seriesScalarHom h) (jetPoint h k d c Y)
      (CMvPolynomial.partialDerivative i T) * displacement h k d δ i) =
      ∑ j, jetPartial h k d c T Y j * hasse k j.val δ := by
  rw [Fin.sum_univ_succ]
  simp only [displacement, Fin.val_zero, if_true, mul_zero, zero_add,
    Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Nat.add_sub_cancel, jetPartial, jetEval]
  rfl

/-- An executed positive-order step doubles nonlinear residual precision up to `k-d`. -/
theorem step_positive (p k d m : ℕ) [CharP E p] (c : E)
    (T : CMvPolynomial (d + 2) E) (Y W : CPolynomial (Representative h))
    (hd : 0 < d) (hdk : d < k) (hk : k ≤ p) (hres : Order m (jetEval h k d c T Y))
    (hW : FundamentalMatrix.nonlinearStep? h k d c T Y = some W) :
    Order (min (k - d) (2 * m)) (jetEval h k d c T W) := by
  obtain ⟨δ, hδ, rfl⟩ := Option.map_eq_some_iff.mp hW
  obtain ⟨horder, hlin⟩ := correction_positive h p k d m c T Y δ hd hdk hk hres hδ
  have hdisp : ∀ i, Order m (displacement h k d δ i) := by
    intro i
    dsimp only [displacement]
    split_ifs
    · exact LowEq.refl _ _
    · exact Nonlinear.hasse_order_of_correction k m d (i.val - 1) (by omega) δ horder
  have hgain := Nonlinear.stored_newton_order (seriesScalarHom h) (jetPoint h k d c Y)
    (displacement h k d δ) m (k - d) hdisp T (by rwa [linearTerm_jet])
  rw [← jetPoint_add] at hgain
  exact ((jetEval_lowEq h k k d c T (truncate_lowEq k (Y + δ))).mono
    (Nat.min_le_left _ _)).trans hgain

/-- Positive-order updates preserve every initial Hasse coordinate. -/
theorem step_positive_initial (p k d m : ℕ) [CharP E p] (c : E)
    (T : CMvPolynomial (d + 2) E) (Y W : CPolynomial (Representative h))
    (hd : 0 < d) (hdk : d < k) (hk : k ≤ p) (hm : 0 < m)
    (hres : Order m (jetEval h k d c T Y))
    (hW : FundamentalMatrix.nonlinearStep? h k d c T Y = some W) :
    LowEq (d + 1) W Y := by
  obtain ⟨δ, hδ, rfl⟩ := Option.map_eq_some_iff.mp hW
  have horder := (correction_positive h p k d m c T Y δ hd hdk hk hres hδ).1
  have he : LowEq (d + 1) (Y + δ) Y := by
    simpa only [add_zero] using (LowEq.refl (d + 1) Y).add
      (horder.mono (show d + 1 ≤ m + d by omega))
  exact ((truncate_lowEq k (Y + δ)).mono (by omega)).trans he

/-- The constant highest partial depends only on the initial Hasse jet, independently of cap. -/
theorem highest_constant_eq (k l d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    (Y W : CPolynomial (Representative h)) (hk : 0 < k) (hl : 0 < l)
    (hY : LowEq (d + 1) Y W) :
    (jetPartial h k d c T Y (Fin.last d)).coeff 0 =
      (jetPartial h l d c T W (Fin.last d)).coeff 0 := by
  have he := jetEval_lowEq h k (d + 1) d c
    (CMvPolynomial.partialDerivative (Fin.last d).succ T) hY
  have hf := jetEval_cap_lowEq h k l 1 d c
    (CMvPolynomial.partialDerivative (Fin.last d).succ T) W hk hl
  exact (he 0 (by omega)).trans (hf 0 (by omega))

/-- A unit constant highest partial makes the actual correction and update succeed. -/
theorem step_exists_of_unit (k d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) (hk : 0 < k)
    (hunit : ∃ b, (jetPartial h k d c T Y (Fin.last d)).coeff 0 * b = 1) :
    ∃ W, FundamentalMatrix.nonlinearStep? h k d c T Y = some W := by
  have hv : ∃ V, inverseSeries? h k (jetPartial h k d c T Y (Fin.last d)) = some V := by
    cases he : inverseSeries? h k (jetPartial h k d c T Y (Fin.last d)) with
    | none => exact False.elim ((inverseSeries?_eq_none_iff h k hk _).mp he hunit)
    | some V => exact ⟨V, rfl⟩
  obtain ⟨V, hV⟩ := hv
  simp only [Fin.last] at hV
  simp only [FundamentalMatrix.nonlinearStep?, FundamentalMatrix.nonlinearCorrection?,
    hV, Option.map_some]
  exact ⟨_, rfl⟩

/-- Every clipped positive-order iteration succeeds, preserves the initial jet, and doubles
its residual precision. All future inverse guards follow from that preserved initial jet. -/
theorem iterate_positive (p k d : ℕ) [CharP E p] (c : E)
    (T : CMvPolynomial (d + 2) E) (hd : 0 < d) (hdk : d < k) (hk : k ≤ p)
    (n m : ℕ) (Y : CPolynomial (Representative h)) (hm : 0 < m)
    (hres : Order (min m (k - d)) (jetEval h k d c T Y))
    (hunit : ∃ b, (jetPartial h k d c T Y (Fin.last d)).coeff 0 * b = 1) :
    ∃ W, FundamentalMatrix.nonlinearIterate? h k d c T n m Y = some W ∧
      LowEq (d + 1) W Y ∧
      Order (min (2 ^ n * m) (k - d)) (jetEval h k d c T W) := by
  induction n generalizing m Y with
  | zero => exact ⟨Y, rfl, LowEq.refl _ _, by simpa using hres⟩
  | succ n ih =>
    let cap := min (2 * m + d) k
    let q := min m (k - d)
    have hcap : d < cap := by dsimp [cap]; omega
    have hcapk : cap ≤ k := Nat.min_le_right _ _
    have hcap0 : 0 < cap := by omega
    have hq : 0 < q := by dsimp [q]; omega
    have hqcap : q ≤ cap := by dsimp [q, cap]; omega
    have hqk : q ≤ k := by dsimp [q]; omega
    have hrescap : Order q (jetEval h cap d c T Y) :=
      (jetEval_cap_lowEq h cap k q d c T Y hqcap hqk).trans hres
    have hunitcap : ∃ b, (jetPartial h cap d c T Y (Fin.last d)).coeff 0 * b = 1 := by
      rw [highest_constant_eq h cap k d c T Y Y hcap0 (by omega) (LowEq.refl _ _)]
      exact hunit
    obtain ⟨W, hW⟩ := step_exists_of_unit h cap d c T Y hcap0 hunitcap
    have hgain := step_positive h p cap d q c T Y W hd hcap (hcapk.trans hk) hrescap hW
    have hpres := step_positive_initial h p cap d q c T Y W hd hcap
      (hcapk.trans hk) hq hrescap hW
    have hprec : min (cap - d) (2 * q) = min (2 * m) (k - d) := by
      dsimp [cap, q]
      omega
    rw [hprec] at hgain
    have hfull : Order (min (2 * m) (k - d)) (jetEval h k d c T W) :=
      (jetEval_cap_lowEq h k cap (min (2 * m) (k - d)) d c T W
        (by omega) (by dsimp [cap]; omega)).trans hgain
    have hunitW : ∃ b, (jetPartial h k d c T W (Fin.last d)).coeff 0 * b = 1 := by
      rw [highest_constant_eq h k k d c T W Y (by omega) (by omega) hpres]
      exact hunit
    obtain ⟨Z, hZ, hZinitial, hZres⟩ := ih (2 * m) W (by omega) hfull hunitW
    refine ⟨Z, ?_, hZinitial.trans hpres, ?_⟩
    · change (FundamentalMatrix.nonlinearStep? h cap d c T Y).bind _ = some Z
      rw [hW, Option.bind_some]
      exact hZ
    · simpa only [pow_succ, mul_assoc] using hZres

/-- The guarded positive-order producer succeeds on a regular initial jet and returns the
advertised solution and residual precisions, without a supplied correction or solution. -/
theorem newton_positive (p k d : ℕ) [CharP E p] (c : E)
    (T : CMvPolynomial (d + 2) E) (jet : Fin (d + 1) → Representative h)
    (hd : 0 < d) (hdk : d < k) (hk : k ≤ p)
    (hroot : (jetEval h k d c T (FundamentalMatrix.initialPolynomial h d jet)).coeff 0 = 0)
    (hunit : ∃ b, (jetPartial h k d c T (FundamentalMatrix.initialPolynomial h d jet)
      (Fin.last d)).coeff 0 * b = 1) :
    ∃ Y, FundamentalMatrix.nonlinearNewton? h p k d c T jet = some Y ∧
      Y.toPoly.degree < k ∧
      LowEq (d + 1) Y (FundamentalMatrix.initialPolynomial h d jet) ∧
      Order (k - d) (jetEval h k d c T Y) := by
  let Y₀ := FundamentalMatrix.initialPolynomial h d jet
  have hres : Order (min 1 (k - d)) (jetEval h k d c T Y₀) := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa only [CPolynomial.coeff_zero] using hroot
  obtain ⟨Y, hY, hinit, hprecision⟩ := iterate_positive h p k d c T hd hdk hk
    (Polynomial.NewtonInverse.rounds (k - d)) 1 Y₀ (by omega) hres hunit
  have hinverse : ∃ b, inverse? h ((jetPartial h k d c T Y₀ (Fin.last d)).coeff 0) = some b := by
    cases hb : inverse? h ((jetPartial h k d c T Y₀ (Fin.last d)).coeff 0) with
    | none => exact False.elim ((inverse?_eq_none_iff h _).mp hb hunit)
    | some b => exact ⟨b, rfl⟩
  obtain ⟨b, hb⟩ := hinverse
  have hrun : FundamentalMatrix.nonlinearNewton? h p k d c T jet = some Y := by
    simp only [FundamentalMatrix.nonlinearNewton?, if_pos (show d < k ∧ k ≤ p from ⟨hdk, hk⟩),
      hroot, beq_self_eq_true, if_true]
    simp only [Fin.last] at hb
    change (inverse? h ((jetPartial h k d c T Y₀ ⟨d, by omega⟩).coeff 0)).bind _ = some Y
    rw [hb, Option.bind_some]
    exact hY
  refine ⟨Y, hrun, FundamentalMatrix.nonlinearNewton?_degree h p k d c T jet Y hrun,
    hinit, ?_⟩
  simpa only [mul_one, Nat.min_eq_right (Polynomial.NewtonInverse.precision_le (k - d))]
    using hprecision

/-- Every successful positive-order public result satisfies the complete local lifting contract. -/
theorem newton_positive_sound (p k d : ℕ) [CharP E p] (c : E)
    (T : CMvPolynomial (d + 2) E) (jet : Fin (d + 1) → Representative h)
    (hd : 0 < d) (Y : CPolynomial (Representative h))
    (hY : FundamentalMatrix.nonlinearNewton? h p k d c T jet = some Y) :
    Y.toPoly.degree < k ∧ LowEq (d + 1) Y (FundamentalMatrix.initialPolynomial h d jet) ∧
      Order (k - d) (jetEval h k d c T Y) := by
  obtain ⟨hg, hroot, b, hb⟩ :=
    FundamentalMatrix.nonlinearNewton?_initialCertificate h p k d c T jet Y hY
  have hunit : ∃ b, (jetPartial h k d c T (FundamentalMatrix.initialPolynomial h d jet)
      (Fin.last d)).coeff 0 * b = 1 := by
    refine ⟨b, ?_⟩
    simpa only [Fin.last] using (inverse?_sound h _ b hb).1
  obtain ⟨W, hW, hdegree, hinit, hres⟩ :=
    newton_positive h p k d c T jet hd hg.1 hg.2 hroot hunit
  have he : W = Y := Option.some.inj (hW.symm.trans hY)
  subst W
  exact ⟨hdegree, hinit, hres⟩

/-- Proof-only untruncated Hasse jets, used to compare stored evaluation with literal numerators. -/
noncomputable def fullHasse (j : ℕ) (Y : CPolynomial (Representative h)) :
    CPolynomial (Representative h) :=
  CPolynomial.ringEquiv.symm (Polynomial.hasseDeriv j Y.toPoly)

/-- The proof-only Hasse jet denotes the exact polynomial derivative. -/
theorem fullHasse_toPoly (j : ℕ) (Y : CPolynomial (Representative h)) :
    (fullHasse h j Y).toPoly = Polynomial.hasseDeriv j Y.toPoly := by
  rw [fullHasse, ← CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply]

/-- Stored and full Hasse jets agree through the storage cap. -/
theorem hasse_full_lowEq (k j : ℕ) (Y : CPolynomial (Representative h)) :
    LowEq k (hasse k j Y) (fullHasse h j Y) := by
  intro i hi
  rw [coeff_hasse, if_pos hi]
  simp only [CPolynomial.coeff_toPoly, fullHasse_toPoly, Polynomial.hasseDeriv_coeff]

/-- Proof-only full polynomial residual in the concrete coordinate convention. -/
noncomputable def fullJetEval (d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) : CPolynomial (Representative h) :=
  CMvPolynomial.eval₂ (seriesScalarHom h)
    (fun i => if i.val = 0 then CPolynomial.X + seriesScalarHom h c
      else fullHasse h (i.val - 1) Y) T

/-- Storage truncates only high residual coefficients; nonlinear substitution preserves the cap. -/
theorem jetEval_full_lowEq (k d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) :
    LowEq k (jetEval h k d c T Y) (fullJetEval h d c T Y) := by
  apply Nonlinear.stored_eval_lowEq
  intro i
  dsimp only [jetPoint]
  split_ifs
  · exact LowEq.refl _ _
  · exact hasse_full_lowEq h k (i.val - 1) Y

/-- Interpret the full stored residual by ordinary polynomial evaluation. -/
theorem fullJetEval_toPoly (d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) :
    (fullJetEval h d c T Y).toPoly =
      MvPolynomial.eval₂ (Polynomial.C.comp (scalarHom h))
        (fun i => if i.val = 0 then Polynomial.X + Polynomial.C (scalarHom h c)
          else Polynomial.hasseDeriv (i.val - 1) Y.toPoly) (fromCMvPolynomial T) := by
  rw [← CPolynomial.toPolyRingHom_apply (fullJetEval h d c T Y)]
  rw [fullJetEval, CPoly.eval₂_equiv, MvPolynomial.eval₂_comp_left]
  congr 1
  · apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, seriesScalarHom, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, CPolynomial.toPolyRingHom_apply, CPolynomial.C_toPoly]
  · funext i
    simp only [Function.comp_apply]
    split_ifs
    · simp only [CPolynomial.toPolyRingHom_apply, CPolynomial.toPoly_add,
        CPolynomial.X_toPoly, seriesScalarHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, CPolynomial.C_toPoly]
    · simpa only [CPolynomial.toPolyRingHom_apply] using fullHasse_toPoly h (i.val - 1) Y

/-- The concrete and option-indexed differential residuals denote the same polynomial. -/
theorem fullJetEval_ringResidual (d : ℕ) (c : E) (T : CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) :
    (fullJetEval h d c T Y).toPoly =
      Global.ringResidual (scalarHom h) c Y.toPoly (semanticEquation T) := by
  rw [Global.ringResidual, semanticEquation]
  change _ = MvPolynomial.eval₂ _ _ (MvPolynomial.rename _ _)
  rw [MvPolynomial.eval₂_rename, fullJetEval_toPoly]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [finToJetVariable, add_comm]
  · simp [finToJetVariable]

/-- Literal numerator provenance is derived from the actual positive-order solver output. -/
theorem newton_positive_provenance (p k d : ℕ) [CharP E p] (c : E)
    (T : CMvPolynomial (d + 2) E) (jet : Fin (d + 1) → Representative h)
    (hd : 0 < d) (Y : CPolynomial (Representative h))
    (hY : FundamentalMatrix.nonlinearNewton? h p k d c T jet = some Y) (j : Fin k) :
    MvPolynomial.eval₂ (scalarHom h) (fun i : Fin (d + 1) => Y.coeff i.val)
      (commonTaylorNumerator c (semanticEquation T) k j) =
      MvPolynomial.eval₂ (scalarHom h) (fun i : Fin (d + 1) => Y.coeff i.val)
        (initialJetSeparant c (semanticEquation T)) ^ (2 * k) * Y.coeff j.val := by
  obtain ⟨hg, _, _⟩ :=
    FundamentalMatrix.nonlinearNewton?_initialCertificate h p k d c T jet Y hY
  have hres := (newton_positive_sound h p k d c T jet hd Y hY).2.2
  have hp : 0 < p := (Nat.zero_lt_of_lt hg.1).trans_le hg.2
  have hbin : ∀ l < k, d < l → (l.choose d : E) ≠ 0 := by
    intro l hl hdl
    exact Polynomial.natCast_choose_ne_zero_of_lt_charP
      (CharP.char_prime_of_ne_zero E hp.ne') (hl.trans_le hg.2) hdl.le
  have hz : ∀ l < k, d < l →
      (Global.ringResidual (scalarHom h) c Y.toPoly (semanticEquation T)).coeff (l - d) = 0 := by
    intro l hl hdl
    rw [← fullJetEval_ringResidual, ← CPolynomial.coeff_toPoly]
    have he := jetEval_full_lowEq h k d c T Y (l - d) (by omega)
    rw [← he]
    simpa only [CPolynomial.coeff_zero] using hres (l - d) (by omega)
  simpa only [← CPolynomial.coeff_toPoly] using
    Global.commonTaylorNumerator_of_ringResidual (scalarHom h) c Y.toPoly
      (semanticEquation T) k hbin hz j

/-- The returned solver's initial coefficients are the supplied local chart coordinates. -/
theorem newton_positive_initial_coeff (p k d : ℕ) [CharP E p] (c : E)
    (T : CMvPolynomial (d + 2) E) (jet : Fin (d + 1) → Representative h)
    (hd : 0 < d) (Y : CPolynomial (Representative h))
    (hY : FundamentalMatrix.nonlinearNewton? h p k d c T jet = some Y)
    (j : Fin (d + 1)) : Y.coeff j.val = jet j := by
  have he := (newton_positive_sound h p k d c T jet hd Y hY).2.1 j.val j.isLt
  simpa only [FundamentalMatrix.initialPolynomial, coeff_ofCoeffs,
    if_pos j.isLt, dif_pos j.isLt] using he

end ReedSolomon.HiddenDerivative.FastTaylor.Lifting

namespace ReedSolomon.HiddenDerivative.FastTaylor

open CompPoly CPoly CPoly.TaylorReconstruction ArkLib.ConfluentAlgebra

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- Specialize the independent variable to the center, retaining the initial jet variables. -/
def initialEquation {r : ℕ} (center : E) (T : CMvPolynomial (r + 2) E) :
    CMvPolynomial (r + 1) E :=
  SquareSystems.computableInitialJetEquation center T

/-- The actual highest jet partial specialized at the same center. -/
def initialSeparant {r : ℕ} (center : E) (T : CMvPolynomial (r + 2) E) :
    CMvPolynomial (r + 1) E :=
  SquareSystems.computableInitialJetSeparant center T

/-- Build the chart's original initial coordinates inside its computed local quotient. -/
def localInitialJet {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (equation : CMvPolynomial (r + 1) E) [Fact (splitLast equation).monic]
    (a : Fin r → E) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Fin (r + 1) → Representative (localEquation N a equation) :=
  fun j => reductionHom (localEquation N a equation)
    (localEquation N a (Geometry.projectPolynomial M (CMvPolynomial.X j)))

/-- Execute one positive-order chart from an upstream component and explicit field prefix.
Direction, monic normalization, confluent sample, inverse, Newton solution, clearing and shift
recovery are computed here. The source component's correctness remains an upstream certificate;
the final producer theorem additionally derives bounded global provenance from this actual run. -/
def construct? (p r k Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E)
    (values : List E) : Option (ChartData E r k) :=
  if 0 < r ∧ r < k ∧ k ≤ p ∧ Bjet < p then
    (Geometry.MonicProjection.construct? component values).bind fun geometry =>
      if hm : (splitLast geometry.polynomial).monic then
        letI : Fact (splitLast geometry.polynomial).monic := ⟨hm⟩
        if hb : 0 < (splitLast geometry.polynomial).natDegree then
          letI : Fact (0 < (splitLast geometry.polynomial).toPoly.degree) := ⟨by
            apply Polynomial.natDegree_pos_iff_degree_pos.mp
            simpa only [CPolynomial.natDegree_toPoly] using hb⟩
          let N := parameterPrecision k Bjet
          letI : Fact (0 < N) := ⟨parameterPrecision_pos k Bjet⟩
          let separant := Geometry.projectPolynomial geometry.forward (initialSeparant center T)
          (ConfluentSample.select? geometry.polynomial separant values).bind fun sample =>
            let equation := localEquation N sample geometry.polynomial
            (ConfluentSample.inverseAt? N geometry.polynomial separant sample).bind fun _ =>
              (FundamentalMatrix.nonlinearNewton? equation p k r center T
                (localInitialJet N geometry.polynomial sample geometry.forward)).map fun solution =>
                let global := GlobalNormalForm.recoverCleared equation sample
                  (ConfluentSample.localSeparant N geometry.polynomial separant sample)
                  (fun j : Fin k => solution.coeff j.val)
                { center := center, projection := geometry.forward,
                  inverseProjection := geometry.inverse, equation := geometry.polynomial,
                  separant := separant, denominator := global.1, numerators := global.2 }
        else none
      else none
  else none

/-- The positive-order chart producer rejects unsupported differential inputs before integration. -/
theorem construct?_unsupported (p r k Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E) (values : List E)
    (hg : ¬ (0 < r ∧ r < k ∧ k ≤ p ∧ Bjet < p)) :
    construct? p r k Bjet center T component values = none := by
  simp only [construct?, if_neg hg]

/-- Stored projection bundled as a homomorphism for quotient provenance. -/
def projectionHom {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    CMvPolynomial n E →+* CMvPolynomial n E where
  toFun := Geometry.projectPolynomial M
  map_one' := by
    apply eq_iff_fromCMvPolynomial.mpr
    simp only [Geometry.from_projectPolynomial, CPoly.map_one, _root_.map_one]
  map_zero' := by
    apply eq_iff_fromCMvPolynomial.mpr
    simp only [Geometry.from_projectPolynomial, CPoly.map_zero, _root_.map_zero]
  map_add' _ _ := CMvPolynomial.bind₁_add _ _ _
  map_mul' _ _ := CMvPolynomial.bind₁_mul _ _ _

/-- The computed coefficient shift and quotient reduction form one executable homomorphism. -/
def localHom {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (equation : CMvPolynomial (r + 1) E) [Fact (splitLast equation).monic] (a : Fin r → E) :
    CMvPolynomial (r + 1) E →+* Representative (localEquation N a equation) :=
  (reductionHom (localEquation N a equation)).comp
    ((mapCoefficientsHom (parameterHom N a)).comp splitLast)

/-- The local homomorphism is the actual localEquation/reduction program. -/
theorem localHom_apply {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (equation : CMvPolynomial (r + 1) E) [Fact (splitLast equation).monic] (a : Fin r → E)
    (P : CMvPolynomial (r + 1) E) :
    localHom N equation a P = reductionHom (localEquation N a equation) (localEquation N a P) := rfl

/-- Local scalar coefficients use precisely the solver's ground-field embedding. -/
theorem localHom_C {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (equation : CMvPolynomial (r + 1) E) [Fact (splitLast equation).monic] (a : Fin r → E)
    (x : E) : localHom N equation a (CMvPolynomial.C x) =
      SeriesNewton.scalarHom (localEquation N a equation) x := by
  have hp : parameterHom N a (CMvPolynomial.C x) =
      (parameterConstantHom (r := r) (N := N)) x := by
    change BoxAlgebra.reduce (shift a (CMvPolynomial.C x)) = BoxAlgebra.reduce (CMvPolynomial.C x)
    rw [shift_C]
  have hc : mapCoefficients (parameterHom N a) (CPolynomial.C (CMvPolynomial.C x)) =
      CPolynomial.C ((parameterConstantHom (r := r) (N := N)) x) := by
    apply CPolynomial.toPoly_injective
    rw [toPoly_mapCoefficients, CPolynomial.C_toPoly, Polynomial.map_C, hp,
      CPolynomial.C_toPoly]
  have hl : localEquation N a (CMvPolynomial.C x) =
      CPolynomial.C ((parameterConstantHom (r := r) (N := N)) x) := by
    unfold CPoly.TaylorReconstruction.localEquation
    rw [splitLast_C]
    exact hc
  rw [localHom_apply, hl]
  simp only [SeriesNewton.scalarHom, constantHom, RingHom.comp_apply, CPolynomial.CHom_apply]

omit [DecidableEq E] in
/-- Every homomorphism out of stored multivariate polynomials evaluates its coordinate images. -/
theorem hom_eq_eval {n : ℕ} {A : Type*} [CommRing A]
    (ψ : CMvPolynomial n E →+* A) (f : E →+* A)
    (hc : ∀ x, ψ (CMvPolynomial.C x) = f x) (P : CMvPolynomial n E) :
    ψ P = MvPolynomial.eval₂ f (fun i => ψ (CMvPolynomial.X i)) (fromCMvPolynomial P) := by
  let φ := ψ.comp (polyRingEquiv (n := n) (R := E)).symm.toRingHom
  have he : φ = MvPolynomial.eval₂Hom f (fun i => ψ (CMvPolynomial.X i)) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, MvPolynomial.eval₂Hom_C]
      have hx : polyRingEquiv (CMvPolynomial.C x : CMvPolynomial n E) = MvPolynomial.C x :=
        CMvPolynomial.fromCMvPolynomial_C x
      rw [← hx, RingEquiv.symm_apply_apply]
      exact hc x
    · intro i
      simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, MvPolynomial.eval₂Hom_X']
      have hx : polyRingEquiv (CMvPolynomial.X i : CMvPolynomial n E) = MvPolynomial.X i :=
        CMvPolynomial.fromCMvPolynomial_X i
      rw [← hx, RingEquiv.symm_apply_apply]
  have ht := DFunLike.congr_fun he (polyRingEquiv P)
  change ψ (polyRingEquiv.symm (polyRingEquiv P)) =
    MvPolynomial.eval₂ f (fun i => ψ (CMvPolynomial.X i)) (fromCMvPolynomial P) at ht
  rwa [RingEquiv.symm_apply_apply] at ht

/-- Projected global polynomials specialize by evaluation at the computed local initial jet. -/
theorem local_project_eq_eval {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (equation : CMvPolynomial (r + 1) E) [Fact (splitLast equation).monic] (a : Fin r → E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (P : CMvPolynomial (r + 1) E) :
    reductionHom (localEquation N a equation) (localEquation N a (Geometry.projectPolynomial M P)) =
      MvPolynomial.eval₂ (SeriesNewton.scalarHom (localEquation N a equation))
        (localInitialJet N equation a M) (fromCMvPolynomial P) := by
  apply hom_eq_eval ((localHom N equation a).comp (projectionHom M))
    (SeriesNewton.scalarHom (localEquation N a equation)) _ P
  intro x
  change localHom N equation a (Geometry.projectPolynomial M (CMvPolynomial.C x)) = _
  rw [Geometry.projectPolynomial, CMvPolynomial.bind₁_C, localHom_C]

omit [BEq E] [LawfulBEq E] in
/-- Initial specialization reuses the existing concrete-to-semantic equation adapter. -/
theorem initialEquation_semantics {r : ℕ} (center : E) (T : CMvPolynomial (r + 2) E) :
    fromCMvPolynomial (initialEquation center T) = initialJetEquation center (semanticEquation T) :=
  SquareSystems.fromCMvPolynomial_computableInitialJetEquation center T

omit [BEq E] [LawfulBEq E] in
/-- The runtime separant is exactly the literal initial highest partial. -/
theorem initialSeparant_semantics {r : ℕ} (center : E) (T : CMvPolynomial (r + 2) E) :
    fromCMvPolynomial (initialSeparant center T) = initialJetSeparant center (semanticEquation T) :=
  SquareSystems.fromCMvPolynomial_computableInitialJetSeparant center T

/-- Initial specialization commutes with evaluation into every coefficient algebra. -/
omit [BEq E] [LawfulBEq E] in
theorem eval₂_initialEquation {r : ℕ} {A : Type*} [CommRing A]
    (f : E →+* A) (jet : Fin (r + 1) → A) (center : E) (T : CMvPolynomial (r + 2) E) :
    CMvPolynomial.eval₂ f jet (initialEquation center T) =
      CMvPolynomial.eval₂ f (Fin.cases (f center) jet) T := by
  rw [eval₂_equiv, initialEquation_semantics, eval₂_equiv]
  unfold initialJetEquation semanticEquation
  calc
    _ = MvPolynomial.eval₂ ((MvPolynomial.eval₂Hom f jet).comp MvPolynomial.C)
        (fun i : Option (Fin (r + 1)) => MvPolynomial.eval₂ f jet
          (i.elim (MvPolynomial.C center) MvPolynomial.X))
        (MvPolynomial.rename (finToJetVariable r) (fromCMvPolynomial T)) :=
      MvPolynomial.map_aeval _ (MvPolynomial.eval₂Hom f jet) _
    _ = _ := by
      rw [MvPolynomial.eval₂_rename, MvPolynomial.eval₂Hom_comp_C]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [finToJetVariable]

/-- Evaluation of the computed separant is evaluation of the actual highest partial. -/
theorem eval₂_initialSeparant {r : ℕ} {A : Type*} [CommRing A]
    (f : E →+* A) (jet : Fin (r + 1) → A) (center : E) (T : CMvPolynomial (r + 2) E) :
    CMvPolynomial.eval₂ f jet (initialSeparant center T) =
      CMvPolynomial.eval₂ f (Fin.cases (f center) jet)
      (CMvPolynomial.partialDerivative (Fin.last (r + 1)) T) := by
  rw [eval₂_equiv, initialSeparant_semantics, eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_partialDerivative]
  unfold initialJetSeparant semanticEquation PolynomialDifferential.separant
  rw [← SquareSystems.finToJetVariable_last r,
    MvPolynomial.pderiv_rename (SquareSystems.finToJetVariable_injective r)]
  calc
    _ = MvPolynomial.eval₂ ((MvPolynomial.eval₂Hom f jet).comp MvPolynomial.C)
        (fun i : Option (Fin (r + 1)) => MvPolynomial.eval₂ f jet
          (i.elim (MvPolynomial.C center) MvPolynomial.X))
        (MvPolynomial.rename (finToJetVariable r)
          (MvPolynomial.pderiv (Fin.last (r + 1)) (fromCMvPolynomial T))) :=
      MvPolynomial.map_aeval _ (MvPolynomial.eval₂Hom f jet) _
    _ = _ := by
      rw [MvPolynomial.eval₂_rename, MvPolynomial.eval₂Hom_comp_C]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [finToJetVariable]

/-- The inverse computed at the selected sample supplies the actual highest-partial unit. -/
theorem local_highest_partial_unit_of_inverseAt {r : ℕ} (N k : ℕ) [Fact (0 < N)]
    (hk : 0 < k) (equation separant : CMvPolynomial (r + 1) E)
    [Fact (splitLast equation).monic]
    [Fact (0 < (splitLast equation).toPoly.degree)] (a : Fin r → E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (center : E)
    (T : CMvPolynomial (r + 2) E)
    (hseparant : separant = Geometry.projectPolynomial M (initialSeparant center T))
    (b : Representative (localEquation N a equation))
    (hb : ConfluentSample.inverseAt? N equation separant a = some b) :
    (SeriesNewton.jetPartial (localEquation N a equation) k r center T
      (FundamentalMatrix.initialPolynomial (localEquation N a equation) r
        (localInitialJet N equation a M)) (Fin.last r)).coeff 0 * b = 1 := by
  have hinv := (ConfluentSample.inverseAt?_sound N equation separant a b hb).1
  have hp :
      (SeriesNewton.jetPartial (localEquation N a equation) k r center T
        (FundamentalMatrix.initialPolynomial (localEquation N a equation) r
          (localInitialJet N equation a M)) (Fin.last r)).coeff 0 =
        ConfluentSample.localSeparant N equation separant a := by
    rw [FundamentalMatrix.jetPartial_initialPolynomial_coeff_zero _ _ _ hk]
    rw [hseparant, ConfluentSample.localSeparant, local_project_eq_eval]
    rw [← eval₂_equiv]
    have hj : (⟨(Fin.last r).val + 1, by omega⟩ : Fin (r + 2)) = Fin.last (r + 1) := by
      ext
      simp [Fin.last]
    rw [hj]
    rw [← eval₂_initialSeparant]
  rwa [hp]

/-- Canonical local reduction is the specialization of the actual global monic remainder. -/
theorem localHom_val {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (equation : CMvPolynomial (r + 1) E) [Fact (splitLast equation).monic] (a : Fin r → E)
    (P : CMvPolynomial (r + 1) E) :
    (localHom N equation a P).val = mapCoefficients (parameterHom N a)
      ((splitLast P).modByMonic (splitLast equation)) := by
  change (mapCoefficients (parameterHom N a) (splitLast P)).modByMonic
    (mapCoefficients (parameterHom N a) (splitLast equation)) = _
  exact (mapCoefficients_remainder (parameterHom N a) (splitLast equation) (splitLast P)
    Fact.out).symm

/-- Recovery in a computed monic chart preserves bounded global degrees after actual reduction. -/
theorem recover_local_bound {r : ℕ} (N L : ℕ) [Fact (0 < N)] (hLN : L < N)
    (component : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic] (a : Fin r → E)
    (P : CMvPolynomial (r + 1) E) (hP : (fromCMvPolynomial P).totalDegree ≤ L) :
    NormalFormBound (splitLast g.polynomial).natDegree L
      (GlobalNormalForm.recoverFlat a (localHom N g.polynomial a P).val) := by
  have hrem := Geometry.MonicProjection.constructed_remainder_degree component P values g hg hP
  have hcoeff := totalDegree_coeff_le_of_flattenLast _ hrem
  constructor
  · have he := GlobalNormalForm.z_degree_recoverFlat_lt
      (localEquation N a g.polynomial) a (localHom N g.polynomial a P)
    rw [ConfluentSample.localEquation_degree] at he
    have hm := (CPolynomial.monic_toPoly_iff _).mp
      (Fact.out : (splitLast g.polynomial).monic)
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, ← CPolynomial.natDegree_toPoly] at he
    exact he
  · exact GlobalNormalForm.totalDegree_recoverFlat_le_of_provenance L hLN a _ _
      (localHom_val N g.polynomial a P) hcoeff hrem

/-- The solver's literal numerator specializes to its actually cleared coefficient in the chart. -/
theorem local_numerator_provenance {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (equation : CMvPolynomial (r + 1) E) [Fact (splitLast equation).monic]
    [Fact (0 < (splitLast equation).toPoly.degree)] (a : Fin r → E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (p k : ℕ) [CharP E p] (center : E) (T : CMvPolynomial (r + 2) E) (hr : 0 < r)
    (Y : CPolynomial (Representative (localEquation N a equation)))
    (hY : FundamentalMatrix.nonlinearNewton? (localEquation N a equation) p k r center T
      (localInitialJet N equation a M) = some Y) (j : Fin k) :
    localHom N equation a (Geometry.projectPolynomial M
      (toCMvPolynomial (commonTaylorNumerator center (semanticEquation T) k j))) =
      (ConfluentSample.localSeparant N equation
        (Geometry.projectPolynomial M (initialSeparant center T)) a) ^ (2 * k) * Y.coeff j.val := by
  have hc := Lifting.newton_positive_provenance (localEquation N a equation)
    p k r center T (localInitialJet N equation a M) hr Y hY j
  have hi : (fun i : Fin (r + 1) => Y.coeff i.val) = localInitialJet N equation a M := by
    funext i
    exact Lifting.newton_positive_initial_coeff (localEquation N a equation)
      p k r center T (localInitialJet N equation a M) hr Y hY i
  rw [hi] at hc
  rw [localHom_apply, local_project_eq_eval, fromCMvPolynomial_toCMvPolynomial]
  have hs : ConfluentSample.localSeparant N equation
      (Geometry.projectPolynomial M (initialSeparant center T)) a =
      MvPolynomial.eval₂ (SeriesNewton.scalarHom (localEquation N a equation))
        (localInitialJet N equation a M) (initialJetSeparant center (semanticEquation T)) := by
    rw [ConfluentSample.localSeparant, local_project_eq_eval, initialSeparant_semantics]
  rw [hs]
  exact hc

/-- Actual solver output yields bounded global normal forms after clearing and recovery.
The proof uses literal Taylor numerators to establish global provenance. -/
theorem cleared_normalForms {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (component : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic]
    [Fact (0 < (splitLast g.polynomial).toPoly.degree)] (a : Fin r → E)
    (p k Bjet : ℕ) [CharP E p] (center : E) (T : CMvPolynomial (r + 2) E)
    (hr : 0 < r) (hN : globalDegreeBudget k Bjet < N)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (Y : CPolynomial (Representative (localEquation N a g.polynomial)))
    (hY : FundamentalMatrix.nonlinearNewton? (localEquation N a g.polynomial) p k r center T
      (localInitialJet N g.polynomial a g.forward) = some Y) :
    let recovered := GlobalNormalForm.recoverCleared (localEquation N a g.polynomial) a
      (ConfluentSample.localSeparant N g.polynomial
        (Geometry.projectPolynomial g.forward (initialSeparant center T)) a)
      (fun j : Fin k => Y.coeff j.val)
    NormalFormBound (splitLast g.polynomial).natDegree (globalDegreeBudget k Bjet) recovered.1 ∧
      ∀ j, NormalFormBound (splitLast g.polynomial).natDegree (globalDegreeBudget k Bjet)
        (recovered.2 j) := by
  let S := initialJetSeparant center (semanticEquation T)
  let sep := ConfluentSample.localSeparant N g.polynomial
    (Geometry.projectPolynomial g.forward (initialSeparant center T)) a
  have hs : sep = MvPolynomial.eval₂ (SeriesNewton.scalarHom (localEquation N a g.polynomial))
      (localInitialJet N g.polynomial a g.forward) S := by
    dsimp only [sep, ConfluentSample.localSeparant, S]
    rw [local_project_eq_eval, initialSeparant_semantics]
  have hden : localHom N g.polynomial a
      (Geometry.projectPolynomial g.forward (toCMvPolynomial (S ^ (2 * k)))) = sep ^ (2 * k) := by
    rw [localHom_apply, local_project_eq_eval, fromCMvPolynomial_toCMvPolynomial,
      MvPolynomial.eval₂_pow, hs]
  constructor
  · change NormalFormBound _ _ (GlobalNormalForm.recoverFlat a (sep ^ (2 * k)).val)
    rw [← hden]
    apply recover_local_bound N (globalDegreeBudget k Bjet) hN component values g hg a
    apply (Geometry.totalDegree_projectPolynomial_le _ _).trans
    rw [fromCMvPolynomial_toCMvPolynomial]
    calc
      (S ^ (2 * k)).totalDegree ≤ 2 * k * S.totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ 2 * k * (Bjet - 1) := Nat.mul_le_mul_left _
        ((totalDegree_initialJetSeparant_le center (semanticEquation T)).trans
          (Nat.sub_le_sub_right hB 1))
      _ ≤ globalDegreeBudget k Bjet := by unfold globalDegreeBudget; omega
  · intro j
    change NormalFormBound _ _ (GlobalNormalForm.recoverFlat a (sep ^ (2 * k) * Y.coeff j.val).val)
    rw [← local_numerator_provenance N g.polynomial a g.forward p k center T hr Y hY j]
    apply recover_local_bound N (globalDegreeBudget k Bjet) hN component values g hg a
    apply (Geometry.totalDegree_projectPolynomial_le _ _).trans
    rw [fromCMvPolynomial_toCMvPolynomial]
    exact (totalDegree_commonTaylorNumerator_le center (semanticEquation T) hv k j).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left (2 * k) (Nat.sub_le_sub_right hB 1)) 1)

/-- Every returned chart has the promised bounded global normal forms. -/
theorem construct?_normalForms (p r k Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E) (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E r k) (hc : construct? p r k Bjet center T component values = some chart) :
    chart.NormalForms (splitLast chart.equation).natDegree (globalDegreeBudget k Bjet) := by
  unfold construct? at hc
  split at hc
  next hguard =>
    simp only [Option.bind_eq_some_iff] at hc
    obtain ⟨g, hg, hc⟩ := hc
    split at hc
    next hm =>
      split at hc
      next hb =>
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
        obtain ⟨a, ha, inv, hinv, Y, hY, rfl⟩ := hc
        let : Fact (0 < parameterPrecision k Bjet) := ⟨parameterPrecision_pos k Bjet⟩
        let : Fact (splitLast g.polynomial).monic := ⟨hm⟩
        let : Fact (0 < (splitLast g.polynomial).toPoly.degree) := ⟨by
          apply Polynomial.natDegree_pos_iff_degree_pos.mp
          simpa only [CPolynomial.natDegree_toPoly] using hb⟩
        exact ⟨hm, rfl, cleared_normalForms (parameterPrecision k Bjet) component values g hg
          a p k Bjet center T hguard.1 (globalDegreeBudget_lt_precision k Bjet) hv hB Y hY⟩
      next => simp at hc
    next => simp at hc
  next => simp at hc

/-- Returned coordinate maps and equation are those computed from the supplied component. -/
theorem construct?_geometry (p r k Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E) (values : List E)
    (chart : ChartData E r k) (hc : construct? p r k Bjet center T component values = some chart) :
    (0 < r ∧ r < k ∧ k ≤ p ∧ Bjet < p) ∧ chart.center = center ∧
      chart.projection * chart.inverseProjection = 1 ∧
      chart.inverseProjection * chart.projection = 1 ∧
      chart.equation = Geometry.MonicProjection.normalize component chart.projection ∧
      (splitLast chart.equation).natDegree = component.totalDegree ∧
      0 < component.totalDegree ∧
      chart.separant = Geometry.projectPolynomial chart.projection (initialSeparant center T) := by
  unfold construct? at hc
  split at hc
  next hguard =>
    simp only [Option.bind_eq_some_iff] at hc
    obtain ⟨g, hg, hc⟩ := hc
    split at hc
    next hm =>
      split at hc
      next hb =>
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
        obtain ⟨a, ha, inv, hinv, Y, hY, rfl⟩ := hc
        obtain ⟨hMI, hIM, _, heq, _, hdeg, _⟩ :=
          Geometry.MonicProjection.construct?_sound component values g hg
        exact ⟨hguard, rfl, hMI, hIM, heq, hdeg, hdeg ▸ hb, rfl⟩
      next => simp at hc
    next => simp at hc
  next => simp at hc

/-- The computed chart quotient kills every multiple of its original component. -/
theorem local_component_multiple_zero {r : ℕ} (N : ℕ) [Fact (0 < N)]
    (component P : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic] (a : Fin r → E) (hdvd : component ∣ P) :
    localHom N g.polynomial a (Geometry.projectPolynomial g.forward P) = 0 := by
  let ψ := (localHom N g.polynomial a).comp (projectionHom g.forward)
  obtain ⟨_, _, _, heq, _, _, _⟩ :=
    Geometry.MonicProjection.construct?_sound component values g hg
  let top := (Geometry.Direction.homogeneousPart component.totalDegree component).eval
    (fun i => g.forward i (Fin.last r))
  have htop : top ≠ 0 := by
    intro hz
    have hzpoly : g.polynomial = 0 := by
      rw [heq, Geometry.MonicProjection.normalize]
      change CMvPolynomial.C top⁻¹ * _ = 0
      rw [hz, inv_zero]
      apply eq_iff_fromCMvPolynomial.mpr
      simp only [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_C,
        MvPolynomial.C_0, zero_mul, CPoly.map_zero]
    have hm := (CPolynomial.monic_toPoly_iff _).mp
      (Fact.out : (splitLast g.polynomial).monic)
    apply hm.ne_zero
    rw [hzpoly, _root_.map_zero, CPolynomial.toPoly_zero]
  have hz : localHom N g.polynomial a g.polynomial = 0 := by
    rw [localHom_apply, reductionHom_modulus]
  have hscaled := (congrArg (localHom N g.polynomial a) heq).symm.trans hz
  rw [Geometry.MonicProjection.normalize, _root_.map_mul, localHom_C] at hscaled
  have hu : IsUnit (SeriesNewton.scalarHom (localEquation N a g.polynomial) top⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero htop)).map _
  have hcomponent : ψ component = 0 := by
    change localHom N g.polynomial a (Geometry.projectPolynomial g.forward component) = 0
    exact hu.mul_left_cancel (by simpa only [mul_zero, top] using hscaled)
  obtain ⟨Q, rfl⟩ := hdvd
  change ψ (component * Q) = 0
  rw [_root_.map_mul, hcomponent, zero_mul]

/-- Component divisibility supplies the actual initial root checked by the nonlinear solver. -/
theorem local_initial_root_of_component_dvd {r : ℕ} (N k : ℕ) [Fact (0 < N)] (hk : 0 < k)
    (component : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic]
    [Fact (0 < (splitLast g.polynomial).toPoly.degree)] (a : Fin r → E)
    (center : E) (T : CMvPolynomial (r + 2) E)
    (hdvd : component ∣ initialEquation center T) :
    (SeriesNewton.jetEval (localEquation N a g.polynomial) k r center T
      (FundamentalMatrix.initialPolynomial (localEquation N a g.polynomial) r
        (localInitialJet N g.polynomial a g.forward))).coeff 0 = 0 := by
  rw [FundamentalMatrix.jetEval_initialPolynomial_coeff_zero _ _ _ hk]
  rw [← eval₂_initialEquation]
  rw [eval₂_equiv, ← local_project_eq_eval]
  exact local_component_multiple_zero N component (initialEquation center T) values g hg a hdvd

/-- Component divisibility and the computed inverse make the actual nonlinear solver succeed. -/
theorem nonlinearNewton_exists_of_component {r : ℕ} (N p k : ℕ) [Fact (0 < N)]
    [CharP E p] (component : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic]
    [Fact (0 < (splitLast g.polynomial).toPoly.degree)] (a : Fin r → E)
    (center : E) (T : CMvPolynomial (r + 2) E) (hr : 0 < r) (hrk : r < k)
    (hkp : k ≤ p) (hdvd : component ∣ initialEquation center T)
    (b : Representative (localEquation N a g.polynomial))
    (hb : ConfluentSample.inverseAt? N g.polynomial
      (Geometry.projectPolynomial g.forward (initialSeparant center T)) a = some b) :
    ∃ Y, FundamentalMatrix.nonlinearNewton? (localEquation N a g.polynomial)
      p k r center T (localInitialJet N g.polynomial a g.forward) = some Y := by
  have hk : 0 < k := hr.trans hrk
  have hroot := local_initial_root_of_component_dvd N k hk component values g hg a center T hdvd
  have hunit : ∃ b, (SeriesNewton.jetPartial (localEquation N a g.polynomial) k r center T
      (FundamentalMatrix.initialPolynomial (localEquation N a g.polynomial) r
        (localInitialJet N g.polynomial a g.forward)) (Fin.last r)).coeff 0 * b = 1 :=
    ⟨b, local_highest_partial_unit_of_inverseAt N k hk g.polynomial
      (Geometry.projectPolynomial g.forward (initialSeparant center T)) a g.forward center T
      rfl b hb⟩
  obtain ⟨Y, hY, _, _, _⟩ := Lifting.newton_positive (localEquation N a g.polynomial)
    p k r center T (localInitialJet N g.polynomial a g.forward) hr hrk hkp hroot hunit
  exact ⟨Y, hY⟩

set_option maxHeartbeats 800000 in
-- Unfolding the dependent constructor trace needs more than the project default.
/-- Valid regular-component input makes the entire executable one-chart constructor succeed. -/
theorem construct?_success_of_component (p r k Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E)
    (values : List E) (hguard : 0 < r ∧ r < k ∧ k ≤ p ∧ Bjet < p)
    (hcomponent : component ≠ 0) (hdegree : 0 < component.totalDegree)
    (hvalues : values.Nodup) (hgeometry : component.totalDegree < values.length)
    (hdvd : component ∣ initialEquation center T)
    (hregular : ∀ g, Geometry.MonicProjection.construct? component values = some g →
      ConfluentSample.obstruction g.polynomial
        (Geometry.projectPolynomial g.forward (initialSeparant center T)) ≠ 0)
    (hsample : ∀ g, Geometry.MonicProjection.construct? component values = some g →
      (fromCMvPolynomial (ConfluentSample.obstruction g.polynomial
        (Geometry.projectPolynomial g.forward (initialSeparant center T)))).totalDegree <
          values.length) :
    ∃ chart, construct? p r k Bjet center T component values = some chart := by
  obtain ⟨g, hg⟩ := Geometry.MonicProjection.construct?_exists component values
    hcomponent hdegree hvalues hgeometry
  obtain ⟨_, _, _, _, hm, hnatDegree, _⟩ :=
    Geometry.MonicProjection.construct?_sound component values g hg
  have hb : 0 < (splitLast g.polynomial).natDegree := hnatDegree.symm ▸ hdegree
  let : Fact (splitLast g.polynomial).monic := ⟨hm⟩
  let : Fact (0 < (splitLast g.polynomial).toPoly.degree) := ⟨by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    simpa only [CPolynomial.natDegree_toPoly] using hb⟩
  let N := parameterPrecision k Bjet
  let : Fact (0 < N) := ⟨parameterPrecision_pos k Bjet⟩
  let separant := Geometry.projectPolynomial g.forward (initialSeparant center T)
  obtain ⟨a, ha⟩ := ConfluentSample.select?_exists g.polynomial separant values
    (hregular g hg) hvalues (hsample g hg)
  obtain ⟨b, hbInverse⟩ :=
    ConfluentSample.inverseAt?_exists N g.polynomial separant values a ha hb
  obtain ⟨Y, hY⟩ := nonlinearNewton_exists_of_component N p k component values g hg a center T
    hguard.1 hguard.2.1 hguard.2.2.1 hdvd b hbInverse
  let global := GlobalNormalForm.recoverCleared (localEquation N a g.polynomial) a
    (ConfluentSample.localSeparant N g.polynomial separant a)
    (fun j : Fin k => Y.coeff j.val)
  let chart : ChartData E r k :=
    ⟨center, g.forward, g.inverse, g.polynomial, separant, global.1, global.2⟩
  refine ⟨chart, ?_⟩
  simp only [construct?, if_pos hguard, hg, Option.bind_some, dif_pos hm, dif_pos hb,
    ha, hbInverse, hY, Option.map_some, chart, global, separant, N]

/-- Bounded recovery equals the computed global remainder, coefficient for coefficient. -/
theorem recover_local_eq {r : ℕ} (N L : ℕ) [Fact (0 < N)] (hLN : L < N)
    (component : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic] (a : Fin r → E)
    (P : CMvPolynomial (r + 1) E) (hP : (fromCMvPolynomial P).totalDegree ≤ L) :
    GlobalNormalForm.recoverFlat a (localHom N g.polynomial a P).val =
      flattenLast ((splitLast P).modByMonic (splitLast g.polynomial)) := by
  exact GlobalNormalForm.recoverFlat_eq_of_provenance L hLN a _ _
    (localHom_val N g.polynomial a P)
    (totalDegree_coeff_le_of_flattenLast _
      (Geometry.MonicProjection.constructed_remainder_degree component P values g hg hP))

/-- Evaluation on the chart hypersurface preserves the computed global remainder. -/
theorem eval_remainder {r : ℕ} {A : Type*} [CommRing A]
    (φ : CMvPolynomial (r + 1) E →+* A) (equation P : CMvPolynomial (r + 1) E)
    (hm : (splitLast equation).monic) (hz : φ equation = 0) :
    φ (flattenLast ((splitLast P).modByMonic (splitLast equation))) = φ P := by
  have he := congrArg (fun q => φ (flattenLast q))
    (CPolynomial.modByMonic_add_mul_divByMonic (splitLast P) (splitLast equation) hm)
  simpa only [_root_.map_add, _root_.map_mul, flattenLast_splitLast, hz, zero_mul,
    add_zero] using he

/-- The computed recovery retains evaluation at every point of the global chart. -/
theorem eval_recover_local {r : ℕ} {A : Type*} [CommRing A]
    (N L : ℕ) [Fact (0 < N)] (hLN : L < N)
    (component : CMvPolynomial (r + 1) E) (values : List E)
    (g : Geometry.MonicProjection.Data r E)
    (hg : Geometry.MonicProjection.construct? component values = some g)
    [Fact (splitLast g.polynomial).monic] (a : Fin r → E)
    (P : CMvPolynomial (r + 1) E) (hP : (fromCMvPolynomial P).totalDegree ≤ L)
    (φ : CMvPolynomial (r + 1) E →+* A) (hz : φ g.polynomial = 0) :
    φ (GlobalNormalForm.recoverFlat a (localHom N g.polynomial a P).val) = φ P := by
  rw [recover_local_eq N L hLN component values g hg a P hP]
  exact eval_remainder φ g.polynomial P Fact.out hz

end ReedSolomon.HiddenDerivative.FastTaylor
