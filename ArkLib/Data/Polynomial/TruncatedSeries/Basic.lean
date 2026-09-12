/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ConfluentAlgebra.Structure
public import CompPoly.Univariate.Deriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.CharP.Basic

/-!
# Executable truncated polynomial series

Series retain CompPoly's canonical coefficient arrays. Precision predicates refer to
coefficients below an explicit cap; differentiation and integration state their precision loss.
-/

@[expose] public section

namespace ArkLib.TruncatedSeries

open CompPoly CompPoly.CPolynomial

variable {A : Type*} [CommRing A] [BEq A] [LawfulBEq A]

/-- Store the first `k` values of a coefficient function. -/
def ofCoeffs (k : ℕ) (f : ℕ → A) : CPolynomial A :=
  CPolynomial.ofArray (Array.ofFn (fun i : Fin k => f i.val))

@[simp] theorem coeff_ofCoeffs (k : ℕ) (f : ℕ → A) (i : ℕ) :
    (ofCoeffs k f).coeff i = if i < k then f i else 0 := by
  simp [ofCoeffs, CPolynomial.coeff_ofArray, Array.getD]

/-- Discard all coefficients at or above the requested cap. -/
def truncate (k : ℕ) (p : CPolynomial A) : CPolynomial A := ofCoeffs k p.coeff

@[simp] theorem coeff_truncate (k : ℕ) (p : CPolynomial A) (i : ℕ) :
    (truncate k p).coeff i = if i < k then p.coeff i else 0 := coeff_ofCoeffs k p.coeff i

/-- Equality of all coefficients strictly below the stated precision. -/
def LowEq (k : ℕ) (p q : CPolynomial A) : Prop := ∀ i < k, p.coeff i = q.coeff i

/-- Vanishing below the given precision. -/
def Order (k : ℕ) (p : CPolynomial A) : Prop := LowEq k p 0

/-- Stored truncated addition. -/
def add (k : ℕ) (p q : CPolynomial A) : CPolynomial A := truncate k (p + q)

/-- Stored truncated multiplication. -/
def mul (k : ℕ) (p q : CPolynomial A) : CPolynomial A := truncate k (p * q)

/-- Stored Hasse derivative with explicit output precision. -/
def hasse (k j : ℕ) (p : CPolynomial A) : CPolynomial A :=
  ofCoeffs k (fun i => ((i + j).choose j : A) * p.coeff (i + j))

/-- Ordinary derivative, with explicit output precision. -/
def derivative (k : ℕ) (p : CPolynomial A) : CPolynomial A := hasse k 1 p

@[simp] theorem coeff_hasse (k j : ℕ) (p : CPolynomial A) (i : ℕ) :
    (hasse k j p).coeff i =
      if i < k then ((i + j).choose j : A) * p.coeff (i + j) else 0 := by
  exact coeff_ofCoeffs k _ i

@[simp] theorem coeff_derivative (k : ℕ) (p : CPolynomial A) (i : ℕ) :
    (derivative k p).coeff i = if i < k then (i + 1 : A) * p.coeff (i + 1) else 0 := by
  simp [derivative]

omit [BEq A] [LawfulBEq A] in
@[refl] theorem LowEq.refl (k : ℕ) (p : CPolynomial A) : LowEq k p p := fun _ _ => rfl

omit [BEq A] [LawfulBEq A] in
@[symm] theorem LowEq.symm {k : ℕ} {p q : CPolynomial A} (h : LowEq k p q) : LowEq k q p :=
  fun i hi => (h i hi).symm

omit [BEq A] [LawfulBEq A] in
@[trans] theorem LowEq.trans {k : ℕ} {p q s : CPolynomial A}
    (h₁ : LowEq k p q) (h₂ : LowEq k q s) : LowEq k p s := fun i hi => (h₁ i hi).trans (h₂ i hi)

omit [BEq A] [LawfulBEq A] in
theorem LowEq.mono {k l : ℕ} {p q : CPolynomial A} (h : LowEq k p q) (hl : l ≤ k) :
    LowEq l p q := fun i hi => h i (lt_of_lt_of_le hi hl)

@[simp] theorem truncate_lowEq (k : ℕ) (p : CPolynomial A) : LowEq k (truncate k p) p := by
  intro i hi
  simp [hi]

theorem lowEq_iff_truncate_eq {k : ℕ} {p q : CPolynomial A} :
    LowEq k p q ↔ truncate k p = truncate k q := by
  constructor
  · intro h
    apply CPolynomial.eq_iff_coeff.mpr
    intro i
    by_cases hi : i < k <;> simp [hi, h i]
  · intro h i hi
    have hc := congrArg (fun f : CPolynomial A => f.coeff i) h
    simpa [hi] using hc

@[simp] theorem truncate_idempotent (k : ℕ) (p : CPolynomial A) :
    truncate k (truncate k p) = truncate k p := lowEq_iff_truncate_eq.mp (truncate_lowEq k p)

theorem LowEq.add {k : ℕ} {p q u v : CPolynomial A} (hp : LowEq k p q) (hu : LowEq k u v) :
    LowEq k (p + u) (q + v) := by
  intro i hi
  simp only [CPolynomial.coeff_add, hp i hi, hu i hi]

theorem LowEq.neg {k : ℕ} {p q : CPolynomial A} (hp : LowEq k p q) : LowEq k (-p) (-q) := by
  intro i hi
  simp only [CPolynomial.coeff_neg, hp i hi]

theorem LowEq.sub {k : ℕ} {p q u v : CPolynomial A} (hp : LowEq k p q) (hu : LowEq k u v) :
    LowEq k (p - u) (q - v) := by
  simpa only [sub_eq_add_neg] using hp.add hu.neg

theorem LowEq.mul {k : ℕ} {p q u v : CPolynomial A} (hp : LowEq k p q) (hu : LowEq k u v) :
    LowEq k (p * u) (q * v) := by
  intro i hi
  simp only [CPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [hp j (by omega), hu (i - j) (by omega)]

/-- Differentiation loses one coefficient of precision. -/
theorem LowEq.derivative {k l : ℕ} {p q : CPolynomial A} (hp : LowEq k p q) :
    LowEq (min l (k - 1)) (derivative l p) (derivative l q) := by
  intro i hi
  have hil : i < l := lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hik : i + 1 < k := by omega
  simp [hil, hp (i + 1) hik]

/-- Multiplication adds vanishing orders even over nonreduced coefficient rings. -/
theorem Order.mul {m n : ℕ} {p q : CPolynomial A} (hp : Order m p) (hq : Order n q) :
    Order (m + n) (p * q) := by
  intro i hi
  rw [CPolynomial.coeff_mul, CPolynomial.coeff_zero]
  apply Finset.sum_eq_zero
  intro j hjmem
  have hjle := Finset.mem_range.mp hjmem
  by_cases hj : j < m
  · have hz := hp j hj
    simp only [CPolynomial.coeff_zero] at hz
    simp [hz]
  · have hz := hq (i - j) (by omega)
    simp only [CPolynomial.coeff_zero] at hz
    simp [hz]

variable {E : Type*} [Field E]

/-- Zero-constant termwise integration; only output indices strictly below `k` are evaluated. -/
def integral (k : ℕ) (ι : E →+* A) (p : CPolynomial A) : CPolynomial A :=
  ofCoeffs k (fun i => if i = 0 then 0 else ι ((i : E)⁻¹) * p.coeff (i - 1))

@[simp] theorem coeff_integral (k : ℕ) (ι : E →+* A) (p : CPolynomial A) (i : ℕ) :
    (integral k ι p).coeff i =
      if i < k then (if i = 0 then 0 else ι ((i : E)⁻¹) * p.coeff (i - 1)) else 0 :=
  coeff_ofCoeffs k _ i

/-- Every integration denominator below the guarded cap is nonzero in the coefficient field. -/
theorem integration_index_ne_zero (p k i : ℕ) [CharP E p] (hk : k ≤ p)
    (hi : 0 < i) (hik : i < k) : (i : E) ≠ 0 := by
  intro hz
  exact Nat.not_dvd_of_pos_of_lt hi (lt_of_lt_of_le hik hk)
    ((CharP.cast_eq_zero_iff E p i).mp hz)

omit [BEq A] [LawfulBEq A] in
/-- Integration derives its scalar inverse identity from the characteristic guard. -/
theorem integration_scalar_unit (p k i : ℕ) [CharP E p] (ι : E →+* A) (hk : k ≤ p)
    (hi : 0 < i) (hik : i < k) : (i : A) * ι ((i : E)⁻¹) = 1 := by
  rw [← map_natCast ι, ← map_mul,
    mul_inv_cancel₀ (integration_index_ne_zero p k i hk hi hik), map_one]

/-- The derivative of the zero-constant integral agrees through precision `k-1`. -/
theorem derivative_integral (p k : ℕ) [CharP E p] (ι : E →+* A) (hk : k ≤ p)
    (f : CPolynomial A) : LowEq (k - 1) (derivative (k - 1) (integral k ι f)) f := by
  intro i hi
  have hik : i + 1 < k := by omega
  rw [coeff_derivative, if_pos hi, coeff_integral, if_pos hik, if_neg (by omega)]
  simp only [Nat.add_sub_cancel, ← mul_assoc]
  have hu := integration_scalar_unit p k (i + 1) ι hk (by omega) hik
  simp only [Nat.cast_add, Nat.cast_one] at hu ⊢
  rw [hu, one_mul]

omit [BEq A] [LawfulBEq A] in
/-- Vanishing order may be weakened to any smaller precision. -/
theorem Order.mono {m n : ℕ} {p : CPolynomial A} (hp : Order m p) (hn : n ≤ m) : Order n p :=
  LowEq.mono hp hn

/-- Powers multiply the vanishing order. -/
theorem Order.pow [Nontrivial A] {m : ℕ} {p : CPolynomial A} (hp : Order m p) (n : ℕ) :
    Order (m * n) (p ^ n) := by
  induction n with
  | zero => intro i hi; simp at hi
  | succ n ih => simpa [pow_succ, Nat.mul_succ] using ih.mul hp

/-- Integration increases vanishing order by one within its output cap. -/
theorem Order.integral {m k : ℕ} {p : CPolynomial A} (hp : Order m p) (ι : E →+* A) :
    Order (min k (m + 1)) (integral k ι p) := by
  intro i hi
  have hik : i < k := lt_of_lt_of_le hi (Nat.min_le_left _ _)
  by_cases hi0 : i = 0
  · simp [hi0, CPolynomial.coeff_zero]
  · have hz := hp (i - 1) (by omega)
    simp only [CPolynomial.coeff_zero] at hz
    simp [hik, hi0, hz, CPolynomial.coeff_zero]

section Quotient

variable [Nontrivial A]

/-- The monic truncation modulus; its quotient reuses the existing stored monic algebra. -/
def modulus (k : ℕ) : CPolynomial A := CPolynomial.X ^ k

instance (k : ℕ) : Fact (modulus (A := A) k).monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [modulus, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  exact Polynomial.monic_X_pow k⟩

/-- Stored truncated series ring, with no competing polynomial representation. -/
abbrev Ring (k : ℕ) := ConfluentAlgebra.Representative (modulus (A := A) k)

/-- Executable truncation bundled as the monic quotient projection. -/
def project (k : ℕ) : CPolynomial A →+* Ring (A := A) k :=
  ConfluentAlgebra.reductionHom (modulus k)

omit [Nontrivial A] in
/-- The stored truncation has no coefficient at or above its cap. -/
theorem degree_truncate_lt (k : ℕ) (p : CPolynomial A) :
    (truncate k p).toPoly.degree < k := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [← CPolynomial.coeff_toPoly, coeff_truncate, if_neg (by omega)]

omit [Nontrivial A] in
/-- Coefficient vanishing is equivalently divisibility by a power of the series variable. -/
theorem order_iff_X_pow_dvd (k : ℕ) (p : CPolynomial A) :
    Order k p ↔ Polynomial.X ^ k ∣ p.toPoly := by
  rw [Polynomial.X_pow_dvd_iff]
  simp only [Order, LowEq, CPolynomial.coeff_toPoly, CPolynomial.toPoly_zero,
    Polynomial.coeff_zero]

/-- Stored array truncation is exactly monic reduction by `Z^k`. -/
theorem truncate_eq_remainder (k : ℕ) (p : CPolynomial A) :
    truncate k p = p.modByMonic (modulus k) := by
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ Fact.out]
  have hd : Polynomial.X ^ k ∣ p.toPoly - (truncate k p).toPoly := by
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    rw [Polynomial.coeff_sub, ← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly]
    simp [hi]
  have he := Polynomial.modByMonic_eq_of_dvd_sub (Polynomial.monic_X_pow k) hd
  have ht := (Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow (R := A) k)).mpr
    (by simpa using degree_truncate_lt k p)
  rw [ht] at he
  simpa only [modulus, CPolynomial.toPoly_pow, CPolynomial.X_toPoly] using he.symm

@[simp] theorem project_val (k : ℕ) (p : CPolynomial A) :
    (project k p).val = truncate k p := (truncate_eq_remainder k p).symm

/-- Equality in the stored series ring is exactly equality below the cap. -/
theorem project_eq_iff (k : ℕ) (p q : CPolynomial A) :
    project k p = project k q ↔ LowEq k p q := by
  rw [lowEq_iff_truncate_eq]
  constructor
  · intro he
    simpa only [project_val] using congrArg Subtype.val he
  · intro he
    apply Subtype.ext
    simpa only [project_val] using he

/-- Vanishing below the cap is precisely zero in the stored series ring. -/
theorem project_eq_zero_iff (k : ℕ) (p : CPolynomial A) :
    project k p = 0 ↔ Order k p := by
  rw [← map_zero (project k), project_eq_iff]
  rfl

@[simp] theorem project_representative (k : ℕ) (p : Ring (A := A) k) : project k p.val = p :=
  ConfluentAlgebra.reductionHom_val (modulus k) p

end Quotient

section More

/-- Finite sums preserve coefficientwise precision. -/
theorem LowEq.sum [Nontrivial A] {ι : Type*} (s : Finset ι) {k : ℕ}
    {f g : ι → CPolynomial A} (hf : ∀ i ∈ s, LowEq k (f i) (g i)) :
    LowEq k (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact LowEq.refl _ _
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))

/-- Congruence is equivalent to vanishing of the difference. -/
theorem lowEq_iff_order_sub {k : ℕ} {p q : CPolynomial A} :
    LowEq k p q ↔ Order k (p - q) := by
  simp only [LowEq, Order, CPolynomial.coeff_sub, CPolynomial.coeff_zero, sub_eq_zero]

theorem Order.add {k : ℕ} {p q : CPolynomial A} (hp : Order k p) (hq : Order k q) :
    Order k (p + q) := by
  intro i hi
  simp only [CPolynomial.coeff_add, hp i hi, hq i hi, CPolynomial.coeff_zero, add_zero]

theorem Order.neg {k : ℕ} {p : CPolynomial A} (hp : Order k p) : Order k (-p) := by
  intro i hi
  simp only [CPolynomial.coeff_neg, hp i hi, CPolynomial.coeff_zero, neg_zero]

theorem Order.sub {k : ℕ} {p q : CPolynomial A} (hp : Order k p) (hq : Order k q) :
    Order k (p - q) := by
  intro i hi
  simp only [CPolynomial.coeff_sub, hp i hi, hq i hi, CPolynomial.coeff_zero, sub_self]

/-- The stored ordinary derivative refines CompPoly differentiation below its cap. -/
theorem derivative_lowEq (k : ℕ) (p : CPolynomial A) :
    LowEq k (derivative k p) p.derivative := by
  intro i hi
  simp [hi, CPolynomial.coeff_derivative, mul_comm]

/-- CompPoly differentiation loses one coefficient of precision. -/
theorem LowEq.rawDerivative {k : ℕ} {p q : CPolynomial A} (hp : LowEq k p q) :
    LowEq (k - 1) p.derivative q.derivative := by
  intro i hi
  rw [CPolynomial.coeff_derivative, CPolynomial.coeff_derivative, hp (i + 1) (by omega)]

/-- Hasse differentiation loses precisely its index in the order bound. -/
theorem Order.hasse {m k j : ℕ} {p : CPolynomial A} (hp : Order m p) :
    Order (min k (m - j)) (hasse k j p) := by
  intro i hi
  have hik : i < k := by omega
  have hz := hp (i+j) (by omega)
  simp only [CPolynomial.coeff_zero] at hz
  simp [hik, hz, CPolynomial.coeff_zero]

/-- Guarded termwise integration is a right inverse to ordinary differentiation. -/
theorem rawDerivative_integral (p k : ℕ) [CharP E p] (ι : E →+* A) (hk : k ≤ p)
    (f : CPolynomial A) : LowEq (k - 1) (integral k ι f).derivative f :=
  (derivative_lowEq (k - 1) (integral k ι f)).symm.trans
    (derivative_integral p k ι hk f)

end More

end ArkLib.TruncatedSeries
