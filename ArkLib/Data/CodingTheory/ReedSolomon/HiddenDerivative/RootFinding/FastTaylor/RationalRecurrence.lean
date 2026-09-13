/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.RationalCircuit

/-!
# Executable finite rational vector recurrence

The coefficient ring supplies executable arithmetic and equality. The numerator
and denominator circuits are concrete, and the initial denominator unit and
required integer units are supplied with their laws. The differential state has
exactly `d` coordinates; inverse-series computation is internal arithmetic.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.RationalCircuit

open CompPoly ArkLib.TruncatedSeries

variable {A : Type*} [CommRing A] [BEq A] [LawfulBEq A] [Nontrivial A]
variable {d : ℕ}

/-- Lift a coefficient-ring unit to pointwise vector arithmetic. -/
def vectorUnit (u : Aˣ) : (Fin d → A)ˣ where
  val := fun _ => (u : A)
  inv := fun _ => (↑u⁻¹ : A)
  val_inv := by funext i; exact u.val_inv
  inv_val := by funext i; exact u.inv_val

/-- The scalar-divided rational recurrence as a finite triangular system. -/
def System.recurrence (S : System A d) (k : ℕ) (u : Aˣ) (index : ℕ → Aˣ) :
    FiniteRecurrence.System (Fin d → A) where
  leading n := vectorUnit (index n)
  remainder known := fun i => -(S.rhs k u known i).coeff (known.length - 1)

/-- Compute all `k` vector coefficients from the supplied initial state. -/
def System.run (S : System A d) (k : ℕ) (u : Aˣ) (index : ℕ → Aˣ)
    (initial : Fin d → A) : List (Fin d → A) :=
  (S.recurrence k u index).through [initial] k

/-- The requested finite state length is exact. -/
theorem System.length_run (S : System A d) (k : ℕ) (u : Aˣ) (index : ℕ → Aˣ)
    (initial : Fin d → A) (hk : 0 < k) : (S.run k u index initial).length = k := by
  exact (S.recurrence k u index).length_through [initial] k hk

/-- The initial vector is copied exactly. -/
theorem System.initial_prefix (S : System A d) (k : ℕ) (u : Aˣ) (index : ℕ → Aˣ)
    (initial : Fin d → A) : [initial] <+: S.run k u index initial :=
  (S.recurrence k u index).initial_prefix [initial] _

/-- The actual denominator of the output has the supplied unit constant coefficient. -/
theorem System.run_denominator_unit (S : System A d) (k : ℕ) (u : Aˣ)
    (index : ℕ → Aˣ) (initial : Fin d → A)
    (hu : (S.denominator.eval (stateSeries [initial])).coeff 0 = (u : A)) :
    (S.denominator.eval (stateSeries (S.run k u index initial))).coeff 0 = (u : A) :=
  S.denominator_constant initial _ (S.initial_prefix k u index initial) u hu

/-- The rational arithmetic uses a proved inverse of the actual output denominator. -/
theorem System.run_inverse_sound (S : System A d) (k : ℕ) (u : Aˣ)
    (index : ℕ → Aˣ) (initial : Fin d → A)
    (hu : (S.denominator.eval (stateSeries [initial])).coeff 0 = (u : A)) :
    LowEq k
      (S.denominator.eval (stateSeries (S.run k u index initial)) *
        UnitSeriesInverse.compute k
          (S.denominator.eval (stateSeries (S.run k u index initial))) u) 1 :=
  UnitSeriesInverse.compute_sound k _ u (S.run_denominator_unit k u index initial hu)

/-- Coefficient form of the differential equation on the completed finite output. -/
theorem System.run_coefficient (S : System A d) (k : ℕ) (u : Aˣ)
    (index : ℕ → Aˣ) (initial : Fin d → A)
    (hindex : ∀ n, 0 < n → n < k → (index n : A) = (n : A))
    (m : ℕ) (hm : m < k - 1) (i : Fin d) :
    (m + 1 : A) * ((S.run k u index initial).getD (m + 1) 0) i =
      (S.rhs k u (S.run k u index initial) i).coeff m := by
  let output := S.run k u index initial
  have hlen : output.length = k := S.length_run k u index initial (by omega)
  have ht : (output.take (1 + m)).length = 1 + m := by simp [hlen]; omega
  have hg := (S.recurrence k u index).gate_run [initial] m (k - 1) hm
  change (S.recurrence k u index).Gate (output.take (1 + m))
    (output.getD (1 + m) 0) at hg
  have hi := congrFun hg i
  change (index (output.take (1 + m)).length : A) * (output.getD (1 + m) 0) i +
    -(S.rhs k u (output.take (1 + m)) i).coeff ((output.take (1 + m)).length - 1) = 0 at hi
  rw [ht, hindex (1 + m) (by omega) (by omega)] at hi
  have hr := S.rhs_prefix k u (output.take (1 + m)) output (List.take_prefix _ _)
    (by rw [ht]; omega) i
  have hc := hr m (by rw [ht]; omega)
  rw [Nat.add_sub_cancel_left] at hi
  rw [hc] at hi
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg, Nat.add_comm, output] using hi

/-- Differential residual vanishes modulo `Z^(k-1)`; no unused tail equation is imposed. -/
theorem System.run_residual (S : System A d) (k : ℕ) (u : Aˣ)
    (index : ℕ → Aˣ) (initial : Fin d → A)
    (hindex : ∀ n, 0 < n → n < k → (index n : A) = (n : A)) (i : Fin d) :
    Order (k - 1)
      (derivative (k - 1) (stateSeries (S.run k u index initial) i) -
        S.rhs k u (S.run k u index initial) i) := by
  intro m hm
  simp only [CPolynomial.coeff_sub, coeff_derivative, if_pos hm,
    coeff_stateSeries, CPolynomial.coeff_zero]
  exact sub_eq_zero.mpr (S.run_coefficient k u index initial hindex m hm i)

/-- The finite differential residual and initial vector uniquely characterize the output. -/
theorem System.eq_run_of_residual (S : System A d) (k : ℕ) (u : Aˣ)
    (index : ℕ → Aˣ) (initial : Fin d → A) (output : List (Fin d → A))
    (hk : 0 < k) (hlen : output.length = k) (hinit : output.take 1 = [initial])
    (hindex : ∀ n, 0 < n → n < k → (index n : A) = (n : A))
    (hres : ∀ i, Order (k - 1)
      (derivative (k - 1) (stateSeries output i) - S.rhs k u output i)) :
    output = S.run k u index initial := by
  apply (S.recurrence k u index).eq_run_of_gates [initial] output (k - 1)
  · simp [hlen]; omega
  · exact hinit
  · intro m hm
    have ht : (output.take (1 + m)).length = 1 + m := by simp [hlen]; omega
    funext i
    change (index (output.take (1 + m)).length : A) * (output.getD (1 + m) 0) i +
      -(S.rhs k u (output.take (1 + m)) i).coeff
        ((output.take (1 + m)).length - 1) = 0
    rw [ht, hindex (1 + m) (by omega) (by omega), Nat.add_sub_cancel_left]
    have hr := S.rhs_prefix k u (output.take (1 + m)) output (List.take_prefix _ _)
      (by rw [ht]; omega) i
    rw [hr m (by rw [ht]; omega)]
    have h := hres i m hm
    simp only [CPolynomial.coeff_sub, coeff_derivative, if_pos hm, coeff_stateSeries,
      CPolynomial.coeff_zero] at h
    simpa [sub_eq_add_neg, Nat.add_comm] using h

/-- The denominator-cleared differential equation holds modulo `Z^(k-1)`. -/
theorem System.run_cleared_residual (S : System A d) (k : ℕ) (u : Aˣ)
    (index : ℕ → Aˣ) (initial : Fin d → A)
    (hu : (S.denominator.eval (stateSeries [initial])).coeff 0 = (u : A))
    (hindex : ∀ n, 0 < n → n < k → (index n : A) = (n : A)) (i : Fin d) :
    Order (k - 1)
      (S.denominator.eval (stateSeries (S.run k u index initial)) *
        derivative (k - 1) (stateSeries (S.run k u index initial) i) -
          (S.numerator i).eval (stateSeries (S.run k u index initial))) := by
  apply lowEq_iff_order_sub.mp
  have hd := lowEq_iff_order_sub.mpr (S.run_residual k u index initial hindex i)
  have hi := (S.run_inverse_sound k u index initial hu).mono (Nat.sub_le k 1)
  have hr := (LowEq.refl (k - 1) ((S.numerator i).eval
    (stateSeries (S.run k u index initial)))).mul hi
  have hp := (LowEq.refl (k - 1) (S.denominator.eval
    (stateSeries (S.run k u index initial)))).mul hd
  exact hp.trans (by simpa [System.rhs, mul_left_comm, mul_assoc] using hr)

/-- Each returned coordinate polynomial has degree below the requested length. -/
theorem System.run_degree (S : System A d) (k : ℕ) (u : Aˣ)
    (index : ℕ → Aˣ) (initial : Fin d → A) (hk : 0 < k) (i : Fin d) :
    (stateSeries (S.run k u index initial) i).toPoly.degree < (k : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [← CPolynomial.coeff_toPoly, coeff_stateSeries, List.getD_eq_default _ _ (by
    rw [S.length_run k u index initial hk]
    exact hn)]
  rfl

/-- Build integer division units from finite supplied data, with a harmless unused default. -/
def finiteIndexUnits (k : ℕ) (units : Fin k → Aˣ) (n : ℕ) : Aˣ :=
  if h : n < k then units ⟨n, h⟩ else 1

omit [BEq A] [LawfulBEq A] [Nontrivial A] in
/-- Only positive indices below the requested precision need the integer-value law. -/
theorem finiteIndexUnits_spec (k : ℕ) (units : Fin k → Aˣ)
    (hunits : ∀ n : Fin k, 0 < n.val → (units n : A) = (n.val : A))
    (n : ℕ) (hn : 0 < n) (hk : n < k) :
    (finiteIndexUnits k units n : A) = (n : A) := by
  simp [finiteIndexUnits, hk, hunits ⟨n, hk⟩ hn]

end ReedSolomon.HiddenDerivative.FastTaylor.RationalCircuit
