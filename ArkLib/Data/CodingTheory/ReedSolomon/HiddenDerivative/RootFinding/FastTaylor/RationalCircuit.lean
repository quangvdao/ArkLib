/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.UnitSeriesInverse
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.FiniteRecurrence

/-!
# Concrete rational differential-system circuits

Circuits have stored polynomial coefficients in the independent variable and
finitely many state variables. Evaluation executes coefficient-ring arithmetic;
causality is proved from circuit syntax rather than supplied by a caller.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.RationalCircuit

open CompPoly ArkLib.TruncatedSeries

variable {A : Type*} [CommRing A] [BEq A] [LawfulBEq A]

/-- A concrete arithmetic circuit with polynomial coefficient leaves. -/
inductive Circuit (A : Type*) [CommRing A] (d : ℕ) where
  /-- An already shifted coefficient polynomial in the local variable. -/
  | coefficient : CPolynomial A → Circuit A d
  /-- A state coordinate. -/
  | state : Fin d → Circuit A d
  /-- Circuit addition. -/
  | add : Circuit A d → Circuit A d → Circuit A d
  /-- Circuit multiplication. -/
  | mul : Circuit A d → Circuit A d → Circuit A d
  /-- Circuit negation. -/
  | neg : Circuit A d → Circuit A d

/-- Evaluate the actual arithmetic circuit at polynomial state coordinates. -/
def Circuit.eval {d : ℕ} (state : Fin d → CPolynomial A) : Circuit A d → CPolynomial A
  | .coefficient p => p
  | .state i => state i
  | .add p q => p.eval state + q.eval state
  | .mul p q => p.eval state * q.eval state
  | .neg p => -(p.eval state)

/-- Circuit evaluation at precision `m` cannot observe later state coefficients. -/
theorem Circuit.eval_lowEq {d : ℕ} (p : Circuit A d) (m : ℕ)
    (a b : Fin d → CPolynomial A) (hab : ∀ i, LowEq m (a i) (b i)) :
    LowEq m (p.eval a) (p.eval b) := by
  induction p with
  | coefficient p => exact LowEq.refl m p
  | state i => exact hab i
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq
  | neg p hp => exact hp.neg

/-- Interpret finite vector coefficients as coordinate polynomials. -/
def stateSeries {d : ℕ} (known : List (Fin d → A)) (i : Fin d) : CPolynomial A :=
  ofCoeffs known.length (fun n => (known.getD n 0) i)

/-- The polynomial representation copies exactly the finite coefficient list. -/
@[simp] theorem coeff_stateSeries {d : ℕ} (known : List (Fin d → A)) (i : Fin d) (n : ℕ) :
    (stateSeries known i).coeff n = (known.getD n 0) i := by
  rw [stateSeries, coeff_ofCoeffs]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

/-- Extending a completed prefix preserves its coordinate series through that precision. -/
theorem stateSeries_prefix {d : ℕ} (known output : List (Fin d → A))
    (h : known <+: output) (i : Fin d) :
    LowEq known.length (stateSeries known i) (stateSeries output i) := by
  obtain ⟨tail, rfl⟩ := h
  intro n hn
  simp only [coeff_stateSeries]
  rw [List.getD_append _ _ _ _ hn]

/-- Concrete numerators and common denominator for a rational vector field. -/
structure System (A : Type*) [CommRing A] (d : ℕ) where
  /-- Numerator arithmetic circuits. -/
  numerator : Fin d → Circuit A d
  /-- Common denominator arithmetic circuit. -/
  denominator : Circuit A d

variable [Nontrivial A]

/-- Evaluate a rational right-hand side using a finite computed denominator inverse. -/
def System.rhs {d : ℕ} (S : System A d) (k : ℕ) (u : Aˣ)
    (known : List (Fin d → A)) (i : Fin d) : CPolynomial A :=
  (S.numerator i).eval (stateSeries known) *
    UnitSeriesInverse.compute k (S.denominator.eval (stateSeries known)) u

/-- Rational evaluation inherits finite causality from circuits and inverse arithmetic. -/
theorem System.rhs_prefix {d : ℕ} (S : System A d) (k : ℕ) (u : Aˣ)
    (known output : List (Fin d → A)) (h : known <+: output) (hk : known.length ≤ k)
    (i : Fin d) : LowEq known.length (S.rhs k u known i) (S.rhs k u output i) := by
  exact ((S.numerator i).eval_lowEq _ _ _ (stateSeries_prefix known output h)).mul
    (UnitSeriesInverse.compute_lowEq k known.length _ _ u hk
      (S.denominator.eval_lowEq _ _ _ (stateSeries_prefix known output h)))

omit [Nontrivial A] in
/-- The supplied initial denominator unit remains the constant denominator of every extension. -/
theorem System.denominator_constant {d : ℕ} (S : System A d) (initial : Fin d → A)
    (output : List (Fin d → A)) (h : [initial] <+: output) (u : Aˣ)
    (hu : (S.denominator.eval (stateSeries [initial])).coeff 0 = (u : A)) :
    (S.denominator.eval (stateSeries output)).coeff 0 = (u : A) := by
  have he := S.denominator.eval_lowEq 1 (stateSeries [initial]) (stateSeries output)
    (stateSeries_prefix [initial] output h)
  exact (he 0 (by decide)).symm.trans hu

end ReedSolomon.HiddenDerivative.FastTaylor.RationalCircuit
