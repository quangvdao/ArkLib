/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.NormalizationArithmetic

/-!
# Executable all-fiber component descent

This is the polynomial-ring realization of the universal-agreement scan.  Every gcd is computed
over the stored function field, primitively descended, and then normalized to a polynomial that
is monic in the fiber variable.  Complements use monic division in `F[U][V]`, so every split has
an exact global product identity.  Consequently specialization at zeros of intermediate
denominators loses no fiber, and distinct generic components may still meet in a special fiber.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.ComponentDescent

open CompPoly CPolynomial
open OrdinaryNormalization

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private theorem semantic_ne_zero_of_monic {h : CBivariate F} (hh : h.monic) :
    CBivariate.toPoly h ≠ 0 := by
  intro hzero
  have hraw : CPolynomial.toPoly h = 0 := by
    rw [CBivariate.toPoly_eq_map] at hzero
    apply Polynomial.map_injective
      ((CPolynomial.ringEquiv (R := F)).toRingHom)
      (CPolynomial.ringEquiv (R := F)).injective
    simpa using hzero
  exact ((CPolynomial.monic_toPoly_iff h).mp hh).ne_zero hraw

/-- The leading coefficient of a divisor of a monic bivariate polynomial is a unit in `F[U]`.
This is the integrality step that permits denominator-free monic normalization. -/
theorem leadingCoeff_isUnit_of_dvd_monic {d h : CBivariate F}
    (hd : CBivariate.toPoly d ∣ CBivariate.toPoly h) (hh : h.monic) :
    IsUnit d.leadingCoeff.toPoly := by
  obtain ⟨q, hq⟩ := hd
  have hq0 : q ≠ 0 := by
    intro hz
    apply semantic_ne_zero_of_monic hh
    rw [hq, hz, MulZeroClass.mul_zero]
  change IsUnit (CBivariate.leadingCoeffY d).toPoly
  rw [CBivariate.leadingCoeffY_toPoly]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨q.leadingCoeff, ?_⟩
  have hm : (CBivariate.toPoly h).Monic := by
    simpa [CBivariate.toPoly_eq_map] using
      ((CPolynomial.monic_toPoly_iff h).mp hh).map
        ((CPolynomial.ringEquiv (R := F)).toRingHom)
  have hm := hm.leadingCoeff
  rw [hq, Polynomial.leadingCoeff_mul (CBivariate.toPoly d) q] at hm
  exact hm

private theorem leadingCoeff_eq_C {d : CBivariate F}
    (hu : IsUnit d.leadingCoeff.toPoly) :
    d.leadingCoeff = CPolynomial.C (d.leadingCoeff.coeff 0) := by
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.C_toPoly, CPolynomial.coeff_toPoly]
  exact Polynomial.eq_C_of_degree_eq_zero
    ((Polynomial.isUnit_iff_degree_eq_zero).mp hu)

private theorem leadingCoeff_coeff_zero_ne {d : CBivariate F}
    (hu : IsUnit d.leadingCoeff.toPoly) : d.leadingCoeff.coeff 0 ≠ 0 := by
  have heq := leadingCoeff_eq_C hu
  rw [heq, CPolynomial.C_toPoly, Polynomial.isUnit_C] at hu
  exact hu.ne_zero

/-- Scale a polynomial by the inverse of its constant fiber-leading coefficient. -/
def normalizeMonicY (d : CBivariate F) : CBivariate F :=
  CBivariate.CC ((d.leadingCoeff.coeff 0)⁻¹) * d

/-- Unit leading coefficient makes the executable normalization monic in `V`. -/
theorem normalizeMonicY_monic {d : CBivariate F} (hu : IsUnit d.leadingCoeff.toPoly) :
    (normalizeMonicY d).monic := by
  rw [CPolynomial.monic_toPoly_iff, normalizeMonicY, CPolynomial.toPoly_mul,
    show CBivariate.CC ((d.leadingCoeff.coeff 0)⁻¹) =
      CPolynomial.C (CPolynomial.C ((d.leadingCoeff.coeff 0)⁻¹)) from rfl,
    CPolynomial.C_toPoly]
  have hunit : IsUnit
      (CPolynomial.C ((d.leadingCoeff.coeff 0)⁻¹) : CPolynomial F) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨CPolynomial.C (d.leadingCoeff.coeff 0), ?_⟩
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly, CPolynomial.C_toPoly,
      CPolynomial.toPoly_one, ← Polynomial.C_mul]
    rw [inv_mul_cancel₀ (leadingCoeff_coeff_zero_ne hu), Polynomial.C_1]
  rw [Polynomial.Monic, Polynomial.leadingCoeff_C_mul_of_isUnit hunit]
  rw [← CPolynomial.leadingCoeff_toPoly d, leadingCoeff_eq_C hu]
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.coeff_C]
  simp only [if_pos]
  rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly, CPolynomial.C_toPoly,
    CPolynomial.toPoly_one, ← Polynomial.C_mul]
  rw [inv_mul_cancel₀ (leadingCoeff_coeff_zero_ne hu), Polynomial.C_1]

/-- Monic normalization is associated to the primitive descent and preserves global divisibility. -/
theorem normalizeMonicY_dvd {d h : CBivariate F} (hu : IsUnit d.leadingCoeff.toPoly)
    (hd : CBivariate.toPoly d ∣ CBivariate.toPoly h) :
    CBivariate.toPoly (normalizeMonicY d) ∣ CBivariate.toPoly h := by
  rw [normalizeMonicY, CBivariate.toPoly_mul]
  have hcc : CBivariate.toPoly
      (CBivariate.CC ((d.leadingCoeff.coeff 0)⁻¹) : CBivariate F) =
      Polynomial.C (Polynomial.C (d.leadingCoeff.coeff 0)⁻¹) := by
    exact CBivariate.CC_toPoly (R := F) (d.leadingCoeff.coeff 0)⁻¹
  rw [hcc]
  have hunit : IsUnit
      (Polynomial.C (Polynomial.C (d.leadingCoeff.coeff 0)⁻¹) :
        Polynomial (Polynomial F)) := by
    rw [Polynomial.isUnit_C, Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr
      (inv_ne_zero (leadingCoeff_coeff_zero_ne hu))
  exact (Associated.dvd_iff_dvd_left (associated_unit_mul_left _ _ hunit)).mpr hd

/-- Actual function-field gcd followed by primitive all-fiber descent and monic normalization. -/
def monicGlobalGcd (h e : CBivariate F) : CBivariate F :=
  normalizeMonicY (globalGcd h e)

theorem monicGlobalGcd_monic (h e : CBivariate F) (hh : h.monic) :
    (monicGlobalGcd h e).monic := by
  have hh0 : h ≠ 0 := by
    intro hz
    apply ((CPolynomial.monic_toPoly_iff h).mp hh).ne_zero
    simpa only [CPolynomial.toPoly_zero] using congrArg CPolynomial.toPoly hz
  apply normalizeMonicY_monic
  exact leadingCoeff_isUnit_of_dvd_monic (globalGcd_dvd h e hh0).1 hh

theorem monicGlobalGcd_semantic_dvd_left (h e : CBivariate F) (hh : h.monic) :
    CBivariate.toPoly (monicGlobalGcd h e) ∣ CBivariate.toPoly h := by
  let d := globalGcd h e
  have hh0 : h ≠ 0 := by
    intro hz
    apply ((CPolynomial.monic_toPoly_iff h).mp hh).ne_zero
    simpa only [CPolynomial.toPoly_zero] using congrArg CPolynomial.toPoly hz
  have hd := (globalGcd_dvd h e hh0).1
  exact normalizeMonicY_dvd (leadingCoeff_isUnit_of_dvd_monic hd hh) hd

theorem monicGlobalGcd_semantic_dvd_right (h e : CBivariate F) (hh : h.monic) :
    CBivariate.toPoly (monicGlobalGcd h e) ∣ CBivariate.toPoly e := by
  have hh0 : h ≠ 0 := by
    intro hz
    apply ((CPolynomial.monic_toPoly_iff h).mp hh).ne_zero
    simpa only [CPolynomial.toPoly_zero] using congrArg CPolynomial.toPoly hz
  have hdLeft := (globalGcd_dvd h e hh0).1
  have hdRight := (globalGcd_dvd h e hh0).2
  exact normalizeMonicY_dvd (leadingCoeff_isUnit_of_dvd_monic hdLeft hh) hdRight

theorem monicGlobalGcd_dvd_left (h e : CBivariate F) (hh : h.monic) :
    CPolynomial.toPoly (monicGlobalGcd h e) ∣ CPolynomial.toPoly h := by
  have hm := monicGlobalGcd_monic h e hh
  have hd := monicGlobalGcd_semantic_dvd_left h e hh
  rw [CBivariate.toPoly_eq_map, CBivariate.toPoly_eq_map] at hd
  exact (Polynomial.map_dvd_map
    ((CPolynomial.ringEquiv (R := F)).toRingHom)
    (CPolynomial.ringEquiv (R := F)).injective
    ((CPolynomial.monic_toPoly_iff _).mp hm)).mp hd

open scoped Classical in
/-- The descended monic factor is associated to the Euclidean gcd actually computed in
`F(U)[V]`.  This separates the computed fact from later squarefree/component assumptions. -/
theorem valueGlobal_monicGlobalGcd_associated (h e : CBivariate F) (hh : h.monic) :
    Associated (ClearDenominators.valueGlobal (monicGlobalGcd h e))
      (EuclideanDomain.gcd (ClearDenominators.valueGlobal h)
        (ClearDenominators.valueGlobal e)) := by
  let g := globalGcd h e
  have hh0 : h ≠ 0 := by
    intro hz
    apply ((CPolynomial.monic_toPoly_iff h).mp hh).ne_zero
    simpa only [CPolynomial.toPoly_zero] using congrArg CPolynomial.toPoly hz
  have hd := (globalGcd_dvd h e hh0).1
  have hu : IsUnit g.leadingCoeff.toPoly :=
    leadingCoeff_isUnit_of_dvd_monic hd hh
  have hcoeff : g.leadingCoeff.coeff 0 ≠ 0 :=
    leadingCoeff_coeff_zero_ne hu
  have hscalar : IsUnit
      (ClearDenominators.valueGlobal
        (CBivariate.CC ((g.leadingCoeff.coeff 0)⁻¹) : CBivariate F)) := by
    rw [show (CBivariate.CC ((g.leadingCoeff.coeff 0)⁻¹) : CBivariate F) =
      CPolynomial.C (CPolynomial.C ((g.leadingCoeff.coeff 0)⁻¹)) from rfl,
      ClearDenominators.valueGlobal_C, Polynomial.isUnit_C]
    apply isUnit_iff_ne_zero.mpr
    apply RatFunc.algebraMap_ne_zero
    rw [CPolynomial.C_toPoly]
    exact Polynomial.C_ne_zero.mpr (inv_ne_zero hcoeff)
  have hnormal : Associated
      (ClearDenominators.valueGlobal (normalizeMonicY g))
      (ClearDenominators.valueGlobal g) := by
    rw [normalizeMonicY, ClearDenominators.valueGlobal_mul]
    exact associated_unit_mul_left _ _ hscalar
  exact hnormal.trans (globalGcd_associated h e)

/-- The exact global complement, kept at the bivariate storage type. -/
def exactComplement (h e : CBivariate F) : CBivariate F :=
  h.divByMonic (monicGlobalGcd h e)

/-- Exact complementary division for the computed monic global gcd. -/
theorem monicGlobalGcd_mul_divByMonic (h e : CBivariate F) (hh : h.monic) :
    monicGlobalGcd h e * exactComplement h e = h := by
  have hdmonic := monicGlobalGcd_monic h e hh
  have hmod : h.modByMonic (monicGlobalGcd h e) = 0 := by
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hdmonic,
      CPolynomial.toPoly_zero,
      Polynomial.modByMonic_eq_zero_iff_dvd
        ((CPolynomial.monic_toPoly_iff _).mp hdmonic)]
    exact monicGlobalGcd_dvd_left h e hh
  have hid := CPolynomial.modByMonic_add_mul_divByMonic
    h (monicGlobalGcd h e) hdmonic
  simpa only [exactComplement, hmod, zero_add] using hid

open scoped Classical in
/-- On a generically squarefree parent, the complementary component is coprime to the tested
residual in the actual stored function field. -/
theorem divByMonic_generic_isCoprime (h e : CBivariate F) (hh : h.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    IsCoprime
      (ClearDenominators.valueGlobal (exactComplement h e))
      (ClearDenominators.valueGlobal e) := by
  let d := ClearDenominators.valueGlobal (monicGlobalGcd h e)
  let q := ClearDenominators.valueGlobal (exactComplement h e)
  let a := ClearDenominators.valueGlobal h
  let r := ClearDenominators.valueGlobal e
  have hfac : d * q = a := by
    simpa only [d, q, a, ClearDenominators.valueGlobal_mul] using congrArg
      (ClearDenominators.valueGlobal (F := F)) (monicGlobalGcd_mul_divByMonic h e hh)
  have hdg : Associated d (EuclideanDomain.gcd a r) := by
    simpa only [d, a, r] using valueGlobal_monicGlobalGcd_associated h e hh
  have hrel : IsRelPrime d q := IsRelPrime.of_squarefree_mul (hfac.symm ▸ hs)
  apply IsRelPrime.isCoprime
  intro z hzq hzr
  have hza : z ∣ a := hzq.trans ⟨d, by rw [← hfac]; ring⟩
  have hzgcd : z ∣ EuclideanDomain.gcd a r := EuclideanDomain.dvd_gcd hza hzr
  have hzd : z ∣ d := hzgcd.trans hdg.symm.dvd
  exact hrel hzd hzq

/-- A live global component and the positions whose residual vanishes identically on it. -/
structure Block (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  modulus : CBivariate F
  universal : List ℕ

inductive Decision where
  | universal
  | coprime
  | split
  deriving DecidableEq, BEq, Repr

structure StepOutput (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  decision : Decision
  blocks : List (Block F)

/-- One global three-way split.  The generic gcd decision is descended before comparison. -/
def step (i : ℕ) (e : CBivariate F) (b : Block F) : StepOutput F :=
  let d := monicGlobalGcd b.modulus e
  if d == b.modulus then
    ⟨.universal, [⟨b.modulus, i :: b.universal⟩]⟩
  else if d == 1 then
    ⟨.coprime, [b]⟩
  else
    ⟨.split, [⟨d, i :: b.universal⟩,
      ⟨exactComplement b.modulus e, b.universal⟩]⟩

theorem step_product (i : ℕ) (e : CBivariate F) (b : Block F) (hb : b.modulus.monic) :
    ((step i e b).blocks.map Block.modulus).prod = b.modulus := by
  unfold step
  dsimp only
  split
  · simp
  · split
    · simp
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have hdmonic := monicGlobalGcd_monic b.modulus e hb
      have hmod : b.modulus.modByMonic (monicGlobalGcd b.modulus e) = 0 := by
        apply CPolynomial.toPoly_injective
        rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hdmonic,
          CPolynomial.toPoly_zero,
          Polynomial.modByMonic_eq_zero_iff_dvd
            ((CPolynomial.monic_toPoly_iff _).mp hdmonic)]
        exact monicGlobalGcd_dvd_left b.modulus e hb
      have hid := CPolynomial.modByMonic_add_mul_divByMonic
        b.modulus (monicGlobalGcd b.modulus e) hdmonic
      rw [hmod, zero_add] at hid
      exact hid

private theorem divByMonic_monic_of_dvd (h d : CBivariate F)
    (hh : h.monic) (hd : d.monic)
    (hdiv : CPolynomial.toPoly d ∣ CPolynomial.toPoly h) :
    (h.divByMonic d).monic := by
  have hmod : h.modByMonic d = 0 := by
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hd,
      CPolynomial.toPoly_zero,
      Polynomial.modByMonic_eq_zero_iff_dvd
        ((CPolynomial.monic_toPoly_iff _).mp hd)]
    exact hdiv
  have hmul := CPolynomial.modByMonic_add_mul_divByMonic h d hd
  rw [hmod, zero_add] at hmul
  apply (CPolynomial.monic_toPoly_iff _).mpr
  apply ((CPolynomial.monic_toPoly_iff _).mp hd).of_mul_monic_left
  rw [← CPolynomial.toPoly_mul, hmul]
  exact (CPolynomial.monic_toPoly_iff h).mp hh

theorem step_monic (i : ℕ) (e : CBivariate F) (b : Block F) (hb : b.modulus.monic) :
    ∀ c ∈ (step i e b).blocks, c.modulus.monic := by
  intro c hc
  unfold step at hc
  dsimp only at hc
  split at hc
  · simp only [List.mem_singleton] at hc
    subst c
    exact hb
  · split at hc
    · simp only [List.mem_singleton] at hc
      subst c
      exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact monicGlobalGcd_monic b.modulus e hb
      · exact divByMonic_monic_of_dvd b.modulus (monicGlobalGcd b.modulus e) hb
          (monicGlobalGcd_monic b.modulus e hb)
          (monicGlobalGcd_dvd_left b.modulus e hb)

/-- Every child is a global polynomial divisor of its parent. -/
theorem step_dvd (i : ℕ) (e : CBivariate F) (b : Block F) (hb : b.modulus.monic) :
    ∀ c ∈ (step i e b).blocks,
      CBivariate.toPoly c.modulus ∣ CBivariate.toPoly b.modulus := by
  intro c hc
  unfold step at hc
  dsimp only at hc
  split at hc
  · simp only [List.mem_singleton] at hc
    subst c
    exact dvd_rfl
  · split at hc
    · simp only [List.mem_singleton] at hc
      subst c
      exact dvd_rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact monicGlobalGcd_semantic_dvd_left b.modulus e hb
      · refine ⟨CBivariate.toPoly (monicGlobalGcd b.modulus e), ?_⟩
        have hdmonic := monicGlobalGcd_monic b.modulus e hb
        have hmod : b.modulus.modByMonic (monicGlobalGcd b.modulus e) = 0 := by
          apply CPolynomial.toPoly_injective
          rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hdmonic,
            CPolynomial.toPoly_zero,
            Polynomial.modByMonic_eq_zero_iff_dvd
              ((CPolynomial.monic_toPoly_iff _).mp hdmonic)]
          exact monicGlobalGcd_dvd_left b.modulus e hb
        have hid := CPolynomial.modByMonic_add_mul_divByMonic
          b.modulus (monicGlobalGcd b.modulus e) hdmonic
        rw [hmod, zero_add] at hid
        rw [mul_comm, ← CBivariate.toPoly_mul]
        exact congrArg CBivariate.toPoly hid.symm

/-- Squarefree input components remain squarefree through the global split. -/
theorem step_squarefree (i : ℕ) (e : CBivariate F) (b : Block F)
    (hb : b.modulus.monic) (hs : Squarefree (CBivariate.toPoly b.modulus)) :
    ∀ c ∈ (step i e b).blocks, Squarefree (CBivariate.toPoly c.modulus) :=
  fun c hc => hs.squarefree_of_dvd (step_dvd i e b hb c hc)

private theorem valueGlobal_dvd_of_semantic_dvd {a b : CBivariate F}
    (h : CBivariate.toPoly a ∣ CBivariate.toPoly b) :
    ClearDenominators.valueGlobal a ∣ ClearDenominators.valueGlobal b := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.map (algebraMap (Polynomial F) (RatFunc F)), ?_⟩
  unfold ClearDenominators.valueGlobal
  rw [hq, Polynomial.map_mul]

/-- Generic squarefreeness is inherited by every executed child. -/
theorem step_generic_squarefree (i : ℕ) (e : CBivariate F) (b : Block F)
    (hb : b.modulus.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal b.modulus)) :
    ∀ c ∈ (step i e b).blocks,
      Squarefree (ClearDenominators.valueGlobal c.modulus) :=
  fun c hc => hs.squarefree_of_dvd
    (valueGlobal_dvd_of_semantic_dvd (step_dvd i e b hb c hc))

/-- A step can add only its current position. -/
theorem step_labels (i : ℕ) (e : CBivariate F) (b : Block F) :
    ∀ c ∈ (step i e b).blocks, ∀ j ∈ c.universal,
      j = i ∨ j ∈ b.universal := by
  simp only [step]
  split
  · simp
  · split <;> simp <;> aesop

/-- Labels already recorded on a block are strictly behind the scan cursor. -/
def Before (b : Block F) (i : ℕ) : Prop := ∀ j ∈ b.universal, j < i

theorem step_before (i : ℕ) (e : CBivariate F) (b : Block F) (hb : Before b i) :
    ∀ c ∈ (step i e b).blocks, Before c (i + 1) := by
  intro c hc j hj
  rcases step_labels i e b c hc j hj with rfl | hjb
  · omega
  · exact Nat.lt_succ_of_lt (hb j hjb)

theorem step_labels_nodup (i : ℕ) (e : CBivariate F) (b : Block F)
    (hbefore : Before b i) (hnodup : b.universal.Nodup) :
    ∀ c ∈ (step i e b).blocks, c.universal.Nodup := by
  intro c hc
  unfold step at hc
  dsimp only at hc
  split at hc
  · simp only [List.mem_singleton] at hc
    subst c
    simp only [List.nodup_cons]
    exact ⟨fun hi => Nat.lt_irrefl i (hbefore i hi), hnodup⟩
  · split at hc
    · simp only [List.mem_singleton] at hc
      subst c
      exact hnodup
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp only [List.nodup_cons]
        exact ⟨fun hi => Nat.lt_irrefl i (hbefore i hi), hnodup⟩
      · exact hnodup

def advance (i : ℕ) (e : CBivariate F) (blocks : List (Block F)) : List (Block F) :=
  (blocks.map (step i e)).flatMap StepOutput.blocks

theorem advance_before (i : ℕ) (e : CBivariate F) (blocks : List (Block F))
    (hb : ∀ b ∈ blocks, Before b i) :
    ∀ c ∈ advance i e blocks, Before c (i + 1) := by
  intro c hc
  obtain ⟨b, hbb, hbc⟩ : ∃ b ∈ blocks, c ∈ (step i e b).blocks := by
    simpa [advance] using hc
  exact step_before i e b (hb b hbb) c hbc

theorem advance_labels_nodup (i : ℕ) (e : CBivariate F) (blocks : List (Block F))
    (hbefore : ∀ b ∈ blocks, Before b i)
    (hnodup : ∀ b ∈ blocks, b.universal.Nodup) :
    ∀ c ∈ advance i e blocks, c.universal.Nodup := by
  intro c hc
  obtain ⟨b, hbb, hbc⟩ : ∃ b ∈ blocks, c ∈ (step i e b).blocks := by
    simpa [advance] using hc
  exact step_labels_nodup i e b (hbefore b hbb) (hnodup b hbb) c hbc

structure Stage where
  position : ℕ
  decisions : List Decision

structure Output (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  blocks : List (Block F)
  transcript : List Stage

def scanFrom (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F)) : Output F :=
  match residuals with
  | [] => ⟨blocks, []⟩
  | e :: es =>
    let steps := blocks.map (step i e)
    let out := scanFrom (i + 1) es (steps.flatMap StepOutput.blocks)
    ⟨out.blocks, ⟨i, steps.map StepOutput.decision⟩ :: out.transcript⟩

/-- Run the actual global component scan from one monic chart equation. -/
def run (h : CBivariate F) (residuals : List (CBivariate F)) : Output F :=
  scanFrom 0 residuals [⟨h, []⟩]

@[simp] theorem mem_advance (i : ℕ) (e : CBivariate F) (blocks : List (Block F))
    (c : Block F) : c ∈ advance i e blocks ↔
      ∃ b ∈ blocks, c ∈ (step i e b).blocks := by
  simp [advance]

theorem advance_product (i : ℕ) (e : CBivariate F) (blocks : List (Block F))
    (hb : ∀ b ∈ blocks, b.modulus.monic) :
    ((advance i e blocks).map Block.modulus).prod =
      (blocks.map Block.modulus).prod := by
  induction blocks with
  | nil => simp [advance]
  | cons b blocks ih =>
    simp only [advance, List.map_cons, List.flatMap_cons, List.map_append,
      List.prod_append, List.prod_cons]
    rw [step_product i e b (hb b (by simp))]
    exact congrArg (b.modulus * ·)
      (ih (fun c hc => hb c (by simp [hc])))

theorem advance_monic (i : ℕ) (e : CBivariate F) (blocks : List (Block F))
    (hb : ∀ b ∈ blocks, b.modulus.monic) :
    ∀ c ∈ advance i e blocks, c.modulus.monic := by
  intro c hc
  obtain ⟨b, hbb, hbc⟩ := (mem_advance i e blocks c).mp hc
  exact step_monic i e b (hb b hbb) c hbc

theorem advance_generic_squarefree (i : ℕ) (e : CBivariate F)
    (blocks : List (Block F))
    (hb : ∀ b ∈ blocks, b.modulus.monic)
    (hs : ∀ b ∈ blocks, Squarefree (ClearDenominators.valueGlobal b.modulus)) :
    ∀ c ∈ advance i e blocks,
      Squarefree (ClearDenominators.valueGlobal c.modulus) := by
  intro c hc
  obtain ⟨b, hbb, hbc⟩ := (mem_advance i e blocks c).mp hc
  exact step_generic_squarefree i e b (hb b hbb) (hs b hbb) c hbc

theorem scanFrom_product (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F)) (hb : ∀ b ∈ blocks, b.modulus.monic) :
    (((scanFrom i residuals blocks).blocks.map Block.modulus).prod) =
      (blocks.map Block.modulus).prod := by
  induction residuals generalizing i blocks with
  | nil => rfl
  | cons e es ih =>
    rw [show (scanFrom i (e :: es) blocks).blocks =
      (scanFrom (i + 1) es (advance i e blocks)).blocks from rfl]
    rw [ih (i := i + 1) (blocks := advance i e blocks) (advance_monic i e blocks hb),
      advance_product i e blocks hb]

/-- The returned global components multiply exactly to the original chart equation. -/
theorem run_product (h : CBivariate F) (residuals : List (CBivariate F)) (hh : h.monic) :
    (((run h residuals).blocks.map Block.modulus).prod) = h := by
  simpa [run] using scanFrom_product 0 residuals [⟨h, []⟩]
    (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact hh)

theorem scanFrom_monic (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F)) (hb : ∀ b ∈ blocks, b.modulus.monic) :
    ∀ c ∈ (scanFrom i residuals blocks).blocks, c.modulus.monic := by
  induction residuals generalizing i blocks with
  | nil => exact hb
  | cons e es ih =>
    exact ih (i := i + 1) (blocks := advance i e blocks) (advance_monic i e blocks hb)

theorem scanFrom_squarefree (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F))
    (hb : ∀ b ∈ blocks, b.modulus.monic)
    (hs : ∀ b ∈ blocks, Squarefree (CBivariate.toPoly b.modulus)) :
    ∀ c ∈ (scanFrom i residuals blocks).blocks,
      Squarefree (CBivariate.toPoly c.modulus) := by
  induction residuals generalizing i blocks with
  | nil => exact hs
  | cons e es ih =>
      apply ih (i := i + 1) (blocks := advance i e blocks)
        (advance_monic i e blocks hb)
      intro c hc
      obtain ⟨b, hbb, hbc⟩ := (mem_advance i e blocks c).mp hc
      exact step_squarefree i e b (hb b hbb) (hs b hbb) c hbc

theorem scanFrom_generic_squarefree (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F))
    (hb : ∀ b ∈ blocks, b.modulus.monic)
    (hs : ∀ b ∈ blocks, Squarefree (ClearDenominators.valueGlobal b.modulus)) :
    ∀ c ∈ (scanFrom i residuals blocks).blocks,
      Squarefree (ClearDenominators.valueGlobal c.modulus) := by
  induction residuals generalizing i blocks with
  | nil => exact hs
  | cons e es ih =>
      exact ih (i := i + 1) (blocks := advance i e blocks)
        (advance_monic i e blocks hb) (advance_generic_squarefree i e blocks hb hs)

theorem scanFrom_before (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F)) (hb : ∀ b ∈ blocks, Before b i) :
    ∀ c ∈ (scanFrom i residuals blocks).blocks,
      Before c (i + residuals.length) := by
  induction residuals generalizing i blocks with
  | nil => simpa only [scanFrom, List.length_nil, Nat.add_zero] using hb
  | cons e es ih =>
      rw [show (scanFrom i (e :: es) blocks).blocks =
        (scanFrom (i + 1) es (advance i e blocks)).blocks from rfl]
      have hnext := ih (i := i + 1)
        (blocks := advance i e blocks) (advance_before i e blocks hb)
      simpa only [List.length_cons, Nat.add_assoc, Nat.one_add] using hnext

theorem scanFrom_labels_nodup (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F)) (hbefore : ∀ b ∈ blocks, Before b i)
    (hnodup : ∀ b ∈ blocks, b.universal.Nodup) :
    ∀ c ∈ (scanFrom i residuals blocks).blocks, c.universal.Nodup := by
  induction residuals generalizing i blocks with
  | nil => exact hnodup
  | cons e es ih =>
      exact ih (i := i + 1) (blocks := advance i e blocks)
        (advance_before i e blocks hbefore)
        (advance_labels_nodup i e blocks hbefore hnodup)

theorem run_monic (h : CBivariate F) (residuals : List (CBivariate F)) (hh : h.monic) :
    ∀ c ∈ (run h residuals).blocks, c.modulus.monic := by
  apply scanFrom_monic
  intro b hb
  simp only [List.mem_singleton] at hb
  subst b
  exact hh

theorem run_squarefree (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (CBivariate.toPoly h)) :
    ∀ c ∈ (run h residuals).blocks, Squarefree (CBivariate.toPoly c.modulus) := by
  apply scanFrom_squarefree 0 residuals [⟨h, []⟩]
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact hh
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact hs

theorem run_generic_squarefree (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    ∀ c ∈ (run h residuals).blocks,
      Squarefree (ClearDenominators.valueGlobal c.modulus) := by
  apply scanFrom_generic_squarefree 0 residuals [⟨h, []⟩]
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact hh
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact hs

/-- Every recorded position is a valid input index. -/
theorem run_labels_lt (h : CBivariate F) (residuals : List (CBivariate F)) :
    ∀ b ∈ (run h residuals).blocks, ∀ i ∈ b.universal, i < residuals.length := by
  simpa [run, Before] using scanFrom_before 0 residuals [⟨h, []⟩]
    (by simp [Before])

/-- A received position is recorded at most once on each returned component. -/
theorem run_labels_nodup (h : CBivariate F) (residuals : List (CBivariate F)) :
    ∀ b ∈ (run h residuals).blocks, b.universal.Nodup := by
  simpa [run] using scanFrom_labels_nodup 0 residuals [⟨h, []⟩]
    (by simp [Before]) (by simp)

/-- A label certifies global polynomial divisibility by the corresponding residual. -/
def UniversalAt (b : Block F) (i : ℕ) (e : CBivariate F) : Prop :=
  i ∈ b.universal → CBivariate.toPoly b.modulus ∣ CBivariate.toPoly e

/-- Exact zero/unit classification over the stored function field.  Universal labels carry
global divisibility; every other label carries generic coprimality in `F(U)[V]`. -/
def GenericClassified (b : Block F) (i : ℕ) (e : CBivariate F) : Prop :=
  (i ∈ b.universal → CBivariate.toPoly b.modulus ∣ CBivariate.toPoly e) ∧
    (i ∉ b.universal → IsCoprime
      (ClearDenominators.valueGlobal b.modulus)
      (ClearDenominators.valueGlobal e))

theorem step_mem_universal_iff (i j : ℕ) (e : CBivariate F) (b : Block F)
    (hji : j ≠ i) :
    ∀ c ∈ (step i e b).blocks, (j ∈ c.universal ↔ j ∈ b.universal) := by
  simp only [step]
  split
  · simp [hji]
  · split <;> simp [hji]

open scoped Classical in
theorem step_generic_classified (i : ℕ) (e : CBivariate F) (b : Block F)
    (hb : b.modulus.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal b.modulus))
    (hbefore : Before b i) :
    ∀ c ∈ (step i e b).blocks, GenericClassified c i e := by
  intro c hc
  unfold step at hc
  dsimp only at hc
  split at hc
  · rename_i heq
    simp only [List.mem_singleton] at hc
    subst c
    constructor
    · intro _
      have hd := monicGlobalGcd_semantic_dvd_right b.modulus e hb
      rw [LawfulBEq.eq_of_beq heq] at hd
      exact hd
    · intro hi
      exact False.elim (hi (by simp))
  · split at hc
    · rename_i _ heq
      simp only [List.mem_singleton] at hc
      subst c
      constructor
      · intro hi
        exact False.elim (Nat.lt_irrefl i (hbefore i hi))
      · intro _
        have hassoc := valueGlobal_monicGlobalGcd_associated b.modulus e hb
        rw [LawfulBEq.eq_of_beq heq] at hassoc
        have hone : ClearDenominators.valueGlobal (1 : CBivariate F) = 1 := by
          unfold ClearDenominators.valueGlobal
          rw [CBivariate.toPoly_one, Polynomial.map_one]
        rw [hone] at hassoc
        exact EuclideanDomain.gcd_isUnit_iff.mp (hassoc.isUnit isUnit_one)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · constructor
        · intro _
          exact monicGlobalGcd_semantic_dvd_right b.modulus e hb
        · intro hi
          exact False.elim (hi (by simp))
      · constructor
        · intro hi
          exact False.elim (Nat.lt_irrefl i (hbefore i hi))
        · intro _
          exact divByMonic_generic_isCoprime b.modulus e hb hs

theorem step_universalAt_current (i : ℕ) (e : CBivariate F) (b : Block F)
    (hb : b.modulus.monic) (hbefore : Before b i) :
    ∀ c ∈ (step i e b).blocks, UniversalAt c i e := by
  intro c hc hi
  unfold step at hc
  dsimp only at hc
  split at hc
  · rename_i heq
    simp only [List.mem_singleton] at hc
    subst c
    have hd := monicGlobalGcd_semantic_dvd_right b.modulus e hb
    rw [LawfulBEq.eq_of_beq heq] at hd
    exact hd
  · split at hc
    · simp only [List.mem_singleton] at hc
      subst c
      exact False.elim (Nat.lt_irrefl i (hbefore i hi))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact monicGlobalGcd_semantic_dvd_right b.modulus e hb
      · exact False.elim (Nat.lt_irrefl i (hbefore i hi))

theorem step_preserves_universalAt (i j : ℕ) (e q : CBivariate F) (b : Block F)
    (hb : b.modulus.monic) (hji : j ≠ i) (hq : UniversalAt b j q) :
    ∀ c ∈ (step i e b).blocks, UniversalAt c j q := by
  intro c hc hj
  exact (step_dvd i e b hb c hc).trans
    (hq ((step_mem_universal_iff i j e b hji c hc).mp hj))

theorem step_preserves_genericClassified (i j : ℕ) (e q : CBivariate F)
    (b : Block F) (hb : b.modulus.monic) (hji : j ≠ i)
    (hq : GenericClassified b j q) :
    ∀ c ∈ (step i e b).blocks, GenericClassified c j q := by
  intro c hc
  have hmem := step_mem_universal_iff i j e b hji c hc
  have hd := valueGlobal_dvd_of_semantic_dvd (step_dvd i e b hb c hc)
  exact ⟨fun hj => (step_dvd i e b hb c hc).trans (hq.1 (hmem.mp hj)),
    fun hj => (hq.2 (fun hjb => hj (hmem.mpr hjb))).of_isCoprime_of_dvd_left hd⟩

theorem scanFrom_preserves_universalAt (i j : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F)) (q : CBivariate F) (hji : j < i)
    (hb : ∀ b ∈ blocks, b.modulus.monic)
    (hq : ∀ b ∈ blocks, UniversalAt b j q) :
    ∀ c ∈ (scanFrom i residuals blocks).blocks, UniversalAt c j q := by
  induction residuals generalizing i blocks with
  | nil => exact hq
  | cons e es ih =>
      apply ih (i := i + 1) (blocks := advance i e blocks)
        (Nat.lt_succ_of_lt hji) (advance_monic i e blocks hb)
      intro c hc
      obtain ⟨b, hbb, hbc⟩ := (mem_advance i e blocks c).mp hc
      exact step_preserves_universalAt i j e q b (hb b hbb)
        (Nat.ne_of_lt hji) (hq b hbb) c hbc

theorem scanFrom_preserves_genericClassified (i j : ℕ)
    (residuals : List (CBivariate F)) (blocks : List (Block F))
    (q : CBivariate F) (hji : j < i)
    (hb : ∀ b ∈ blocks, b.modulus.monic)
    (hq : ∀ b ∈ blocks, GenericClassified b j q) :
    ∀ c ∈ (scanFrom i residuals blocks).blocks, GenericClassified c j q := by
  induction residuals generalizing i blocks with
  | nil => exact hq
  | cons e es ih =>
      apply ih (i := i + 1) (blocks := advance i e blocks)
        (Nat.lt_succ_of_lt hji) (advance_monic i e blocks hb)
      intro c hc
      obtain ⟨b, hbb, hbc⟩ := (mem_advance i e blocks c).mp hc
      exact step_preserves_genericClassified i j e q b (hb b hbb)
        (Nat.ne_of_lt hji) (hq b hbb) c hbc

theorem scanFrom_universalAt (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F))
    (hb : ∀ b ∈ blocks, b.modulus.monic)
    (hbefore : ∀ b ∈ blocks, Before b i) :
    ∀ n e, residuals[n]? = some e →
      ∀ c ∈ (scanFrom i residuals blocks).blocks, UniversalAt c (i + n) e := by
  induction residuals generalizing i blocks with
  | nil => simp
  | cons e es ih =>
      intro n q hq
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
          subst q
          simp only [Nat.add_zero]
          apply scanFrom_preserves_universalAt (i + 1) i es (advance i e blocks) e
            (Nat.lt_succ_self i) (advance_monic i e blocks hb)
          intro c hc
          obtain ⟨b, hbb, hbc⟩ := (mem_advance i e blocks c).mp hc
          exact step_universalAt_current i e b (hb b hbb) (hbefore b hbb) c hbc
      | succ n =>
          have htail := ih (i + 1) (advance i e blocks)
            (advance_monic i e blocks hb) (advance_before i e blocks hbefore) n q hq
          rw [show (scanFrom i (e :: es) blocks).blocks =
            (scanFrom (i + 1) es (advance i e blocks)).blocks from rfl]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem scanFrom_genericClassified (i : ℕ) (residuals : List (CBivariate F))
    (blocks : List (Block F))
    (hb : ∀ b ∈ blocks, b.modulus.monic)
    (hs : ∀ b ∈ blocks, Squarefree (ClearDenominators.valueGlobal b.modulus))
    (hbefore : ∀ b ∈ blocks, Before b i) :
    ∀ n e, residuals[n]? = some e →
      ∀ c ∈ (scanFrom i residuals blocks).blocks,
        GenericClassified c (i + n) e := by
  induction residuals generalizing i blocks with
  | nil => simp
  | cons e es ih =>
      intro n q hq
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
          subst q
          simp only [Nat.add_zero]
          apply scanFrom_preserves_genericClassified (i + 1) i es
            (advance i e blocks) e (Nat.lt_succ_self i) (advance_monic i e blocks hb)
          intro c hc
          obtain ⟨b, hbb, hbc⟩ := (mem_advance i e blocks c).mp hc
          exact step_generic_classified i e b (hb b hbb) (hs b hbb)
            (hbefore b hbb) c hbc
      | succ n =>
          have htail := ih (i + 1) (advance i e blocks)
            (advance_monic i e blocks hb)
            (advance_generic_squarefree i e blocks hb hs)
            (advance_before i e blocks hbefore) n q hq
          rw [show (scanFrom i (e :: es) blocks).blocks =
            (scanFrom (i + 1) es (advance i e blocks)).blocks from rfl]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Every returned universal label certifies a global divisor, including on denominator-zero
fibers after specialization. -/
theorem run_universal_dvd (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) :
    ∀ n e, residuals[n]? = some e → ∀ b ∈ (run h residuals).blocks,
      n ∈ b.universal → CBivariate.toPoly b.modulus ∣ CBivariate.toPoly e := by
  simpa [run, UniversalAt] using scanFrom_universalAt 0 residuals [⟨h, []⟩]
    (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact hh)
    (by simp [Before])

/-- Every supplied residual receives its exact generic zero/unit classification on every
returned component.  Generic squarefreeness is an explicit chart premise. -/
theorem run_genericClassified (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    ∀ n e, residuals[n]? = some e → ∀ b ∈ (run h residuals).blocks,
      GenericClassified b n e := by
  simpa [run] using scanFrom_genericClassified 0 residuals [⟨h, []⟩]
    (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact hh)
    (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact hs)
    (by simp [Before])

/-- Evaluate a global bivariate polynomial at an arbitrary extension point. -/
noncomputable def evalAt {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (h : CBivariate F) : K :=
  (CBivariate.toPoly h).eval₂ (Polynomial.eval₂RingHom phi u) v

private theorem exists_evalAt_zero_of_prod
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (blocks : List (Block F))
    (hz : evalAt phi u v ((blocks.map Block.modulus).prod) = 0) :
    ∃ b ∈ blocks, evalAt phi u v b.modulus = 0 := by
  induction blocks with
  | nil =>
      exfalso
      change evalAt phi u v (1 : CBivariate F) = 0 at hz
      rw [evalAt, CBivariate.toPoly_eq_map, CPolynomial.toPoly_one,
        Polynomial.map_one, Polynomial.eval₂_one] at hz
      exact (one_ne_zero (α := K)) hz
  | cons b blocks ih =>
    simp only [List.map_cons, List.prod_cons] at hz
    rw [evalAt, CBivariate.toPoly_mul, Polynomial.eval₂_mul] at hz
    rcases mul_eq_zero.mp hz with hb | hrest
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨c, hc, hcz⟩ := ih hrest
      exact ⟨c, by simp [hc], hcz⟩

/-- Every geometric point of the input lies on at least one returned global component after any
coefficient-field extension.  No denominator restriction, separability, or unramified premise is
used; at a meeting fiber the witness need not be unique. -/
theorem run_allFiber_coverage
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (h : CBivariate F) (residuals : List (CBivariate F)) (hh : h.monic)
    (hroot : evalAt phi u v h = 0) :
    ∃ b ∈ (run h residuals).blocks, evalAt phi u v b.modulus = 0 := by
  apply exists_evalAt_zero_of_prod phi u v (run h residuals).blocks
  rw [run_product h residuals hh]
  exact hroot

end Polynomial.FunctionFieldAlgorithms.ComponentDescent
