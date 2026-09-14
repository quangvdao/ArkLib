/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimaryAccounting
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Localization preserving nonreduced fibers

Localization retains exactly the unit-tagged children of the canonical primary splitter.
It performs neither fiber radicalization nor a characteristic-degree check.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial FirstOrderNormDecoder.D5

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- Keep the unit side of primary splitting without changing its fiber multiplicities. -/
def localizeFiber (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) : List (TowerRepresentation (F := F)) :=
  ((splitZeroUnitPrimary r s hr).filter fun out => !out.tag.isZero).map TaggedTower.tower

/-- Localization membership records an actual unit-tagged primary child. -/
theorem mem_localizeFiber_iff
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (child : TowerRepresentation (F := F)) :
    child ∈ localizeFiber r s hr ↔
      ∃ out ∈ splitZeroUnitPrimary r s hr, out.tag = .unit ∧ out.tower = child := by
  simp only [localizeFiber, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨out, ⟨hout, htag⟩, hchild⟩
    refine ⟨out, hout, ?_, hchild⟩
    cases ht : out.tag <;> simp_all [SplitTag.isZero]
  · rintro ⟨out, hout, htag, hchild⟩
    exact ⟨out, ⟨hout, by simp [htag, SplitTag.isZero]⟩, hchild⟩

/-- Every retained localization child satisfies the canonical weak tower contract. -/
theorem localizeFiber_nonreducedWellFormed
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (child : TowerRepresentation (F := F))
    (hc : child ∈ localizeFiber r s hr) : child.NonreducedWellFormed width := by
  obtain ⟨out, ho, _, rfl⟩ := (mem_localizeFiber_iff r s hr child).mp hc
  exact splitZeroUnitPrimary_nonreducedWellFormed r s hr out ho

/-- Retained points are exactly the parent points where the localized element is nonzero. -/
theorem localizeFiber_point_iff
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    {K : Type} [Field K] (phi : F →+* K) (u v : K) :
    (∃ child ∈ localizeFiber r s hr, child.Point phi u v) ↔
      r.Point phi u v ∧ TowerRepresentation.evalNested s phi u v ≠ 0 := by
  constructor
  · rintro ⟨child, hc, hp⟩
    obtain ⟨out, ho, ht, rfl⟩ := (mem_localizeFiber_iff r s hr child).mp hc
    exact ⟨(splitZeroUnitPrimary_point_sound r s hr out ho phi u v hp).1,
      primary_residual_ne_zero_of_unit_child r s hr out ho ht phi u v hp⟩
  · rintro ⟨hp, hs⟩
    obtain ⟨out, ho, hpoint, htag⟩ := splitZeroUnitPrimary_point_complete r s hr phi u v hp
    have ht : out.tag = .unit := by
      cases he : out.tag
      · exact (hs (htag.mp he)).elim
      · rfl
    exact ⟨out.tower, (mem_localizeFiber_iff r s hr out.tower).mpr
      ⟨out, ho, ht, rfl⟩, hpoint⟩

/-- Restriction to localization preserves the represented polynomial at every retained point. -/
theorem localizeFiber_specialize
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (child : TowerRepresentation (F := F))
    (hc : child ∈ localizeFiber r s hr)
    {K : Type} [Field K] (phi : F →+* K) (u v : K) (hp : child.Point phi u v) :
    child.specialize phi u v = r.specialize phi u v := by
  obtain ⟨out, ho, _, rfl⟩ := (mem_localizeFiber_iff r s hr child).mp hc
  exact (splitZeroUnitPrimary_specialize r s hr out ho phi u v hp).symm

/-- The localization list has pairwise disjoint geometric supports. -/
theorem localizeFiber_pairwise_geometricallyDisjoint
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) :
    (localizeFiber r s hr).Pairwise GeometricallyDisjoint := by
  rw [localizeFiber, List.pairwise_map]
  exact (splitZeroUnitPrimary_pairwise_geometricallyDisjoint r s hr).filter _

/-- Localization can only discard complete primary pieces, so total dimension does not increase. -/
theorem localizeFiber_dimension_le
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) :
    ((localizeFiber r s hr).map TowerRepresentation.dimension).sum ≤ r.dimension := by
  rw [← splitZeroUnitPrimary_dimension_sum r s hr, localizeFiber, List.map_map]
  induction splitZeroUnitPrimary r s hr with
  | nil => simp
  | cons out rest ih =>
      simp only [List.filter_cons]
      split <;> simp_all
      omega

/-- A retained localization fiber is an actual terminal quotient with canonical restriction. -/
theorem localizeFiber_terminal
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (child : TowerRepresentation (F := F))
    (hc : child ∈ localizeFiber r s hr) :
    ∃ terminal ∈ factorTower (splitStatePrimary r s hr),
      child = restrictTower r terminal.modulus
        (terminalQuotientPolynomial (splitStatePrimary r s hr) terminal) := by
  obtain ⟨out, ho, ht, rfl⟩ := (mem_localizeFiber_iff r s hr child).mp hc
  obtain ⟨terminal, hterminal, hz | hu⟩ := mem_splitZeroUnitPrimary_iff.mp ho
  · obtain ⟨_, he⟩ := makeTagged?_eq_some_iff.mp hz
    rw [he] at ht
    cases ht
  · obtain ⟨_, rfl⟩ := makeTagged?_eq_some_iff.mp hu
    exact ⟨terminal, hterminal, rfl⟩

/-- In every residue fiber, the original localized element has a Bezout inverse modulo the
retained fiber, including its nilpotent structure. -/
theorem localizeFiber_unit_coprime
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (child : TowerRepresentation (F := F))
    (hc : child ∈ localizeFiber r s hr)
    {K : Type} [Field K] (phi : F →+* K) (u : K)
    (hu : child.modulus.toPoly.eval₂ phi u = 0) :
    IsCoprime (specializeFiberCPolynomial child.fiber phi u)
      (specializeFiberCPolynomial s phi u) := by
  obtain ⟨terminal, ht, rfl⟩ := localizeFiber_terminal r s hr child hc
  have hmonic := (factorTower_terminal_invariants (splitStatePrimary r s hr) terminal ht).2.1
  rw [restrictTower, TowerRepresentation.reduceBase,
    specialize_reduceFiberCoefficients phi u hmonic hu]
  simpa only [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial] using
    primary_terminal_unit_coprime r s hr terminal ht phi u hu

/-- Every primary factor supported on the localized element's zero set is absent from the
retained fiber. Combined with multiplicity preservation, this identifies complete primary pieces. -/
theorem localizeFiber_no_agreeing_factor
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (child : TowerRepresentation (F := F))
    (hc : child ∈ localizeFiber r s hr)
    {K : Type} [Field K] (phi : F →+* K) (u : K)
    (hu : child.modulus.toPoly.eval₂ phi u = 0)
    (p : K[X]) (hp : Irreducible p) (hps : p ∣ specializeFiberCPolynomial s phi u) :
    ¬p ∣ specializeFiberCPolynomial child.fiber phi u := by
  intro hpc
  exact hp.not_isUnit
    ((localizeFiber_unit_coprime r s hr child hc phi u hu).isRelPrime hpc hps)

/-- The localized residual is an actual unit in the full specialized quotient algebra. -/
theorem localizeFiber_residual_isUnit
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (child : TowerRepresentation (F := F))
    (hc : child ∈ localizeFiber r s hr)
    {K : Type} [Field K] (phi : F →+* K) (u : K)
    (hu : child.modulus.toPoly.eval₂ phi u = 0) :
    IsUnit (AdjoinRoot.mk (specializeFiberCPolynomial child.fiber phi u)
      (specializeFiberCPolynomial s phi u)) := by
  have h := (localizeFiber_unit_coprime r s hr child hc phi u hu).map
    (AdjoinRoot.mk (specializeFiberCPolynomial child.fiber phi u))
  simpa only [AdjoinRoot.mk_self, isCoprime_zero_left] using h

/-- Restriction retains every power of every primary factor away from the localized residual. -/
theorem localizeFiber_primary_multiplicity
    (r : TowerRepresentation (F := F)) (s : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (child : TowerRepresentation (F := F))
    (hc : child ∈ localizeFiber r s hr)
    {K : Type} [Field K] (phi : F →+* K) (u : K)
    (hu : child.modulus.toPoly.eval₂ phi u = 0)
    (p : K[X]) (hp : Irreducible p) (hps : ¬p ∣ specializeFiberCPolynomial s phi u) (m : ℕ) :
    p ^ m ∣ specializeFiberCPolynomial child.fiber phi u ↔
      p ^ m ∣ specializeFiberCPolynomial r.fiber phi u := by
  obtain ⟨terminal, ht, rfl⟩ := localizeFiber_terminal r s hr child hc
  let state := splitStatePrimary r s hr
  have hmonic := (factorTower_terminal_invariants state terminal ht).2.1
  rw [restrictTower, TowerRepresentation.reduceBase,
    specialize_reduceFiberCoefficients phi u hmonic hu]
  have hf := terminal_gcd_mul_terminalQuotient_specialize state
    (by simpa [state, splitStatePrimary] using hr.2.2.2.1) terminal ht phi u hu
  have hd := primary_terminal_gcd_dvd_power r s hr terminal ht phi u hu
  have h := PrimarySplit.primary_power_dvd_quotient_iff hf hd hp hps m
  simpa only [state, splitStatePrimary, makeTerminalQuotientBranch,
    FiberPolynomial.specialize_ofCPolynomial] using h

end ReedSolomon.ListDecoding.TowerAlgebra
