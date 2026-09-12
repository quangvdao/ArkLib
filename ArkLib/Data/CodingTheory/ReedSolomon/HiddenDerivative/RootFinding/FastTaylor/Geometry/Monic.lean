/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Geometry.Direction
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Geometry.Projection
public import ArkLib.Data.MvPolynomial.TaylorReconstruction.WeightedMonicReduction

/-!
# Computed monic projections

A nonvanishing top-degree direction becomes the final column of an invertible coordinate
matrix. Scaling its image by the computed leading scalar gives the monic chart polynomial.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.Geometry.MonicProjection

open CPoly CompPoly CPoly.TaylorReconstruction

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {r : ℕ}

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
private theorem line_monomial (m : Fin (r + 1) →₀ ℕ) (c : E) (v : Fin (r + 1) → E) :
    MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X)
      (MvPolynomial.monomial m c) =
      Polynomial.C (c * m.prod (fun i e => v i ^ e)) * Polynomial.X ^ m.degree := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← Polynomial.C_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree, Polynomial.C_mul]
  change Polynomial.C c * (Polynomial.C _ * Polynomial.X ^ _) = _
  rw [mul_assoc]
  rfl

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
/-- A coefficient of the line restriction evaluates the matching homogeneous component. -/
theorem line_coeff (p : MvPolynomial (Fin (r + 1)) E) (v : Fin (r + 1) → E) (b : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X) p).coeff b =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent b p) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [MvPolynomial.eval₂_sum, line_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  rw [MvPolynomial.homogeneousComponent_apply, MvPolynomial.eval_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  simp [MvPolynomial.eval_monomial, eq_comm]

/-- Setting all free parameters to zero turns the split view into the final coordinate line. -/
theorem splitLast_zero (p : CMvPolynomial (r + 1) E) :
    (splitLast p).toPoly.map (CMvPolynomial.evalHom (0 : Fin r → E)) =
      MvPolynomial.eval₂ Polynomial.C
        (Fin.lastCases Polynomial.X (fun _ : Fin r => 0)) (fromCMvPolynomial p) := by
  rw [splitLast_toPoly]
  change Polynomial.mapRingHom (CMvPolynomial.evalHom (0 : Fin r → E)) _ = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · apply RingHom.ext
    intro a
    simp [coefficientConstant, CMvPolynomial.evalHom_apply]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [CMvPolynomial.evalHom_apply]

/-- After projection, that final line has the computed direction as its coordinate vector. -/
theorem projected_line (p : CMvPolynomial (r + 1) E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (splitLast (projectPolynomial M p)).toPoly.map
      (CMvPolynomial.evalHom (0 : Fin r → E)) =
      MvPolynomial.eval₂ Polynomial.C
        (fun i => Polynomial.C (M i (Fin.last r)) * Polynomial.X)
        (fromCMvPolynomial p) := by
  rw [splitLast_zero, from_projectPolynomial]
  change MvPolynomial.eval₂Hom Polynomial.C
    (Fin.lastCases Polynomial.X (fun _ : Fin r => 0))
    (MvPolynomial.eval₂ MvPolynomial.C
      (fun i => ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j)
      (fromCMvPolynomial p)) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · apply RingHom.ext
    intro a
    simp
  · funext i
    simp only [Function.comp_apply, _root_.map_sum, _root_.map_mul, MvPolynomial.eval₂Hom_C]
    rw [Fin.sum_univ_castSucc]
    simp

/-- The top coefficient is a constant parameter polynomial whose value is computed from
exactly the stored top homogeneous part. -/
theorem projected_top_coeff (p : CMvPolynomial (r + 1) E) (b : ℕ)
    (hb : (fromCMvPolynomial p).totalDegree ≤ b)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (splitLast (projectPolynomial M p)).coeff b =
      CMvPolynomial.C ((Direction.homogeneousPart b p).eval (fun i => M i (Fin.last r))) := by
  let q := splitLast (projectPolynomial M p)
  have hdeg : (fromCMvPolynomial (q.coeff b)).totalDegree = 0 := by
    by_cases hz : q.coeff b = 0
    · simp [hz]
    · have hd := totalDegree_coeff_splitLast_add_le (projectPolynomial M p) b hz
      have hp := (totalDegree_projectPolynomial_le M p).trans hb
      change (fromCMvPolynomial (q.coeff b)).totalDegree + b ≤ _ at hd
      omega
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have he := congrArg (fun f : Polynomial E => f.coeff b) (projected_line p M)
  rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly, line_coeff] at he
  apply eq_iff_fromCMvPolynomial.mpr
  rw [CMvPolynomial.fromCMvPolynomial_C]
  change fromCMvPolynomial (q.coeff b) = _
  rw [hc]
  congr 1
  rw [CMvPolynomial.evalHom_apply, eval_equiv, MvPolynomial.eval_zero] at he
  rw [eval_equiv, Direction.homogeneousPart_semantics]
  exact he

/-- Scale the actual projected input by the inverse of its computed top coefficient. -/
def normalize (p : CMvPolynomial (r + 1) E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : CMvPolynomial (r + 1) E :=
  CMvPolynomial.C
    (((Direction.homogeneousPart p.totalDegree p).eval (fun i => M i (Fin.last r)))⁻¹) *
    projectPolynomial M p

omit [DecidableEq E] in
/-- Normalization preserves the total-degree bound of the original input. -/
theorem totalDegree_normalize_le (p : CMvPolynomial (r + 1) E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (fromCMvPolynomial (normalize p M)).totalDegree ≤ p.totalDegree := by
  rw [normalize, CPoly.map_mul]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [CMvPolynomial.fromCMvPolynomial_C, MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_projectPolynomial_le M p

/-- The executed inverse scaling makes the coefficient at the input total degree exactly one. -/
theorem normalize_top_coeff (p : CMvPolynomial (r + 1) E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hne : (Direction.homogeneousPart p.totalDegree p).eval
      (fun i => M i (Fin.last r)) ≠ 0) :
    (splitLast (normalize p M)).coeff p.totalDegree = 1 := by
  rw [normalize, _root_.map_mul, splitLast_C]
  rw [CPolynomial.coeff_toPoly, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
    Polynomial.coeff_C_mul, ← CPolynomial.coeff_toPoly,
    projected_top_coeff p p.totalDegree le_rfl M]
  apply eq_iff_fromCMvPolynomial.mpr
  simp only [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_C, CPoly.map_one]
  rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hne, MvPolynomial.C_1]

/-- The normalized chart has exact final-variable degree, is monic, and has all weighted
coefficient bounds required for degree-preserving reduction. -/
theorem normalize_spec (p : CMvPolynomial (r + 1) E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hne : (Direction.homogeneousPart p.totalDegree p).eval
      (fun i => M i (Fin.last r)) ≠ 0) :
    (splitLast (normalize p M)).monic ∧
      (splitLast (normalize p M)).natDegree = p.totalDegree ∧
      WeightedDegreeLE (splitLast (normalize p M)) p.totalDegree := by
  let q := splitLast (normalize p M)
  have hw : WeightedDegreeLE q p.totalDegree :=
    weightedDegreeLE_splitLast _ (totalDegree_normalize_le p M)
  have hc : q.toPoly.coeff p.totalDegree = 1 := by
    rw [← CPolynomial.coeff_toPoly]
    exact normalize_top_coeff p M hne
  have hd : q.toPoly.natDegree = p.totalDegree := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ (hc ▸ one_ne_zero)
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [← CPolynomial.coeff_toPoly]
    by_contra hn
    have := hw i hn
    omega
  have hm : q.toPoly.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hd, hc]
  exact ⟨(CPolynomial.monic_toPoly_iff q).mpr hm,
    (CPolynomial.natDegree_toPoly q).trans hd, hw⟩

omit [DecidableEq E] in
/-- Evaluation of the normalized polynomial follows the actual forward coordinate map. -/
theorem eval_normalize (p : CMvPolynomial (r + 1) E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (x : Fin (r + 1) → E) :
    (normalize p M).eval x =
      ((Direction.homogeneousPart p.totalDegree p).eval (fun i => M i (Fin.last r)))⁻¹ *
        p.eval (M.mulVec x) := by
  simp [normalize, eval_projectPolynomial]

/-- Every normalized coefficient has the paper's parameter-degree bound `b-i`. -/
theorem normalize_coeff_degree (p : CMvPolynomial (r + 1) E)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (i : ℕ) :
    (fromCMvPolynomial ((splitLast (normalize p M)).coeff i)).totalDegree ≤ p.totalDegree - i :=
  totalDegree_coeff_le_sub _ (weightedDegreeLE_splitLast _ (totalDegree_normalize_le p M)) i

/-- The computed coordinate changes and normalized flat polynomial of one projection. -/
structure Data (r : ℕ) (E : Type*) [CommSemiring E] where
  direction : Fin (r + 1) → E
  forward : Matrix (Fin (r + 1)) (Fin (r + 1)) E
  inverse : Matrix (Fin (r + 1)) (Fin (r + 1)) E
  polynomial : CMvPolynomial (r + 1) E

/-- Search the supplied grid, build both coordinate matrices, and normalize the projected input. -/
def construct? (p : CMvPolynomial (r + 1) E) (values : List E) : Option (Data r E) :=
  (Direction.chooseFor? p values).map fun (v, M, I) => ⟨v, M, I, normalize p M⟩

/-- All monicity, coordinate, and weighted-degree certificates concern the returned data. -/
theorem construct?_sound (p : CMvPolynomial (r + 1) E) (values : List E)
    (d : Data r E) (hd : construct? p values = some d) :
    d.forward * d.inverse = 1 ∧ d.inverse * d.forward = 1 ∧
      (∀ i, d.forward i (Fin.last r) = d.direction i) ∧
      d.polynomial = normalize p d.forward ∧
      (splitLast d.polynomial).monic ∧
      (splitLast d.polynomial).natDegree = p.totalDegree ∧
      WeightedDegreeLE (splitLast d.polynomial) p.totalDegree := by
  obtain ⟨⟨v, M, I⟩, hv, he⟩ := Option.map_eq_some_iff.mp hd
  cases he
  obtain ⟨_, hn, hMI, hIM, hl⟩ := Direction.choose?_sound _ _ v M I hv
  have hs := normalize_spec p M (by simpa only [hl] using hn)
  exact ⟨hMI, hIM, hl, rfl, hs⟩

omit [DecidableEq E] in
/-- A sufficiently long distinct prefix guarantees construction for every nonconstant input. -/
theorem construct?_exists (p : CMvPolynomial (r + 1) E) (values : List E)
    (hp : p ≠ 0) (hb : 0 < p.totalDegree) (hdistinct : values.Nodup)
    (hsize : p.totalDegree < values.length) : ∃ d, construct? p values = some d := by
  obtain ⟨v, M, I, he⟩ := Direction.chooseFor?_exists p values hp hb hdistinct hsize
  exact ⟨⟨v, M, I, normalize p M⟩, by simp [construct?, he]⟩

omit [DecidableEq E] in
/-- On nonconstant input, construction fails precisely when the entire supplied grid
annihilates the computed highest homogeneous part. -/
theorem construct?_eq_none_iff (p : CMvPolynomial (r + 1) E) (values : List E)
    (hb : 0 < p.totalDegree) : construct? p values = none ↔
      ∀ x, (∀ i, x i ∈ values) → (Direction.homogeneousPart p.totalDegree p).eval x = 0 := by
  rw [construct?, Option.map_eq_none_iff, Direction.chooseFor?]
  apply Direction.choose?_eq_none_iff _ _ hb
  rw [Direction.homogeneousPart_semantics]
  exact MvPolynomial.homogeneousComponent_isHomogeneous _ _

/-- Reducing in a constructed chart retains every polynomial total-degree bound. -/
theorem constructed_remainder_degree (p f : CMvPolynomial (r + 1) E) (values : List E)
    (d : Data r E) (hd : construct? p values = some d) {L : ℕ}
    (hf : (fromCMvPolynomial f).totalDegree ≤ L) :
    (fromCMvPolynomial
      (flattenLast ((splitLast f).modByMonic (splitLast d.polynomial)))).totalDegree ≤ L := by
  obtain ⟨_, _, _, _, hm, hn, hw⟩ := construct?_sound p values d hd
  apply totalDegree_flattenLast_le
  apply weightedDegreeLE_modByMonic _ _ hm
  · simpa only [hn] using hw
  · exact weightedDegreeLE_splitLast f hf

end ReedSolomon.HiddenDerivative.FastTaylor.Geometry.MonicProjection
