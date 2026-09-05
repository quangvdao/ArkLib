/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderOne.Certificate
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderOne.Dimension

/-! # Unrestricted intermediate-gap certificate from the selected monomial family -/

noncomputable section

open Polynomial

namespace ReedSolomon.HiddenDerivative.IntermediateGapSelectedCertificate

open MvPolynomial SymbolicReceivedInterpolation SymbolicBandInterpolation
open scoped BigOperators

variable {F : Type*} [Field F]
variable {D A : ℕ} {ι : Type*}

private theorem sum_const_sub_le (s : Finset ι) (x : ℕ) (cost : ι → ℕ) :
    s.card * x - ∑ i ∈ s, cost i ≤ ∑ i ∈ s, (x - cost i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha, Finset.sum_insert ha,
        Nat.succ_mul]
      omega

private theorem selected_card_lower {D A : ℕ} (hD : 1 < D) :
    121856 * A - 120700 * D ≤
      Fintype.card (IntermediateGapDimension.SelectedIndex D A) := by
  let S : Finset (Σ b : Fin 17, Fin (120 - b.val)) := Finset.univ
  have h := sum_const_sub_le S (64 * A)
    (fun p ↦ (D - 1) * p.1.val + D * p.2.val)
  have hcard : Fintype.card (Σ b : Fin 17, Fin (120 - b.val)) = 1904 := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, Fin.sum_univ_eq_sum_range]
    norm_num [Finset.sum_range_succ]
  simp only [S, Finset.card_univ, hcard] at h
  have hcost : (∑ p : Σ b : Fin 17, Fin (120 - b.val),
      ((D - 1) * p.1.val + D * p.2.val)) = 120700 * D - 14824 := by
    have hrange :
        (∑ b : Fin 17, ∑ a : Fin (120 - b.val),
            ((D - 1) * b.val + D * a.val)) =
          Finset.sum (Finset.range 17) (fun b ↦
            Finset.sum (Finset.range (120 - b)) (fun a ↦ (D - 1) * b + D * a)) := by
      calc
        _ = ∑ b : Fin 17, Finset.sum (Finset.range (120 - b.val))
              (fun a ↦ (D - 1) * b.val + D * a) := by
            apply Finset.sum_congr rfl
            intro b _
            convert Fin.sum_univ_eq_sum_range
              (fun a : ℕ ↦ (D - 1) * b.val + D * a) (120 - b.val) using 1
        _ = _ := by
          convert Fin.sum_univ_eq_sum_range (fun b : ℕ ↦
            Finset.sum (Finset.range (120 - b))
              (fun a ↦ (D - 1) * b + D * a)) 17 using 1
    rw [Fintype.sum_sigma'
      (fun (b : Fin 17) (a : Fin (120 - b.val)) ↦ (D - 1) * b.val + D * a.val),
      hrange]
    have hadd : Finset.sum (Finset.range 17)
        (fun b ↦ Finset.sum (Finset.range (120 - b)) (fun a ↦ a + b)) = 120700 := by
      simp only [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const_nat,
        Finset.card_range]
      norm_num [Finset.sum_range_succ]
    have hb : Finset.sum (Finset.range 17)
        (fun b ↦ Finset.sum (Finset.range (120 - b)) (fun _a ↦ b)) = 14824 := by
      simp only [Finset.sum_const_nat, Finset.card_range]
      norm_num [Finset.sum_range_succ]
    let SA := Finset.sum (Finset.range 17)
      (fun b ↦ Finset.sum (Finset.range (120 - b)) (fun a ↦ a))
    let SB := Finset.sum (Finset.range 17)
      (fun b ↦ Finset.sum (Finset.range (120 - b)) (fun _a ↦ b))
    have hsum : SA + SB = 120700 := by
      rw [← hadd]
      simp [SA, SB, Finset.sum_add_distrib]
    have hSB : SB = 14824 := hb
    have hSA : SA = 120700 - 14824 := by omega
    calc
      _ = (D - 1) * SB + D * SA := by
        simp [SA, SB, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc]
      _ = (D - 1) * 14824 + D * (120700 - 14824) := by rw [hSB, hSA]
      _ = _ := by omega
  rw [hcost] at h
  have hrewrite : 1904 * (64 * A) = 121856 * A := by ring
  rw [hrewrite] at h
  have hsub : 121856 * A - 120700 * D ≤
      121856 * A - (120700 * D - 14824) := Nat.sub_le_sub_left (Nat.sub_le _ _) _
  have hsource : Fintype.card (IntermediateGapDimension.SelectedIndex D A) =
      ∑ p : Σ b : Fin 17, Fin (120 - b.val),
        ((64 * A - (D - 1) * p.1.val) - D * p.2.val) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_sigma, Fintype.card_fin]
    rw [Fintype.sum_sigma'
      (fun (b : Fin 17) (a : Fin (120 - b.val)) ↦
        (64 * A - (D - 1) * b.val) - D * a.val)]
  rw [hsource]
  simpa only [Nat.sub_sub] using le_trans hsub h

/-- Exponent of one selected manuscript column. -/
def selectedExponent {D A : ℕ} (p : IntermediateGapDimension.SelectedIndex D A) :
    JetVariable 1 →₀ ℕ :=
  Finsupp.single none p.2.2.val + Finsupp.single (some 0) p.2.1.val +
    Finsupp.single (some 1) p.1.val

theorem selectedExponent_eligible {D A : ℕ} (_hD : 1 < D)
    (p : IntermediateGapDimension.SelectedIndex D A) :
    ExactInterpolationEligibleExponent D A 1 64 16 0 (selectedExponent p) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [firstJetExponent, selectedExponent, Finsupp.weight_apply,
      Finsupp.sum_fintype, Fin.sum_univ_two]
    omega
  · simp [fullHigherJetWeight, selectedExponent, Finsupp.weight_apply,
      Finsupp.sum_fintype, Fin.sum_univ_two]
  · rw [exactInterpolationMonomialWeight_eq]
    have h₁ := Nat.lt_sub_iff_add_lt.mp p.2.2.isLt
    have h₂ := Nat.lt_sub_iff_add_lt.mp h₁
    simpa [selectedExponent, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using h₂

theorem selectedExponent_injective {D A : ℕ} :
    Function.Injective (selectedExponent : IntermediateGapDimension.SelectedIndex D A → _) := by
  rintro ⟨b, a, x⟩ ⟨b', a', x'⟩ h
  have hb : b = b' := Fin.ext (by
    simpa [selectedExponent] using congrArg (fun u ↦ u (some 1)) h)
  subst b'
  have ha : a = a' := Fin.ext (by
    simpa [selectedExponent] using congrArg (fun u ↦ u (some 0)) h)
  subst a'
  have hx : x = x' := Fin.ext (by
    simpa [selectedExponent] using congrArg (fun u ↦ u none) h)
  subst x'
  rfl

/-- Canonical enumeration of the selected manuscript columns. -/
def columns {D A : ℕ} :
    Fin (Fintype.card (IntermediateGapDimension.SelectedIndex D A)) → SourceColumn 1 :=
  fun j ↦ SourceColumn.ofExponent
    (selectedExponent ((Fintype.equivFin _).symm j))

theorem columns_injective {D A : ℕ} : Function.Injective (columns (D := D) (A := A)) := by
  intro i j hij
  have he : selectedExponent
      ((Fintype.equivFin (IntermediateGapDimension.SelectedIndex D A)).symm i) =
      selectedExponent
        ((Fintype.equivFin (IntermediateGapDimension.SelectedIndex D A)).symm j) := by
    simpa only [columns, SourceColumn.exponent_ofExponent] using
      congrArg (fun c : SourceColumn 1 ↦ c.exponent) hij
  apply (Fintype.equivFin (IntermediateGapDimension.SelectedIndex D A)).symm.injective
  apply selectedExponent_injective
  exact he

theorem columns_eligible {D A : ℕ} (hD : 1 < D)
    (j : Fin (Fintype.card (IntermediateGapDimension.SelectedIndex D A))) :
    ExactInterpolationEligibleExponent D A 1 64 16 0 (columns (D := D) (A := A) j).exponent := by
  rw [columns, SourceColumn.exponent_ofExponent]
  exact selectedExponent_eligible hD _

theorem columns_y₀_le {D A : ℕ}
    (j : Fin (Fintype.card (IntermediateGapDimension.SelectedIndex D A))) :
    (columns (D := D) (A := A) j).y₀ ≤ 119 := by
  let p := (Fintype.equivFin (IntermediateGapDimension.SelectedIndex D A)).symm j
  have hp : p.2.1.val < 120 - p.1.val := p.2.1.isLt
  simp [columns, SourceColumn.ofExponent, selectedExponent]
  omega

theorem columns_totalJetDegree_le {D A : ℕ}
    (j : Fin (Fintype.card (IntermediateGapDimension.SelectedIndex D A))) :
    totalJetDegree (columns (D := D) (A := A) j).exponent ≤ 119 := by
  let p := (Fintype.equivFin (IntermediateGapDimension.SelectedIndex D A)).symm j
  have hp : p.2.1.val < 120 - p.1.val := p.2.1.isLt
  rw [columns, SourceColumn.exponent_ofExponent]
  simp [selectedExponent, totalJetDegree,
    Finsupp.degree_eq_sum, Fin.sum_univ_two]
  omega

theorem interpolant_totalJetDegree_le_of_columns {N : ℕ}
    (cs : Fin N → SourceColumn 1)
    (hcs : ∀ j, totalJetDegree (cs j).exponent ≤ 119)
    (v : Fin N → F[X]) {u : JetVariable 1 →₀ ℕ}
    (hu : u ∈ (interpolant cs v).support) :
    totalJetDegree u ≤ 119 := by
  classical
  by_contra hbad
  have hneq : ∀ j, u ≠ (cs j).exponent := by
    intro j heq
    apply hbad
    rw [heq]
    exact hcs j
  have hc : MvPolynomial.coeff u (interpolant cs v) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hu
  apply hc
  rw [interpolant, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [MvPolynomial.coeff_monomial]
  exact if_neg (fun h => hneq j h.symm)

theorem jetTotalDegree_map_le_of_support_bound
    (Q : DifferentialPolynomial F[X] 1)
    (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ 119)
    {E : Type*} [Field E] (ι : F →+* E) (z : E) :
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) ≤ 119 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  simpa [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.some_apply] using
    hQ u (MvPolynomial.support_map_subset _ _ hu)

/-- The stronger selected-family output records the total jet cap used by root counting. -/
structure SelectedCertificate (F : Type*) [Field F] {n : ℕ} (D A k : ℕ)
    (centers : Fin n ↪ F) (f g : Fin n → F)
    extends IntermediateGapCertificate.Certificate F D A k centers f g where
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ 119
  specialization_jetTotalDegree_le : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) ≤ 119

/-- The selected symbolic matrix is a column submatrix of the full exact-space matrix. -/
theorem matrix_rank_le {D A n : ℕ} (hD : 1 < D) (centers f g : Fin n → F) :
    ((matrix 64 centers f g (columns (D := D) (A := A))).map
      (algebraMap F[X] (RatFunc F))).rank ≤
      n * 28152 := by
  let e : Fin (Fintype.card (IntermediateGapDimension.SelectedIndex D A)) →
      Fin (Fintype.card (ExactInterpolationIndex D A 1 64 16 0 hD)) := fun j ↦
    Fintype.equivFin _ ⟨selectedExponent ((Fintype.equivFin _).symm j),
      mem_exactInterpolationExponents.mpr (selectedExponent_eligible hD _)⟩
  have heq : (matrix 64 centers f g (columns (D := D) (A := A))).map
      (algebraMap F[X] (RatFunc F)) =
      ((matrix 64 centers f g (IntermediateGapCertificate.exactColumns hD)).map
        (algebraMap F[X] (RatFunc F))).submatrix id e := by
    ext row j
    simp [matrix, columns, e, IntermediateGapCertificate.exactColumns]
  rw [heq]
  exact (Matrix.rank_submatrix_le _ id e).trans
    (IntermediateGapCertificate.receivedLine_matrix_rank_le hD centers f g)

private theorem map_interpolant_mem_exactSpace {D A : ℕ} (hD : 1 < D)
    (v : Fin (Fintype.card (IntermediateGapDimension.SelectedIndex D A)) → F[X])
    {E : Type*} [Field E] (ι : F →+* E) (z : E) :
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v) ∈
      exactInterpolationSpace E D A 1 64 16 0 hD := by
  rw [interpolant, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [MvPolynomial.map_monomial, monomial_mem_exactInterpolationSpace]
  exact Or.inl (columns_eligible hD j)

/-- The intermediate lower agreement bound alone produces the primitive symbolic certificate.
The explicit selected columns make `Y₀≤119` intrinsic, so no upper-rate hypothesis remains. -/
theorem exists_prescribed_selected_certificate
    {A k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (hA : 4 * k + n ≤ 4 * A)
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (SelectedCertificate F (k - 1) A k centers f g) := by
  let D := k - 1
  have hD : 1 < D := by dsimp [D]; omega
  have hbudget : 0 < 64 * A := by omega
  let N := Fintype.card (IntermediateGapDimension.SelectedIndex D A)
  let cs : Fin N → SourceColumn 1 := columns
  have hNlower : 30464 * n + 1156 * k ≤ N := by
    have hs := selected_card_lower (A := A) hD
    have hnume : 30464 * n + 1156 * k ≤ 121856 * A - 120700 * D := by
      dsimp [D]
      omega
    exact hnume.trans hs
  have hN : n * 28152 < N := by omega
  obtain ⟨v, _hv, _hkernel, hvdeg, _hprimitive, hnozero, hconstraints⟩ :=
    exists_symbolic_received_line_interpolant_of_rank_le
      64 119 28152 (fun i ↦ centers i) f g cs columns_injective columns_y₀_le
        (matrix_rank_le hD (fun i ↦ centers i) f g) hN
  have hheight : ∀ j, (v j).natDegree ≤ 1449 := by
    intro j
    refine (hvdeg j).trans ?_
    rw [Nat.div_le_iff_le_mul (Nat.sub_pos_of_lt hN)]
    omega
  let Q : DifferentialPolynomial F[X] 1 := interpolant cs v
  have hvlt : ∀ j, (v j).natDegree < 1450 := fun j ↦ by
    simpa using Nat.lt_succ_of_le (hheight j)
  have hchallenge : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ 1449 := by
    intro u
    have hlt := coeff_interpolant_natDegree_lt cs columns_injective v
      (by omega : 0 < 1450) hvlt u
    simpa [Q] using Nat.le_sub_one_of_lt hlt
  have helig : ∀ u ∈ Q.support, ExactInterpolationEligibleExponent D A 1 64 16 0 u := by
    have hQ : Q ∈ exactInterpolationSpace F[X] D A 1 64 16 0 hD := by
      dsimp only [Q]
      rw [interpolant]
      apply Submodule.sum_mem
      intro j _
      rw [monomial_mem_exactInterpolationSpace]
      exact Or.inl (columns_eligible hD j)
    exact mem_exactInterpolationSpace_iff.mp hQ
  have hcstotal : ∀ j : Fin N, totalJetDegree (cs j).exponent ≤ 119 := by
    intro j
    dsimp only [cs, N]
    exact columns_totalJetDegree_le (D := D) (A := A) j
  have htotal0 : ∀ u ∈ (interpolant cs v).support, totalJetDegree u ≤ 119 :=
    @interpolant_totalJetDegree_le_of_columns F _ N cs hcstotal v
  have htotal : ∀ u ∈ Q.support, totalJetDegree u ≤ 119 := by
    simpa only [Q] using htotal0
  refine ⟨{
    Q := Q
    challengeDegree_le := hchallenge
    support_eligible := helig
    specialization_sound := ?_
    totalJetDegree_le := htotal
    specialization_jetTotalDegree_le := ?_
  }⟩
  · intro E _ ι z
    have hQnonzero : MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 := by
      dsimp only [Q]
      exact hnozero ι z
    refine ⟨hQnonzero, ?_⟩
    intro indices P hP hcard hagree
    have hPnat : P.natDegree ≤ D := by
      by_cases hz : P = 0
      · simp [hz]
      · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP
        dsimp [D]
        omega
    let φ := Polynomial.eval₂RingHom ι z
    have hconstraintsE : ∀ i, SatisfiesLocalConstraints 64 (ι (centers i))
        (ι (f i) + z * ι (g i)) (MvPolynomial.map φ Q) := by
      intro i
      have hbase : SatisfiesLocalConstraints 64 (Polynomial.C (centers i))
          (receivedLine (f i) (g i)) Q := by
        dsimp only [Q]
        exact hconstraints i
      have hi := SatisfiesLocalConstraints.map φ 64 (Polynomial.C (centers i))
        (receivedLine (f i) (g i)) Q hbase
      change SatisfiesLocalConstraints 64
        (Polynomial.eval₂ ι z (Polynomial.C (centers i)))
        (Polynomial.eval₂ ι z (receivedLine (f i) (g i)))
        (MvPolynomial.map φ Q) at hi
      simpa only [Polynomial.eval₂_C, receivedLine, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_X] using hi
    apply differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
      hbudget hD
      (fun i ↦ ι (centers i)) (fun i ↦ ι (f i) + z * ι (g i)) indices
        (by dsimp only [Q]; exact map_interpolant_mem_exactSpace hD v ι z)
        hconstraintsE P hPnat
    · intro i hi j hj hij
      exact centers.injective (ι.injective hij)
    · exact hcard
    · exact hagree
  · intro E _ ι z
    exact jetTotalDegree_map_le_of_support_bound Q htotal ι z

end ReedSolomon.HiddenDerivative.IntermediateGapSelectedCertificate
