/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.TaylorReconstruction.LocalEquation
public import ArkLib.Data.MvPolynomial.NonvanishingGrid
public import ArkLib.Data.Polynomial.Rojas.Producer.Univariate
public import ArkLib.Data.Polynomial.ConfluentAlgebra.Inverse

/-!
# A computed confluent sample and its quotient inverse

The obstruction is the actual stored Sylvester determinant of the chart equation and
separant. Grid selection tests that polynomial. Nonzero specialization gives a Bézout
identity even when the equation's fiber has repeated roots.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.ConfluentSample

open CompPoly CPoly CPoly.TaylorReconstruction ArkLib.ConfluentAlgebra

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E] [DecidableEq E]
variable {r : ℕ}

/-- Compute the separant obstruction directly from the stored chart coefficients. -/
def obstruction (h s : CMvPolynomial (r + 1) E) : CMvPolynomial r E :=
  ArkLib.Rojas.Producer.Univariate.storedResultant (splitLast h) (splitLast s)
    (splitLast h).natDegree (splitLast s).natDegree

/-- Find the first confluent sample by testing the computed obstruction on a scalar grid. -/
def select? (h s : CMvPolynomial (r + 1) E) (values : List E) : Option (Fin r → E) :=
  NonvanishingGrid.selectNonzero (obstruction h s) values

/-- Sample-search exhaustion means every supplied-grid point annihilates the computed resultant. -/
theorem select?_eq_none_iff (h s : CMvPolynomial (r + 1) E) (values : List E) :
    select? h s values = none ↔
      ∀ a, (∀ i, a i ∈ values) → CMvPolynomial.eval a (obstruction h s) = 0 :=
  NonvanishingGrid.selectNonzero_eq_none_iff _ _

/-- Obstruction evaluation is precisely the resultant of the two specialized fibers. -/
theorem eval_obstruction (h s : CMvPolynomial (r + 1) E) (a : Fin r → E) :
    CMvPolynomial.eval a (obstruction h s) =
      Polynomial.resultant (constantFiber a h).toPoly (constantFiber a s).toPoly
        (splitLast h).natDegree (splitLast s).natDegree := by
  rw [constantFiber, constantFiber, toPoly_mapCoefficients, toPoly_mapCoefficients,
    Polynomial.resultant_map_map]
  exact congrArg (CMvPolynomial.eval₂Hom (RingHom.id E) a)
    (ArkLib.Rojas.Producer.Univariate.storedResultant_eq _ _ _ _)

omit [BEq E] [LawfulBEq E] [DecidableEq E] in
/-- A nonzero padded resultant of positive size gives coprimality over the scalar field. -/
theorem coprime_of_resultant_ne_zero (f g : Polynomial E) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hm : 0 < m)
    (hne : Polynomial.resultant f g m n ≠ 0) : IsCoprime f g := by
  obtain ⟨u, v, _, _, huv⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg (Or.inl (Nat.ne_of_gt hm))
  refine ⟨u * Polynomial.C (Polynomial.resultant f g m n)⁻¹,
    v * Polynomial.C (Polynomial.resultant f g m n)⁻¹, ?_⟩
  calc
    _ = (f * u + g * v) * Polynomial.C (Polynomial.resultant f g m n)⁻¹ := by ring
    _ = 1 := by rw [huv, ← Polynomial.C_mul, mul_inv_cancel₀ hne, Polynomial.C_1]

/-- Every selected sample makes the actual equation and separant fibers coprime. -/
theorem select?_coprime (h s : CMvPolynomial (r + 1) E) (values : List E)
    (a : Fin r → E) (ha : select? h s values = some a)
    (hb : 0 < (splitLast h).natDegree) :
    IsCoprime (constantFiber a h).toPoly (constantFiber a s).toPoly := by
  apply coprime_of_resultant_ne_zero _ _ (splitLast h).natDegree (splitLast s).natDegree
  · rw [constantFiber, toPoly_mapCoefficients, CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_map_le
  · rw [constantFiber, toPoly_mapCoefficients, CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_map_le
  · exact hb
  · rw [← eval_obstruction]
    exact (NonvanishingGrid.selectNonzero_sound ha).2

/-- A sufficient distinct grid makes the executed sample search succeed. -/
theorem select?_exists (h s : CMvPolynomial (r + 1) E) (values : List E)
    (hne : obstruction h s ≠ 0) (hdistinct : values.Nodup)
    (hsize : (fromCMvPolynomial (obstruction h s)).totalDegree < values.length) :
    ∃ a, select? h s values = some a :=
  NonvanishingGrid.selectNonzero_exists_of_nodup _ _ hne hdistinct hsize

/-- Generic coprimality over any injective coefficient field proves obstruction nonzeroness.
The field is used only in this certificate; the resultant and grid search stay over `E`. -/
theorem obstruction_ne_zero_of_generic_coprime {K : Type*} [Field K]
    (f : CMvPolynomial r E →+* K) (hf : Function.Injective f)
    (h s : CMvPolynomial (r + 1) E)
    (hcoprime : IsCoprime ((splitLast h).toPoly.map f) ((splitLast s).toPoly.map f)) :
    obstruction h s ≠ 0 := by
  intro hz
  have hn := Polynomial.resultant_ne_zero _ _ hcoprime
  apply hn
  rw [Polynomial.natDegree_map_eq_of_injective hf,
    Polynomial.natDegree_map_eq_of_injective hf, Polynomial.resultant_map_map]
  rw [← CPolynomial.natDegree_toPoly, ← CPolynomial.natDegree_toPoly,
    ← ArkLib.Rojas.Producer.Univariate.storedResultant_eq]
  change f (obstruction h s) = 0
  rw [hz, f.map_zero]

variable (N : ℕ) [Fact (0 < N)]
variable (h s : CMvPolynomial (r + 1) E) [Fact (splitLast h).monic]

/-- The local equation's monicity follows from the computed coefficient homomorphism. -/
instance localMonic (a : Fin r → E) : Fact (localEquation N a h).monic :=
  ⟨localEquation_monic N a h Fact.out⟩

/-- Monic local conversion preserves the exact quotient degree over the nonreduced base. -/
theorem localEquation_degree (a : Fin r → E) :
    (localEquation N a h).toPoly.degree = (splitLast h).toPoly.degree := by
  rw [localEquation, toPoly_mapCoefficients]
  exact ((CPolynomial.monic_toPoly_iff _).mp (Fact.out : (splitLast h).monic)).degree_map _

/-- A positive global chart degree supplies the nontriviality guard used by the series solver. -/
instance localDegreePositive [Fact (0 < (splitLast h).toPoly.degree)] (a : Fin r → E) :
    Fact (0 < (localEquation N a h).toPoly.degree) :=
  ⟨by rw [localEquation_degree]; exact Fact.out⟩

/-- Reduce the actual shifted separant in the stored monic quotient. -/
def localSeparant (a : Fin r → E) : Representative (localEquation N a h) :=
  reductionHom (localEquation N a h) (localEquation N a s)

/-- Compute the quotient inverse; no inverse or approximate inverse is supplied. -/
def inverseAt? (a : Fin r → E) : Option (Representative (localEquation N a h)) :=
  inverse? (localEquation N a h) (localSeparant N h s a)

/-- A chosen sample guarantees success of the actual constant-fiber and Newton inverse. -/
theorem inverseAt?_exists (values : List E) (a : Fin r → E)
    (ha : select? h s values = some a) (hb : 0 < (splitLast h).natDegree) :
    ∃ b, inverseAt? N h s a = some b := by
  apply (inverse?_exists_iff_coprime (localEquation N a h) (localSeparant N h s a)).mpr
  change IsCoprime
    (mapCoefficients (BoxAlgebra.constantSpecialization (Fact.out : 0 < N))
      ((localEquation N a s).modByMonic (localEquation N a h))).toPoly _
  rw [mapCoefficients_remainder _ _ _ (localEquation_monic N a h Fact.out),
    localEquation_constantFiber N Fact.out a s, localEquation_constantFiber N Fact.out a h,
    CPolynomial.modByMonic_toPoly_eq_modByMonic]
  · apply IsCoprime.of_add_mul_left_left
    rw [Polynomial.modByMonic_add_div]
    exact (select?_coprime h s values a ha hb).symm
  · exact monic_mapCoefficients _ _ (Fact.out : (splitLast h).monic)

/-- Every returned inverse is a two-sided inverse of the stored shifted separant. -/
theorem inverseAt?_sound (a : Fin r → E) (b : Representative (localEquation N a h))
    (hb : inverseAt? N h s a = some b) :
    localSeparant N h s a * b = 1 ∧ b * localSeparant N h s a = 1 :=
  inverse?_sound _ _ _ hb

/-- Inverse failure has the concrete meaning that the local separant is a nonunit. -/
theorem inverseAt?_eq_none_iff (a : Fin r → E) :
    inverseAt? N h s a = none ↔ ¬ ∃ b, localSeparant N h s a * b = 1 :=
  inverse?_eq_none_iff _ _

end ReedSolomon.HiddenDerivative.FastTaylor.ConfluentSample
