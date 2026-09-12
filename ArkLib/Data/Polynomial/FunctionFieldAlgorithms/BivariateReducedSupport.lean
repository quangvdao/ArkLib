/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Bivariate.CMv
public import ArkLib.ToCompPoly.Bivariate.Content
public import ArkLib.ToCompPoly.Univariate.Basic
public import CompPoly.Bivariate.Deriv
public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Frobenius

/-!
# Stored bivariate support operations

The ordinary variable order is `[X,Y]`. Conversion evaluates the stored term tree in
`F[X][Y]`, using executable constant embeddings. Joint Frobenius contraction acts only on
base coefficients and checks both exponent coordinates; it never takes roots in `F(X)`.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.BivariateReducedSupport

open CompPoly CPolynomial CPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Term-fold conversion of the actual stored ordinary interpolant into `F[X][Y]`. -/
def fromOrdinaryCMv (Q : CMvPolynomial 2 F) : CBivariate F :=
  Q.eval₂ (CHom.comp CHom) ![CPolynomial.C CPolynomial.X, CPolynomial.X]

/-- The term fold is a ring homomorphism; its runtime is the stored tree traversal. -/
def fromOrdinaryHom : CMvPolynomial 2 F →+* CBivariate F :=
  CMvPolynomial.eval₂Hom (CHom.comp CHom) ![CPolynomial.C CPolynomial.X, CPolynomial.X]

/-- Conversion preserves addition exactly in stored form. -/
theorem fromOrdinaryCMv_add (Q R : CMvPolynomial 2 F) :
    fromOrdinaryCMv (Q + R) = fromOrdinaryCMv Q + fromOrdinaryCMv R :=
  fromOrdinaryHom.map_add Q R

/-- Conversion preserves multiplication exactly in stored form. -/
theorem fromOrdinaryCMv_mul (Q R : CMvPolynomial 2 F) :
    fromOrdinaryCMv (Q * R) = fromOrdinaryCMv Q * fromOrdinaryCMv R :=
  fromOrdinaryHom.map_mul Q R

/-- The executable conversion preserves the complete polynomial graph equation. -/
theorem fromOrdinaryCMv_graph (Q : CMvPolynomial 2 F) (P : Polynomial F) :
    (CBivariate.toPoly (fromOrdinaryCMv Q)).eval P =
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P] (fromCMvPolynomial Q) := by
  classical
  let h := (Polynomial.evalRingHom P).comp CBivariate.toPolyRingHom
  have heq := MvPolynomial.eval₂_comp_left h
    (CHom.comp CHom) ![CPolynomial.C CPolynomial.X, CPolynomial.X]
    (fromCMvPolynomial Q)
  rw [fromOrdinaryCMv, CPoly.eval₂_equiv]
  change h _ = _
  rw [heq]
  congr 1
  · ext a
    simp [h, CBivariate.toPolyRingHom, CBivariate.ringEquiv, CBivariate.toPoly_eq_map,
      CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;>
      simp [h, CBivariate.toPolyRingHom, CBivariate.ringEquiv, CBivariate.toPoly_eq_map,
        CPolynomial.C_toPoly, CPolynomial.X_toPoly]

/-- Converting a stored bivariate polynomial to ordinary coordinates and back is exact. -/
theorem fromOrdinaryCMv_toOrdinaryCMv (T : CBivariate F) :
    fromOrdinaryCMv (CBivariate.toOrdinaryCMv T) = T := by
  classical
  rw [fromOrdinaryCMv, CBivariate.toOrdinaryCMv]
  rw [CPoly.eval₂_equiv]
  simp only [CPoly.CMvPolynomial.fromCMvPolynomial_sum,
    CPoly.CMvPolynomial.fromCMvPolynomial_monomial,
    CBivariate.toFinsupp_ordinaryMonomial, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_monomial]
  rw [CPolynomial.eq_iff_coeff]
  intro j
  have hprod (i d : ℕ) :
      (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) d).prod
          (fun index exponent =>
            ![CPolynomial.C (R := CPolynomial F) (CPolynomial.X (R := F)),
              CPolynomial.X (R := CPolynomial F)] index ^ exponent) =
        CPolynomial.C (R := CPolynomial F) ((CPolynomial.X (R := F)) ^ i) *
          (CPolynomial.X (R := CPolynomial F)) ^ d := by
    rw [Finsupp.prod_add_index]
    · rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      congr 1
      exact (map_pow CPolynomial.CHom (CPolynomial.X (R := F)) i).symm
    · intro index _
      simp
    · intro index _ left right
      exact pow_add _ left right
  simp_rw [hprod]
  have hcoeff (a : F) (i d : ℕ) :
      CPolynomial.coeff
          ((CPolynomial.CHom.comp CPolynomial.CHom) a *
            (CPolynomial.C (R := CPolynomial F) ((CPolynomial.X (R := F)) ^ i) *
              (CPolynomial.X (R := CPolynomial F)) ^ d)) j =
        if d = j then CPolynomial.C a * CPolynomial.X ^ i else 0 := by
    rw [CPolynomial.coeff_toPoly]
    change ((CPolynomial.C (CPolynomial.C a) *
      (CPolynomial.C (CPolynomial.X ^ i) * CPolynomial.X ^ d)).toPoly.coeff j) = _
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
      CPolynomial.C_toPoly, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    rw [← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    simp [eq_comm]
  rw [CPolynomial.coeff_toPoly, CPolynomial.toPoly_sum, Polynomial.finsetSum_coeff]
  by_cases hj : j ∈ T.supportY
  · rw [Finset.sum_eq_single j]
    · rw [CPolynomial.toPoly_sum, Polynomial.finsetSum_coeff]
      simp_rw [← CPolynomial.coeff_toPoly]
      simp_rw [hcoeff]
      simp only [if_pos]
      apply CPolynomial.toPoly_injective
      rw [CPolynomial.toPoly_sum]
      simp_rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
        CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
      have hstored : (CPolynomial.coeff T j).toPoly = (T.val.coeff j).toPoly := by
        rw [← CBivariate.coeff_toPoly_Y]
        exact (CBivariate.toPoly_coeff T j).symm
      rw [hstored]
      rw [Polynomial.as_sum_support (T.val.coeff j).toPoly,
        ← CPolynomial.support_toPoly]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.C_mul_X_pow_eq_monomial]
      exact congrArg (Polynomial.monomial i)
        (CPolynomial.coeff_toPoly (T.val.coeff j) i)
    · intro b hb hbj
      rw [CPolynomial.toPoly_sum, Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i hi
      rw [← CPolynomial.coeff_toPoly, hcoeff, if_neg hbj]
    · exact fun hnot => (hnot hj).elim
  · rw [Finset.sum_eq_zero]
    · simpa [eq_comm] using (CPolynomial.mem_support_iff T j).not.mp hj
    · intro b hb
      rw [CPolynomial.toPoly_sum, Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i hi
      rw [← CPolynomial.coeff_toPoly, hcoeff,
        if_neg (show b ≠ j from fun h => hj (h ▸ hb))]

/-- Check both stored exponent coordinates before attempting a joint root. -/
def jointExponents (p : ℕ) (Q : CBivariate F) : Bool :=
  (List.range Q.size).all fun j =>
    (List.range (CPolynomial.coeff Q j).size).all fun i =>
      (CPolynomial.coeff Q j).coeff i == 0 || (i % p == 0 && j % p == 0)

/-- Divide both exponent coordinates and apply only the supplied base-field operation. -/
def jointContract (p : ℕ) (inverse : F → F) (Q : CBivariate F) : CBivariate F :=
  CPolynomial.ofArray <| Array.ofFn fun j : Fin (Q.natDegree / p + 1) =>
    CPolynomial.FullSquarefreeDecomposition.contractWith p inverse (CPolynomial.coeff Q (j * p))

/-- Coefficients of the executed joint contraction, including the trimmed tail. -/
theorem coeff_jointContract (p : ℕ) (inverse : F → F) (Q : CBivariate F) (j : ℕ) :
    CPolynomial.coeff (jointContract p inverse Q) j =
      if j < Q.natDegree / p + 1 then
        FullSquarefreeDecomposition.contractWith p inverse (CPolynomial.coeff Q (j * p))
      else 0 := by
  rw [jointContract, CPolynomial.coeff_ofArray]
  simp only [Array.getD, Array.size_ofFn]
  split <;> simp_all

/-- Joint contraction reconstructs any polynomial whose two partial derivatives vanish.
Only the base field has a certified inverse Frobenius; no perfection of `F(X)` is used. -/
theorem jointContract_pow [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a) (Q : CBivariate F)
    (hx : CBivariate.partialDerivX Q = 0) (hy : CBivariate.partialDerivY Q = 0) :
    jointContract p inverse Q ^ p = Q := by
  classical
  have hp := (Fact.out : Nat.Prime p).ne_zero
  have hd (j : ℕ) : (CPolynomial.coeff Q j).derivative = 0 := by
    have h := congrArg (fun T : CBivariate F => CPolynomial.coeff T j) hx
    simpa only [CBivariate.outerCoeff_partialDerivX, CPolynomial.coeff_zero] using h
  have hmap : (CBivariate.toPoly (jointContract p inverse Q)).map
      (frobenius (Polynomial F) p) = Polynomial.contract p (CBivariate.toPoly Q) := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_contract hp, CBivariate.toPoly_coeff,
      coeff_jointContract]
    split_ifs with hj
    · rw [frobenius_def, ← CPolynomial.toPoly_pow,
        FullSquarefreeDecomposition.contractWith_pow_eq p inverse hinverse _ (hd _),
        CBivariate.toPoly_coeff]
    · have hdeg : Q.natDegree < j * p := by
        exact (Nat.div_lt_iff_lt_mul (Fact.out : Nat.Prime p).pos).mp (by omega)
      have hz : CPolynomial.coeff Q (j * p) = 0 := by
        rw [CPolynomial.coeff_toPoly]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (by simpa only [CPolynomial.natDegree_toPoly] using hdeg)
      simp [CBivariate.toPoly_coeff, hz, CPolynomial.toPoly_zero]
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly (jointContract p inverse Q ^ p) = CBivariate.toPoly Q
  rw [show CBivariate.toPoly (jointContract p inverse Q ^ p) =
      CBivariate.toPoly (jointContract p inverse Q) ^ p from map_pow CBivariate.ringEquiv _ _]
  rw [← Polynomial.map_frobenius_expand, Polynomial.map_expand, hmap]
  apply Polynomial.expand_contract p _ hp
  simpa only [CBivariate.partialDerivY_toPoly, CBivariate.toPoly_zero] using
    congrArg CBivariate.toPoly hy

private theorem dvd_index_of_derivative_zero {R : Type*} [CommRing R]
    [NoZeroDivisors R] (p : ℕ) [CharP R p] (f : Polynomial R)
    (hd : f.derivative = 0) (i : ℕ) (hi : f.coeff i ≠ 0) : p ∣ i := by
  cases i with
  | zero => exact dvd_zero p
  | succ i =>
    have h := Polynomial.coeff_derivative f i
    rw [hd, Polynomial.coeff_zero, zero_eq_mul] at h
    exact (CharP.cast_eq_zero_iff R p (i + 1)).mp
      (by simpa only [Nat.cast_add, Nat.cast_one] using h.resolve_left hi)

/-- Both derivative-zero hypotheses imply that the stored exponent guard succeeds. -/
theorem jointExponents_of_partials [DecidableEq F] (p : ℕ) [CharP F p]
    (Q : CBivariate F) (hx : CBivariate.partialDerivX Q = 0)
    (hy : CBivariate.partialDerivY Q = 0) : jointExponents p Q = true := by
  simp only [jointExponents, List.all_eq_true, List.mem_range]
  intro j _ i _
  by_cases hc : (CPolynomial.coeff Q j).coeff i = 0
  · simp [hc]
  · have hdx : (CPolynomial.coeff Q j).toPoly.derivative = 0 := by
      have h := congrArg (fun T : CBivariate F => CPolynomial.coeff T j) hx
      rw [CBivariate.outerCoeff_partialDerivX, CPolynomial.coeff_zero] at h
      simpa only [CPolynomial.derivative_toPoly, CPolynomial.toPoly_zero] using
        congrArg CPolynomial.toPoly h
    have hi := dvd_index_of_derivative_zero p _ hdx i
      (by simpa only [CPolynomial.coeff_toPoly] using hc)
    have hdy : (CBivariate.toPoly Q).derivative = 0 := by
      simpa only [CBivariate.partialDerivY_toPoly, CBivariate.toPoly_zero] using
        congrArg CBivariate.toPoly hy
    have hj := dvd_index_of_derivative_zero p _ hdy j (by
      rw [CBivariate.toPoly_coeff]
      intro hz
      apply hc
      rw [CPolynomial.coeff_toPoly, hz, Polynomial.coeff_zero])
    simp [Nat.mod_eq_zero_of_dvd hi, Nat.mod_eq_zero_of_dvd hj]

/-- Checked joint root. Exponent checks precede coefficient contraction and the exact
stored power identity is independently checked before returning a root. -/
def jointRoot (p : ℕ) (inverse : F → F) (Q : CBivariate F) : Option (CBivariate F) :=
  if p ≤ 1 then none else
  if jointExponents p Q then
    let R := jointContract p inverse Q
    if R ^ p == Q then some R else none
  else none

/-- On every certified two-partial-zero input, the actual checked producer succeeds. -/
theorem jointRoot_eq_some [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a) (Q : CBivariate F)
    (hx : CBivariate.partialDerivX Q = 0) (hy : CBivariate.partialDerivY Q = 0) :
    jointRoot p inverse Q = some (jointContract p inverse Q) := by
  simp [jointRoot, Nat.not_le.mpr (Fact.out : Nat.Prime p).one_lt,
    jointExponents_of_partials p Q hx hy, jointContract_pow p inverse hinverse Q hx hy]

/-- A returned root comes with a global polynomial identity, valid at every fiber. -/
theorem jointRoot_pow {p : ℕ} {inverse : F → F} {Q R : CBivariate F}
    (h : jointRoot p inverse Q = some R) : R ^ p = Q := by
  unfold jointRoot at h
  split at h
  · simp at h
  · split at h
    · dsimp only at h
      split at h
      · rename_i heq
        have hr := Option.some.inj h
        subst R
        simpa using heq
      · simp at h
    · simp at h

/-- Joint-root extraction preserves polynomial graphs globally, before specialization. -/
theorem jointRoot_graph_iff {p : ℕ} {inverse : F → F} {Q R : CBivariate F}
    (hp : p ≠ 0) (h : jointRoot p inverse Q = some R) (P : CPolynomial F) :
    CBivariate.composeY R P = 0 ↔ CBivariate.composeY Q P = 0 := by
  classical
  rw [← CPolynomial.toPoly_eq_zero_iff, ← CPolynomial.toPoly_eq_zero_iff]
  rw [GuruswamiSudan.composeY_toPoly, GuruswamiSudan.composeY_toPoly]
  rw [← jointRoot_pow h]
  have hpow : CBivariate.toPoly (R ^ p) = CBivariate.toPoly R ^ p :=
    map_pow CBivariate.ringEquiv R p
  rw [hpow, Polynomial.eval_pow, pow_eq_zero_iff hp]

/-- Polynomial graphs over every constant-field extension survive joint contraction. -/
theorem jointRoot_graph_extension_iff {K : Type*} [Field K] (embedding : F →+* K)
    {p : ℕ} {inverse : F → F} {Q R : CBivariate F}
    (hp : p ≠ 0) (h : jointRoot p inverse Q = some R) (P : Polynomial K) :
    (CBivariate.toPoly R).eval₂ (Polynomial.mapRingHom embedding) P = 0 ↔
      (CBivariate.toPoly Q).eval₂ (Polynomial.mapRingHom embedding) P = 0 := by
  classical
  rw [← jointRoot_pow h]
  have hpow : CBivariate.toPoly (R ^ p) = CBivariate.toPoly R ^ p :=
    map_pow CBivariate.ringEquiv _ _
  rw [hpow, Polynomial.eval₂_pow, pow_eq_zero_iff hp]

/-- A nonconstant joint root strictly decreases Y degree, certifying recursive progress. -/
theorem jointRoot_degree_lt {p : ℕ} {inverse : F → F} {Q R : CBivariate F}
    (hp : 1 < p) (h : jointRoot p inverse Q = some R) (hQ : 0 < Q.natDegree) :
    R.natDegree < Q.natDegree := by
  classical
  have hpoly := congrArg CBivariate.toPoly (jointRoot_pow h)
  have hpow : CBivariate.toPoly (R ^ p) = CBivariate.toPoly R ^ p :=
    map_pow CBivariate.ringEquiv _ _
  rw [hpow] at hpoly
  have hd := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_pow, CBivariate.natDegreeY_toPoly,
    CBivariate.natDegreeY_toPoly] at hd
  change p * R.natDegree = Q.natDegree at hd
  have hr : 0 < R.natDegree := by
    by_contra hzero
    have hz : R.natDegree = 0 := by omega
    simp [hz] at hd
    omega
  nlinarith

/-- The power identity remains a polynomial identity at every coefficient fiber. -/
theorem jointRoot_specialize {p : ℕ} {inverse : F → F} {Q R : CBivariate F}
    (h : jointRoot p inverse Q = some R) (c : F) :
    (CBivariate.toPoly Q).map (Polynomial.evalRingHom c) =
      ((CBivariate.toPoly R).map (Polynomial.evalRingHom c)) ^ p := by
  classical
  rw [← jointRoot_pow h]
  change (CBivariate.ringEquiv (R ^ p)).map _ = _
  rw [map_pow, Polynomial.map_pow]
  rfl

/-- A globally squarefree derivative-zero polynomial cannot contain any polynomial graph.
This justifies discarding an inseparable factor only after reducedness is established. -/
theorem eval_ne_zero_of_squarefree_derivative_zero {R : Type*} [CommRing R]
    [Nontrivial R] (H : Polynomial R) (hsq : Squarefree H) (hd : H.derivative = 0)
    (a : R) : H.eval a ≠ 0 := by
  intro ha
  obtain ⟨B, hB⟩ := Polynomial.dvd_iff_isRoot.mpr ha
  have heval := congrArg (fun f : Polynomial R => f.eval a) hd
  rw [hB, Polynomial.derivative_mul] at heval
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, MulZeroClass.zero_mul,
    one_mul, add_zero, Polynomial.eval_zero] at heval
  obtain ⟨B', hB'⟩ := Polynomial.dvd_iff_isRoot.mpr heval
  apply Polynomial.not_isUnit_X_sub_C a
  apply hsq
  exact ⟨B', by rw [hB, hB', mul_assoc]⟩

/-- Global reducedness and zero Y derivative prove absence of all polynomial messages. -/
theorem no_graph_of_squarefree_inseparable (Q : CBivariate F)
    (hsq : Squarefree (CBivariate.toPoly Q))
    (hd : CBivariate.partialDerivY Q = 0) (P : CPolynomial F) :
    CBivariate.composeY Q P ≠ 0 := by
  classical
  rw [Ne, ← CPolynomial.toPoly_eq_zero_iff, GuruswamiSudan.composeY_toPoly]
  apply eval_ne_zero_of_squarefree_derivative_zero _ hsq
  simpa only [CBivariate.partialDerivY_toPoly, CBivariate.toPoly_zero] using
    congrArg CBivariate.toPoly hd

omit [BEq F] [LawfulBEq F] in
/-- In characteristic `p`, `Y^p-X` contributes no polynomial graph, even though
its Y derivative is zero. The X derivative supplies the contradiction. -/
theorem pow_ne_X (p : ℕ) [CharP F p] (P : Polynomial F) : P ^ p ≠ Polynomial.X := by
  intro h
  have hd := congrArg Polynomial.derivative h
  rw [Polynomial.derivative_pow, Polynomial.derivative_X] at hd
  have hp : (p : F) = 0 := (CharP.cast_eq_zero_iff F p p).mpr dvd_rfl
  simp only [hp, Polynomial.C_0, MulZeroClass.zero_mul] at hd
  exact zero_ne_one hd

end Polynomial.FunctionFieldAlgorithms.BivariateReducedSupport
