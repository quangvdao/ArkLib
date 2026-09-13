/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.NormProducts.ComponentNorms

/-! Runtime checks for determinant products computed from descended components. -/

namespace ComponentNormsTests

open CompPoly CPolynomial
open CompPoly.CPolynomial.NormProducts.ComponentNorms

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def x : CBivariate (ZMod 5) := CPolynomial.C CPolynomial.X
private def y : CBivariate (ZMod 5) := CPolynomial.X

def execute : IO Unit := do
  let left := y - x
  let right := y + x
  let meeting := left * right
  let residual := x * left
  let factors := runAggregateNormList meeting [residual]
  unless factors.length == 2 do
    throw (IO.userError "norm producer did not use both descended components")
  unless factors.count 1 == 1 do
    throw (IO.userError "universal component did not contribute exactly one unit factor")
  let product := runAggregateNormProduct meeting [residual]
  unless product != 0 && product.eval 0 == 0 && product.eval 1 != 0 do
    throw (IO.userError "computed component norm product accepted the wrong base point")
  -- At the meeting fiber `u = 0`, the left component has one universal
  -- position and the right component has none.  The aggregate diagnostic
  -- reaches multiplicity three by adding the two components, but neither
  -- component reaches its own threshold `A - |U_b|`.
  let adversarialResiduals := [y, left]
  let aggregateFalsePositive :=
    runAggregateRetainedNormProduct 5 3 meeting adversarialResiduals
  unless aggregateFalsePositive.eval 0 == 0 do
    throw (IO.userError "meeting-fiber test did not trigger aggregate false acceptance")
  let blocks :=
    Polynomial.FunctionFieldAlgorithms.ComponentDescent.run meeting adversarialResiduals |>.blocks
  unless blocks.map (fun b => b.universal.length) == [1, 0] do
    throw (IO.userError "meeting-fiber blocks did not have the expected varied universal counts")
  let retainedBlocks := runBlockRetainedNormProducts 5 3 meeting adversarialResiduals
  unless retainedBlocks.length == 2 && retainedBlocks.all (fun q => q.eval 0 != 0) do
    throw (IO.userError "per-block thresholds accepted a cross-component false candidate")
  let M := MulContext.naive (R := ZMod 5)
  let D := ModContext.naive (R := ZMod 5)
  let .ok fastBlocks := blocks.mapM (fun b =>
      fastBlockRetainedNormProduct 5 3 id M D b adversarialResiduals)
    | throw (IO.userError "G02 decomposition failed on a component-local norm product")
  unless fastBlocks == retainedBlocks do
    throw (IO.userError "G02 component thresholds disagree with retained norm support")
  let ramified := y ^ 2 - x
  let ramifiedProduct := runAggregateNormProduct ramified [y]
  unless ramifiedProduct != 0 && ramifiedProduct.eval 0 == 0 &&
      ramifiedProduct.eval 1 != 0 do
    throw (IO.userError "determinant norm lost the ramified fiber")

namespace SuppliedLinear

private abbrev modulus : CPolynomial (ZMod 5) := X

private instance : Fact modulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
  exact Polynomial.monic_X⟩

private instance : Fact (Irreducible modulus.toPoly) := ⟨by
  rw [CPolynomial.X_toPoly]
  exact Polynomial.irreducible_X⟩

open ArkLib.FiniteField.ExplicitConstruction
private abbrev E := Carrier modulus

/-- The public supplied boundary performs descent and one concrete G02 run per block without an
inverse-Frobenius callback from the caller. -/
def execute : IO Unit := do
  let x : CBivariate E := CPolynomial.C CPolynomial.X
  let y : CBivariate E := CPolynomial.X
  let h := y - x
  let residuals := [y]
  let M := MulContext.naive (R := E)
  let D := ModContext.naive (R := E)
  let .ok fast := fastSuppliedRunBlockRetainedNormProducts
      5 1 modulus M D h residuals
    | throw (IO.userError "supplied component-local G02 producer failed")
  unless fast.length == 1 && fast.all (fun q => q.eval 0 == 0 && q.eval 1 != 0) do
    throw (IO.userError "supplied component-local G02 output has the wrong roots")

end SuppliedLinear

#print axioms map_coefficientHom_eq_valueGlobal
#print axioms determinantFactor_ne_zero
#print axioms determinantFactor_eval₂_eq_zero_of_point
#print axioms runAggregateNormList_ne_zero
#print axioms runAggregateNormProduct_ne_zero
#print axioms natDegree_blockNormProduct_eq_sum
#print axioms natDegree_determinantFactor_le
#print axioms natDegree_blockNormProduct_le_degreeBudget
#print axioms run_natDegree_blockNormProduct_le_degreeBudget
#print axioms rootMultiplicity_blockNormProduct_map
#print axioms card_le_rootMultiplicity_blockNormProduct_map_of_points
#print axioms eval₂_blockRetainedNormProduct_eq_zero_iff_sum_rootMultiplicity
#print axioms blockRetainedNormProduct_monic
#print axioms blockRetainedNormProduct_squarefree
#print axioms run_blockRetainedNormProduct_eval₂_eq_zero_of_card_le_points
#print axioms threshold_mul_natDegree_blockRetainedNormProduct_le
#print axioms threshold_mul_natDegree_blockRetainedNormProduct_le_degreeBudget
#print axioms run_threshold_mul_natDegree_blockRetainedNormProduct_le_degreeBudget
#print axioms fastBlockRetainedNormProduct_eq_ok
#print axioms fastSuppliedBlockRetainedNormProduct_eq_ok
#print axioms thresholdProduct_eval₂_eq_zero_iff_blockRetainedNormProduct
#print axioms suppliedThresholdProduct_eval₂_eq_zero_iff_blockRetainedNormProduct

end ComponentNormsTests
