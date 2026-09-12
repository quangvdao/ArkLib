import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.Assembly

namespace ReedSolomon.ListDecoding.FirstOrderNormProducerTests

open CompPoly CPolynomial CPoly
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.FirstOrderNormProducer
open ReedSolomon.ListDecoding.FirstOrderNormProducer.ChartPolynomials

private abbrev E := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def U : CPolynomial E := CPolynomial.X
private def V : CPolynomial (CPolynomial E) := CPolynomial.X

private theorem U_monic : U.monic := by
  rw [CPolynomial.monic_toPoly_iff]
  simp [U, CPolynomial.X_toPoly]

private theorem U_squarefree : Squarefree U.toPoly := by
  rw [U, CPolynomial.X_toPoly]
  exact Polynomial.irreducible_X.squarefree

private theorem V_monic : V.monic := by
  rw [CPolynomial.monic_toPoly_iff]
  simp [V, CPolynomial.X_toPoly]

private theorem V_degree : V.natDegree < 5 := by
  rw [CPolynomial.natDegree_toPoly, V, CPolynomial.X_toPoly,
    Polynomial.natDegree_X]
  omega

/-- A ramified monic fiber `V²-U`. -/
private def fiber : CPolynomial (CPolynomial E) := V ^ 2 - CPolynomial.C U

/-- A small literal chart used to check the variable order `[U,V]`. -/
private def chart : ChartData E 1 2 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2 - CMvPolynomial.X 0
    separant := 1
    denominator := 1
    numerators := fun j => if j.val = 0 then CMvPolynomial.X 0 else CMvPolynomial.X 1 }

/-- Multiplication by `V` on `E[U,V]/(V²-U)` has determinant `-U`; two identical
nonuniversal rows therefore create a repeated norm root. -/
example : (blockNorm fiber V).toPoly.eval 0 = 0 := by
  apply blockNorm_eq_zero_of_point (RingHom.id E) 0 0 fiber V
  · rw [CPolynomial.monic_toPoly_iff]
    rw [fiber, V, CPolynomial.toPoly_sub, CPolynomial.toPoly_pow,
      CPolynomial.X_toPoly, CPolynomial.C_toPoly]
    exact Polynomial.monic_X_pow_sub_C _ (by omega)
  · simp [TowerRepresentation.evalNested,
      FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
      FirstOrderNormDecoder.D5.coefficientEval, fiber, V, U,
      CPolynomial.X_toPoly, CPolynomial.C_toPoly, CPolynomial.toPoly_sub,
      CPolynomial.toPoly_pow]
  · simp [TowerRepresentation.evalNested,
      FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
      FirstOrderNormDecoder.D5.coefficientEval, V, CPolynomial.X_toPoly]

private def linearFiber : CPolynomial (CPolynomial E) := V

private def candidates : List (TowerRepresentation (F := E)) :=
  materializeRetained (k := 2) U linearFiber
    (1 : CPolynomial (CPolynomial E)) (1 : CPolynomial (CPolynomial E))
    (fun j => if j.val = 0 then 1 else 0)
    U_monic U_squarefree (by simpa [linearFiber] using V_monic)

/-- The actual D5 preprocessing and coefficient materializer produce a nonempty well-formed
tower; this is not a supplied candidate list. -/
example (out : TowerRepresentation (F := E)) (hout : out ∈ candidates) : out.WellFormed 2 := by
  exact materializeRetained_wellFormed 5 U linearFiber
    (1 : CPolynomial (CPolynomial E)) (1 : CPolynomial (CPolynomial E))
    (fun j => if j.val = 0 then 1 else 0)
    U_monic U_squarefree (by simpa [linearFiber] using V_monic)
    (by simpa [linearFiber] using V_degree) out (by simpa [candidates] using hout)

/-- A geometric point selected by the retained norm support reaches an actual materialized
candidate, including through the preprocessing membership proof. -/
example : ∃ out ∈ candidates, out.Point (RingHom.id E) 0 0 := by
  obtain ⟨out, hout, hpoint, _⟩ := materializeRetained_point_complete 5 U linearFiber
    (1 : CPolynomial (CPolynomial E)) (1 : CPolynomial (CPolynomial E))
    (fun j : Fin 2 => if j.val = 0 then 1 else 0)
    U_monic U_squarefree (by simpa [linearFiber] using V_monic)
    (by simpa [linearFiber] using V_degree)
    (by
      intro u v _ _
      simpa only [TowerAlgebra.evalNested_one] using (one_ne_zero : (1 : AlgebraicClosure E) ≠ 0))
    (RingHom.id E) 0 0
    (by
      constructor
      · simp [retainedTower, U, CPolynomial.X_toPoly]
      · simp [retainedTower, linearFiber, V, TowerRepresentation.evalNested,
          FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
          FirstOrderNormDecoder.D5.coefficientEval, CPolynomial.X_toPoly])
    (by
      simpa only [TowerAlgebra.evalNested_one] using (one_ne_zero : (1 : E) ≠ 0))
  exact ⟨out, by simpa [candidates] using hout, hpoint⟩

/-- Runtime entrypoint for integration into the shared decoder suite. -/
def run : IO Unit := do
  unless (ofChart chart).equation == fiber do
    throw <| IO.userError "first-order chart variable order changed"
  unless blockNorm fiber V == -U do
    throw <| IO.userError "ramified multiplication-matrix norm is incorrect"
  unless blockNormProduct fiber [V, V] [] == (-U) ^ 2 do
    throw <| IO.userError "repeated norm roots were not preserved"
  unless candidates.length == 1 do
    throw <| IO.userError "tower preprocessing/materialization did not execute"

end ReedSolomon.ListDecoding.FirstOrderNormProducerTests
