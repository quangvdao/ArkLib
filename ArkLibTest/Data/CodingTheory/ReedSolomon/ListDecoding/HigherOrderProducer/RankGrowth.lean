/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.CotangentClasses

/-! Compile-time regressions for powered-edge rank growth and cotangent-to-Jacobian capture. -/

namespace ReedSolomon.ListDecoding.HigherOrderProducerTest

open ReedSolomon.ListDecoding.HigherOrderProducer
open ReedSolomon.HiddenDerivative.SquareSystems

example {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {n : ℕ} (pool : Fin n → V) (selected : Finset (Fin n))
    (edge : Fin n × Fin n)
    (hindependent : LinearIndepOn F pool (selected : Set (Fin n)))
    (hescape : EscapesPair (F := F) pool selected edge) :
    LinearIndepOn F pool (insert edge.2 (insert edge.1 selected) : Finset (Fin n)) :=
  linearIndepOn_insert_pair hindependent hescape

example {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {n r : ℕ}
    (map : V →ₗ[F] (Fin n → F)) (selected : Finset (Fin n))
    (hcard : selected.card = r) (hdim : Module.finrank F V = r)
    (hindependent : LinearIndepOn F (coordinateFunctional map)
      (selected : Set (Fin n))) :
    Function.Injective (selectedCoordinateMap map (rowSubsetEmbedding selected hcard)) :=
  selectedCoordinateMap_injective_of_independent map selected hcard hdim hindependent

example {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {n k : ℕ} (agreeing : Finset (Fin n))
    (map : V →ₗ[F] (Fin n → F))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional map) k)
    (hk : k ≤ agreeing.card) : Function.Injective map :=
  coordinateMap_injective_of_original_hypotheses agreeing map hbound hk

example {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {n k : ℕ} (agreeing : Finset (Fin n))
    (map : V →ₗ[F] (Fin n → F))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional map) k)
    (hk : k ≤ agreeing.card) :
    Function.Injective
      (selectedCoordinateMap map (agreeing.orderEmbOfFin rfl)) :=
  agreeingCoordinateMap_injective_of_original_hypotheses agreeing map hbound hk

example {F P : Type*} [Field F] {n r : ℕ}
    (hypersurface : P) (equations : Fin n → P) (evaluate : P → F)
    (agreeing selected : Finset (Fin n)) (hcard : selected.card = r)
    (hsubset : selected ⊆ agreeing) (hhypersurface : evaluate hypersurface = 0)
    (hagree : ∀ i ∈ agreeing, evaluate (equations i) = 0) :
    ∀ j, evaluate
      (squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) j) = 0 :=
  squareSystemRows_commonZero_of_subset hypersurface equations evaluate agreeing selected
    hcard hsubset hhypersurface hagree

end ReedSolomon.ListDecoding.HigherOrderProducerTest
