"""Reviewed AR-4B client fixes and a genuine polynomial-guarantee witness."""
from pathlib import Path

version = 'ar4-resource-polynomial-v5'
marker = Path('.github/ar4-applied.txt')
if marker.read_text().strip() != version:
    assert marker.read_text().strip() == 'ar4-resource-clients-v4'
    path = Path('ArkLibTest/Interaction/Oracle/ResourceExample.lean')
    text = path.read_text()
    text = text.replace('import ArkLib.Interaction.Oracle.Resource',
        'import ArkLib.Interaction.Oracle.Resource\n'
        'import Mathlib.Algebra.Polynomial.Degree.Operations\n'
        'import Mathlib.Algebra.Polynomial.Eval.Defs')
    text = text.replace('⟨2, by decide⟩', 'smallObject')
    text = text.replace('⟨4, by decide⟩', 'largeObject')
    target = '/-- Neither side\'s backing data is constant or interchangeable with the other\'s type. -/'
    addition = '''/-- A concrete object in the three-valued backing type. -/
def smallObject : Fin 3 := ⟨2, by decide⟩

/-- A concrete object in the five-valued backing type. -/
def largeObject : Fin 5 := ⟨4, by decide⟩

'''
    assert target in text
    text = text.replace(target, addition + target)
    old = 'example : ¬ catalog.meaning false 0 (⟨0, by decide⟩ : Fin 3) := by decide'
    assert old in text
    text = text.replace(old, '''example : ¬ catalog.meaning false 0 (⟨0, by decide⟩ : Fin 3) := by
  change ¬ (0 < (0 : Nat))
  decide''')
    target = 'section Universes\n'
    addition = '''/-- A reified degree promise is witnessed by the actual polynomial used for evaluation.

The polynomial stays in the backing environment; the query interface only exposes evaluation.
This client uses Mathlib's refined mathematical objects, not an arbitrary function tagged as
low-degree. -/
noncomputable def polynomialCatalog : ResourceCatalog Unit (fun _ => Nat)
    (fun _ => {p : Polynomial Nat // p.natDegree < 2}) Unit Nat (fun _ => Nat) where
  source := fun _ =>
    { spec := Nat →ₒ Nat
      impl := fun query (obj : {p : Polynomial Nat // p.natDegree < 2}) => obj.val.eval query }
  owner := fun _ => ()
  origin := fun _ => 7
  promise := fun _ => 2
  meaning := fun _ bound obj => obj.val.natDegree < bound
  promise_holds := fun _ obj => obj.property

/-- A nonconstant polynomial whose refined type certifies its advertised degree bound. -/
noncomputable def linearObject : {p : Polynomial Nat // p.natDegree < 2} :=
  ⟨Polynomial.X, by simp⟩

example : (polynomialCatalog.source ()).handler linearObject 3 = (3 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 3 = 3
  simp

example : (polynomialCatalog.source ()).handler linearObject 7 = (7 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 7 = 7
  simp

example : polynomialCatalog.meaning () (polynomialCatalog.promise ()) linearObject :=
  polynomialCatalog.promise_holds () linearObject

/-- The descriptor zero cannot be substituted for the actual degree promise. -/
example : ¬ polynomialCatalog.meaning () 0 linearObject := by
  change ¬ (Polynomial.X : Polynomial Nat).natDegree < 0
  exact Nat.not_lt_zero _

'''
    assert target in text
    path.write_text(text.replace(target, addition + target))
    marker.write_text(version + '\n')
