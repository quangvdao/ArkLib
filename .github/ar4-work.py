"""Reviewed, idempotent AR-4B coherence fix and adversarial acceptance clients."""
from pathlib import Path

version = 'ar4-resource-clients-v4'
marker = Path('.github/ar4-applied.txt')
if marker.read_text().strip() != version:
    assert marker.read_text().strip() == 'ar4-resource-coherence-v3'
    path = Path('ArkLib/Interaction/Oracle/Resource.lean')
    text = path.read_text()
    old = '  unfold toSourceHom\n  rw [SourceHom.familyMap_comp]'
    assert old in text
    text = text.replace(old, '  dsimp only [toSourceHom, ResourceSchema.asSource, comp]\n'
                             '  rw [SourceHom.familyMap_comp]')
    path.write_text(text)
    path = Path('ArkLibTest/Interaction/Oracle/ResourceExample.lean')
    text = path.read_text()
    target = 'section Universes\n'
    addition = '''/-- Tensor forgetting routes both resources to their matching product environments. -/
example : ((left.asSource catalog).tensor (right.asSource catalog)).eval
    ((fun _ => ⟨2, by decide⟩), (fun _ => ⟨4, by decide⟩))
    ((ResourceSchema.tensorSourceEquiv left right separate catalog).toHom.mapProgram readPair) =
      (3, 4) := rfl

/-- Combining views of one allocation is sharing, not a second allocation. -/
def shared := (ResourceView.full left).share aliases

/-- Different handles and primitive queries still use exactly one backing object. -/
def readShared : OracleComp (shared.asSource catalog).spec (Nat × Nat) := do
  let x : Nat ← liftM ((shared.asSource catalog).spec.query ⟨.inl ⟨⟩, true⟩)
  let y : Nat ← liftM ((shared.asSource catalog).spec.query ⟨.inr true, false⟩)
  return (x, y)

example : (left.asSource catalog).eval (fun _ => ⟨2, by decide⟩)
    ((shared.toSourceHom catalog).mapProgram readShared) = (3, 2) := rfl

/-- Both the primitive-query and response types vary with resource identity. -/
def mixedCatalog : ResourceCatalog Bool (fun r => if r then Fin 2 else Bool)
    (fun r => Fin (if r then 5 else 3)) Nat Nat (fun _ => Nat) where
  source := fun r => match r with
    | false =>
      { spec := Bool →ₒ Nat
        impl := fun _ (obj : Fin 3) => obj.val }
    | true =>
      { spec := Fin 2 →ₒ Bool
        impl := fun (query : Fin 2) (obj : Fin 5) => decide (query.val < obj.val) }
  owner := fun _ => 0
  origin := fun _ => 7
  promise := fun r => if r then 5 else 3
  meaning := fun _ bound obj => obj.val < bound
  promise_holds := fun _ obj => obj.isLt

/-- After renaming, the false handle has a `Fin 2` query and a `Bool` response. -/
def readMixed : OracleComp (renamed.asSource mixedCatalog).spec (Bool × Nat) := do
  let bit : Bool ← liftM ((renamed.asSource mixedCatalog).spec.query
    ⟨false, (⟨1, by decide⟩ : Fin 2)⟩)
  let value : Nat ← liftM ((renamed.asSource mixedCatalog).spec.query ⟨true, false⟩)
  return (bit, value)

example : (both.asSource mixedCatalog).eval bothEnv
    ((inclusion.toSourceHom mixedCatalog).mapProgram readMixed) = (true, 2) := rfl

'''
    assert target in text
    path.write_text(text.replace(target, addition + target))
    marker.write_text(version + '\n')
