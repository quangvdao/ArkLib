"""Reviewed, idempotent AR-4B edits; no AR-3 or AR-4A source changes."""
from pathlib import Path

version = 'ar4-resource-coherence-v3'
marker = Path('.github/ar4-applied.txt')
if marker.read_text().strip() != version:
    assert marker.read_text().strip() == 'ar4-source-clients-v2'
    path = Path('ArkLib/Interaction/Oracle/Resource.lean')
    text = path.read_text()
    old = 'SourceHom.fromReindex (S.asSource C) (fun query => ⟨view.resolve query.1, query.2⟩)'
    assert old in text
    text = text.replace(old, '''SourceHom.fromReindex (S.asSource C)
    (fun query : (x : view.Handle) × Query (view.key x) => ⟨view.resolve query.1, query.2⟩)''')
    text = text.replace('under an independence pretense.', 'as a disjoint allocation.')
    target = '/-- Owner metadata is preserved independently of the extensional handler. -/'
    addition = '''/-- Forgetting allocation identity preserves identity routing, including backing data. -/
@[simp]
theorem toSourceHom_id (S : ResourceSchema.{i, s} Id)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    (id S).toSourceHom C = SourceHom.id (S.asSource C) := rfl

/-- Forgetting allocation identity preserves composition, not merely query labels. -/
theorem toSourceHom_comp (g : SchemaHom T U) (f : SchemaHom S T)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    (g.comp f).toSourceHom C = (g.toSourceHom C).comp (f.toSourceHom C) := by
  unfold toSourceHom
  rw [SourceHom.familyMap_comp]
  congr 1
  funext x
  exact (SourceHom.congrFamily_trans C.source (f.key_eq x).symm
    (g.key_eq (f.map x)).symm).symm

'''
    assert target in text
    text = text.replace(target, addition + target)
    target = '/-- The stable identity of the allocation serving a handle. -/'
    addition = '''/-- Handle reindexing preserves identity. -/
@[simp]
theorem reindex_id (view : ResourceView.{i, s, h} S) :
    view.reindex (fun x => x) = view := by cases view; rfl

/-- Handle reindexing preserves composition without changing the allocation. -/
theorem reindex_comp (view : ResourceView.{i, s, h} S) {A : Type j} {B : Type k}
    (f : A → view.Handle) (g : B → A) :
    (view.reindex f).reindex g = view.reindex (f ∘ g) := rfl

/-- Combine two views of the same allocation with explicit sharing, not a disjoint tensor. -/
def share (left : ResourceView.{i, s, h} S) (right : ResourceView.{i, s, j} S) :
    ResourceView S :=
  ⟨left.Handle ⊕ right.Handle, Sum.elim left.resolve right.resolve⟩

@[simp]
theorem share_resolve_inl (left : ResourceView.{i, s, h} S)
    (right : ResourceView.{i, s, j} S) (x : left.Handle) :
    (left.share right).resolve (.inl x) = left.resolve x := rfl

@[simp]
theorem share_resolve_inr (left : ResourceView.{i, s, h} S)
    (right : ResourceView.{i, s, j} S) (x : right.Handle) :
    (left.share right).resolve (.inr x) = right.resolve x := rfl

'''
    assert target in text
    text = text.replace(target, addition + target)
    addition = '''
/-- Forgetting a disjoint allocation tensor agrees with tensoring its extensional sources.

The explicit equivalence accounts for the dependent sum of slots and the product presentation of
backing environments. Both round trips preserve query routing and the complete backing data. -/
def tensorSourceEquiv (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id)
    (h : S.Disjoint T)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    SourceEquiv ((S.tensor T h).asSource C) ((S.asSource C).tensor (T.asSource C)) where
  toHom :=
    { route :=
        { toFunA := fun
            | ⟨.inl x, query⟩ => .inl ⟨x, query⟩
            | ⟨.inr x, query⟩ => .inr ⟨x, query⟩
          toFunB := by
            rintro ⟨x, query⟩ answer
            cases x <;> exact answer }
      onEnv := fun env x => match x with
        | .inl x => env.1 x
        | .inr x => env.2 x
      commutes := by
        rintro env ⟨x, query⟩
        cases x <;> rfl }
  invHom :=
    { route :=
        { toFunA := fun
            | .inl ⟨x, query⟩ => ⟨.inl x, query⟩
            | .inr ⟨x, query⟩ => ⟨.inr x, query⟩
          toFunB := by
            intro query answer
            cases query <;> exact answer }
      onEnv := fun env => (fun x => env (.inl x), fun x => env (.inr x))
      commutes := by
        intro env query
        cases query <;> rfl }
  left_inv := by
    apply SourceHom.ext
    · apply PFunctor.Lens.ext_mapObj
      rintro ⟨x, query⟩
      cases x <;> rfl
    · funext env x
      cases x <;> rfl
  right_inv := by
    apply SourceHom.ext
    · apply PFunctor.Lens.ext_mapObj
      intro query
      cases query <;> rfl
    · rfl

'''
    text = text.replace('\nend ResourceSchema\n', '\n' + addition + 'end ResourceSchema\n', 1)
    path.write_text(text)
    marker.write_text(version + '\n')
