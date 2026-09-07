"""Reviewed, idempotent edits for the isolated AR-4 validation branch only."""
from pathlib import Path

version = 'ar4-source-clients-v2'
marker = Path('.github/ar4-applied.txt')
if marker.read_text().strip() != version:
    assert marker.read_text().strip() == 'ar4-source-levels-v1'
    path = Path('ArkLibTest/Interaction/Oracle/SourceExample.lean')
    text = path.read_text()
    replacements = {
        'let bit ←': 'let bit : Bool ←',
        'let value ←': 'let value : Fin 3 ←',
        '(env, 4 : (Bool × Fin 3) × Nat)': '((env, 4) : (Bool × Fin 3) × Nat)',
        'fun _ answer => answer + 3': 'fun _ (answer : Nat) => (answer + 3 : Nat)',
        'fun _ answer => answer * 2': 'fun _ (answer : Nat) => (answer * 2 : Nat)',
        'fun env q => env (!q) + 3': 'fun (env : Bool → Nat) q => (env (!q) + 3 : Nat)',
        'fun env q => env q * 2': 'fun (env : Bool → Nat) q => (env q * 2 : Nat)',
        ').handler answers false = 5': ').handler answers false = (5 : Nat)',
        '(true, false) = (⟨2, by decide⟩, 2)':
            '(true, false) = ((⟨2, by decide⟩ : Fin 3), (2 : Nat))',
        '⟨true, false⟩ = 29': '⟨true, false⟩ = (29 : Nat)',
        ').handler answers) true = 5': ').handler answers) true = (5 : Nat)',
    }
    for old, new in replacements.items():
        assert old in text, old
        text = text.replace(old, new)
    path.write_text(text)
    path = Path('ArkLib/Interaction/Oracle/Source.lean')
    text = path.read_text()
    target = '/-- Select one component of an indexed source family. -/'
    assert target in text
    addition = '''/-- Componentwise identity routing is identity routing of the complete family. -/
@[simp]
theorem familyMap_id {A : Type k} {Q : A → Type u} {Env : A → Type w}
    (S : (a : A) → SourceCtx.{u, v, w} (Q a) (Env a)) :
    familyMap S S (fun a => a) (fun a => id (S a)) = id (SourceCtx.family S) := rfl

/-- Family routing preserves composition, including contravariant backing-data maps. -/
theorem familyMap_comp {A : Type k} {B : Type k'} {C : Type k''}
    {QA : A → Type u} {EA : A → Type w} {QB : B → Type u'} {EB : B → Type w'}
    {QC : C → Type u''} {EC : C → Type w''}
    (S : (a : A) → SourceCtx.{u, v, w} (QA a) (EA a))
    (T : (b : B) → SourceCtx.{u', v', w'} (QB b) (EB b))
    (U : (c : C) → SourceCtx.{u'', v'', w''} (QC c) (EC c))
    (index : A → B) (next : B → C)
    (f : (a : A) → SourceHom (S a) (T (index a)))
    (g : (b : B) → SourceHom (T b) (U (next b))) :
    (familyMap T U next g).comp (familyMap S T index f) =
      familyMap S U (next ∘ index) (fun a => (g (index a)).comp (f a)) := rfl

'''
    path.write_text(text.replace(target, addition + target))
    marker.write_text(version + '\n')
