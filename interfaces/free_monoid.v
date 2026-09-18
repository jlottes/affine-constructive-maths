Require Import
 abstract_algebra bundled_algebra.

Section definition.
  Universes u.
  Local Notation "X ⟶ Y" := (monoid_morphism@{u} X Y).

  Context {X:set@{u}} {Xs:monoid@{u}}.
  Class FromFreeMonoid (i:X ⇾ Xs)
    := from_free_monoid : ∀ {M:monoid@{u}}, (X ⇾ M) → (Xs ⟶ M).

  Context (i:X ⇾ Xs).

  Class FreeMonoid {U:FromFreeMonoid i} : SProp :=
  { from_free_monoid_spec {M:monoid@{u}} (f:X ⇾ M) : f = from_free_monoid f ∘ i
  ; from_free_monoid_unique {M:monoid@{u}} (f:X ⇾ M) (h:Xs ⟶ M) :
      f = h ∘ i → h = from_free_monoid f
  }.
End definition.

Section strong.
  Universes u.
  Local Notation "X ⟶ Y" := (strong_op_monoid_morphism@{u} X Y).

  Context {X:set@{u}} {Xs:strong_op_monoid@{u}}.
  Class FromFreeStrongMonoid (i:X ⇾ Xs)
    := from_free_strong_monoid : ∀ {M:strong_op_monoid@{u}}, (X ⇾ M) ⇾ (Xs ⟶ M).

  Context (i:X ⇾ Xs).

  Class FreeStrongMonoid {U:FromFreeStrongMonoid i} : SProp :=
  { from_free_strong_monoid_spec {M:strong_op_monoid@{u}} (f:X ⇾ M) : f = from_free_strong_monoid f ∘ i
  ; from_free_strong_monoid_unique {M:strong_op_monoid@{u}} (f:X ⇾ M) (h:Xs ⟶ M) :
      f = h ∘ i → h = from_free_strong_monoid f
  }.
End strong.

