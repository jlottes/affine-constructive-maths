Require Import abstract_algebra.

(*Class FromFreeSemiGroup `(i:X ⇾ F) := from_free_semigroup : ∀ `{oY: SgOp Y}                 (f:X ⇾ Y), F ⇾ Y. *)

Class FromFreeMonoid@{u} {X F:set@{u}} (i:X ⇾ F) := from_free_monoid    : ∀ {Y:set@{u}} {oY: SgOp Y} {uY: MonUnit Y} (f:X ⇾ Y), F ⇾ Y.
Arguments from_free_monoid {_ _} i {_ _ _ _} f.

Class FreeMonoid@{u} {X F:set@{u}} (i:X ⇾ F) {U:FromFreeMonoid i} {oF: SgOp F} {uF: MonUnit F} : SProp :=
{ free_monoid_structure : Monoid F
; from_free_monoid_mor {Y:set@{u}} `{Monoid Y} {f:X ⇾ Y} : Monoid_Morphism (from_free_monoid i f)
; from_free_monoid_ext {Y:set@{u}} `{Monoid Y} (f:X ⇾ Y) : from_free_monoid i f ∘ i = f
; free_monoid_initial {Y:set@{u}} `{Monoid Y} (f:X ⇾ Y) (h:F ⇾ Y) `{!Monoid_Morphism h} : h ∘ i = f → h = from_free_monoid i f
}.
Coercion free_monoid_structure : FreeMonoid >-> Monoid.
#[global] Hint Extern 1 (Monoid_Morphism (from_free_monoid _ _)) => simple notypeclasses refine from_free_monoid_mor : typeclass_instances.
#[global] Hint Extern 1 (MonUnit_Pointed_Morphism (from_free_monoid _ _)) => simple notypeclasses refine from_free_monoid_mor : typeclass_instances.
#[global] Hint Extern 1 (SemiGroup_Morphism (from_free_monoid _ _)) => simple notypeclasses refine from_free_monoid_mor : typeclass_instances.

