Require Export interfaces.set.
Require Import easy.

Local Open Scope cat_scope.

Record cat_t@{u} :=
{ cat_ob :> Type@{u+1}
; cat_hom : cat_ob → cat_ob → set@{u}
}.
Arguments cat_hom {_} _ _.
Infix "⟶" := cat_hom : cat_scope.

Canonical Structure set_cat_t := Build_cat_t set func_set.

Class Id (C:cat_t) := 𝗂𝖽 (X:C) : X ⟶ X.
Class Compose (C:cat_t) := compose : ∀ {X Y Z : C}, (Y ⟶ Z) ⊗ (X ⟶ Y) ⇾ (X ⟶ Z).
Notation "g ⊚ f" := (func_op compose (g, f)) : cat_scope.

Global Hint Extern 1 (Id set_cat_t) => refine id_fun : typeclass_instances.
Global Hint Extern 1 (Compose set_cat_t) => refine @scompose : typeclass_instances.

Class IsCat (C:cat_t) {Ident:Id C} {c:Compose C} : SProp :=
{ cat_assoc {X Y Z W : C} (h:Z⟶W) (g:Y⟶Z) (f:X⟶Y) : h ⊚ (g ⊚ f) = h ⊚ g ⊚ f
; cat_id_l {X Y : C} (f:X⟶Y) : 𝗂𝖽 _ ⊚ f = f
; cat_id_r {X Y : C} (f:X⟶Y) : f ⊚ 𝗂𝖽 _ = f
}.

Lemma set_IsCat@{u} : IsCat set_cat_t@{u} (Ident:=id_fun@{u}).  Proof. now split. Qed.
Global Hint Extern 1 (IsCat set_cat_t) => refine set_IsCat : typeclass_instances.

Record cat :=
{ cat_data :> cat_t
; #[canonical=no, reversible=no] cat_id :> Id cat_data
; #[canonical=no, reversible=no] cat_compose :> Compose cat_data
; #[canonical=no, reversible=no] cat_is_cat :> IsCat cat_data
}.
Arguments Build_cat _ {_ _ _}.

Canonical Structure 𝐒𝐞𝐭 := Build_cat set_cat_t.

