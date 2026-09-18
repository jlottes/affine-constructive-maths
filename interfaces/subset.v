Require Import theory.set theory.projected_set algebra_notation.
Require Import logic.aprop.
Require Export interfaces.subset.notation.
Require Import set_lambda.
Require Import rewrite tactics.misc.

Definition element {X:set} : X ⊗ 𝒫 X ⇾ Ω := set:(λ '(x, U) : X ⊗ 𝒫 X, U x).
Notation "x ∊ U" := (func_op element (@pair (set_T _) (set_T (subset_set _)) x U)) (at level 70, only parsing) : aprop_scope.
Notation "x ∊ U" := (func_op element (x, U)) (at level 70, only printing) : aprop_scope.
Notation "x ∊̸ U" := (anot (x ∊ U)) (at level 70, only parsing) : aprop_scope.
Notation "x ∊̸ U" := (anot (func_op element (x, U))) (at level 70, only printing) : aprop_scope.

Lemma equal_element `(U:𝒫 X) x y : x = y ⊠ x ∊ U ⊸ y ∊ U.
Proof. rew (aprod_adj _ _ _), (is_fun U x y). apply aandl. Qed.

Lemma member_apart_nonmember `(U:𝒫 X) x y : x ∊ U ⊠ y ∊̸ U ⊸ x ≠ y.
Proof. apply by_contrapositive. change (x = y ⊸ x ∊ U ⊸ y ∊ U). rew <-(aprod_adj _ _ _). apply equal_element. Qed.

Definition is_subset {X:set} := λ '(U, V), ∏ x:X, x ∊ U ⊸ x ∊ V.
Global Hint Extern 1 (Le (subset ?X)) => refine (@is_subset X) : typeclass_instances.
Global Hint Extern 1 (Le (set_T (subset_set ?X))) => refine (@is_subset X) : typeclass_instances.

(* Notation "x ⊆ y" := (@le (subset _) (@is_subset _) x y) : set_scope. *)
Notation "x ⊆ y" := (@le (set_T (subset_set _)) (@is_subset _)
   (@pair (subset _) (subset _) x y)) (only parsing) : set_scope.
Notation "x ⊆ y" := (@le _ is_subset (x, y)) (only printing) : set_scope.

Lemma subset_apply {X:set} (x:X) (U V : 𝒫 X) : x ∊ U ⊠ U ⊆ V ⊸ x ∊ V.
Proof. change (U ⊆ V) with (∏ x, x ∊ U ⊸ x ∊ V). rew (all_lb _ x). exact (aprod_mp_r _ _). Qed.

Import projection_notation.

Definition empty_subset X : 𝒫 X := { x : X | 𝐅 }.
Definition full_subset  X : 𝒫 X := { x : X | 𝐓 }.
Notation "⌈ X ⌉" := (full_subset X) (at level 0, format "⌈ X ⌉") : subset_scope.

Definition singleton {X} : X ⇾ 𝒫 X := set:(λ x:X, { y:X | x = y }).

Definition intersection {X} : 𝒫 X × 𝒫 X ⇾ 𝒫 X := set:(λ '(U, V) : 𝒫 X × 𝒫 X, { x | x ∊ U ∧ x ∊ V }).
Definition union        {X} : 𝒫 X × 𝒫 X ⇾ 𝒫 X := set:(λ '(U, V) : 𝒫 X × 𝒫 X, { x | x ∊ U ∨ x ∊ V }).
Definition complement   {X} : 𝒫 X ⇾ 𝒫 X := set:(λ U : 𝒫 X, { x | x ∊̸ U }).

Global Hint Extern 1 (Inverse (@complement ?X)) => refine (@complement X) : typeclass_instances.

Notation "∅" := (@bottom (subset_set _) (empty_subset _)) : set_scope.
Notation "U 'ᗮ'" := (complement U) (at level 1, left associativity) : subset_scope.


Global Hint Extern 1 (Bottom (subset_set ?X)) => refine (empty_subset X) : typeclass_instances.
Global Hint Extern 1 (Top    (subset_set ?X)) => refine (full_subset  X) : typeclass_instances.
Global Hint Extern 1 (Meet (subset_set ?X)) => refine (@intersection X ∘ tensor_to_prod _ _) : typeclass_instances.
Global Hint Extern 1 (Join (subset_set ?X)) => refine (@union X ∘ tensor_to_prod _ _) : typeclass_instances.

Global Hint Extern 1 (apos (_ ∊ full_subset _)) => refine sprop.I : typeclass_instances.
Global Hint Extern 1 (apos (_ ∊ @top _ (full_subset _))) => refine sprop.I : typeclass_instances.
Global Hint Extern 1 (apos (?y ∊ func_op (@singleton ?X) ?x)) => change (x = y :> X)  : typeclass_instances.

Definition mult_intersection {X} : 𝒫 X ⊗ 𝒫 X ⇾ 𝒫 X := λₛ '(U, V), { x : X | ∐ y, x = y ⊠ y ∊ U ⊠ y ∊ V }.
Definition mult_union        {X} : 𝒫 X ⊗ 𝒫 X ⇾ 𝒫 X := λₛ '(U, V), { x : X | ∏ y, x = y ⊸ y ∊ U ⊞ y ∊ V }.
Notation "U ⨶ V" := (func_op mult_intersection (@pair (𝒫 _) (𝒫 _) U V)) (at level 54, left associativity) : subset_scope.

Definition tensor_subset@{u} {X Y:set@{u}} := set:(λ '(U, V) : 𝒫 X ⊗ 𝒫 Y, { '(x, y) : X ⊗ Y | x ∊ U ⊠ y ∊ V }).
Definition prod_subset@{u}   {X Y:set@{u}} := set:(λ '(U, V) : 𝒫 X × 𝒫 Y, { '(x, y) : X × Y | x ∊ U ∧ y ∊ V }).
Notation "U ⊗ V" := (func_op tensor_subset (@pair (𝒫 _) (𝒫 _) U V)) (only parsing) : subset_scope.
Notation "U × V" := (func_op prod_subset   (@pair (𝒫 _) (𝒫 _) U V)) (only parsing) : subset_scope.
Notation "U ⊗ V" := (func_op tensor_subset (U, V)) (only printing) : subset_scope.
Notation "U × V" := (func_op prod_subset   (U, V)) (only printing) : subset_scope.

#[global] Hint Extern 2 (apos ((_, _) ∊ func_op tensor_subset (_, _))) => split : typeclass_instances.
#[global] Hint Extern 2 (apos ((_, _) ∊ func_op prod_subset (_, _))) => split : typeclass_instances.

(** Relations *)

Definition id_rel X := { '(x,y) : X ⊗ X | x = y }.

Definition compose_rel@{u} {X Y Z : set@{u}}
  := set:(λ '(R, S) : 𝒫 (X ⊗ Y) ⊗ 𝒫 (Y ⊗ Z), { '(x, z) : X ⊗ Z | ∐ y, (x, y) ∊ R ⊠ (y, z) ∊ S}).
Notation "R ⋄ S" := (func_op compose_rel (@pair (𝒫 _) (𝒫 _) R S)) (only parsing) : set_scope.
Notation "R ⋄ S" := (func_op compose_rel (R, S)) (only printing) : set_scope.
Notation "(⋄)" := compose_rel (only parsing) : set_scope.

Definition flip@{u} {X Y : set@{u}} := set:(λ R : 𝒫 (X ⊗ Y), { '(y, x) : Y ⊗ X | (x, y) ∊ R }).
Declare Scope rel_inv_scope.
Notation "R ⁻¹" := (flip R) (at level 1, left associativity, format "R ⁻¹") : rel_inv_scope.

#[global] Hint Extern 2 (SgOp (subset_set (_ ⊗ _))) => refine compose_rel : typeclass_instances.
#[global] Hint Extern 2 (MonUnit (subset_set (_ ⊗ _))) => refine (id_rel _) : typeclass_instances.
#[global] Hint Extern 2 (Inv (subset_set (_ ⊗ _))) => refine flip : typeclass_instances.


(** Image and preimage, and range *)


Definition preimage@{u} {X Y:set@{u}} : (X ⇾ Y) ⇾ 𝒫 Y ⇾ 𝒫 X := set:(λ (f:X ⇾ Y) (V: 𝒫 Y), { x : X | f x ∊ V } ).
Definition image@{u} {X Y:set@{u}} : (X → Y) ⇾ 𝒫 X ⇾ 𝒫 Y := set:(λ (f:X → Y) (U: 𝒫 X), { y : Y | ∐ x, f x = y ⊠ x ∊ U } ).
Definition range@{u} {A:Type@{u}} {Y:set@{u}} : (A → Y) ⇾ 𝒫 Y := set:(λ (f:A → Y), { y : Y | ∐ x, f x = y } ).

(** universal_image f ≡ {y:Y | ∏ x, f x = y ⊸ x ∊ U} *)
Definition universal_image@{u} {X Y:set@{u}} := set:(λ (f:X → Y), complement ∘ image f ∘ complement).


Module image_notation.
  Notation "f ⁎" := (func_op image f) (at level 1, left associativity, format "f ⁎") : op_scope.
  Notation "f *" := (func_op preimage f) (at level 1, left associativity, format "f *") : op_scope.
  Notation "f ⁎⁎" := (f⁎ ⁎) (at level 1, no associativity, only parsing) : op_scope.
  Notation "f **" := (f* *) (at level 1, no associativity, only parsing) : op_scope.
  Notation "∀.[ f ]" := (func_op universal_image f) (format "∀.[ f ]") : op_scope.
End image_notation.

#[global] Hint Extern 2 (Inverse (func_op image (func_op ?f))) => refine (func_op preimage f) : typeclass_instances.
#[global] Hint Extern 2 (Inverse (func_op preimage ?f)) => refine (func_op    image f) : typeclass_instances.
#[global] Hint Extern 2 (Inverse (func_op universal_image (func_op ?f))) => refine (func_op preimage f) : typeclass_instances.

Ltac unfold_image :=
  progress (try change (?y ∊ func_op (func_op image ?f) ?U) with (∐ x, f x = y ⊠ x ∊ U);
            try change (?x ∊ func_op (func_op preimage ?f) ?U) with (f x ∊ U)).


(** Define a coercion subset → set, that forgets the negative part of "∊". *)
Record subset_el `(U:𝒫 X) :=
{ subset_pt :> set_T X
; subset_pt_is_el : subset_pt ∊ U
}.
Arguments subset_pt {X U} _.
Arguments subset_pt_is_el {X U} _.

#[global] Hint Extern 1 (Equiv (@subset_el ?X ?U)) => refine (projected_set_eq (@subset_pt X U)) : typeclass_instances.
#[global] Hint Extern 2 (apos (subset_pt (U:=?U) ?x ∊ ?V)) => match U with V => refine (subset_pt_is_el x) end : typeclass_instances.

Canonical subset_to_set@{u} {X:set@{u}} (U:𝒫 X) := @set_make (subset_el U) (projected_set_eq subset_pt) _.
Coercion  subset_to_set : subset >-> set.

#[global] Hint Extern 1 (IsProjectedSet (set_T (subset_to_set _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure from_subset@{u} {X:set@{u}} (U:𝒫 X) : U ⇾ X
  := Eval red in projected_set_project (subset_to_set U).
Definition from_subset_injective@{u} {X:set@{u}} {U:𝒫 X} : Injective (from_subset U)
  := projected_set_project_injective (subset_to_set U).
Global Hint Extern 2 (Injective (from_subset _)) => simple notypeclasses refine from_subset_injective : typeclass_instances.
#[global] Hint Extern 2 (apos (func_op (from_subset ?U) ?x ∊ ?V)) => match U with V => refine (subset_pt_is_el x) end : typeclass_instances.

(** Congruence through the [subset_pt] coercion for the properness search.
    [subset_pt] is a primitive projection, so a [Proj] node is not an
    application and the generic [?f ?x] upgrade hints in orders/maps.v and
    theory/set.v can never match it; upgrade explicitly to the canonical
    [from_subset] morphism and let those hints descend. *)
#[global] Hint Extern 4 (apos (subset_pt ?x ≤ subset_pt ?y)) =>
  change (apos (func_op (from_subset _) x ≤ func_op (from_subset _) y)) : proper.
#[global] Hint Extern 4 (apos (subset_pt ?x = subset_pt ?y)) =>
  change (apos (func_op (from_subset _) x = func_op (from_subset _) y)) : proper.

Definition to_subset `{U:𝒫 X} x {el:x ∊ U} : U := {| subset_pt := x ; subset_pt_is_el := el |}.

Lemma singleton_inhabited {X:set} {x:X} : sprop.Inhabited (subset_to_set (singleton x)).
Proof. exists (to_subset x). constructor. Qed.
#[global] Hint Extern 1 (sprop.Inhabited (set_T (subset_to_set (func_op singleton _)))) => simple notypeclasses refine singleton_inhabited : typeclass_instances.


(** restrictions of maps *)

Class MapsInto@{u} {A:Type@{u}} {Y:set@{u}} (f:A → Y) (V : 𝒫 Y) : SProp := maps_into x : f x ∊ V.
Arguments maps_into {_ _} f V {_} x.
#[global] Hint Extern 19 (apos (?f ?x ∊ ?V)) => simple notypeclasses refine (maps_into f V x) : typeclass_instances.

Lemma corestrict_is_fun@{u} {X Y:set@{u}} {f:X ⇾ Y} {V:𝒫 Y} {H:MapsInto f V} : @IsFun X V (λ x, to_subset (f x)).
Proof. intros x y. exact (is_fun f x y). Qed.

Definition corestrict@{u} {X Y:set@{u}} (f:X ⇾ Y) (V:𝒫 Y) {H:MapsInto f V} : X ⇾ V := @func_make X V (λ x, to_subset (f x)) corestrict_is_fun.

(** MapsTo f U V ≣ U ⊆ f* V *)
Class MapsTo@{u} {X Y:set@{u}} (f:X ⇾ Y) (U : 𝒫 X) (V : 𝒫 Y) : SProp := maps_to x : x ∊ U ⊸ f x ∊ V.
Arguments maps_to {_ _} f U V {_} x.

Class WeakMapsTo@{u} {X Y:set@{u}} (f:X ⇾ Y) (U : 𝒫 X) (V : 𝒫 Y) : SProp := weak_maps_to x : x ∊ U → f x ∊ V.
Arguments weak_maps_to {_ _} f U V {_} x.

Coercion MapsTo_WeakMapsTo@{u} {X Y:set@{u}} `{@MapsTo X Y f U V} : WeakMapsTo f U V
  := λ x, aimpl_impl_pos (maps_to f U V x).

Coercion WeaksMapsTo_MapsInto `{@WeakMapsTo X Y f U V} : MapsInto (f ∘ from_subset U) V
  := λ u, H u (subset_pt_is_el u).

Definition restrict@{u} {X Y} f U V `{@WeakMapsTo@{u} X Y f U V} : U ⇾ V := corestrict (f ∘ from_subset U) V.

(** A map maps its preimage of [V] into [V], definitionally; so [restrict f (f* V) V]
    needs no side condition. *)
Definition preimage_maps_to@{u} {X Y:set@{u}} (f:X ⇾ Y) (V:𝒫 Y) : MapsTo f (func_op2 preimage f V) V
  := λ x, aimpl_refl _.
#[global] Hint Extern 2 (MapsTo _ ?U _) =>
  lazymatch U with func_op2 preimage _ _ => simple notypeclasses refine (preimage_maps_to _ _) end : typeclass_instances.
#[global] Hint Extern 2 (WeakMapsTo _ ?U _) =>
  lazymatch U with func_op2 preimage _ _ => simple notypeclasses refine (MapsTo_WeakMapsTo (H:=preimage_maps_to _ _)) end : typeclass_instances.
#[global] Hint Extern 2 (MapsInto ?fc _) =>
  lazymatch fc with _ ∘ from_subset (func_op2 preimage _ _) => simple notypeclasses refine (WeaksMapsTo_MapsInto (H:=MapsTo_WeakMapsTo (H:=preimage_maps_to _ _))) end : typeclass_instances.

(** Iterated powerset *)

Definition double_subset (X:set) := 𝒫 (𝒫 X).
Notation "𝒫²" := double_subset.
#[global] Hint Extern 1 (Le (double_subset _)) => unfold double_subset : typeclass_instances.

Definition powerset_el {X:set} : 𝒫² X → Type := @subset_el (𝒫 X).
Definition powerset_pt `(A:@powerset_el X F) : 𝒫 X := subset_pt A.
#[reversible] Coercion powerset_pt : powerset_el >-> subset.
Coercion powerset_el : double_subset >-> Sortclass.
#[global] Hint Extern 2 (apos (powerset_pt (F:=?F) ?x ∊ ?F)) => refine (subset_pt_is_el x) : typeclass_instances.

#[global] Hint Extern 1 (Equiv (@powerset_el ?X ?F)) => refine (projected_set_eq (@powerset_pt X F)) : typeclass_instances.

Canonical Structure powerset_pt_fun `(F:𝒫² X) : F ⇾ 𝒫 X := @func_make F (𝒫 X) powerset_pt (from_subset F).

Canonical double_subset_to_set `(F:𝒫² X) := @set_make (powerset_el F) (projected_set_eq powerset_pt) _.
Coercion double_subset_to_set : double_subset >-> set.
Identity Coercion double_subset_subset : double_subset >-> subset.


#[global] Hint Extern 50 => real_progress ltac:(fun _ => match goal with |- context [ double_subset_to_set ?F ] =>
  change (double_subset_to_set F) with (subset_to_set F) end) : typeclass_instances.
#[global] Hint Extern 50 => real_progress ltac:(fun _ => match goal with |- context [ double_subset_to_set ?F ] =>
  change (double_subset_to_set F) with (subset_to_set F) end) : proper.
  
