Require Import theory.set theory.projected_set algebra_notation.
Require Import logic.aprop.
Require Export interfaces.subset.notation.
Require Import set_lambda.
Require Import rewrite.

Definition element {X:set} : X ⊗ 𝒫 X ⇾ Ω := eval ∘ tensor_swap _ _.
Notation "x ∊ U" := (func_op element (@pair (set_T _) (set_T (subset_set _)) x U)) (at level 70) : aprop_scope.

Lemma equal_element `(U:𝒫 X) x y : x = y ⊠ x ∊ U ⊸ y ∊ U.
Proof. rew (aprod_adj _ _ _), (is_fun U x y). apply aandl. Qed.

Definition is_subset {X} (U V : 𝒫 X) := ∏ x:X, x ∊ U ⊸ x ∊ V.
Global Hint Extern 1 (Le (subset ?X)) => refine (@is_subset X) : typeclass_instances.
Global Hint Extern 1 (Le (set_T (subset_set ?X))) => refine (@is_subset X) : typeclass_instances.

(* Notation "x ⊆ y" := (@le (subset _) (@is_subset _) x y) : set_scope. *)
Notation "x ⊆ y" := (@le (set_T (subset_set _)) (@is_subset _) x y) : set_scope.

Import projection_notation.

Definition empty_subset X : 𝒫 X := { x : X | 𝐅 }.
Coercion   full_subset  X : 𝒫 X := { x : X | 𝐓 }.

Definition intersection {X} : 𝒫 X × 𝒫 X ⇾ 𝒫 X := set:(λ (p : 𝒫 X × 𝒫 X), { x | x ∊ π₁ p ∧ x ∊ π₂ p }).
Definition union        {X} : 𝒫 X × 𝒫 X ⇾ 𝒫 X := set:(λ (p : 𝒫 X × 𝒫 X), { x | x ∊ π₁ p ∨ x ∊ π₂ p }).
Definition complement   {X} : 𝒫 X ⇾ 𝒫 X := set:(λ U : 𝒫 X, { x | (x ∊ U)ᗮ }).

Notation "∅" := (@bottom (subset_set _) (empty_subset _)) : set_scope.

Global Hint Extern 1 (Bottom (subset_set ?X)) => refine (empty_subset X) : typeclass_instances.
Global Hint Extern 1 (Top    (subset_set ?X)) => refine (full_subset  X) : typeclass_instances.
Global Hint Extern 1 (Meet (subset_set ?X)) => refine (@intersection X ∘ tensor_to_prod _ _) : typeclass_instances.
Global Hint Extern 1 (Join (subset_set ?X)) => refine (@union X ∘ tensor_to_prod _ _) : typeclass_instances.

Global Hint Extern 1 (apos (_ ∊ full_subset _)) => refine sprop.I : typeclass_instances.
Global Hint Extern 1 (apos (_ ∊ @top _ (full_subset _))) => refine sprop.I : typeclass_instances.


Definition preimage {X Y} : (X ⇾ Y) ⇾ 𝒫 Y ⇾ 𝒫 X := set:(λ (f:X ⇾ Y) (V: 𝒫 Y), { x : X | f x ∊ V } ).
Definition    image {X Y} : (X ⇾ Y) ⇾ 𝒫 X ⇾ 𝒫 Y := set:(λ (f:X ⇾ Y) (U: 𝒫 X), { y : Y | ∐ x, x ∊ U ⊠ f x = y } ).

Module image_notation.
  Notation "f ⁺" := (func_op image f) (at level 7, no associativity, format "f ⁺") : op_scope.
  Notation "f ⁻" := (func_op preimage f) (at level 7, no associativity, format "f ⁻") : op_scope.
End image_notation.

Ltac unfold_image :=
  progress (try change (?y ∊ func_op (func_op image ?f) ?U) with (∐ x, x ∊ U ⊠ f x = y);
            try change (?x ∊ func_op (func_op preimage ?f) ?U) with (f x ∊ U)).

(** Define a coercion subset → set, that forgets the negative part of "∊". *)

Record subset_el `(U:𝒫 X) :=
{ subset_pt :> set_T X
; subset_pt_is_el : subset_pt ∊ U
}.
Arguments subset_pt {X U} _.

Global Hint Extern 2 (apos (subset_pt (U:=?U) ?x ∊ ?U)) => refine (subset_pt_is_el _ x) : typeclass_instances.

Definition subset_to_set `(U:𝒫 X) : set := projected_set (subset_pt (U:=U)).
Coercion subset_to_set : subset >-> set.

Global Hint Extern 1 (IsProjectedSet (set_T (subset_to_set _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure from_subset `(U:𝒫 X) : U ⇾ X
  := projected_set_project (subset_to_set U).
Definition from_subset_injective `{U:𝒫 X} : Injective (from_subset U)
  := projected_set_project_injective (subset_to_set U).
Global Hint Extern 2 (Injective (from_subset _)) => simple notypeclasses refine from_subset_injective : typeclass_instances.

Definition to_subset `{U:𝒫 X} x {el:x ∊ U} : U := {| subset_pt := x ; subset_pt_is_el := el |}.
