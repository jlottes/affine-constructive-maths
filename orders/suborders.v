Require Import orders.orders orders.maps.
Require Import interfaces.subset.
Require Import logic.aprop.
Require Import easy tactics.misc.

(** Induced order on subsets when viewed as sets. *)
(* Global Hint Extern 2 (Le (set_T (subset_to_set (X:=?X) _))) => let t := get_instance (Le X) in refine t : typeclass_instances. *)

(** Sub structures are instances of structures when viewed as sets. *)

Lemma sub_preorder_preorder {X:set} {Xle:Le X} `{!PreOrder X} {U:𝒫 X} : PreOrder U.
Proof. split.
+ intros x. now change (x ≤ x :> X).
+ intros x y z. change (x ≤ y :> X ⊠ y ≤ z :> X ⊸ x ≤ z :> X). now apply transitivity.
Qed.
Global Hint Extern 2 (PreOrder (set_T (subset_to_set _))) => simple notypeclasses refine sub_preorder_preorder : typeclass_instances.
Global Hint Extern 2 (PreOrder (@subset_el _ _))          => simple notypeclasses refine sub_preorder_preorder : typeclass_instances.
Global Hint Extern 2 (PreOrder (@powerset_el _ _))        => simple notypeclasses refine sub_preorder_preorder : typeclass_instances.


Lemma sub_weakposet_weakposet `{WeakPoset X} {U: 𝒫 X} : WeakPoset U.
Proof. pose proof _ : PreOrder U.  apply alt_Build_WeakPoset; try exact _.
+ intros [x y]. change (x = y :> X ⊸ x ≤ y :> X). now apply subrelation.
+ intros x y. change (x ≤ y :> X ⊠ y ≤ x :> X ⊸ x = y :> X). now apply pseudo_antisymmetry.
Qed.
Global Hint Extern 2 (WeakPoset (subset_to_set _)) => simple notypeclasses refine sub_weakposet_weakposet : typeclass_instances.


Lemma sub_poset_poset `{Poset X} {U: 𝒫 X} : Poset U.
Proof. split; try exact _.
  intros x y. change (x ≤ y :> X ∧ y ≤ x :> X ⊸ x = y :> X). now apply antisymmetry.
Qed.
Global Hint Extern 2 (Poset (subset_to_set _)) => simple notypeclasses refine sub_poset_poset : typeclass_instances.


Lemma sub_strongle_strongle {X:set} `{StrongLe X} {U: 𝒫 X} : StrongLe U.
Proof. intros x y z. change (x ≤ y :> X ∧ y ≤ z :> X ⊸ x ≤ z :> X). now apply strong_transitivity. Qed.
Global Hint Extern 2 (StrongLe (set_T (subset_to_set _))) => simple notypeclasses refine sub_strongle_strongle : typeclass_instances.

Lemma sub_decidablele_decidablele {X:set} `{DecidableLe X} {U: 𝒫 X} : DecidableLe U.
Proof. intros [x y]. now change (Decidable (x ≤ y :> X)). Qed.
Global Hint Extern 2 (DecidableLe (set_T (subset_to_set _))) => simple notypeclasses refine sub_decidablele_decidablele : typeclass_instances.

Lemma sub_affirmativele_affirmativele {X:set} `{AffirmativeLe X} {U: 𝒫 X} : AffirmativeLe U.
Proof. intros [x y]. now change (Affirmative (x ≤ y :> X)). Qed.
Global Hint Extern 2 (AffirmativeLe (set_T (subset_to_set _))) => simple notypeclasses refine sub_affirmativele_affirmativele : typeclass_instances.

Lemma sub_refutativele_refutativele {X:set} `{RefutativeLe X} {U: 𝒫 X} : RefutativeLe U.
Proof. intros [x y]. now change (Refutative (x ≤ y :> X)). Qed.
Global Hint Extern 2 (RefutativeLe (set_T (subset_to_set _))) => simple notypeclasses refine sub_refutativele_refutativele : typeclass_instances.


Lemma sub_strongposet_strongposet           `{StrongPoset      X} {U: 𝒫 X} : StrongPoset      U.  Proof. now split. Qed.
Lemma sub_decidableorder_decidableorder     `{DecidableOrder   X} {U: 𝒫 X} : DecidableOrder   U.  Proof. now split. Qed.
Lemma sub_affirmativeorder_affirmativeorder `{AffirmativeOrder X} {U: 𝒫 X} : AffirmativeOrder U.  Proof. now split. Qed.
Lemma sub_refutativeorder_refutativeorder   `{RefutativeOrder  X} {U: 𝒫 X} : RefutativeOrder  U.  Proof. now split. Qed.

Global Hint Extern 2 (StrongPoset      (subset_to_set _)) => simple notypeclasses refine sub_strongposet_strongposet : typeclass_instances.
Global Hint Extern 2 (DecidableOrder   (subset_to_set _)) => simple notypeclasses refine sub_decidableorder_decidableorder : typeclass_instances.
Global Hint Extern 2 (AffirmativeOrder (subset_to_set _)) => simple notypeclasses refine sub_affirmativeorder_affirmativeorder : typeclass_instances.
Global Hint Extern 2 (RefutativeOrder  (subset_to_set _)) => simple notypeclasses refine sub_refutativeorder_refutativeorder : typeclass_instances.


Lemma sub_total_order_total_order `{TotalOrder X} {U: 𝒫 X} : TotalOrder U.
Proof. split; try exact _.
  intros x y. change (x ≤ y :> X ∨ y ≤ x :> X). now apply total.
Qed.
Global Hint Extern 2 (TotalOrder (subset_to_set _)) => simple notypeclasses refine sub_total_order_total_order : typeclass_instances.

Lemma sub_linear_order_linear_order `{LinearOrder X} {U: 𝒫 X} : LinearOrder U.
Proof. split; try exact _.
  intros x y. change (x ≤ y :> X ⊞ y ≤ x :> X). now apply pseudo_total.
Qed.
Global Hint Extern 2 (LinearOrder (subset_to_set _)) => simple notypeclasses refine sub_linear_order_linear_order : typeclass_instances.

(** Inclusion of a subset is an order embedding *)

Lemma from_subset_order_embedding `{WeakPoset X} {U: 𝒫 X} : OrderEmbedding (from_subset U).
Proof. now apply alt_Build_OrderEmbedding. Qed.
Global Hint Extern 2 (OrderEmbedding  (from_subset _)) => simple notypeclasses refine from_subset_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (from_subset _)) => simple notypeclasses refine from_subset_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (from_subset _)) => simple notypeclasses refine from_subset_order_embedding : typeclass_instances.

