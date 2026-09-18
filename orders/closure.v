Require Import interfaces.sprop logic.relations.
Require Import interfaces.orders interfaces.subset interfaces.common_props.
Require Import theory.sublattices.
Require Import orders.orders orders.maps orders.lattices orders.suborders orders.sublattices orders.subset orders.directed_sets.
Require Import orders.subset_images.
Require Import theory.set.
Require Import logic.aprop.
Require Import set_lambda.
Require Import easy rewrite simplify.

Import image_notation.
Local Notation "X 'ᵒᵖ'" := (Order_op X) (at level 1, format "X 'ᵒᵖ'").

(** Build lemmas for up-sets, down-sets, and directed subsets *)

Lemma Build_UpSet `{WeakPoset X} {U : 𝒫 X} :
  (∀ x y : X, x ≤ y ⊸ x ∊ U ⊸ y ∊ U) → UpSet U.
Proof. intro; red. now apply alt_Build_OrderPreserving. Qed.

Lemma Build_DownSet `{WeakPoset X} {U : 𝒫 X} :
  (∀ x y : X, x ≤ y ⊸ y ∊ U ⊸ x ∊ U) → DownSet U.
Proof. intro P; do 2 red. apply alt_Build_OrderPreserving. intros x y. exact (P y x). Qed.

Lemma Build_LeastDownSet `{WeakPoset X} {U : 𝒫 X} :
  (∀ x : X, x ∊ U ⧟ ∐ a : U, x ≤ subset_pt a) → LeastDownSet U.
Proof. intro; now split. Qed.

Lemma Build_UpDirectedSubset {X:set} {Xle:Le X} `{PreOrder X} {U : 𝒫 X} :
  (∐ x : X, x ∊ U)
 → (∀ x y : X, x ∊ U ⊠ y ∊ U ⊸ ∐ z : X, z ∊ U ⊠ x ≤ z ⊠ y ≤ z)
 → UpDirectedSubset U.
Proof. now split. Qed.

Lemma Build_DownDirectedSubset {X:set} {Xle:Le X} `{PreOrder X} {U : 𝒫 X} :
  (∐ x : X, x ∊ U)
 → (∀ x y : X, x ∊ U ⊠ y ∊ U ⊸ ∐ z : X, z ∊ U ⊠ z ≤ x ⊠ z ≤ y)
 → DownDirectedSubset U.
Proof. now split. Qed.

Coercion DownSet_OrderPreservingFlip `{H:@DownSet X Xle U} : OrderPreservingFlip U.
Proof. simple notypeclasses refine (alt_Build_OrderPreservingFlip _); try exact _.
+ now change (WeakPoset ((X ᵒᵖ) ᵒᵖ)).
+ exact (down_closed U).
Qed.

Coercion LeastUpSet_UpSet `{@LeastUpSet X Xle U} : UpSet U.
Proof. apply Build_UpSet. intros x y.
  rew <-(aprod_adj _ _ _), (least_upset U _), aex_frob_l, <-aex_adj; intros a.
  rew (aprod_com _ _), (transitivity (≤) _ _ _).
  exact (aex_ub _ a).
Qed.

Coercion LeastDownSet_DownSet `{H:@LeastDownSet X Xle U} : DownSet U.
Proof. exact (@LeastUpSet_UpSet _ _ _ H). Qed.


Coercion UpDirectedSubset_UpDirected `{@UpDirectedSubset X Xle U} : UpDirected U.
Proof. split; try exact _.
+ destruct (up_directed_subset_inhabited U) as [x el].
  now exists (to_subset x).
+ intros [x elx] [y ely].
  pose proof aimpl_impl_pos (up_directed_subset U x y) (sprop.conj _ _) as [z [elz ?]].
  now exists (to_subset z).
Qed.

Coercion DownDirectedSubset_DownDirected `{@DownDirectedSubset X Xle U} : DownDirected U.
Proof. exact (UpDirectedSubset_UpDirected (X:=X ᵒᵖ)). Qed.


(** Opposite order instances *)

Definition UpSet_op `{H:DownSet (X:=X) U} : UpSet (X:=X ᵒᵖ) U := H.
Definition DownSet_op `{H:UpSet (X:=X) U} : DownSet (X:=X ᵒᵖ) U := H.
Global Hint Extern 2 (UpSet (X:=_ ᵒᵖ) _) => simple notypeclasses refine UpSet_op : typeclass_instances.
Global Hint Extern 2 (DownSet (X:=_ ᵒᵖ) _) => simple notypeclasses refine DownSet_op : typeclass_instances.

Definition LeastUpSet_op `{H:LeastDownSet (X:=X) U} : LeastUpSet (X:=X ᵒᵖ) U := H.
Definition LeastDownSet_op `{H:LeastUpSet (X:=X) U} : LeastDownSet (X:=X ᵒᵖ) U := H.
Global Hint Extern 2 (LeastUpSet (X:=_ ᵒᵖ) _) => simple notypeclasses refine LeastUpSet_op : typeclass_instances.
Global Hint Extern 2 (LeastDownSet (X:=_ ᵒᵖ) _) => simple notypeclasses refine LeastDownSet_op : typeclass_instances.

Definition UpDirectedSubset_op `{H:DownDirectedSubset (X:=X) U} : UpDirectedSubset (X:=X ᵒᵖ) U := H.
Definition DownDirectedSubset_op `{H:UpDirectedSubset (X:=X) U} : DownDirectedSubset (X:=X ᵒᵖ) U := H.
Global Hint Extern 2 (UpDirectedSubset (X:=_ ᵒᵖ) _) => simple notypeclasses refine UpDirectedSubset_op : typeclass_instances.
Global Hint Extern 2 (DownDirectedSubset (X:=_ ᵒᵖ) _) => simple notypeclasses refine DownDirectedSubset_op : typeclass_instances.

(** Canonical function instances for UpSet / DownSet, enabling subset-equality rewrites. *)

Lemma UpSet_proper_impl {X:set} {Xle:Le X} {U V : 𝒫 X}
  : U = V → impl (UpSet U, UpSet V).
Proof. intros E P. apply Build_UpSet. intros x y.
  change (U = V) with (∏ z, z ∊ U ⧟ z ∊ V) in E.
  rew <-(E x), <-(E y). exact (up_closed U x y).
Qed.
Canonical Structure UpSet_fun {X:set} {Xle:Le X} :=
  make_weak_spred (@UpSet X Xle) (@UpSet_proper_impl X Xle).

Lemma DownSet_proper_impl {X:set} {Xle:Le X} {U V : 𝒫 X}
  : U = V → impl (DownSet U, DownSet V).
Proof. intros E P. apply Build_DownSet. intros x y.
  change (U = V) with (∏ z, z ∊ U ⧟ z ∊ V) in E.
  rew <-(E x), <-(E y). exact (down_closed U x y).
Qed.
Canonical Structure DownSet_fun {X:set} {Xle:Le X} :=
  make_weak_spred (@DownSet X Xle) (@DownSet_proper_impl X Xle).

Lemma LeastUpSet_proper_impl {X:set} {Xle:Le X} {U V : 𝒫 X}
  : U = V → impl (LeastUpSet U, LeastUpSet V).
Proof. intros E P. split; try exact _. intros x.
  rew <-E at 1. rew (least_upset U x).
  split; rew <-aex_adj; intros [a Ha]; unfold subset_pt.
* assert (a ∊ V) by now rew <-E. exact (aex_ub _ (to_subset a)).
* assert (a ∊ U) by now rew   E. exact (aex_ub _ (to_subset a)).
Qed.
Canonical Structure LeastUpSet_fun {X:set} {Xle:Le X} :=
  make_weak_spred (@LeastUpSet X Xle) (@LeastUpSet_proper_impl X Xle).

Lemma LeastDownSet_proper_impl {X:set} {Xle:Le X} {U V : 𝒫 X}
  : U = V → impl (LeastDownSet U, LeastDownSet V).
Proof. exact (LeastUpSet_proper_impl (X:=X ᵒᵖ)). Qed.
Canonical Structure LeastDownSet_fun {X:set} {Xle:Le X} :=
  make_weak_spred (@LeastDownSet X Xle) (@LeastDownSet_proper_impl X Xle).

Lemma UpDirectedSubset_proper_impl {X:set} {Xle:Le X} (U V : 𝒫 X)
  : U = V → UpDirectedSubset U → UpDirectedSubset V.
Proof. intros E P; split.
+ exact _.
+ rew <-E. exact (up_directed_subset_inhabited U).
+ intros x y. rew <-E. exact (up_directed_subset U x y).
Qed.
Canonical Structure UpDirectedSubset_fun {X:set} {Xle:Le X} :=
  make_weak_spred (@UpDirectedSubset X Xle) UpDirectedSubset_proper_impl.

Definition DownDirectedSubset_proper_impl {X:set} {Xle:Le X} (U V : 𝒫 X)
  : U = V → DownDirectedSubset U → DownDirectedSubset V
  := UpDirectedSubset_proper_impl (X:=X ᵒᵖ) U V.
Canonical Structure DownDirectedSubset_fun {X:set} {Xle:Le X} :=
  make_weak_spred (@DownDirectedSubset X Xle) DownDirectedSubset_proper_impl.

(** Miscellaneous *)
Lemma up_closed_alt `{@UpSet X Xle U} x y : x ∊ U ⊸ (x ≤ y ⊸ y ∊ U).
Proof. generalize (up_closed U x y). tautological. Qed.
Arguments up_closed_alt {_ _} U {_} x y.

Lemma down_closed_alt `{@DownSet X Xle U} x y : x ∊ U ⊸ (y ≤ x ⊸ y ∊ U).
Proof. exact (up_closed_alt (X:=X ᵒᵖ) U x y). Qed.
Arguments down_closed_alt {_ _} U {_} x y.

(** top directed *)
Lemma top_up_directed {X:set} `{@UpDirected X Xle} : UpDirectedSubset ⌈X⌉.
Proof. apply Build_UpDirectedSubset.
+ pose proof inhabited X as [x _]. now exists x.
+ intros x y. change (𝐓 ⊠ 𝐓 ⊸ ∐ z, 𝐓 ⊠ x ≤ z ⊠ y ≤ z). simplify.
  exact (up_directed x y).
Qed.
#[global] Hint Extern 2 (UpDirectedSubset ⌈_⌉) => simple notypeclasses refine top_up_directed : typeclass_instances.
#[global] Hint Extern 2 (UpDirectedSubset ⊤) => simple notypeclasses refine top_up_directed : typeclass_instances.

Lemma top_down_directed {X:set} `{@DownDirected X Xle} : DownDirectedSubset ⌈X⌉.
Proof. exact (top_up_directed (X:=X ᵒᵖ)). Qed.
#[global] Hint Extern 2 (DownDirectedSubset ⌈_⌉) => simple notypeclasses refine top_down_directed : typeclass_instances.
#[global] Hint Extern 2 (DownDirectedSubset ⊤) => simple notypeclasses refine top_down_directed : typeclass_instances.

(** Singletons *)
Lemma singleton_up_directed `{WeakPoset X} {x:X} : UpDirectedSubset (singleton x).
Proof. apply Build_UpDirectedSubset.
+ now exists x.
+ intros a b. rew <-(aex_ub _ x). change (x = a ⊠ x = b ⊸ x = x ⊠ a ≤ x ⊠ b ≤ x). simplify.
  now rew (eq_le_flip _ _).
Qed.
#[global] Hint Extern 2 (UpDirectedSubset (func_op singleton _)) => simple notypeclasses refine singleton_up_directed : typeclass_instances.
#[global] Hint Extern 2 (UpDirected (set_T (subset_to_set (func_op singleton _)))) => simple notypeclasses refine singleton_up_directed : typeclass_instances.

Definition singleton_down_directed `{WeakPoset X} {x:X} : DownDirectedSubset (singleton x)
  := singleton_up_directed (X:=X ᵒᵖ) (x:=x).
#[global] Hint Extern 2 (DownDirectedSubset (func_op singleton _)) => simple notypeclasses refine singleton_down_directed : typeclass_instances.
#[global] Hint Extern 2 (DownDirected (set_T (subset_to_set (func_op singleton _)))) => simple notypeclasses refine singleton_down_directed : typeclass_instances.

(** products *)
Lemma up_directed_tensor_subset@{u} `{@UpDirectedSubset@{u} X Xle U} `{@UpDirectedSubset@{u} Y Yle V} : UpDirectedSubset (U ⊗ V).
Proof. apply Build_UpDirectedSubset.
+ pose proof up_directed_subset_inhabited U as [x elx].
  pose proof up_directed_subset_inhabited V as [y ely].
  now exists (x, y).
+ intros [x₁ y₁][x₂ y₂]. change (_ ⊸ ?P) with ( (x₁ ∊ U ⊠ y₁ ∊ V) ⊠ (x₂ ∊ U ⊠ y₂ ∊ V) ⊸ P ).
  rew (aprod_medial _ _ _ _). rew [(up_directed_subset U _ _)|(up_directed_subset V _ _)].
  rew <-aex_adj2; intros x y. rew <-(aex_ub _ (x, y)).
  change ((x, y) ∊ (U ⊗ V)%subset) with (x ∊ U ⊠ y ∊ V). unfold_pair_le. tautological.
Qed.
#[global] Hint Extern 2 (UpDirectedSubset (_ ⊗ _)) => simple notypeclasses refine up_directed_tensor_subset : typeclass_instances.
#[global] Hint Extern 2 (UpDirected (set_T (subset_to_set (_ ⊗ _)))) => simple notypeclasses refine up_directed_tensor_subset : typeclass_instances.

Lemma down_directed_tensor_subset@{u} `{@DownDirectedSubset@{u} X Xle U} `{@DownDirectedSubset@{u} Y Yle V} : DownDirectedSubset (U ⊗ V).
Proof. exact (up_directed_tensor_subset (X:=X ᵒᵖ) (Y:=Y ᵒᵖ)). Qed.
#[global] Hint Extern 2 (DownDirectedSubset (_ ⊗ _)) => simple notypeclasses refine down_directed_tensor_subset : typeclass_instances.
#[global] Hint Extern 2 (DownDirected (set_T (subset_to_set (_ ⊗ _)))) => simple notypeclasses refine down_directed_tensor_subset : typeclass_instances.

(*
Lemma up_directed_prod_subset@{u} `{@UpDirectedSubset@{u} X Xle U} `{@UpDirectedSubset@{u} Y Yle V} : UpDirectedSubset (U × V).
Proof. apply Build_UpDirectedSubset.
+ pose proof up_directed_subset_inhabited U as [x elx].
  pose proof up_directed_subset_inhabited V as [y ely].
  now exists (x, y).
+ intros [x₁ y₁][x₂ y₂]. change (_ ⊸ ?P) with ( (x₁ ∊ U ∧ y₁ ∊ V) ⊠ (x₂ ∊ U ∧ y₂ ∊ V) ⊸ P ).
  rew (aand_aprod_swap _ _ _ _). rew [(up_directed_subset U _ _)|(up_directed_subset V _ _)].
  apply aimpl_split_dual.
  rew <-aex_adj2; intros x y. rew <-(aex_ub _ (x, y)).
  change ((x, y) ∊ (U ⊗ V)%subset) with (x ∊ U ⊠ y ∊ V). unfold_pair_le. tautological.
Qed.
#[global] Hint Extern 2 (UpDirectedSubset (_ ⊗ _)) => simple notypeclasses refine up_directed_tensor_subset : typeclass_instances.

Lemma down_directed_tensor_subset@{u} `{@DownDirectedSubset@{u} X Xle U} `{@DownDirectedSubset@{u} Y Yle V} : DownDirectedSubset (U ⊗ V).
Proof. exact (up_directed_tensor_subset (X:=X ᵒᵖ) (Y:=Y ᵒᵖ)). Qed.
#[global] Hint Extern 2 (DownDirectedSubset (_ ⊗ _)) => simple notypeclasses refine down_directed_tensor_subset : typeclass_instances.
*)


(** image *)
Lemma image_up_directed@{u} `{@OrderPreserving@{u} X Y Xle Yle f, U:𝒫 X, !UpDirectedSubset U}
  : UpDirectedSubset (f⁎ U).
Proof. pose proof _ : WeakPoset Y. apply Build_UpDirectedSubset.
+ pose proof (up_directed_subset_inhabited U) as [x ?]. now exists (f x).
+ intros y₁ y₂. change ((∐ x₁, f x₁ = y₁ ⊠ x₁ ∊ U) ⊠ (∐ x₂, f x₂ = y₂ ⊠ x₂ ∊ U) ⊸ ∐ z, z ∊ f⁎ U ⊠ y₁ ≤ z ⊠ y₂ ≤ z).
  rew <-aex_adj2; intros x₁ x₂. rew (aprod_medial _ _ _ _).
  rew (up_directed_subset U x₁ x₂), aex_frob_l, <-aex_adj; intros x. rew <-(aex_ub _ (f x)), <-(image_el f _ _).
  rew (eq_le_flip _ _).
  rew [<-(transitivity (≤) y₁ (f x₁) (f x)) | <-(transitivity (≤) y₂ (f x₂) (f x))].
  rew <-(order_preserving f _ _).
  tautological.
Qed.
#[global] Hint Extern 2 (UpDirectedSubset (func_op _⁎ _)) => simple notypeclasses refine image_up_directed : typeclass_instances.
#[global] Hint Extern 2 (UpDirected (set_T (subset_to_set (func_op _⁎ _)))) => simple notypeclasses refine image_up_directed : typeclass_instances.

Lemma image_down_directed@{u} `{@OrderPreserving@{u} X Y Xle Yle f, U:𝒫 X, !DownDirectedSubset U}
  : DownDirectedSubset (f⁎ U).
Proof. exact (image_up_directed (X:=X ᵒᵖ)). Qed.
#[global] Hint Extern 2 (DownDirectedSubset (func_op _⁎ _)) => simple notypeclasses refine image_down_directed : typeclass_instances.
#[global] Hint Extern 2 (DownDirected (set_T (subset_to_set (func_op _⁎ _)))) => simple notypeclasses refine image_down_directed : typeclass_instances.

Lemma range_up_directed@{u} `{@OrderPreserving@{u} X Y Xle Yle f, !UpDirected X} : UpDirectedSubset (range f).
Proof. now rew (range_image _). Qed.
#[global] Hint Extern 2 (UpDirectedSubset (func_op range _)) => simple notypeclasses refine range_up_directed : typeclass_instances.
#[global] Hint Extern 2 (UpDirected (set_T (subset_to_set (func_op range _)))) => simple notypeclasses refine range_up_directed : typeclass_instances.

Lemma range_down_directed@{u} `{@OrderPreserving@{u} X Y Xle Yle f, !DownDirected X} : DownDirectedSubset (range f).
Proof. now rew (range_image _). Qed.
#[global] Hint Extern 2 (DownDirectedSubset (func_op range _)) => simple notypeclasses refine range_down_directed : typeclass_instances.
#[global] Hint Extern 2 (DownDirected (set_T (subset_to_set (func_op range _)))) => simple notypeclasses refine range_down_directed : typeclass_instances.

(** Lattices *)
Lemma upset_join_sub_sl `{JoinSemiLatticeOrder L} {U:𝒫 L} `{!UpSet U} : JoinSubSemiLattice U.
Proof. apply alt_Build_JoinSubSemiLattice. intros x y.
  now rew <-(sprop.andl (up_closed U _ _) (join_ub_l _ _)).
Qed.

Lemma downset_meet_sub_sl : ∀ `{MeetSemiLatticeOrder L} {U:𝒫 L} `{!DownSet U}, MeetSubSemiLattice U.
Proof. intros L ??. exact (@upset_join_sub_sl (L ᵒᵖ) _ _). Qed.

(** Upward and downward closure of a subset of a preorder *)

Definition upward_closure `{WeakPoset P} : 𝒫 P ⇾ 𝒫 P := set:(λ B : 𝒫 P, { w : P |  ∐ b : P, b ∊ B ⊠ b ≤ w }).
Definition downward_closure `{WeakPoset P} : 𝒫 P ⇾ 𝒫 P := set:(λ B : 𝒫 P, { w : P |  ∐ b : P, b ∊ B ⊠ w ≤ b }).

Section upward_closure.
  Context `{WeakPoset P}.

  Local Instance subset_upward_closure (B : 𝒫 P) : B ⊆ upward_closure B.
  Proof. change (∏ x, x ∊ B ⊸ x ∊ upward_closure B). intros b.
    change (b ∊ B ⊸ ∐ b' : P, b' ∊ B ⊠ b' ≤ b).
    rew <-(aex_ub _ b). now simplify.
  Qed.

  Local Instance upward_closure_is_upset (B : 𝒫 P) : UpSet (upward_closure B).
  Proof. apply Build_UpSet. intros x y. change (x ≤ y ⊸ (∐ b, b ∊ B ⊠ b ≤ x) ⊸ ∐ b, b ∊ B ⊠ b ≤ y).
    rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj. intros b. rew <-(aex_ub _ b).
    rew <-(transitivity (≤) b x y). tautological.
  Qed.

  Local Instance upward_closure_monotone : OrderPreserving upward_closure.
  Proof. apply alt_Build_OrderPreserving. intros B₁ B₂.
    change ((∏ x, x ∊ B₁ ⊸ x ∊ B₂) ⊸ ∏ w, (∐ b, b ∊ B₁ ⊠ b ≤ w) ⊸ ∐ b, b ∊ B₂ ⊠ b ≤ w).
    rew <-all_adj; intros w. rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj. intros b.
    rew <-(aex_ub _ b). rew (aprod_com _ _), (aprod_assoc _ _ _).
    rew (all_lb _ b). tautological.
  Qed.

  Lemma upset_upward_closed (B : 𝒫 P) : UpSet B ↔ upward_closure B = B.
  Proof. split.
  + intro. apply le_antisym; split; try exact _. intros x.
    change ((∐ b : P, b ∊ B ⊠ b ≤ x) ⊸ x ∊ B). rew <-aex_adj; intros b.
    rew (aprod_com _ _), (aprod_adj _ _ _).
    now apply up_closed.
  + intros E. now rew <-E.
  Qed.

  Lemma upward_closed_idempotent : Idempotent upward_closure.
  Proof. intros B. change (upward_closure (upward_closure B) = upward_closure B).
    rew <-(upset_upward_closed _). apply upward_closure_is_upset.
  Qed.

  Local Instance upward_closure_directed (B : 𝒫 P) `{!DownDirectedSubset B}
    : DownDirectedSubset (upward_closure B).
  Proof. apply Build_DownDirectedSubset; try exact _.
  + rew <-(subset_upward_closure B). apply down_directed_subset_inhabited.
  + intros x y.
    change ((∐ b, b ∊ B ⊠ b ≤ x) ⊠ (∐ b, b ∊ B ⊠ b ≤ y) ⊸
            ∐ z : P, (∐ b, b ∊ B ⊠ b ≤ z) ⊠ z ≤ x ⊠ z ≤ y).
    rew aex_frob_l, <-aex_adj; intros bx.
    rew (aprod_com (∐ b, b ∊ B ⊠ b ≤ x) _), aex_frob_l, <-aex_adj; intros b_x.
    assert (shuffle : ∀ A B C D, (A ⊠ B) ⊠ (C ⊠ D) ⊸ (A ⊠ C) ⊠ (B ⊠ D)) by tautological;
      rew (shuffle _ _ _ _); clear shuffle.
    rew (down_directed_subset (U:=B) bx b_x).
    rew (aprod_com (∐ z, z ∊ B ⊠ z ≤ bx ⊠ z ≤ b_x) _), aex_frob_l, <-aex_adj; intros c.
    rew <-(aex_ub _ c).
    rew <-(aex_ub (λ b : P, b ∊ B ⊠ b ≤ c) c).
    simplify.
    rew <-(transitivity (≤) c bx y), <-(transitivity (≤) c b_x x).
    tautological.
  Qed.

  Lemma upward_closure_filter (B : 𝒫 P) `{!DownDirectedSubset B} : Filter (upward_closure B).
  Proof. now split. Qed.
End upward_closure.

#[global] Hint Extern 2 (apos (?B ⊆ func_op upward_closure ?B)) => simple notypeclasses refine (subset_upward_closure B) : typeclass_instances.
#[global] Hint Extern 2 (UpSet (func_op upward_closure _)) => simple notypeclasses refine (upward_closure_is_upset _) : typeclass_instances.
#[global] Hint Extern 2 (OrderPreserving upward_closure) => simple notypeclasses refine upward_closure_monotone : typeclass_instances.
#[global] Hint Extern 2 (DownDirectedSubset (func_op upward_closure _)) => simple notypeclasses refine (upward_closure_directed _) : typeclass_instances.
#[global] Hint Extern 2 (Filter (func_op upward_closure _)) => simple notypeclasses refine (upward_closure_filter _) : typeclass_instances.
#[global] Hint Extern 2 (Idempotent upward_closure) => simple notypeclasses refine upward_closed_idempotent : typeclass_instances.

Lemma upward_closure_image@{u} {X Y:set@{u}} `{@WeakPoset Y Yle} (f:X ⇾ Y) (U:𝒫 X)
  : upward_closure (f⁎ U) = { y : Y |  ∐ x : X, x ∊ U ⊠ f x ≤ y } .
Proof. intros y. change ((∐ b : Y, b ∊ f⁎ U ⊠ b ≤ y) ⧟ ∐ x : X, x ∊ U ⊠ f x ≤ y). split.
+ rew <-aex_adj; intros b. change (b ∊ f⁎ U) with (∐ x, f x = b ⊠ x ∊ U).
  rew aex_frob_r, <-aex_adj; intros x; rew <-(aex_ub _ x).
  now rew (aprod_com (f x = b) _), (aprod_assoc _ _ _), (eq_le _ _), (transitivity (≤) _ _ _).
+ rew <-aex_adj; intros x. rew <-(aex_ub _ (f x)). now rew <-(image_el _ _ _).
Qed.

(** Downward closure: results follow by duality from upward closure on the opposite order. *)

Section downward_closure.
  Context `{WeakPoset P}.

  Lemma subset_downward_closure : ∀ (B : 𝒫 P), B ⊆ downward_closure B.
  Proof. exact (subset_upward_closure (P:=P ᵒᵖ)). Qed.

  Local Instance downward_closure_is_downset (B : 𝒫 P) : DownSet (downward_closure B)
    := upward_closure_is_upset (P:=P ᵒᵖ) B.

  Local Instance downward_closure_monotone : OrderPreserving downward_closure.
  Proof. exact (upward_closure_monotone (P:=P ᵒᵖ)). Qed.

  Lemma downset_downward_closed (B : 𝒫 P) : DownSet B ↔ downward_closure B = B.
  Proof. exact (upset_upward_closed (P:=P ᵒᵖ) B). Qed.

  Lemma downward_closed_idempotent : Idempotent downward_closure.
  Proof. exact (upward_closed_idempotent (P:=P ᵒᵖ)). Qed.

  Local Instance downward_closure_directed (B : 𝒫 P) `{!UpDirectedSubset B}
    : UpDirectedSubset (downward_closure B)
    := upward_closure_directed (P:=P ᵒᵖ) B.

  Lemma downward_closure_ideal (B : 𝒫 P) `{!UpDirectedSubset B} : Ideal (downward_closure B).
  Proof. exact (upward_closure_filter (P:=P ᵒᵖ) B). Qed.
End downward_closure.

#[global] Hint Extern 2 (apos (?B ⊆ func_op downward_closure ?B)) => simple notypeclasses refine (subset_downward_closure B) : typeclass_instances.
#[global] Hint Extern 2 (DownSet (func_op downward_closure _)) => simple notypeclasses refine (downward_closure_is_downset _) : typeclass_instances.
#[global] Hint Extern 2 (OrderPreserving downward_closure) => simple notypeclasses refine downward_closure_monotone : typeclass_instances.
#[global] Hint Extern 2 (UpDirectedSubset (func_op downward_closure _)) => simple notypeclasses refine (downward_closure_directed _) : typeclass_instances.
#[global] Hint Extern 2 (Ideal (func_op downward_closure _)) => simple notypeclasses refine (downward_closure_ideal _) : typeclass_instances.
#[global] Hint Extern 2 (Idempotent downward_closure) => simple notypeclasses refine downward_closed_idempotent : typeclass_instances.

Lemma downward_closure_image@{u} {X Y:set@{u}} `{@WeakPoset Y Yle} (f:X ⇾ Y) (U:𝒫 X)
  : downward_closure (f⁎ U) = { y : Y |  ∐ x : X, x ∊ U ⊠ y ≤ f x } .
Proof. exact (upward_closure_image (Y:=Y ᵒᵖ) f U). Qed.
 
(** "Point" upward closure. *)

Definition point_upward_closure `{WeakPoset X} (U:𝒫 X) := { x:X | ∐ a:U, subset_pt a ≤ x }.

Lemma point_upward_closure_alt `{WeakPoset X} (U:𝒫 X) : point_upward_closure U = upward_closure (of_course_subset U).
Proof. intros x.
  change ( (∐ a:U, subset_pt a ≤ x) ⧟ ∐ b : X, (∐ x : U, from_subset U x = b) ⊠ b ≤ x ). split.
+ rew <-aex_adj; intros a. rew <-(aex_ub _ (subset_pt a)), <-(aex_ub _ a).
  change (from_subset U a) with (subset_pt a). now simplify.
+ rew <-aex_adj; intros b. rew aex_frob_r, <-aex_adj; intros a.
  change (from_subset U a) with (subset_pt a). rew (eq_le _ _), (transitivity (≤) _ _ _).
  exact (aex_ub _ a).
Qed.

Lemma point_upward_closure_is_fun `{WeakPoset X} : @IsFun (of_course_set (𝒫 X)) (𝒫 X) point_upward_closure.
Proof. intros U V. rew (point_upward_closure_alt _). exact (is_fun (upward_closure ∘ of_course_subset_fun X) _ _). Qed.
#[global] Hint Extern 2 (IsFun point_upward_closure) => simple notypeclasses refine point_upward_closure_is_fun : typeclass_instances.

Canonical Structure point_upward_closure_fun `{WeakPoset X} : _ ⇾ _ := @func_make _ _ _ (point_upward_closure_is_fun (X:=X)).

Lemma point_upward_closure_fun_alt `{WeakPoset X} : point_upward_closure_fun = upward_closure ∘ of_course_subset_fun X.
Proof. intros U. exact (point_upward_closure_alt _). Qed.

Lemma point_upward_closure_order_preserving `{WeakPoset X} : OrderPreserving (point_upward_closure_fun (X:=X)).
Proof. now rew point_upward_closure_fun_alt. Qed.
#[global] Hint Extern 2 (OrderPreserving point_upward_closure_fun) => simple notypeclasses refine point_upward_closure_order_preserving : typeclass_instances.

Lemma point_upward_closure_pt_el `{WeakPoset X} {U:𝒫 X} {a:U} : subset_pt a ∊ point_upward_closure U.
Proof. now exists a. Qed.
#[global] Hint Extern 2 (apos (@subset_pt _ ?U _ ∊ point_upward_closure ?V)) =>
  lazymatch U with V => simple notypeclasses refine point_upward_closure_pt_el end : typeclass_instances.

Lemma point_upward_closure_least_upset `{WeakPoset X} {U:𝒫 X} : LeastUpSet (point_upward_closure U).
Proof. split; try exact _. intros x.
  change ( (∐ a : U, subset_pt a ≤ x) ⧟ (∐ a:point_upward_closure U, subset_pt a ≤ x) ). split.
+ rew <-aex_adj; intros a. exact (aex_ub _ (to_subset (subset_pt a))).
+ rew <-aex_adj; intros [a [b Hb]]; unfold subset_pt.
  rew <-Hb. exact (aex_ub _ b).
Qed.
#[global] Hint Extern 2 (LeastUpSet (point_upward_closure _)) => simple notypeclasses refine point_upward_closure_least_upset : typeclass_instances.
#[global] Hint Extern 2 (UpSet (point_upward_closure _)) => simple notypeclasses refine point_upward_closure_least_upset : typeclass_instances.

Lemma least_upset_point_upward_closed `{WeakPoset X} (U:𝒫 X) : LeastUpSet U ↔ point_upward_closure U = U.
Proof. split.
+ intros ? x. change ( (∐ a:U, subset_pt a ≤ x) ⧟ x ∊ U ). now rew (least_upset U x).
+ intros E. now rew <-E.
Qed.

Lemma point_upward_closure_lub `{WeakPoset X} (U V:𝒫 X) {HV:UpSet V}
  : point_upward_closure U ⊆ V ⧟ of_course_subset U ⊆ V.
Proof. split.
+ now rew (point_upward_closure_alt _), <-(subset_upward_closure _).
+ rew (order_preserving upward_closure (of_course_subset U) V), <-(point_upward_closure_alt _).
  rew (upset_upward_closed _) in HV.
  now rew HV.
Qed.

Lemma LeastUpSet_DownDirectedSubset `{@LeastUpSet X Xle U, !DownDirected U} : DownDirectedSubset U.
Proof. apply Build_DownDirectedSubset.
+ pose proof inhabited U as [x _]. now exists x.
+ intros x y. rew [(least_upset U x)|(least_upset U y)].
  rew <-aex_adj2; intros a b.
  pose proof down_directed a b as [z[Ea Eb]]. rew [<-Ea | <-Eb].
  rew <-(aex_ub _ (subset_pt z)). now simplify.
Qed.

Lemma LeastUpSet_lub `{@LeastUpSet X Xle U} {V:𝒫 X} `{!UpSet V} :
  (∀ (x:U), subset_pt x ∊ V) → (U ⊆ V).
Proof. intros P x. rew (least_upset U x). rew <-aex_adj; intros a. now apply (up_closed_alt V). Qed.

Lemma point_upward_closure_filter `{WeakPoset X} {U:𝒫 X} `{!DownDirected U} : Filter (point_upward_closure U).
Proof. split; try exact _. refine LeastUpSet_DownDirectedSubset.
  simple refine (Build_DownDirected _); try exact _.
+ pose proof inhabited U as [x _]. split; [| easy ]. now exists (subset_pt x).
+ intros [x [a Ea]] [y [b Eb]]. change (∐ z:point_upward_closure U, subset_pt z ≤ x ⊠ subset_pt z ≤ y).
  pose proof down_directed a b as [z Ez].
  change (apos (subset_pt z ≤ subset_pt a ⊠ subset_pt z ≤ subset_pt b)) in Ez. rew Ea, Eb in Ez.
  now exists (to_subset (subset_pt z)).
Qed.
#[global] Hint Extern 2 (Filter (point_upward_closure _)) => simple notypeclasses refine point_upward_closure_filter : typeclass_instances.

Lemma point_upward_closure_range@{u} {A:Type@{u}} {Y:set@{u}} `{@WeakPoset Y Yle} (f:A → Y)
  : point_upward_closure (range f) = { y : Y |  ∐ a : A, f a ≤ y } .
Proof. intros y. change ((∐ b : subset_to_set (range f), subset_pt b ≤ y) ⧟ ∐ a : A, f a ≤ y). split.
+ rew <-aex_adj; intros [b [x Ex]]; unfold subset_pt. rew <-Ex. exact (aex_ub _ x).
+ rew <-aex_adj; intros x. now rew <-(aex_ub _ (to_subset (f x))).
Qed.

(** "Point" downward closure.  Dual of the "point" upward closure on the
    opposite order. *)

Definition point_downward_closure `{WeakPoset X} (U:𝒫 X) := { x:X | ∐ a:U, x ≤ subset_pt a }.

Lemma point_downward_closure_alt `{WeakPoset X} (U:𝒫 X) : point_downward_closure U = downward_closure (of_course_subset U).
Proof. exact (point_upward_closure_alt (X:=X ᵒᵖ) U). Qed.

Lemma point_downward_closure_is_fun `{WeakPoset X} : @IsFun (of_course_set (𝒫 X)) (𝒫 X) point_downward_closure.
Proof. exact (point_upward_closure_is_fun (X:=X ᵒᵖ)). Qed.
#[global] Hint Extern 2 (IsFun point_downward_closure) => simple notypeclasses refine point_downward_closure_is_fun : typeclass_instances.

Canonical Structure point_downward_closure_fun `{WeakPoset X} : _ ⇾ _ := @func_make _ _ _ (point_downward_closure_is_fun (X:=X)).

Lemma point_downward_closure_fun_alt `{WeakPoset X} : point_downward_closure_fun = downward_closure ∘ of_course_subset_fun X.
Proof. intros U. exact (point_downward_closure_alt _). Qed.

Lemma point_downward_closure_order_preserving `{WeakPoset X} : OrderPreserving (point_downward_closure_fun (X:=X)).
Proof. now rew point_downward_closure_fun_alt. Qed.
#[global] Hint Extern 2 (OrderPreserving point_downward_closure_fun) => simple notypeclasses refine point_downward_closure_order_preserving : typeclass_instances.

Lemma point_downward_closure_pt_el `{WeakPoset X} {U:𝒫 X} {a:U} : subset_pt a ∊ point_downward_closure U.
Proof. now exists a. Qed.
#[global] Hint Extern 2 (apos (@subset_pt _ ?U _ ∊ point_downward_closure ?V)) =>
  lazymatch U with V => simple notypeclasses refine point_downward_closure_pt_el end : typeclass_instances.

Lemma point_downward_closure_least_downset `{WeakPoset X} {U:𝒫 X} : LeastDownSet (point_downward_closure U).
Proof. exact (point_upward_closure_least_upset (X:=X ᵒᵖ)). Qed.
#[global] Hint Extern 2 (LeastDownSet (point_downward_closure _)) => simple notypeclasses refine point_downward_closure_least_downset : typeclass_instances.
#[global] Hint Extern 2 (DownSet (point_downward_closure _)) => simple notypeclasses refine point_downward_closure_least_downset : typeclass_instances.

Lemma leastdownset_point_downward_closed `{WeakPoset X} (U:𝒫 X) : LeastDownSet U ↔ point_downward_closure U = U.
Proof. exact (least_upset_point_upward_closed (X:=X ᵒᵖ) U). Qed.

Lemma point_downward_closure_lub `{WeakPoset X} (U V:𝒫 X) {HV:DownSet V}
  : point_downward_closure U ⊆ V ⧟ of_course_subset U ⊆ V.
Proof. exact (point_upward_closure_lub (X:=X ᵒᵖ) U V). Qed.

Lemma LeastDownSet_UpDirectedSubset `{@LeastDownSet X Xle U, !UpDirected U} : UpDirectedSubset U.
Proof. exact (LeastUpSet_DownDirectedSubset (X:=X ᵒᵖ)). Qed.

Lemma point_downward_closure_ideal `{WeakPoset X} {U:𝒫 X} `{!UpDirected U} : Ideal (point_downward_closure U).
Proof. exact (point_upward_closure_filter (X:=X ᵒᵖ)). Qed.
#[global] Hint Extern 2 (Ideal (point_downward_closure _)) => simple notypeclasses refine point_downward_closure_ideal : typeclass_instances.

Lemma point_downward_closure_range@{u} {A:Type@{u}} {Y:set@{u}} `{@WeakPoset Y Yle} (f:A → Y)
  : point_downward_closure (range f) = { y : Y |  ∐ a : A, y ≤ f a } .
Proof. exact (point_upward_closure_range (Y:=Y ᵒᵖ) f). Qed.

