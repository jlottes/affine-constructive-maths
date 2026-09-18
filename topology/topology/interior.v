Require Import interfaces.set abstract_algebra.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology.
Require Import theory.set orders.orders orders.maps orders.subset.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices.
Require Import easy rewrite simplify.

Local Open Scope topology_scope.

Import set.of_course_set_notation.
Canonical Structure open_fun X {XN:Neighborhood X} := @func_make !(𝒫 X) Ω open set:(λ U : !(𝒫 X), interior U = U) .
Canonical Structure closed_fun X {XN:Neighborhood X} := @func_make !(𝒫 X) Ω closed set:(λ U : !(𝒫 X), closure U = U) .

Import image_notation.

Section interior.
  Context `{XN:Neighborhood X}.
  Local Abbreviation int := (@interior X XN).

  Context `{!Topology X}.

  Definition interior_subset U : int U ⊆ U
    := λ x, top_refl x U.

  Lemma interior_order_preserving : OrderPreserving int.
  Proof. apply alt_Build_OrderPreserving. intros U V.
    change (U ⊆ V ⊸ ∏ x : X, x ⪽ U ⊸ x ⪽ V).
    rew <-all_adj; intros x. rew <-(aprod_adj _ _ _).
    rew (aprod_com _ _). exact (top_isotony x U V).
  Qed.

  Lemma interior_space : int (full_subset X) = full_subset X.
  Proof. intros x. change (x ⪽ full_subset X ⧟ 𝐓). simplify.
    exact (top_nullary_additivity x).
  Qed.
  
  Lemma interior_empty : int ∅ = ∅.
  Proof. rew <-(below_bottom _). exact (interior_subset _). Qed.

  Local Open Scope subset_scope.
  Lemma interior_intersection U V : int U ⨶ int V ⊆ int (U ⊓ V).
  Proof. intros x.
    change ((∐ y, x = y ⊠ (y ⪽ U ⊠ y ⪽ V)) ⊸ x ⪽ U ⊓ V). rew <-aex_adj; intros y.
    rew (top_binary_additivity y U V), (aprod_adj _ _ _).
    rew <-(aandr _ _ : (_ ⧟ _) ⊸ (y ⪽ U ⊓ V ⊸ x ⪽ U ⊓ V)).
    exact (is_fun (ap2 nbrhood (U ⊓ V)) _ _).
  Qed.

  Local Instance interior_idempotent : Idempotent int.
  Proof. intros U; change (int (int U) = int U). apply le_antisym; split.
  + exact (interior_subset _).
  + intros x. exact (top_trans x U).
  Qed.

  Definition interior_separation_T₀ `{!Separation_T₀ X} : ∀ x y : X, (∏ U, x ∊ int U ⧟ y ∊ int U) ⊸ x = y
    := separation_T₀.

  Definition interior_open U : open (int U) := idempotent int U.
  
  Lemma open_nbrhood (x:X) (U:𝒫 X) : x ∊ U ⊠ open U ⊸ x ⪽ U.
  Proof. change (x ∊ U ⊠ interior U = U ⊸ x ⪽ U).
    rew (is_fun set:(λ V, x ∊ V) (interior U) U : _ ⊸ x ⪽ U ⧟ x ∊ U).
    full_tautological.
  Qed.
End interior.
#[global] Hint Extern 2 (OrderPreserving interior) => simple notypeclasses refine interior_order_preserving : typeclass_instances.
#[global] Hint Extern 2 (Idempotent interior) => simple notypeclasses refine interior_idempotent : typeclass_instances.
#[global] Hint Extern 2 (apos (open (func_op interior _))) => simple notypeclasses refine (interior_open _) : typeclass_instances.
#[global] Hint Extern 4 (apos (func_op interior ?M ≤ ?N)) => match M with N => simple notypeclasses refine (interior_subset _) end : typeclass_instances.

Section closure.
  Context `{XN:Neighborhood X}.
  Local Abbreviation int := (@interior X XN).
  Local Abbreviation cl := (@closure X XN).
  Local Open Scope subset_scope.

  Context `{!Topology X}.

  Definition subset_closure U : U ⊆ cl U.
  Proof. rew <-(order_reflecting_flip complement _ _).
    change ((int (U ᗮ) ) ᗮ ᗮ ⊆ U ᗮ).
    rew (involutive_alt complement _).
    exact (interior_subset _).
  Qed.

  Lemma closure_order_preserving : OrderPreserving cl.
  Proof. now unfold cl. Qed.

  Lemma closure_empty : cl ∅ = ∅.
  Proof. change ((int (full_subset X) ) ᗮ = (full_subset X) ᗮ). now rew interior_space. Qed.

  Lemma closure_space : cl ⌈X⌉ = ⌈X⌉.
  Proof. apply (above_top _). exact (subset_closure _). Qed.

  Lemma closure_union U V : cl (U ⊔ V) ⊆ mult_union (cl U, cl V).
  Proof. rew <-(order_reflecting_flip complement _ _).
    change (cl ?U) with ( (int (U ᗮ) ) ᗮ ).
    rew (involutive_alt complement _).
    rew (preserves_join_flip complement U V).
    rew <-(interior_intersection _ _).
    set (A := int U ᗮ). set (B := int V ᗮ).
    clearbody A B. clear U V. full_tautological.
  Qed.

  Lemma closure_idempotent : Idempotent cl.
  Proof. change (complement ∘ int ∘ (complement ∘ complement) ∘ int ∘ complement = cl).
    rew (involutive complement). change (complement ∘ (int ∘ int) ∘ complement = cl).
    now rew (idempotent int).
  Qed.

  Definition closure_closed U : closed (cl U) := closure_idempotent U.

  Lemma open_complement_closed (U:𝒫 X) : open (U ᗮ) ⧟ closed U.
  Proof. exact (injective_iff complement _ _). Qed.

  Lemma closed_complement_open (U:𝒫 X) : closed (U ᗮ) ⧟ open U.
  Proof. exact (injective_iff complement _ _). Qed.
End closure.
#[global] Hint Extern 2 (OrderPreserving closure) => simple notypeclasses refine closure_order_preserving : typeclass_instances.
#[global] Hint Extern 2 (Idempotent closure) => simple notypeclasses refine closure_idempotent : typeclass_instances.
#[global] Hint Extern 2 (apos (closed (func_op closure _))) => simple notypeclasses refine (closure_closed _) : typeclass_instances.
#[global] Hint Extern 4 (apos (?N ≤ func_op closure ?M)) => match M with N => simple notypeclasses refine (subset_closure _) end : typeclass_instances.

Local Open Scope subset_scope.

Lemma in_closure `{@Topology X XN} (U : 𝒫 X) (x : X)
  : (∏ N, x ⪽ N ⊸ ∐ z, z ∊ N ⊠ z ∊ U) ⊸ x ∊ closure U.
Proof. apply by_contrapositive.
  change (x ⪽ U ᗮ ⊸ ∐ N, x ⪽ N ⊠ ∏ z, z ∊ N ⊸ z ∊ U ᗮ).
  rew <-(aex_ub _ (U ᗮ)). now simplify.
Qed.

Lemma closure_meets `{@Topology X XN} (U V : 𝒫 X) (x : X)
  : x ∊ closure U ⊠ x ⪽ V ⊸ ∐ z, z ∊ V ⊠ z ∊ U.
Proof. apply by_contrapositive.
  change (V ⊆ U ᗮ ⊸ x ⪽ U ᗮ ⊞ anot (x ⪽ V) ).
  rew (apar_com _ _).
  change (V ⊆ U ᗮ ⊸ x ⪽ V ⊸ x ⪽ U ᗮ ).
  rew <-(top_isotony x V (U ᗮ)). tautological.
Qed.

Lemma in_closure_meets `{@Topology X XN} (U : 𝒫 X) (x : X)
  : x ∊ closure U ⧟ (∏ N, x ⪽ N ⊸ ∐ z, z ∊ N ⊠ z ∊ U).
Proof. split.
+ rew <-all_adj. intros V. rew <-(aprod_adj _ _ _). exact (closure_meets _ _ _).
+ exact (in_closure _ _).
Qed.

Lemma dense_meets `{@Topology X XN} (U V : 𝒫 X) (x : X) :
  dense U → x ⪽ V ⊸ ∐ z, z ∊ V ⊠ z ∊ U.
Proof. intros HU. rew <-(closure_meets U V x). now rew HU, (aprod_true_l (_ : x ∊ ⊤)). Qed.

Lemma dense_order_preserving `{@Topology X NX} : OrderPreserving (dense (X:=X)).
Proof. apply alt_Build_OrderPreserving. intros U V.
  change (U ⊆ V ⊸ (closure U = ⊤ ⊸ closure V = ⊤)).
  rew (order_preserving closure U V).
  rew <-(above_top _). rew <-(aprod_adj _ _ _), (aprod_com _ _).
  now apply transitivity.
Qed.
#[global] Hint Extern 2 (OrderPreserving dense) => simple notypeclasses refine dense_order_preserving : typeclass_instances.

