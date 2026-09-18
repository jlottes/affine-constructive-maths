Require Import interfaces.set abstract_algebra.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset theory.lattices orders.lattices.
Require Import orders.subset_images.
Require Import topology.base topology.interior topology.maps.
Require Import reflection_pair.base.
Require Import easy rewrite simplify tactics.misc.

Import image_notation.
Local Open Scope op_scope.
Local Open Scope topology_scope.

(** Initial (pullback) topology: the coarsest topology on [X] making [f]
    continuous — [U] is a neighborhood of [x] iff some neighborhood of [f x]
    pulls back into [U].  The Joy-of-Cats initial lift; the topological
    analogue of [uniform/subspace.v]'s [pullback_uniformity]. *)
Definition pullback_neighborhood@{u} {X:set@{u}} `{NY:Neighborhood@{u} Y} (f:X ⇾ Y) : Neighborhood X
  := set:(λ '(x, U) : X ⊗ (𝒫 X), ∐ N:𝒫 Y, f x ⪽ N ⊠ f* N ⊆ U).

Section pullback_topology.
  Universes u.
  Context {X Y:set@{u}} `{@Topology Y NY} {f:X ⇾ Y}.
  Local Abbreviation NX := (@pullback_neighborhood X Y NY f).
  #[local] Hint Extern 0 (Neighborhood X) => exact NX : typeclass_instances.

  Local Ltac unfold_N := change (func_op (nbrhood (X:=X)) (?x, ?U)) with (∐ N:𝒫 Y, f x ⪽ N ⊠ f* N ⊆ U).

  Local Instance pullback_topology : Topology X.
  Proof. apply Build_Topology.
  - intros x U. unfold_N. rew <-aex_adj; intros N. rew (top_refl (f x) N). exact (subset_apply x (f* N) U).
  - intros x U V. unfold_N. rew aex_frob_r, <-aex_adj; intros N. rew <-(aex_ub _ N).
    now rew (aprod_assoc _ _ _), (transitivity _ _ _ _).
  - intros x. unfold_N. rew <-(aex_ub _ (full_subset Y)). split; [ exact _ | exact (below_top _ ) ].
  - intros x U V. unfold_N. rew <-aex_adj2; intros N₁ N₂. rew <-(aex_ub _ (N₁ ⊓ N₂)).
    refine ((tautology : ∀ P₁ Q₁ P₂ Q₂ P Q:Ω, (P₁ ⊠ P₂ ⊸ P) → (Q₁ ⊠ Q₂ ⊸ Q) → (P₁ ⊠ Q₁) ⊠ (P₂ ⊠ Q₂) ⊸ P ⊠ Q) _ _ _ _ _ _ _ _).
    + exact (top_binary_additivity (f x) _ _).
    + rew (preserves_meet_lax f* N₁ N₂).
      exact (order_preserving (⊓) (f* N₁, f* N₂) (U, V)).
  - intros x U. unfold_N. rew <-aex_adj; intros N. rew <-(aex_ub _ {z:Y | z ⪽ N}). apply aprod_proper_aimpl.
    + exact (top_trans (f x) N).
    + change (f* {z:Y | z ⪽ N} ⊆ {y:X | y ⪽ U}) with (∏ y:X, y ∊ f* {z:Y | z ⪽ N} ⊸ y ∊ {y:X | y ⪽ U}).
      rew <-all_adj; intros y. rew <-(aprod_adj _ _ _).
      change (y ∊ f* {z:Y | z ⪽ N}) with (f y ⪽ N).
      change (y ∊ {y0:X | y0 ⪽ U}) with (y ⪽ U). unfold_N.
      rew <-(aex_ub _ N). tautological.
  Qed.

  Local Instance pullback_neighborhood_continuous : Continuous f.
  Proof. split; try exact _. intros x N. unfold_N.
    rew <-(aex_ub _ N). now simplify.
  Qed.

  Local Instance pullback_neighborhood_initial : ContinuouslyInitial f.
  Proof. split; try exact _. split; try exact _. now intros x N. Qed.
End pullback_topology.
#[global] Hint Extern 2 (@Topology _ (pullback_neighborhood _)) => simple notypeclasses refine pullback_topology : typeclass_instances.

#[global] Hint Extern 0 (Cleavage 𝐀𝐓𝐨𝐩) => exact @pullback_neighborhood : typeclass_instances.

Lemma atop_cloven : ClovenPair 𝐀𝐓𝐨𝐩.
Proof. esplit. intros X Y f NY HY. exact pullback_neighborhood_initial. Qed.
#[global] Hint Extern 0 (ClovenPair 𝐀𝐓𝐨𝐩) => exact atop_cloven : typeclass_instances.
#[global] Hint Extern 0 (SaturatedPair 𝐀𝐓𝐨𝐩) => exact atop_cloven : typeclass_instances.



(** [ContinuouslyInitial] is the Joy-of-Cats (AHS) initial morphism for the
    forgetful functor to [Set], with the initial (pullback) topology as test
    object. *)
Lemma continuously_initial_alt@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY} (f:X ⇾ Y)
  : ContinuouslyInitial f ↔
    (∀ (Z:set@{u}) (NZ:Neighborhood Z), Topology Z → ∀ (g:Z ⇾ X),
       Continuous (f ∘ g) ↔ Continuous g).
Proof. exact (ini_lift_alt (C:=𝐀𝐓𝐨𝐩) f). Qed.

Lemma continuously_initial_alt2@{u} `{Hf:@Continuous@{u} X Y NX NY f}
  : ContinuouslyInitial f ↔
    (∀ (Z:set@{u}) (NZ:Neighborhood Z), Topology Z → ∀ (g:Z ⇾ X),
       Continuous (f ∘ g) → Continuous g).
Proof. exact (ini_lift_alt2 (C:=𝐀𝐓𝐨𝐩) f). Qed.

