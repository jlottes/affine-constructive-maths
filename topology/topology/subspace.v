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
    continuous.  [U] is a neighborhood of [x] iff [∀.[f] U] is a
    neighborhood of [f x], equivalently iff some neighborhood of [f x]
    pulls back into [U] ([pullback_neighborhood_ex]).  With this form
    continuous reflection of [f] is definitional.  The Joy-of-Cats initial
    lift; the topological analogue of [uniform/subspace.v]'s
    [pullback_uniformity]. *)
Definition pullback_neighborhood@{u} {X:set@{u}} `{NY:Neighborhood@{u} Y} (f:X ⇾ Y) : Neighborhood X
  := set:(λ '(x, U) : X ⊗ (𝒫 X), f x ⪽ ∀.[f] U).

Section pullback_topology.
  Universes u.
  Context {X Y:set@{u}} `{@Topology Y NY} {f:X ⇾ Y}.
  Local Abbreviation NX := (@pullback_neighborhood X Y NY f).
  #[local] Hint Extern 0 (Neighborhood X) => exact NX : typeclass_instances.

  Local Ltac unfold_N := change (func_op (nbrhood (X:=X)) (?x, ?U)) with (f x ⪽ ∀.[f] U).

  Local Instance pullback_topology : Topology X.
  Proof. apply Build_Topology.
  - intros x U. unfold_N. rew (top_refl (f x) _). exact (universal_image_counit f U x).
  - intros x U V. unfold_N. rew (order_preserving ∀.[f] U V). exact (top_isotony _ _ _).
  - intros x. unfold_N. rew (preserves_top ∀.[f]). exact (top_nullary_additivity _).
  - intros x U V. unfold_N. rew (preserves_meet ∀.[f] U V). exact (top_binary_additivity _ _ _).
  - intros x U. unfold_N.
    change (f x ⪽ ∀.[f] U ⊸ f x ⪽ ∀.[f] (f* {y:Y | y ⪽ ∀.[f] U})).
    rew <-(universal_image_unit f _). exact (top_trans _ _).
  Qed.

  Local Instance pullback_neighborhood_continuous : Continuous f.
  Proof. split; try exact _. intros x N. unfold_N.
    now rew <-(universal_image_unit f N).
  Qed.

  Local Instance pullback_neighborhood_initial : ContinuouslyInitial f.
  Proof. split; try exact _. split; try exact _. now intros x U. Qed.

  Lemma pullback_neighborhood_ex x U : x ⪽ U ⧟ ∐ N:𝒫 Y, f x ⪽ N ⊠ f* N ⊆ U.
  Proof. split.
  + unfold_N. now rew <-(aex_ub _ (∀.[f] U)), (aprod_true_r (universal_image_counit f U)).
  + unfold_N. rew <-aex_adj; intros N. rew (preimage_universal_image_adj f U N). exact (top_isotony _ _ _).
  Qed.
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

