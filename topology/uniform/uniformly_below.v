(** The "uniformly below" relation of pointfree topology (Picado-Pultr):
    [K ◁ S] when [S] is a uniform neighborhood of [K] (interfaces/uniform.v).
    Basic theory: order and lattice structure, interpolation, closure and
    interior, and supporting [thicken] lemmas. *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base.
Require Import easy rewrite replc simplify tactics.misc.

Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Local Open Scope subset_scope.

Import thicken_notation.
Local Ltac unfold_ub := change (func_op (@uniformly_below _ ?Φ) (?K, ?S)) with (∐ U:Φ, U.[K] ⊆ S).

Section uniformly_below.
  Context `{@UniformSpace X Φ}.

  Lemma unif_below_le (K S : 𝒫 X) : K ◁ S ⊸ K ⊆ S.
  Proof. unfold_ub. rew <-aex_adj; intros U.
    rew <-(aprod_true_l (thicken_expanding U K) : (K ⊆ U.[K]) ⊠ (U.[K] ⊆ S) ⧟ (U.[K] ⊆ S)).
    exact (transitivity _ _ _ _).
  Qed.

  Local Instance unif_below_subrel : Subrelation (@uniformly_below X Φ) le.
  Proof. intros [K S]. exact (unif_below_le K S). Qed.

  Lemma unif_below_top (K : 𝒫 X) : K ◁ ⊤.
  Proof. exists top. apply below_top. Qed.

  Lemma unif_below_empty (S : 𝒫 X) : ∅ ◁ S.
  Proof. unfold_ub. exists top. intros y.
    change ((∐ x:X, 𝐅 ⊠ (x, y) ∊ (top : Φ)) ⊸ y ∊ S).
    rew <-aex_adj; intros x. now simplify.
  Qed.

  Lemma thicken_le (U V : Φ) (A B : 𝒫 X) : powerset_pt U ⊆ powerset_pt V ⊠ A ⊆ B ⊸ U.[A] ⊆ V.[B].
  Proof. exact (order_preserving thicken _ _). Qed.

  Lemma thicken_le_r (U : Φ) (A B : 𝒫 X) : A ⊆ B ⊸ U.[A] ⊆ U.[B].
  Proof. rew <-(thicken_le _ _ _ _); now simplify. Qed.

  Lemma unif_below_le_l (K' K S : 𝒫 X) : K' ⊆ K ⊠ K ◁ S ⊸ K' ◁ S.
  Proof. unfold_ub. rew aex_frob_l, <-aex_adj; intros U. rew <-(aex_ub _ U).
    rew (thicken_le_r U K' K).
    exact (transitivity _ _ _ _).
  Qed.

  Lemma unif_below_le_r (K S S' : 𝒫 X) : K ◁ S ⊠ S ⊆ S' ⊸ K ◁ S'.
  Proof. unfold_ub. rew aex_frob_r, <-aex_adj; intros U. rew <-(aex_ub _ U).
    exact (transitivity _ _ _ _).
  Qed.

  Lemma unif_below_trans : Transitive (@uniformly_below X Φ).
  Proof. intros K S T. rew (unif_below_le S T). exact (unif_below_le_r _ _ _). Qed.
  
  Lemma unif_below_proper_aimpl {K K' S S' : 𝒫 X} : K' ⊆ K → S ⊆ S' → K ◁ S ⊸ K' ◁ S' .
  Proof. intros EK ES.
    rew <-(unif_below_le_l K' K S'), (aprod_true_l EK).
    now rew <-(unif_below_le_r K S S'), (aprod_true_r ES).
  Qed.
End uniformly_below.
#[global] Hint Extern 2 (Subrelation (func_op uniformly_below) _) => simple notypeclasses refine unif_below_subrel : typeclass_instances.
#[global] Hint Extern 2 (Transitive (func_op uniformly_below)) => simple notypeclasses refine unif_below_trans : typeclass_instances.
#[global] Hint Extern 2 (apos (aimpl (_ ◁ _, _))) => sapply_2 unif_below_proper_aimpl : proper.

Section uniformly_below.
  Context `{@UniformSpace X Φ}.

  Lemma thicken_join_le (U₁ U₂ : Φ) (K₁ K₂ : 𝒫 X) : (U₁ ⊓ U₂).[K₁ ⊔ K₂] ⊆ U₁.[K₁] ⊔ U₂.[K₂].
  Proof. intros y.
    change ((∐ x, (x ∊ K₁ ∨ x ∊ K₂) ⊠ ((x, y) ∊ U₁ ∧ (x, y) ∊ U₂))
            ⊸ (∐ x, x ∊ K₁ ⊠ (x, y) ∊ U₁) ∨ (∐ x, x ∊ K₂ ⊠ (x, y) ∊ U₂)).
    rew <-aex_adj; intros x. rew <-(aex_ub _ x).
    tautological.
  Qed.

  Lemma unif_below_join (K₁ K₂ S : 𝒫 X) : K₁ ◁ S ⊠ K₂ ◁ S ⊸ K₁ ⊔ K₂ ◁ S.
  Proof. unfold_ub. rew <-aex_adj2; intros U₁ U₂. rew <-(aex_ub _ (U₁ ⊓ U₂)).
    rew (thicken_join_le U₁ U₂ K₁ K₂).
    now rew <-(join_lub _ _ _).
  Qed.

  Lemma unif_below_meet (K S₁ S₂ : 𝒫 X) : K ◁ S₁ ⊠ K ◁ S₂ ⊸ K ◁ S₁ ⊓ S₂.
  Proof. unfold_ub. rew <-aex_adj2; intros U₁ U₂. rew <-(aex_ub _ (U₁ ⊓ U₂)).
    rew <-(meet_glb _ _ _). rew (meet_lb_l _ _) at 1. now rew (meet_lb_r _ _).
  Qed.

  Lemma unif_below_thicken (U : Φ) (K : 𝒫 X) : K ◁ U.[K].
  Proof. now exists U. Qed.

  Lemma unif_below_interpolate (K S : 𝒫 X) : K ◁ S ⊸ ∐ U:Φ, U.[K] ◁ S.
  Proof. change ((∐ V:Φ, V.[K] ⊆ S) ⊸ ∐ U:Φ, ∐ V:Φ, V.[U.[K]] ⊆ S).
    rew <-aex_adj; intros U.
    pose proof uniform_split_alt U as [V PV].
    rew <-(aex_ub _ V), <-(aex_ub _ V).
    now rew (thicken_compose _ _ _), PV.
  Qed.

  Lemma unif_below_closure (K S : 𝒫 X) : K ◁ S ⊸ closure K ◁ S.
  Proof.
    rew (unif_below_interpolate K S), <-aex_adj; intros U.
    now rew (closure_sub_thicken U K).
  Qed.

  Lemma unif_below_int_r (K S : 𝒫 X) : K ◁ S ⊸ K ◁ interior S.
  Proof. unfold_ub. rew <-aex_adj; intros U.
    pose proof uniform_split_alt U as [V PV].
    rew [<-PV | <-(aex_ub _ V)]. rew <-(thicken_compose _ _ _).
    apply thicken_sub_interior.
  Qed.

  Lemma singleton_unif_below (x:X) (S : 𝒫 X) {el : x ∊ interior S} : singleton x ◁ S.
  Proof.
    rew uniform_interior_applied2 in el; destruct el as [U P].
    exists U. intros y.
    change ((∐ x', x = x' ⊠ near U x' y) ⊸ y ∊ S).
    rew <-aex_adj; intros x'.
    rew <-(P y : near U x y ⊸ y ∊ S).
    rew (is_fun set:(λ z, near U z y) x x' : x = x' ⊸ near U x y ⧟ near U x' y).
    tautological.
  Qed.

  Lemma unif_below_sub_interior (K S : 𝒫 X) : K ◁ S ⊸ K ⊆ interior S.
  Proof. rew (unif_below_int_r K S). exact (unif_below_le _ _). Qed.
End uniformly_below.

