(** Theory of the well-containment relation [K ⋐ S] (interfaces/unif_born.v):
    bounded ([K ∊ 𝒜]) and uniformly below ([K ◁ S]), additively conjoined.
    Mirrors uniform/uniformly_below.v; the WCUnif thickening axiom upgrades
    interpolation and closure to keep the interpolant bounded. *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base topology.uniform.uniformly_below.
Require Import bornology.base.
Require Import easy rewrite replc simplify tactics.misc.

Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Local Open Scope subset_scope.

Import thicken_notation.

Section well_contained.
  Context `{@UnifBornSpace X Φ 𝒜}.

  Lemma wc_le_l (K' K : 𝒜) (S : 𝒫 X) : K' ≤ K ⊠ K ⋐ S ⊸ K' ⋐ S.
  Proof. exact (unif_below_le_l _ _ _). Qed.

  Lemma wc_le_r (K:𝒜) (S S' : 𝒫 X) : K ⋐ S ⊠ S ⊆ S' ⊸ K ⋐ S'.
  Proof. exact (unif_below_le_r _ _ _). Qed.

  Lemma wc_proper_aimpl {K K':𝒜} {S S' : 𝒫 X} : K' ≤ K → S ⊆ S' → K ⋐ S ⊸ K' ⋐ S'.
  Proof. exact unif_below_proper_aimpl. Qed.
End well_contained.
#[global] Hint Extern 1 (apos (aimpl (_ ⋐ _, _))) => sapply_2 wc_proper_aimpl : proper.

Section well_contained.
  Context `{@UnifBornSpace X Φ 𝒜}.

  Lemma wc_join (K₁ K₂:𝒜) (S : 𝒫 X) : K₁ ⋐ S ⊠ K₂ ⋐ S ⊸ K₁ ⊔ K₂ ⋐ S.
  Proof. exact (unif_below_join _ _ _). Qed.

  Lemma wc_meet (K:𝒜) (S₁ S₂ : 𝒫 X) : K ⋐ S₁ ⊠ K ⋐ S₂ ⊸ K ⋐ S₁ ⊓ S₂.
  Proof. exact (unif_below_meet _ _ _). Qed.

  Lemma wc_empty (S : 𝒫 X) : ⊥ ⋐ S.
  Proof. exact (unif_below_empty S). Qed.

  Lemma wc_top (K : 𝒜) : K ⋐ ⊤.
  Proof. exact (unif_below_top K). Qed.

  Lemma wc_int_r (K:𝒜) (S : 𝒫 X) : K ⋐ S ⊸ K ⋐ interior S.
  Proof. exact (unif_below_int_r _ _). Qed.

  Lemma wc_sub_interior (K:𝒜) (S : 𝒫 X) : K ⋐ S ⊸ K ⊆ interior S.
  Proof. exact (unif_below_sub_interior _ _). Qed.

  Lemma wc_trans (K S:𝒜) (T : 𝒫 X) : K ⋐ powerset_pt S ⊠ S ⋐ T ⊸ K ⋐ T.
  Proof. exact (transitivity uniformly_below _ _ _). Qed.
End well_contained.

(** With the WCUnif thickening axiom, interpolation and closure keep the
    bounded leg: the interpolant [U.[K]] is again well-contained. *)
Section wcunif.
  Context `{@WCUnifSpace X Φ 𝒜}.

  Lemma wc_interpolate (K:𝒜) (S : 𝒫 X) : K ⋐ S ⊸ ∐ K', K ⋐ powerset_pt K' ⊠ K' ⋐ S.
  Proof. change (?a ⋐ ?b) with (powerset_pt a ◁ b).
    rew (unif_below_interpolate K S).
    rew <-aex_adj; intros U.
    pose proof wcunif_thicken X K as [V HV].
    assert ((U ⊓ V).[powerset_pt K] ∊ 𝒜) by now rew (meet_lb_r _ _).
    rew <-(meet_lb_l U V).
    pose (K' := (to_subset (U ⊓ V).[powerset_pt K])).
    rew <-(aex_ub _ K').
    change ((U ⊓ V).[powerset_pt K] ◁ S ⊸ powerset_pt K ◁  (U ⊓ V).[powerset_pt K] ⊠ (U ⊓ V).[powerset_pt K] ◁ S).
    now rew (aprod_true_l (unif_below_thicken _ K)).
  Qed.

  Local Instance wcunif_closure_bounded (K:𝒜) : closure K ∊ 𝒜.
  Proof. pose proof (wcunif_thicken X K) as [U HU].
    now rew (closure_sub_thicken U K).
  Qed.
  
  Definition born_closure (K:𝒜) : 𝒜 := to_subset (closure K).

  Lemma wc_closure (K:𝒜) (S : 𝒫 X) : K ⋐ S ⊸ born_closure K ⋐ S.
  Proof. exact (unif_below_closure K S). Qed.
End wcunif.

