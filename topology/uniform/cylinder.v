(** Cylinder algebra over uniform spaces: projection-preimage subsets
    ("cylinders" [π₁* K ⊓ W]), their interaction with thickening and
    relational composition, and the dense-descent core
    ([uniform_dense_thicken] composed with [preimage_cylinder_thicken]) that
    the WCUnif dense-descent theorems ([unif_born/local_maps.v]) and the
    localization's reflecting UP ([unif_born/localization.v]) reduce to
    after their entry moves.  The subset-level projection/tensor algebra
    ([proj1_preimage_tensor_top], [compose_proj1_preimage]) is in
    [orders/subset_images.v]. *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology uniform.base uniform.product.
Require Import easy rewrite simplify tactics.misc.

Import image_notation.
Import tensor_map_notation.
Import thicken_notation.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope grp_scope.
Local Open Scope sg_op_scope.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Abbreviation π₁ := (tensor_proj1 _ _).
Local Abbreviation π₂ := (tensor_proj2 _ _).
Local Abbreviation int := interior.
Local Abbreviation cl := closure.

Lemma ufm_proj2_image_entourage `{@UniformSpace X Φ} (U:Φ) : π₂⁎ U = ⊤.
Proof. intros x. change ( (∐ p, π₂ p = x ⊠ p ∊ U) ⧟ 𝐓 ). simplify.
  exists (x, x). simplify. apply near_refl.
Qed.

Lemma proj1_preimage_thicken@{u} `{@UniformSpace@{u} X Φ} {Y:set@{u}} (K:𝒫 X) (U:Φ) :
   π₁* U.[K] = powerset_pt U⁻¹ ⋄ π₁* K :> 𝒫 (X ⊗ Y).
Proof. intros [x y].
  change ((∐ z, z ∊ K ⊠ (z, x) ∊ U)  ⧟ ∐ z, (z, x) ∊ U ⊠ z ∊ K).
  apply aex_proper_aiff. intros z. now rew (aprod_com _ _).
Qed.

Lemma ufm_compose_proj1_preimage@{u} {X:set@{u}} `{@UniformSpace@{u} Y Ψ} (A:𝒫 X) (V:Ψ) :
   (π₁* A) ⋄ V = π₁* A.
Proof. rew (compose_proj1_preimage _ _), (ufm_proj2_image_entourage _).
  now rew (proj1_preimage_tensor_top _).
Qed.

#[local] Hint Extern 0 (Neighborhood _) => exact UniformNeighborhood : typeclass_instances.

Lemma cylinder_thicken `{@UniformSpace X Φ} (K : 𝒫 X) (U V W : Φ)
  (EW : W⁻¹ = W) (HW : W ∙ W ∙ W ≤ U ⊓ V)
  : powerset_pt W ∙ (π₁* K ⊓ powerset_pt W) ∙ powerset_pt W ⊆ π₁* U.[K] ⊓ powerset_pt V.
Proof. apply meet_glb; split.
+ rew (meet_lb_l (π₁* K) W).
  rew <-(proj1_preimage_thicken (Y:=X) K W⁻¹).
  rew (ufm_compose_proj1_preimage (W⁻¹).[K] W).
  rew [ EW | <-(meet_lb_l U V) ].
  rew <-HW. now do 2 rew <-(ufm_compose_ub_l _ _).
+ now rew [(meet_lb_r (π₁* K) W)| <-(meet_lb_r U V)].
Qed.

Lemma cylinder_sub_interior@{u} `{@UniformSpace@{u} X Φ} `{!TensorProductUniformity Φ Φ Φ₂}
  (K:𝒫 X) (U V:Φ) : ∐ (W:Φ), π₁* K ⊓ powerset_pt W ⊆ int (π₁* U.[K] ⊓ powerset_pt V).
Proof.
  pose proof uniform_split_sym3 (U ⊓ V) as [W[EW HW]]. exists W.
  rew <-(sub_interior_thicken _ _ W W).
  exact (cylinder_thicken K U V W EW HW).
Qed. 

