Require Import abstract_algebra theory.groups theory.lattices theory.common_props.
Require Import interfaces.orders orders.orders orders.lattices orders.maps orders.suborders.
Require Import set_lambda sprop srelations logic.aprop logic.relations.
Require Export orders.subset.
Require Import tactics.misc easy rewrite simplify.

Local Open Scope subset_scope.

(** Relation composition *)

Lemma compose_rel_assoc@{u} {X Y Z W:set@{u}} (R:𝒫 (X ⊗ Y)) (S:𝒫 (Y ⊗ Z)) (T:𝒫 (Z ⊗ W))
  : R ⋄ (S ⋄ T) = (R ⋄ S) ⋄ T.
Proof. intros [x w]. change ((∐ y, (x, y) ∊ R ⊠ ∐ z, (y, z) ∊ S ⊠ (z, w) ∊ T) ⧟ (∐ z, (∐ y, (x, y) ∊ R ⊠ (y, z) ∊ S) ⊠ (z, w) ∊ T) ). split.
+ rew <-aex_adj; intros y. rew aex_frob_l, <-aex_adj; intros z.
  rew <-(aex_ub _ z), <-(aex_ub _ y).
  apply aprod_assoc.
+ rew <-aex_adj; intros z. rew aex_frob_r, <-aex_adj; intros y.
  rew <-(aex_ub _ y), <-(aex_ub _ z).
  apply aprod_assoc.
Qed.

Lemma compose_rel_assoc_alt {X:set} : Associative (X:=𝒫 (X ⊗ X)) (⋄).
Proof. exact compose_rel_assoc. Qed.
#[global] Hint Extern 2 (Associative (⋄)) => simple notypeclasses refine compose_rel_assoc_alt : typeclass_instances.


Lemma rel_compose@{u} {X Y Z:set@{u}} (R:𝒫 (X ⊗ Y)) (S:𝒫 (Y ⊗ Z))
  x y z : (x, y) ∊ R ⊠ (y, z) ∊ S ⊸ (x, z) ∊ R ⋄ S .
Proof. exact (aex_ub _ y). Qed.

Lemma rel_compose3@{u} {X Y Z W:set@{u}} (R:𝒫 (X ⊗ Y)) (S:𝒫 (Y ⊗ Z)) (T:𝒫 (Z ⊗ W))
  a b c d : (a, b) ∊ R ⊠ (b, c) ∊ S ⊠ (c, d) ∊ T ⊸ (a, d) ∊ R ⋄ S ⋄ T.
Proof. rew <-(aprod_assoc _ _ _), (rel_compose _ _ _ _ _). exact (rel_compose (R ⋄ S) T a c d). Qed.

Lemma rel_compose4@{u} {X Y Z W V:set@{u}} (R:𝒫 (X ⊗ Y)) (S:𝒫 (Y ⊗ Z)) (T:𝒫 (Z ⊗ W)) (U:𝒫 (W ⊗ V))
  a b c d e : (a, b) ∊ R ⊠ (b, c) ∊ S ⊠ (c, d) ∊ T ⊠ (d, e) ∊ U ⊸ (a, e) ∊ R ⋄ S ⋄ T ⋄ U.
Proof. rew (rel_compose3 _ _ _ _ _ _ _), (rel_compose _ _ _ _ _).
  now do 2 rew (compose_rel_assoc _ _ _).
Qed.

Lemma compose_rel_join_distr_l@{u} {X Y Z:set@{u}} (R:𝒫 (X ⊗ Y)) (S T:𝒫 (Y ⊗ Z))
  : R ⋄ (S ⊔ T) = (R ⋄ S) ⊔ (R ⋄ T).
Proof.
  intros [x z]. change ( (∐ y, (x, y) ∊ R ⊠ ((y, z) ∊ S ∨ (y, z) ∊ T)) ⧟ ( (∐ y, (x, y) ∊ R ⊠ (y, z) ∊ S) ∨ (∐ y, (x, y) ∊ R ⊠ (y, z) ∊ T) )).
  split.
+ rew <-aex_adj; intros y. rew <-(aex_ub _ y). tautological.
+ apply aor_elim; rew <-aex_adj; intros y; rew <-(aex_ub _ y); tautological.
Qed.

Lemma compose_rel_join_distr_l_alt {X:set} : LeftDistribute (X:=𝒫 (X ⊗ X)) (⋄) (⊔).
Proof. exact compose_rel_join_distr_l. Qed.
#[global] Hint Extern 2 (LeftDistribute (⋄) (⊔)) => simple notypeclasses refine compose_rel_join_distr_l_alt : typeclass_instances.
#[global] Hint Extern 2 (LeftDistribute (@sg_op _ (⋄)) (⊔)) => simple notypeclasses refine compose_rel_join_distr_l_alt : typeclass_instances.

Lemma compose_rel_join_distr_r@{u} {X Y Z:set@{u}} (R S:𝒫 (X ⊗ Y)) (T:𝒫 (Y ⊗ Z))
  : (R ⊔ S) ⋄ T = (R ⋄ T) ⊔ (S ⋄ T).
Proof.
  intros [x z]. change ( (∐ y, ((x, y) ∊ R ∨ (x, y) ∊ S) ⊠ (y, z) ∊ T) ⧟ ( (∐ y, (x, y) ∊ R ⊠ (y, z) ∊ T) ∨ (∐ y, (x, y) ∊ S ⊠ (y, z) ∊ T) )).
  split.
+ rew <-aex_adj; intros y. rew <-(aex_ub _ y). tautological.
+ apply aor_elim; rew <-aex_adj; intros y; rew <-(aex_ub _ y); tautological.
Qed.

Lemma compose_rel_join_distr_r_alt {X:set} : RightDistribute (X:=𝒫 (X ⊗ X)) (⋄) (⊔).
Proof. exact compose_rel_join_distr_r. Qed.
#[global] Hint Extern 2 (RightDistribute (⋄) (⊔)) => simple notypeclasses refine compose_rel_join_distr_r_alt : typeclass_instances.
#[global] Hint Extern 2 (RightDistribute (@sg_op _ (⋄)) (⊔)) => simple notypeclasses refine compose_rel_join_distr_r_alt : typeclass_instances.

Lemma compose_rel_join_sl_mor_l@{u} {X Y Z:set@{u}} (R:𝒫 (X ⊗ Y))
  : BoundedJoinSemiLattice_Morphism (ap1 (@compose_rel X Y Z) R).
Proof. apply alt_Build_BoundedJoinSemiLattice_Morphism.
+ exact (compose_rel_join_distr_l R).
+ full_tautological.
Qed.

Lemma compose_rel_join_sl_mor_r@{u} {X Y Z:set@{u}} (R:𝒫 (Y ⊗ Z))
  : BoundedJoinSemiLattice_Morphism (ap2 (@compose_rel X Y Z) R).
Proof. apply alt_Build_BoundedJoinSemiLattice_Morphism.
+ intros S T. exact (compose_rel_join_distr_r _ _ _).
+ full_tautological.
Qed.

#[global] Hint Extern 2 (BoundedJoinSemiLattice_Morphism (func_op2 ap1 (⋄) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_l _) : typeclass_instances.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (func_op2 ap1 (⋄) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_l _) : typeclass_instances.
#[global] Hint Extern 2 (Bottom_Pointed_Morphism (func_op2 ap1 (⋄) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_l _) : typeclass_instances.
#[global] Hint Extern 2 (BoundedJoinSemiLattice_Morphism (func_op2 ap2 (⋄) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_r _) : typeclass_instances.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (func_op2 ap2 (⋄) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_r _) : typeclass_instances.
#[global] Hint Extern 2 (Bottom_Pointed_Morphism (func_op2 ap2 (⋄) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_r _) : typeclass_instances.

#[global] Hint Extern 2 (BoundedJoinSemiLattice_Morphism (func_op2 ap1 (@sg_op _ (⋄)) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_l _) : typeclass_instances.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (func_op2 ap1 (@sg_op _ (⋄)) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_l _) : typeclass_instances.
#[global] Hint Extern 2 (Bottom_Pointed_Morphism (func_op2 ap1 (@sg_op _ (⋄)) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_l _) : typeclass_instances.
#[global] Hint Extern 2 (BoundedJoinSemiLattice_Morphism (func_op2 ap2 (@sg_op _ (⋄)) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_r _) : typeclass_instances.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (func_op2 ap2 (@sg_op _ (⋄)) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_r _) : typeclass_instances.
#[global] Hint Extern 2 (Bottom_Pointed_Morphism (func_op2 ap2 (@sg_op _ (⋄)) _)) => simple notypeclasses refine (compose_rel_join_sl_mor_r _) : typeclass_instances.

Lemma compose_rel_order_preserving@{u} {X Y Z:set@{u}} : OrderPreserving (@compose_rel X Y Z).
Proof. apply alt_Build_OrderPreserving. intros [R₁ S₁][R₂ S₂]; unfold_pair_le.
  enough ((R₁ ⊆ R₂ ⊸ R₁ ⋄ S₁ ⊆ R₂ ⋄ S₁) ∧ (S₁ ⊆ S₂ ⊸ R₂ ⋄ S₁ ⊆ R₂ ⋄ S₂)) as [ER ES]
    by (rew [ER|ES]; now apply transitivity); split.
+ refine (order_preserving (ap2 (⋄) S₁) _ _). now apply join_sl_mor_preserving.
+ refine (order_preserving (ap1 (⋄) R₂) _ _). now apply join_sl_mor_preserving.
Qed.
#[global] Hint Extern 2 (OrderPreserving (⋄)) => simple notypeclasses refine compose_rel_order_preserving : typeclass_instances.
#[global] Hint Extern 2 (OrderPreserving (@sg_op _ (⋄))) => simple notypeclasses refine compose_rel_order_preserving : typeclass_instances.



Lemma compose_rel_meet_lax_distr_l@{u} {X Y Z:set@{u}} (R:𝒫 (X ⊗ Y)) (S T:𝒫 (Y ⊗ Z))
  : R ⋄ (S ⊓ T) ⊆ (R ⋄ S) ⊓ (R ⋄ T).
Proof.
  apply meet_glb; split.
  * now rew (meet_lb_l _ _).
  * now rew (meet_lb_r _ _).
Qed.

Lemma compose_rel_meet_lax_distr_r@{u} {X Y Z:set@{u}} (R S:𝒫 (X ⊗ Y)) (T:𝒫 (Y ⊗ Z))
  : (R ⊓ S) ⋄ T ⊆ (R ⋄ T) ⊓ (S ⋄ T).
Proof.
  apply meet_glb; split.
  * now rew (meet_lb_l _ _).
  * now rew (meet_lb_r _ _).
Qed.

Lemma compose_rel_left_id@{u} {X Y:set@{u}} : LeftIdentity (@compose_rel X X Y) (id_rel _).
Proof. intros R [x y]. change ( (∐ x', x = x' ⊠ (x', y) ∊ R) ⧟ (x, y) ∊ R). split.
+ rew <-aex_adj; intros x'. rew (aprod_adj _ _ _).
  rew (is_fun { x:X | (x, y) ∊ R } x x'); full_tautological.
+ rew <-(aex_ub _ x). now simplify.
Qed.
#[global] Hint Extern 2 (LeftIdentity (⋄) _) => simple notypeclasses refine compose_rel_left_id : typeclass_instances.

Lemma compose_rel_right_id@{u} {X Y:set@{u}} : RightIdentity (@compose_rel X Y Y) (id_rel _).
Proof. intros R [x y]. change ( (∐ y', (x, y') ∊ R ⊠ y' = y) ⧟ (x, y) ∊ R). split.
+ rew <-aex_adj; intros y'. rew (aprod_com _ _), (aprod_adj _ _ _).
  rew (is_fun { y:Y | (x, y) ∊ R } y' y); full_tautological.
+ rew <-(aex_ub _ y). now simplify.
Qed.
#[global] Hint Extern 2 (RightIdentity (⋄) _) => simple notypeclasses refine compose_rel_right_id : typeclass_instances.

Lemma compose_rel_left_absorb@{u} {X Y Z:set@{u}} (R:𝒫 (Y ⊗ Z)) : ∅ ⋄ R = ∅ :> 𝒫 (X ⊗ Z) .
Proof. intros [x z]. change ( (∐ y, 𝐅 ⊠ (y,z) ∊ R) ⧟ 𝐅 ). now simplify. Qed.

Lemma compose_rel_right_absorb@{u} {X Y Z:set@{u}} (R:𝒫 (X ⊗ Y)) : R ⋄ ∅ = ∅ :> 𝒫 (X ⊗ Z) .
Proof. intros [x z]. change ( (∐ y, (x,y) ∊ R ⊠ 𝐅) ⧟ 𝐅 ). now simplify. Qed.

Local Open Scope rel_inv_scope.
Lemma flip_involutive@{u} {X Y:set@{u}} (R:𝒫 (X ⊗ Y)) : (R⁻¹)⁻¹ = R.
Proof. refl. Qed.
#[global] Hint Extern 2 (Involutive flip) => simple notypeclasses refine flip_involutive : typeclass_instances.

#[global] Hint Extern 1 (Inverse flip) => refine flip : typeclass_instances.
Lemma flip_bijective@{u} {X Y:set@{u}} : Bijective (@flip X Y).
Proof. apply alt_Build_Bijective; intros R; exact (flip_involutive R). Qed.
#[global] Hint Extern 2 (Bijective flip) => simple notypeclasses refine flip_bijective : typeclass_instances.
#[global] Hint Extern 2 (Injective flip) => simple notypeclasses refine flip_bijective : typeclass_instances.
#[global] Hint Extern 2 (Surjective flip) => simple notypeclasses refine flip_bijective : typeclass_instances.

Lemma flip_lat_mor@{u} {X Y:set@{u}} : BoundedLattice_Morphism (@flip X Y).
Proof. apply alt_Build_BoundedLattice_Morphism.
+ now intros R S [y x].
+ now intros R S [y x].
+ refl.
+ refl.
Qed.
#[global] Hint Extern 2 (BoundedLattice_Morphism flip) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (Lattice_Morphism flip) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (BoundedJoinSemiLattice_Morphism flip) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (BoundedMeetSemiLattice_Morphism flip) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism flip) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (MeetSemiLattice_Morphism flip) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (Bottom_Pointed_Morphism flip) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (Top_Pointed_Morphism flip) => simple notypeclasses refine flip_lat_mor : typeclass_instances.

Lemma flip_ord_embed@{u} {X Y:set@{u}} : OrderEmbedding (@flip X Y).
Proof. exact (join_sl_mor_embedding _). Qed.
#[global] Hint Extern 2 (OrderEmbedding flip) => simple notypeclasses refine flip_ord_embed : typeclass_instances.
#[global] Hint Extern 2 (OrderMorphism flip) => simple notypeclasses refine flip_ord_embed : typeclass_instances.
#[global] Hint Extern 2 (OrderPreserving flip) => simple notypeclasses refine flip_ord_embed : typeclass_instances.
#[global] Hint Extern 2 (OrderReflecting flip) => simple notypeclasses refine flip_ord_embed : typeclass_instances.

Lemma flip_compose_rel_distr@{u} {X Y Z:set@{u}} (R:𝒫 (X ⊗ Y)) (S:𝒫 (Y ⊗ Z)) : (R ⋄ S)⁻¹ = S⁻¹ ⋄ R⁻¹.
Proof. intros [z x]. change ((∐ y, (x,y) ∊ R ⊠ (y,z) ∊ S) ⧟ (∐ y, (y,z) ∊ S ⊠ (x,y) ∊ R)).
  apply aex_aiff; intros y; apply aprod_com.
Qed.
Lemma flip_anti_distribute {X} : AntiDistribute (X:=𝒫 (X ⊗ X)) flip (⋄).
Proof. exact flip_compose_rel_distr. Qed.
#[global] Hint Extern 2 (AntiDistribute flip (⋄)) => simple notypeclasses refine flip_anti_distribute : typeclass_instances.

Lemma flip_id {X} : (id_rel X)⁻¹ = id_rel X.
Proof. intros [x y]. change (y = x ⧟ x = y). now apply symmetry_iff. Qed.

Lemma compose_rel_star_monoid {X} : StarMonoid (𝒫 (X ⊗ X)).
Proof. apply alt_Build_StarMonoid.
+ now change (Associative (X:=𝒫 (X ⊗ X)) (⋄)).
+ now change (LeftIdentity (@compose_rel X X X) (id_rel X)).
+ now change (RightIdentity (@compose_rel X X X) (id_rel X)).
+ now change (Involutive (X:=𝒫 (X ⊗ X)) flip).
+ now change (AntiDistribute (X:=𝒫 (X ⊗ X)) flip (⋄)).
Qed.
#[global] Hint Extern 2 (StarMonoid (subset_set (_ ⊗ _))) => simple notypeclasses refine compose_rel_star_monoid : typeclass_instances.
#[global] Hint Extern 2 (Monoid (subset_set (_ ⊗ _))) => simple notypeclasses refine compose_rel_star_monoid : typeclass_instances.
#[global] Hint Extern 2 (SemiGroup (subset_set (_ ⊗ _))) => simple notypeclasses refine compose_rel_star_monoid : typeclass_instances.
#[global] Hint Extern 2 (StarSemiGroup (subset_set (_ ⊗ _))) => simple notypeclasses refine compose_rel_star_monoid : typeclass_instances.

#[global] Hint Extern 2 (BoundedLattice_Morphism (@inv _ flip)) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (Lattice_Morphism (@inv _ flip)) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (BoundedJoinSemiLattice_Morphism (@inv _ flip)) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (BoundedMeetSemiLattice_Morphism (@inv _ flip)) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (@inv _ flip)) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (MeetSemiLattice_Morphism (@inv _ flip)) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (Bottom_Pointed_Morphism (@inv _ flip)) => simple notypeclasses refine flip_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (Top_Pointed_Morphism (@inv _ flip)) => simple notypeclasses refine flip_lat_mor : typeclass_instances.

#[global] Hint Extern 2 (OrderEmbedding  (@inv _ flip)) => simple notypeclasses refine flip_ord_embed : typeclass_instances.
#[global] Hint Extern 2 (OrderPreserving (@inv _ flip)) => simple notypeclasses refine flip_ord_embed : typeclass_instances.
#[global] Hint Extern 2 (OrderReflecting (@inv _ flip)) => simple notypeclasses refine flip_ord_embed : typeclass_instances.

Local Open Scope sg_op_scope.

Lemma compose_rel_ub_l@{u} {X:set@{u}} (R S : 𝒫 (X ⊗ X))
  : mon_unit ⊆ S ⊸ R ⊆ R ∙ S.
Proof. now rew (order_preserving_simp (R∙) (mon_unit) S). Qed.

Lemma compose_rel_ub_r@{u} {X:set@{u}} (R S : 𝒫 (X ⊗ X))
  : mon_unit ⊆ R ⊸ S ⊆ R ∙ S.
Proof. now rew (order_preserving_simp (∙S) (mon_unit) R). Qed.

Local Close Scope sg_op_scope.


(** Tensor subset *)

Local Open Scope subset_scope.
Lemma tensor_subset_order_preserving {X Y} : OrderPreserving (@tensor_subset X Y).
Proof. apply alt_Build_OrderPreserving. intros [U₁ V₁][U₂ V₂].
  change (U₁ ⊆ U₂ ⊠ V₁ ⊆ V₂ ⊸ U₁ ⊗ V₁ ⊆ U₂ ⊗ V₂).
  change (?A ⊆ ?B) with (∏ x, x ∊ A ⊸ x ∊ B).
  rew <-all_adj; intros [x y]. rew [(all_lb _ x)|(all_lb _ y)].
  full_tautological.
Qed.
#[global] Hint Extern 2 (OrderPreserving tensor_subset) => simple notypeclasses refine tensor_subset_order_preserving : typeclass_instances.

Lemma tensor_subset_flip@{u} {X Y:set@{u}} (U : 𝒫 X) (V : 𝒫 Y) : (U ⊗ V)⁻¹ = V ⊗ U.
Proof. intros [y x]. apply aprod_com. Qed.

Lemma tensor_subset_compose@{u} {X Y Z:set@{u}} (A : 𝒫 X) (B : 𝒫 Y) (C : 𝒫 Z) U V `{!Inhabited B} :
  A ⊗ B ⊆ U ⊠ B ⊗ C ⊆ V ⊸ A ⊗ C ⊆ U ⋄ V.
Proof. 
  change (?A ⊆ ?B) with (∏ x, x ∊ A ⊸ x ∊ B).
  rew <-all_adj; intros [x z].
  pose proof inhabited B as [y _].
  rew [(all_lb _ (x, y:Y)) | (all_lb _ (y:Y, z))].
  change ((?x, ?y) ∊ ?A ⊗ ?B) with (x ∊ A ⊠ y ∊ B); simplify.
  destruct y as [y ?].
  change ((x ∊ A ⊸ (x, y) ∊ U) ⊠ (z ∊ C ⊸ (y, z) ∊ V) ⊸ x ∊ A ⊠ z ∊ C ⊸ ∐ y:Y, (x, y) ∊ U ⊠ (y, z) ∊ V).
  rew <-(aex_ub _ y). tautological.
Qed.

(** Product subset *)

Lemma prod_subset_order_preserving {X Y} : OrderPreserving (@prod_subset X Y).
Proof. apply alt_Build_OrderPreserving. intros [U₁ V₁][U₂ V₂]. unfold_pair_le.
  change (?A ≤ ?B) with (∏ x, x ∊ A ⊸ x ∊ B).
  rew <-all_adj; intros [x y]. rew [(all_lb _ x)|(all_lb _ y)].
  full_tautological.
Qed.
#[global] Hint Extern 2 (OrderPreserving prod_subset) => simple notypeclasses refine prod_subset_order_preserving : typeclass_instances.
