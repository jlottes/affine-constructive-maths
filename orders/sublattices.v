Require Import interfaces.orders theory.sublattices orders.maps orders.lattices orders.suborders.
Require Import easy.

Lemma sub_meet_sl_order `{MeetSemiLatticeOrder L} {U:𝒫 L} `{!MeetSubSemiLattice U} : MeetSemiLatticeOrder U.
Proof. split; try exact _.
+ intros x y. exact (meet_lb_l (x:L) (y:L)).
+ intros x y. exact (meet_lb_r (x:L) (y:L)).
+ intros x y z. exact (meet_glb (x:L) (y:L) (z:L)).
Qed.
Global Hint Extern 2 (MeetSemiLatticeOrder (subset_to_set _)) => simple notypeclasses refine sub_meet_sl_order : typeclass_instances.

Lemma sub_join_sl_order `{JoinSemiLatticeOrder L} {U:𝒫 L} `{!JoinSubSemiLattice U} : JoinSemiLatticeOrder U.
Proof. split; try exact _.
+ intros x y. exact (join_ub_l (x:L) (y:L)).
+ intros x y. exact (join_ub_r (x:L) (y:L)).
+ intros x y z. exact (join_lub (x:L) (y:L) (z:L)).
Qed.
Global Hint Extern 2 (JoinSemiLatticeOrder (subset_to_set _)) => simple notypeclasses refine sub_join_sl_order : typeclass_instances.

Lemma sub_lattice_order `{LatticeOrder L} {U:𝒫 L} `{!SubLattice U} : LatticeOrder U.
Proof. now split. Qed.
Global Hint Extern 2 (LatticeOrder (subset_to_set _)) => simple notypeclasses refine sub_lattice_order : typeclass_instances.


Local Open Scope sg_op_scope.

Lemma sub_sg_op_order_preserving `{@SubSemiGroup G op H} {Gle:Le G} `{!OrderPreserving (X:=G ⊗ G) (Y:=G) (∙)} : OrderPreserving (X:=H ⊗ H) (Y:=H) (∙).
Proof. apply alt_Build_OrderPreserving. intros [a b][c d].
  exact (order_preserving (∙) (subset_pt a, subset_pt b) (subset_pt c, subset_pt d)).
Qed.
#[global] Hint Extern 2 (OrderPreserving (X:=subset_to_set _ ⊗ subset_to_set _) (Y:=subset_to_set _) (∙)) =>
  simple notypeclasses refine sub_sg_op_order_preserving : typeclass_instances.

Lemma sub_sg_op_join_sl_mor_l `{@SubSemiGroup G op H} `{@JoinSubSemiLattice G Gjoin H} {x:H} `{!JoinSemiLattice_Morphism (subset_pt x ∙)}
  : JoinSemiLattice_Morphism (x ∙).
Proof. split; [ exact sub_semigroup_semigroup ..|].
  change (∀ y z : H, x ∙ (y ⊔ z) = (x ∙ y) ⊔ (x ∙ z)).
  intros y z. exact (preserves_join (subset_pt x ∙) _ _).
Qed.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) (func_op2 ap1 (∙) _)) =>
  simple notypeclasses refine sub_sg_op_join_sl_mor_l : typeclass_instances.

Lemma sub_sg_op_join_sl_mor_r `{@SubSemiGroup G op H} `{@JoinSubSemiLattice G Gjoin H} {x:H} `{!JoinSemiLattice_Morphism (∙ subset_pt x)}
  : JoinSemiLattice_Morphism (∙ x).
Proof. split; [ exact sub_semigroup_semigroup ..|].
  change (∀ y z : H, (y ⊔ z) ∙ x = (y ∙ x) ⊔ (z ∙ x)).
  intros y z. exact (preserves_join (∙ subset_pt x) _ _).
Qed.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) (func_op2 ap2 (∙) _)) =>
  simple notypeclasses refine sub_sg_op_join_sl_mor_r : typeclass_instances.

Lemma sub_sg_op_join_distr_l `{@SubSemiGroup G op H} `{@JoinSubSemiLattice G Gjoin H} `{!LeftDistribute (X:=G) (∙) (⊔)}
  : LeftDistribute (X:=H) (∙) (⊔).
Proof. change (∀ x y z : H, x ∙ (y ⊔ z) = (x ∙ y) ⊔ (x ∙ z)).
  intros x y z. exact (distribute_l _ _ (subset_pt x) _ _).
Qed.
#[global] Hint Extern 2 (LeftDistribute (X:=subset_to_set _) (∙) (⊔)) =>
  simple notypeclasses refine sub_sg_op_join_distr_l : typeclass_instances.

Lemma sub_sg_op_join_distr_r `{@SubSemiGroup G op H} `{@JoinSubSemiLattice G Gjoin H} `{!RightDistribute (X:=G) (∙) (⊔)}
  : RightDistribute (X:=H) (∙) (⊔).
Proof. change (∀ y z x : H, (y ⊔ z) ∙ x = (y ∙ x) ⊔ (z ∙ x)).
  intros y z x. exact (distribute_r _ _ (subset_pt y) _ _).
Qed.
#[global] Hint Extern 2 (RightDistribute (X:=subset_to_set _) (∙) (⊔)) =>
  simple notypeclasses refine sub_sg_op_join_distr_r : typeclass_instances.

Local Open Scope star_scope.

Lemma sub_star_sg_inv_order_preserving `{@SubStarSemiGroup G op i H} {Gle:Le G} `{!OrderPreserving (X:=G) (Y:=G) inv} : OrderPreserving (X:=H) (Y:=H) inv.
Proof. apply alt_Build_OrderPreserving. intros x y.
  exact (order_preserving inv (subset_pt x) (subset_pt y)).
Qed.
#[global] Hint Extern 2 (OrderPreserving (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_order_preserving : typeclass_instances.

Lemma sub_star_sg_inv_order_reflecting `{@SubStarSemiGroup G op i H} {Gle:Le G} `{!OrderReflecting (X:=G) (Y:=G) inv} : OrderReflecting (X:=H) (Y:=H) inv.
Proof. apply alt_Build_OrderReflecting. intros x y.
  exact (order_reflecting inv (subset_pt x) (subset_pt y)).
Qed.
#[global] Hint Extern 2 (OrderReflecting (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_order_reflecting : typeclass_instances.

Lemma sub_star_sg_inv_order_embedding `{@SubStarSemiGroup G op i H} {Gle:Le G} `{!OrderEmbedding (X:=G) (Y:=G) inv} : OrderEmbedding (X:=H) (Y:=H) inv.
Proof. now split. Qed.
#[global] Hint Extern 2 (OrderEmbedding (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_order_embedding : typeclass_instances.


Lemma sub_star_sg_inv_join_sl_mor `{@SubStarSemiGroup G op i H} `{@JoinSubSemiLattice G j H} `{!JoinSemiLattice_Morphism (X:=G) inv}
  : JoinSemiLattice_Morphism (X:=H) inv.
Proof. split; [ exact sub_semigroup_semigroup ..|].
  change (∀ x y : H, (x ⊔ y)* = x* ⊔ y*).
  intros x y. exact (preserves_join _ (subset_pt x) _).
Qed.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_join_sl_mor : typeclass_instances.

Lemma sub_star_sg_inv_meet_sl_mor `{@SubStarSemiGroup G op i H} `{@MeetSubSemiLattice G m H} `{!MeetSemiLattice_Morphism (X:=G) inv}
  : MeetSemiLattice_Morphism (X:=H) inv.
Proof. split; [ exact sub_semigroup_semigroup ..|].
  change (∀ x y : H, (x ⊓ y)* = x* ⊓ y*).
  intros x y. exact (preserves_meet _ (subset_pt x) _).
Qed.
#[global] Hint Extern 2 (MeetSemiLattice_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_meet_sl_mor : typeclass_instances.

Lemma sub_star_sg_inv_lat_mor `{@SubStarSemiGroup G op i H} `{@SubLattice G m j H} `{!Lattice_Morphism (X:=G) inv}
  : Lattice_Morphism (X:=H) inv.
Proof. now split. Qed.
#[global] Hint Extern 2 (Lattice_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_lat_mor : typeclass_instances.

Lemma sub_star_sg_inv_bounded_join_sl_mor `{@SubStarSemiGroup G op i H} `{@JoinSubBoundedSemiLattice G j b H} `{!BoundedJoinSemiLattice_Morphism (X:=G) inv}
  : BoundedJoinSemiLattice_Morphism (X:=H) inv.
Proof. split; [exact sub_monoid_monoid .. | | ].
+ exact sub_star_sg_inv_join_sl_mor.
+ exact (preserves_bottom _).
Qed.
#[global] Hint Extern 2 (BoundedJoinSemiLattice_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_bounded_join_sl_mor : typeclass_instances.
#[global] Hint Extern 2 (Bottom_Pointed_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_bounded_join_sl_mor : typeclass_instances.

Lemma sub_star_sg_inv_bounded_meet_sl_mor `{@SubStarSemiGroup G op i H} `{@MeetSubBoundedSemiLattice G j b H} `{!BoundedMeetSemiLattice_Morphism (X:=G) inv}
  : BoundedMeetSemiLattice_Morphism (X:=H) inv.
Proof. split; [exact sub_monoid_monoid .. | | ].
+ exact sub_star_sg_inv_meet_sl_mor.
+ exact (preserves_top _).
Qed.
#[global] Hint Extern 2 (BoundedMeetSemiLattice_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_bounded_meet_sl_mor : typeclass_instances.
#[global] Hint Extern 2 (Top_Pointed_Morphism (X:=subset_to_set _) (Y:=subset_to_set _) inv) =>
  simple notypeclasses refine sub_star_sg_inv_bounded_meet_sl_mor : typeclass_instances.


