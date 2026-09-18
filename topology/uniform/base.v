Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.uniform interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology.
Require Import reflection_pair.base.
Require Import easy rewrite replc simplify tactics.misc.

Local Open Scope topology_scope.
Local Abbreviation id := (id_fun _).

Coercion  uniformity_sub_lattice `{@UniformSpace X Φ} : SubLattice Φ.
Proof. exact filter_sub_lattice. Qed.

Coercion  uniformity_meet_sub_sl `{@UniformSpace X Φ} : MeetSubBoundedSemiLattice Φ.
Proof. exact filter_bounded_meet_sub_sl. Qed.

Lemma pre_uniformity_sub_ssg `{@PreUniformSpace X Φ, !UpSet Φ} : SubStarSemiGroup Φ.
Proof. apply alt_Build_SubStarSemiGroup.
+ intros U V.
  change (U ∊ Φ ⊠ V ∊ Φ ⊸ U ⋄ V ∊ Φ).
  rew (uniform_refl V).
  rew (order_preserving (ap1 compose_rel U) (id_rel X) V).
  change (U ∊ Φ ⊠ U ⋄ id_rel X ⊆ U ⋄ V ⊸ U ⋄ V ∊ Φ).
  rew (aprod_com _ _).
  rew (right_identity (⋄) U).
  rew (aprod_adj _ _ _).
  apply (up_closed Φ).
+ exact uniform_sym.
Qed.

Coercion uniformity_sub_ssg `{@UniformSpace X Φ}  : SubStarSemiGroup Φ.
Proof. exact pre_uniformity_sub_ssg. Qed.

#[global] Hint Extern 4 (SubLattice ?Φ) => match type of Φ with Uniformity _ => simple notypeclasses refine (@uniformity_sub_lattice _ Φ _) end : typeclass_instances.
#[global] Hint Extern 4 (JoinSubSemiLattice ?Φ) => match type of Φ with Uniformity _ => simple notypeclasses refine (@uniformity_sub_lattice _ Φ _) end : typeclass_instances.
#[global] Hint Extern 4 (MeetSubSemiLattice ?Φ) => match type of Φ with Uniformity _ => simple notypeclasses refine (@uniformity_sub_lattice _ Φ _) end : typeclass_instances.

#[global] Hint Extern 4 (MeetSubBoundedSemiLattice ?Φ) => match type of Φ with Uniformity _ => simple notypeclasses refine (@uniformity_meet_sub_sl _ Φ _) end : typeclass_instances.

#[global] Hint Extern 4 (SubStarSemiGroup ?Φ) => match type of Φ with Uniformity _ => simple notypeclasses refine (@uniformity_sub_ssg _ Φ _) end : typeclass_instances.
#[global] Hint Extern 4 (SubSemiGroup ?Φ) => match type of Φ with Uniformity _ => simple notypeclasses refine (@uniformity_sub_ssg _ Φ _) end : typeclass_instances.

Local Open Scope sg_op_scope.
Local Open Scope grp_scope.

Lemma alt_Build_UniformSpace `{Φ: Uniformity X} :
  Filter Φ
→ (∀ U, U ∊ Φ ⊸ id_rel X ⊆ U)
→ (∀ U, U ∊ Φ ⊸ U⁻¹ ∊ Φ)
→ (∀ (U:Φ), ∐ (V:Φ), ∏ x y z, near V x y ⊠ near V y z ⊸ near U x z )
→ UniformSpace X.
Proof. intros ? refl sym split. do 2 (split; trivial).
  intros U. specialize (split U). destruct split as [V split]. exists V. intros [x z].
  change ( (∐ y, near V x y ⊠ near V y z) ⊸ near U x z).
  rew <-aex_adj; intros y. apply split.
Qed.

Lemma alt_Build_StrongUniformSpace `{Φ: Uniformity X} :
  Filter Φ
→ (∀ U, U ∊ Φ ⊸ id_rel X ⊆ U)
→ (∀ (U:Φ), ∐ (V:Φ), ∏ x y z, near V x y ∧ near V y z ⊸ near U x z )
→ (∀ U, U ∊ Φ ⊸ U⁻¹ ∊ Φ)
→ StrongUniformSpace X.
Proof. intros ? refl split sym. split; [ apply alt_Build_UniformSpace |]; trivial.
  intros U. specialize (split U). destruct split as [V split]. exists V. intros x y z.
  now rew <-(split x y z).
Qed.


(** Miscellaneous *)
  
Lemma uniform_split_alt `{@UniformSpace X Φ} (U:Φ) : ∐ (V:Φ), V ∙ V ≤ U.
Proof. exact (uniform_split U). Qed.

Lemma uniform_refl_alt `{@PreUniformSpace X Φ} (U:Φ) : id_rel _ ⊆ U.
Proof. now apply uniform_refl. Qed.

Lemma ufm_compose_ub_l `{@UniformSpace X Φ} (U V:Φ) : U ≤ U ∙ V.
Proof. apply compose_rel_ub_l. exact (uniform_refl_alt _). Qed.

Lemma ufm_compose_ub_r `{@UniformSpace X Φ} (U V:Φ) : V ≤ U ∙ V.
Proof. apply compose_rel_ub_r. exact (uniform_refl_alt _). Qed.

Lemma near_refl_alt `{@PreUniformSpace X Φ} x y (U:Φ) : x = y ⊸ near U x y.
Proof. change (x = y ⊸ (x, y) ∊ U). rew <-(uniform_refl_alt U). now change (x = y ⊸ x = y). Qed.

Lemma near_refl `{@PreUniformSpace X Φ} (U:Φ) x : near U x x.
Proof. now rew <-(near_refl_alt _ _ _). Qed.

Lemma near_sym `{@UniformSpace X Φ} (U:Φ) : ∐ (V:Φ), ∏ x y, near V y x ⊸ near U x y.
Proof. now exists (U⁻¹). Qed.

Lemma near_split `{@PreUniformSpace X Φ} (U:Φ) : ∐ (V:Φ), ∏ x y z, near V x y ⊠ near V y z ⊸ near U x z.
Proof. pose proof uniform_split U as [V PV]. exists V. intros x y z.
  change ((x, y) ∊ V ⊠ (y, z) ∊ V ⊸ (x, z) ∊ U).
  rew <-(PV (x, z) : (x, z) ∊ V ⋄ V ⊸ (x, z) ∊ U).
  change ((x, y) ∊ V ⊠ (y, z) ∊ V ⊸ ∐ y, (x, y) ∊ V ⊠ (y, z) ∊ V).
  now rew <-(aex_ub _ y).
Qed.

Lemma le_near_proper `{@PreUniformSpace X Φ} {U V:Φ} {x y:X} : U ≤ V → x = y → near U x ⊆ near V y.
Proof. intros EU Ex z. trans (near U y z). now apply (is_fun set:(λ w, near U w z)). refine (EU _). Qed.
#[global] Hint Extern 2 (apos (func_op2 near _ _ ≤ _)) => sapply_2 le_near_proper : proper.

Lemma aimpl_near_proper `{@PreUniformSpace X Φ} {U V:Φ} {x y z w:X} : U ≤ V → x = y → z = w → near U x z ⊸ near V y w.
Proof. intros EU Ex Ez. trans (near V x z); [ refine (EU _) |].
  apply (is_fun V (x,z) (y,w)). now split.
Qed.
#[global] Hint Extern 2 (apos (func_op (func_op2 near _ _) _ ⊸ _)) => sapply_3 aimpl_near_proper : proper.

Lemma uniform_sym_alt `{@UniformSpace X Φ} (U : Φ) : ∐ (V:Φ), V⁻¹ = V ⊠ V ≤ U.
Proof. exists (U ⊓ U⁻¹). split.
+ rew (preserves_meet inv _ _). simplify. now apply commutativity.
+ apply meet_lb_l.
Qed.

Lemma uniform_split_sym `{@UniformSpace X Φ} (U:Φ) : ∐ (V:Φ), V⁻¹ = V ⊠ V ∙ V ≤ U.
Proof. pose proof uniform_split_alt U as [W PW].
  pose proof uniform_sym_alt W as [V [EV PV]].
  exists V; split; trivial. now rew PV.
Qed.

Lemma uniform_split_sym4 `{@UniformSpace X Φ} (U:Φ) : ∐ (V:Φ), V⁻¹ = V ⊠ V ∙ V ∙ V ∙ V ≤ U.
Proof.
  pose proof uniform_split_alt U as [W PW].
  pose proof uniform_split_sym W as [V [EV PV]].
  exists V; split; trivial.
  replc (V ∙ V ∙ V ∙ V) with ((V ∙ V) ∙ (V ∙ V)) by now group_simplify.
  now rew PV.
Qed.

Lemma uniform_split_sym3 `{@UniformSpace X Φ} (U:Φ) : ∐ (V:Φ), V⁻¹ = V ⊠ V ∙ V ∙ V ≤ U.
Proof.
  pose proof uniform_split_sym4 U as [V [E PV]]. exists V. split; trivial.
  rew <-PV.
  change (V ⋄ V ⋄ V ⊆ V ⋄ V ⋄ V ⋄ V).
  rew <-(right_identity (⋄) (V ⋄ V ⋄ V)) at 1.
  now rew (uniform_refl_alt V).
Qed.

Lemma uniform_split_sym6 `{@UniformSpace X Φ} (U:Φ) : ∐ (V:Φ), V⁻¹ = V ⊠ V ∙ V ∙ V ∙ V ∙ V ∙ V ≤ U.
Proof.
  pose proof uniform_split_sym3 U as [W [_ PW]].
  pose proof uniform_split_sym W as [V [EV PV]].
  exists V; split; trivial.
  replc (V ∙ V ∙ V ∙ V ∙ V ∙ V) with ((V ∙ V) ∙ (V ∙ V) ∙ (V ∙ V)) by now group_simplify.
  now rew PV.
Qed.

Lemma uniform_split_sym5 `{@UniformSpace X Φ} (U:Φ) : ∐ (V:Φ), V⁻¹ = V ⊠ V ∙ V ∙ V ∙ V ∙ V ≤ U.
Proof.
  pose proof uniform_split_sym6 U as [V [EV PV]].
  exists V. split; trivial. rew <-PV.
  apply ufm_compose_ub_l.
Qed.


Lemma near_compose `{@UniformSpace X Φ} (U V : Φ) (x y z : X)
  : near U x y ⊠ near V y z ⊸ (x, z) ∊ U ∙ V .
Proof. exact (rel_compose _ _ _ _ _). Qed.

Lemma near_compose_alt `{@UniformSpace X Φ} (U V : Φ) (x y z : X)
  : near U x y ⊠ near V y z ⊸ near (U ∙ V) x z.
Proof. exact (rel_compose _ _ _ _ _). Qed.

Lemma near_compose3 `{@UniformSpace X Φ} (U V W : Φ) (a b c d : X)
  : near U a b ⊠ near V b c ⊠ near W c d ⊸ (a, d) ∊ U ∙ V ∙ W.
Proof. exact (rel_compose3 _ _ _ _ _ _ _). Qed.

Lemma near_compose3_alt `{@UniformSpace X Φ} (U V W : Φ) (a b c d : X)
  : near U a b ⊠ near V b c ⊠ near W c d ⊸ near (U ∙ V ∙ W) a d.
Proof. exact (rel_compose3 _ _ _ _ _ _ _). Qed.

Lemma near_compose4_alt `{@UniformSpace X Φ} (U V W A : Φ) (a b c d e : X)
  : near U a b ⊠ near V b c ⊠ near W c d ⊠ near A d e ⊸ near (U ∙ V ∙ W ∙ A) a e.
Proof. exact (rel_compose4 _ _ _ _ _ _ _ _ _). Qed.

Lemma near_compose4 `{@UniformSpace X Φ} (U V W A : Φ) (a b c d e : X)
  : near U a b ⊠ near V b c ⊠ near W c d ⊠ near A d e ⊸ (a, e) ∊ U ∙ V ∙ W ∙ A.
Proof. exact (rel_compose4 _ _ _ _ _ _ _ _ _). Qed.

Section tensor_compose.
  Universes u.
  Local Open Scope subset_scope.
  Context `{@UniformSpace@{u} X Φ}.

  Lemma ufm_tensor_subset_compose  (A B C : 𝒫 X) (U V : Φ) `{!Inhabited B}
    : A ⊗ B ⊆ powerset_pt U ⊠ B ⊗ C ⊆ powerset_pt V ⊸ A ⊗ C ⊆ powerset_pt (U ∙ V).
  Proof. exact (tensor_subset_compose _ _ _ _ _). Qed.
  
  Lemma ufm_tensor_subset_flip (A B : 𝒫 X) (U : Φ)
    : A ⊗ B ⊆ powerset_pt (U⁻¹) ⧟ B ⊗ A ⊆ powerset_pt U.
  Proof. rew <-(tensor_subset_flip B A). apply (symmetry _). exact (order_embedding flip _ _). Qed.
  
  Lemma ufm_tensor_subset_flip_sym (A B : 𝒫 X) (U : Φ) {EU:U⁻¹ = U}
    : A ⊗ B ⊆ powerset_pt U ⧟ B ⊗ A ⊆ powerset_pt U.
  Proof. now rew <-(ufm_tensor_subset_flip A B U), EU. Qed.

  Lemma near_singleton_r (U : Φ) (x:X)
    : singleton x ⊗ near U x ⊆ powerset_pt U.
  Proof. intros [y z]. change (x = y ⊠ near U x z ⊸ near U y z).
    rew (aprod_adj _ _ _). rew (is_fun (ap2 U z) x y). apply aandl.
  Qed.

  Lemma near_singleton_l (U : Φ) (x:X)
    : near U x ⊗ singleton x ⊆ powerset_pt U⁻¹.
  Proof. rew (ufm_tensor_subset_flip _ _ _). exact (near_singleton_r _ _). Qed.

  Lemma near_singleton_compose_r {Y:set@{u}} (A : 𝒫 Y) (B : 𝒫 (Y ⊗ X)) (x:X) (U : Φ)
    : A ⊗ singleton x ⊆ B ⊸ A ⊗ near U x ⊆ B ⋄ U.
  Proof.
    rew <-(tensor_subset_compose _ (singleton x) _ _ _).
    rew (aiff_is_true (near_singleton_r U x)).
    now simplify.
  Qed.

  Lemma near_singleton_compose_l {Y:set@{u}} (A : 𝒫 Y) (B : 𝒫 (X ⊗ Y)) (x:X) (U : Φ)
    : singleton x ⊗ A ⊆ B ⊸ near U x ⊗ A ⊆ powerset_pt U⁻¹ ⋄ B.
  Proof.
    rew <-(tensor_subset_compose _ (singleton x) _ _ _).
    rew (aiff_is_true (near_singleton_l U x)).
    now simplify.
  Qed.
  
  Lemma near_singleton_compose_l_alt (A : 𝒫 X) (x:X) (U V : Φ)
    : singleton x ⊗ A ⊆ U ⊸ near V x ⊗ A ⊆ powerset_pt (V⁻¹ ∙ U).
  Proof. exact (near_singleton_compose_l _ _ _ _). Qed.
  
  Lemma near_singleton_compose_r_alt (A : 𝒫 X) (x:X) (U V : Φ)
    : A ⊗ singleton x ⊆ U ⊸ A ⊗ near V x ⊆ powerset_pt (U ∙ V).
  Proof. exact (near_singleton_compose_r _ _ _ _). Qed.
End tensor_compose.

Section thicken.
  Import thicken_notation.
  
  Context `{@UniformSpace X Φ}.

  Local Instance thicken_order_preserving : OrderPreserving (@thicken X Φ).
  Proof. apply alt_Build_OrderPreserving. intros [U A][V B].
    change (powerset_pt U ⊆ powerset_pt V ⊠ A ⊆ B ⊸ ∏ y, (∐ x, x ∊ A ⊠ (x, y) ∊ U) ⊸ ∐ x, x ∊ B ⊠ (x, y) ∊ V).
    rew <-all_adj; intros y. rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj; intros x. rew <-(aex_ub _ x).
    rew [<-(subset_apply x A B)|<-(subset_apply (x,y) (powerset_pt U) (powerset_pt V))].
    tautological.
  Qed.

  Lemma thicken_expanding (U:Φ) (A:𝒫 X) : A ⊆ U.[A].
  Proof. intros x. change (x ∊ A ⊸ ∐ y, y ∊ A ⊠ near U y x).
    rew <-(aex_ub _ x). now rew (aprod_true_r (near_refl U x)).
  Qed.

  Lemma thicken_compose (U V : Φ) (A:𝒫 X) : U.[V.[A]] = (V ∙ U).[A].
  Proof. intros y. change ((∐ z, (∐ x, x ∊ A ⊠ (x, z) ∊ V) ⊠ (z, y) ∊ U) ⧟ ∐ x, x ∊ A ⊠ ∐ z, (x, z) ∊ V ⊠ (z, y) ∊ U). split.
  + rew <-aex_adj; intros z. rew aex_frob_r, <-aex_adj; intros x.
    rew <-(aex_ub _ x), <-(aex_ub _ z). now rew (aprod_assoc _ _ _).
  + rew <-aex_adj; intros x. rew aex_frob_l, <-aex_adj; intros z.
    rew <-(aex_ub _ z), <-(aex_ub _ x). now rew (aprod_assoc _ _ _).
  Qed.
  
  Lemma thicken_compose_sub (U V W : Φ) (A:𝒫 X) : V ∙ W ≤ U ⊸ W.[V.[A]] ⊆ U.[A].
  Proof.
    rew (thicken_compose _ _ _), <-(order_preserving thicken _ _).
    change (V ∙ W ≤ U ⊸ V ∙ W ≤ U ⊠ A ≤ A). now simplify.
  Qed.

  Lemma thicken_singleton (U:Φ) (x:X) : U.[singleton x] = near U x.
  Proof. intros y. change ( (∐ x', x = x' ⊠ near U x' y) ⧟ near U x y). split.
  + rew <-aex_adj; intros x'.
    rew (is_fun set:(λ z, near U z y) x x' : x = x' ⊸ near U x y ⧟ near U x' y). tautological.
  + rew <-(aex_ub _ x). now rew (aprod_true_l (ltac:(refl):x = x)).
  Qed.

  Lemma thicken_empty (U:Φ) : U.[∅] = ∅.
  Proof. intros x. change ( (∐ y, 𝐅 ⊠ near U y x) ⧟ 𝐅). now simplify. Qed.

  Local Open Scope subset_scope.
  
  Lemma thicken_apart_swap_aux (U : Φ) (A B : 𝒫 X) : U.[A] ⊆ B ᗮ ⊸ A ⊆ U⁻¹.[B] ᗮ.
  Proof. change ( (∏ x, (∐ a, a ∊ A ⊠ near U a x) ⊸ x ∊̸ B) ⊸ (∏ x, x ∊ A ⊸ (∏ b, b ∊ B ⊸ anot (near U x b))) ).
    rew <-all_adj; intros a. rew <-(aprod_adj _ _ _), <-all_adj; intros b.
    rew (all_lb _ b), <-(aex_ub _ a). tautological.
  Qed.

  Lemma thicken_apart_swap (U : Φ) (A B : 𝒫 X) : U.[A] ⊆ B ᗮ ⧟ A ⊆ U⁻¹.[B] ᗮ.
  Proof. split; [ exact (thicken_apart_swap_aux _ _ _) |].
    rew <-(mult_empty_subset_complement_r _ _), (mult_empty_subset_complement_l _ _).
    exact (thicken_apart_swap_aux U⁻¹ _ _).
  Qed.

  Lemma thicken_apart_swap_alt (U : Φ) (A B : 𝒫 X) : U⁻¹.[A] ⊆ B ᗮ ⧟ A ⊆ U.[B] ᗮ.
  Proof. exact (thicken_apart_swap _ _ _). Qed.

  Lemma thicken_apart_split (U : Φ) (A B : 𝒫 X) : U.[A] ⊆ B ᗮ ⊸ ∐ V:Φ, V.[A] ⊆ (V.[B])ᗮ.
  Proof.
    pose proof uniform_split_sym U as [V [EV PV]]. rew [<-PV | <-(aex_ub _ V)].
    now rew <-(thicken_compose _ _ _), (thicken_apart_swap V V.[A] B), EV.
  Qed.
End thicken.
#[global] Hint Extern 2 (OrderPreserving thicken) => simple notypeclasses refine thicken_order_preserving : typeclass_instances.


(** Induced topology *)

Local Ltac unfold_nh :=
 change  (func_op (@nbrhood ?X (@UniformNeighborhood _ ?Φ)) (?x, ?N))
 with  (∐ (U:Φ), ∏ (y: X), near U x y ⊸ y ∊ N) .

Section uniform_topology.
  Context `{Φ:Uniformity X} `{!UniformSpace X}.

  Definition near_meet_l (U V : Φ) (x y : X) : near (U ⊓ V) x y ⊸ near U x y := aandl _ _.
  Definition near_meet_r (U V : Φ) (x y : X) : near (U ⊓ V) x y ⊸ near V x y := aandr _ _.

  Local Instance uniform_topology : Topology X.
  Proof. split.
  + intros x N; unfold_nh. rew <-aex_adj; intros U.
    rew (all_lb _ x). pose proof (near_refl U x); now simplify.
  + intros x N₁ N₂; unfold_nh. rew (aprod_adj _ _ _), <-aex_adj; intros U.
    rew <-(aex_ub _ U). rew <-(aprod_adj _ _ _), <-all_adj; intros y.
    rew (all_lb _ y). rew <-(aprod_adj _ _ _).
    rew (aprod_com _ _), <-(aprod_assoc _ _ _), (aprod_mp_r _ _).
    change (N₁ ⊆ N₂) with (∏ z, z ∊ N₁ ⊸ z ∊ N₂). rew (all_lb _ y). exact (aprod_mp_r _ _).
  + intros x; unfold_nh. exists top. intros y. now change (atrue ⊸ atrue).
  + intros x N₁ N₂; unfold_nh. rew <-aex_adj2; intros U V.
    rew <-(aex_ub _ (U ⊓ V)), <-all_adj; intros y. rew (all_lb _ y).
    rew <-(aprod_adj _ _ _); apply aand_intro.
    * change ( ((near U x y ⊸ y ∊ N₁) ⊠ (near V x y ⊸ y ∊ N₂)) ⊠ near (U ⊓ V) x y ⊸ y ∊ N₁ ).
      rew [ (aprodl (near U x y ⊸ y ∊ N₁) _) | (near_meet_l _ _ _ _) ].
      exact (aprod_mp_l _ _).
    * change ( ((near U x y ⊸ y ∊ N₁) ⊠ (near V x y ⊸ y ∊ N₂)) ⊠ near (U ⊓ V) x y ⊸ y ∊ N₂ ).
      rew [ (aprodr (near U x y ⊸ y ∊ N₁) _) | (near_meet_r _ _ _ _) ].
      exact (aprod_mp_l _ _).
  + intros x N; unfold_nh. rew <-aex_adj; intros U.
    pose proof near_split U as [V P]. rew <-(aex_ub _ V). rew <-all_adj; intros y.
    change ( (∏ z : X, near U x z ⊸ z ∊ N) ⊸ near V x y ⊸ y ⪽ N ). unfold_nh.
    rew <-(aex_ub _ V). rew <-(aprod_adj _ _ _). rew <-all_adj; intros z.
    rew (all_lb _ z). rew <-(aprod_adj _ _ _). rew (aprod_assoc _ _ _).
    rew (P x y z). exact (aprod_mp_l _ _).
  Qed.

  Lemma near_nbrhood_refl x (U:Φ) : x ⪽ near U x.
  Proof. unfold_nh. exists U. now intros y. Qed.
End uniform_topology.

Coercion uniform_topology : UniformSpace >-> Topology.

#[global] Hint Extern 2 (apos (?x ⪽ func_op2 near _ ?x)) => simple notypeclasses refine (near_nbrhood_refl _ _) : typeclass_instances.

(** Separation. For a uniform space, T₀ and Hausdorff collapse to "separated" *)

Lemma uniform_T₀_separated `{!@UniformSpace X Φ} : Separation_T₀ X → SeparatedUniformSpace X.
Proof. intro. split; trivial.
  enough (∀ x y N,  (∏ U : Φ, near U x y) ⊸ x ⪽ N ⊸ y ⪽ N ) as P.
  - intros x y. rew <-(separation_T₀ x y). rew <-all_adj. intros N. apply aand_intro; [ apply P |].
    rew <-(P y x _). rew <-all_adj; intros U.
    pose proof near_sym U as [V PV]; rew <-(PV _ _). exact (all_lb _ _).
  - intros x y N. unfold_nh.
    rew <-(aprod_adj _ _ _), aex_frob_l.
    rew <-aex_adj; intros U.
    pose proof near_split U as [V PV]. rew <-(aex_ub _ V).
    rew <-all_adj; intros z. rew <-(aprod_adj _ _ _). rew [(all_lb _ V) | (all_lb _ z)].
    rew <-(PV x y z). rew (aprod_assoc _ _ _). tautological.
Qed.

Lemma uniform_separated_iff `{!@SeparatedUniformSpace X Φ} x y : x = y ⧟ ∏ U : Φ, near U x y.
Proof. split; [| now apply uniform_separated ].
  rew <-all_adj; intros U. apply near_refl_alt.
Qed.

Coercion separated_uniform_hausdorff `{!@SeparatedUniformSpace X Φ} : Hausdorff X.
Proof. intros x y. rew (uniform_separated_iff _ _).
  rew <-all_adj; intros U.
  pose proof near_split U as [V PV].
  pose proof near_sym V as [W PW].
  rew (all_lb _ (near V x)), (all_lb _ (near W y)). simplify.
  rew <-aex_adj; intros z.
  change (near V x z ⊠ near W y z ⊸ near U x y). rew (PW z y).
  exact (PV _ _ _).
Qed.

Coercion separated_uniform_T₀ `{!@SeparatedUniformSpace X Φ} : Separation_T₀ X.
Proof. now apply Hausdorff_T₀. Qed.

Lemma uniform_reflects_hausdorff@{u} `{@UniformSpace@{u} X Φ, NY:Neighborhood@{u} Y}
  `{f:X ⇾ Y, !Continuous f, !Injective f, !Hausdorff Y} : SeparatedUniformSpace X.
Proof. apply uniform_T₀_separated, Hausdorff_T₀. exact (reflects_hausdorff f). Qed.
Arguments uniform_reflects_hausdorff {_ _ _ _ _} f {_ _ _}.

Coercion SeparatedStrongUniformSpace_StrongSet `{@SeparatedStrongUniformSpace X Φ} : StrongSet X.
Proof. intros x y z.
  rew (uniform_separated_iff _ _), <-all_adj; intros U.
  pose proof strong_uniform_split U as [V PV].
  rew (all_lb _ V).
  apply PV.
Qed.

(** Regularity *)

Lemma uniform_regularity_alt `{@UniformRegularity X Φ} (U:Φ)
  : ∐ (V:Φ), V ⊆ U ⊠ ∏ (p:X ⊗ X), p ∊ U ∨ p ∊̸ V.
Proof.
  pose proof uniform_regularity U as [V [EV HV]]. exists V. split; trivial.
  intros p. generalize (I:p ∊ ⊤). now rew <-HV.
Qed.

Coercion regular_uniform_space_strong `{@RegularUniformSpace X Φ} : StrongUniformSpace X.
Proof. split; try exact _. intros U.
  pose proof uniform_split_alt U as [W HW].
  pose proof uniform_regularity_alt W as [V [EV HV]].
  rew <-(aex_ub _ V). intros x y z.
  pose proof HV (x, y) as [ Hxy | Hxy ].
  + pose proof HV (y, z) as [ Hyz | Hyz ].
    * refine (aimpl_true_r _). rew <-HW.
      now apply (near_compose_alt _ _ x y z).
    * rew (aiff_is_false Hyz : near V y z ⧟ 𝐅). now simplify.
  + rew (aiff_is_false Hxy : near V x y ⧟ 𝐅). now simplify.
Qed.

Coercion separated_regular_uniform_space_sep_strong `{@SeparatedRegularUniformSpace X Φ} : SeparatedStrongUniformSpace X.
Proof. now split. Qed.

(** Properness of morphism classes *)

Import of_course_set_notation.

Import image_notation.

Lemma UniformlyContinuous_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f g : X ⇾ Y)
  : f = g → impl (UniformlyContinuous f, UniformlyContinuous g).
Proof. intros E [SX SY UC]; split; try exact _. red. now rew <-E. Qed.
Canonical Structure UniformlyContinuous_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@UniformlyContinuous X Y Φ Ψ) UniformlyContinuous_proper_impl.

Lemma UniformlyReflecting_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f g : X ⇾ Y)
  : f = g → impl (UniformlyReflecting f, UniformlyReflecting g).
Proof. intros E [SX SY UR]; split; try exact _. red. now rew <-E. Qed.
Canonical Structure UniformlyReflecting_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@UniformlyReflecting X Y Φ Ψ) UniformlyReflecting_proper_impl.

Lemma UniformlyInitial_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f g : X ⇾ Y)
  : f = g → impl (UniformlyInitial f, UniformlyInitial g).
Proof. intros E [UC UR]; split; now rew <-E. Qed.
Canonical Structure UniformlyInitial_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@UniformlyInitial X Y Φ Ψ) UniformlyInitial_proper_impl.

Lemma UniformlyEmbedding_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f g : X ⇾ Y)
  : f = g → impl (UniformlyEmbedding f, UniformlyEmbedding g).
Proof. intros E ?; split; now rew <-E. Qed.
Canonical Structure UniformlyEmbedding_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@UniformlyEmbedding X Y Φ Ψ) UniformlyEmbedding_proper_impl.


Lemma uniform_continuity_is_fun@{u} `{@UniformSpace@{u} X Φ} `{@SeparatedUniformSpace@{u} Y Ψ}
  {f:X → Y} `{!UniformContinuity f} : IsFun f.
Proof. intros x y. rew (uniform_separated_iff (f x) _), <-all_adj; intros V.
  pose proof (ufm_continuity f V) as [U PU]. rew <-(PU _ _). apply near_refl_alt.
Qed.

Import tensor_map_notation.
Lemma uniformly_continuous_alt@{u} `{@UniformSpace@{u} X Φ} `{@UniformSpace@{u} Y Ψ} (f:X ⇾ Y)
  : UniformlyContinuous f ↔ (∀ V:Ψ, ⟨f, f⟩* V ∊ Φ).
Proof. split.
+ intros ? V. pose proof ufm_continuity f V as [U' PU'].
  apply (up_closed Φ U' _); try exact _.
  intros [x y]. apply PU'.
+ intros P. split; try exact _. intros V. specialize (P V).
  now exists (to_subset (⟨f, f⟩* V)).
Qed.


Local Instance ufm_preimage_maps_to `{H:@UniformlyContinuous X Y Φ Ψ f} : WeakMapsTo ⟨f, f⟩* Ψ Φ.
Proof. intros V ?. rew (uniformly_continuous_alt f) in H. exact (H (to_subset V)). Qed.

Definition ufm_preimage `{H:@UniformlyContinuous X Y Φ Ψ f} := restrict ⟨f, f⟩* Ψ Φ.
Arguments ufm_preimage {_ _ _ _} f {_}.

Lemma ufm_reflection_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) `{H:@UniformReflection X Y Φ Ψ f} (U:Φ) : ∐ V:Ψ, ⟨f, f⟩* V ⊆ U.
Proof. pose proof (ufm_reflection f U) as [V PV]. exists V. intros [x y]. exact (PV x y). Qed.

Lemma uniform_reflection_alt@{u} `{@UniformSpace@{u} X Φ} `{@UniformSpace@{u} Y Ψ} (f:X ⇾ Y)
    : UniformReflection f ↔ (∀ U:Φ, ∐ V:Ψ, ⟨f, f⟩* V ⊆ U).
Proof. split; [ apply ufm_reflection_alt |].
  intros P U. specialize (P U) as [V PV]. exists V. intros x y. exact (PV (x, y)).
Qed.

Lemma uniform_reflection_injective@{u} `{@SeparatedUniformSpace@{u} X Φ} `{@UniformSpace@{u} Y Ψ}
  {f:X ⇾ Y} `{!UniformReflection f} : Injective f.
Proof. intros x y. rew (uniform_separated_iff x _), <-all_adj; intros V.
  pose proof (ufm_reflection f V) as [U PU]. rew <-(PU _ _). apply near_refl_alt.
Qed.

Lemma uniform_initial_embedding@{u} `{@SeparatedUniformSpace@{u} X Φ} `{@UniformSpace@{u} Y Ψ}
  {f:X ⇾ Y} `{!UniformlyInitial f} : UniformlyEmbedding f.
Proof. pose proof uniform_reflection_injective : Injective f. now split. Qed.



Coercion uniformly_continuous_continuous `{@UniformlyContinuous X Y Φ Ψ f} : Continuous f.
Proof.
 split; try exact _. intros x N. unfold_nh. rew <-aex_adj. intros V.
 rew <-(aex_ub _ (ufm_preimage f V)), <-all_adj; intros y.
 now rew (all_lb _ (f y)).
Qed.

Coercion uniformly_reflecting_continuously_reflecting
  `{H:@UniformlyReflecting X Y Φ Ψ f} : ContinuouslyReflecting f.
Proof. split; try exact _. intros x U.
  change (x ⪽ U) with (∐ (W:Φ), ∏ (y:X), near W x y ⊸ y ∊ U).
  rew <-aex_adj; intros W.
  pose proof ufm_reflection_alt f W as [W' PW'].
  rew <-(aex_ub _ (near W' (f x))).
  rew (aprod_true_l (near_nbrhood_refl (f x) W')).
  change (f* (near W' (f x)) ⊆ U) with (∏ x', (x, x') ∊ ⟨f,f⟩* W' ⊸ x' ∊ U).
  rew <-all_adj; intros x'. rew (all_lb _ x').
  now rew PW'.
Qed.

Coercion uniformly_initial_continuously_initial
  `{H:@UniformlyInitial X Y Φ Ψ f} : ContinuouslyInitial f.
Proof. now split. Qed.

Coercion uniformly_embedding_continuously_embedding
  `{H:@UniformlyEmbedding X Y Φ Ψ f} : ContinuouslyEmbedding f.
Proof. now split. Qed.

Lemma id_ufm_emb `{@UniformSpace X Φ} : UniformlyEmbedding (id_fun X).
Proof. do 3 (split; try exact _); intros U; now exists U. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding (id_fun _)) => simple notypeclasses refine id_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial (id_fun _)) => simple notypeclasses refine id_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (id_fun _)) => simple notypeclasses refine id_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformContinuity (func_op (id_fun _))) => simple notypeclasses refine id_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (id_fun _)) => simple notypeclasses refine id_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (id_fun _))) => simple notypeclasses refine id_ufm_emb : typeclass_instances.

Lemma compose_ufm_cont@{u} `{@UniformlyContinuous@{u} X Y Φ Ψ f} `{@UniformlyContinuous@{u} Y Z Ψ Ξ g} : UniformlyContinuous (g ∘ f).
Proof. apply uniformly_continuous_alt. now change (∀ W, subset_pt (ufm_preimage f (ufm_preimage g W)) ∊ Φ). Qed.
#[global] Hint Extern 2 (UniformlyContinuous (_ ∘ _)) => simple notypeclasses refine compose_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (UniformContinuity (func_op (_ ∘ _))) => simple notypeclasses refine compose_ufm_cont : typeclass_instances.

Lemma compose_ufm_reflect@{u} {X Y Z:set@{u}} {f:X⇾Y} {g:Y⇾Z}
  `{Φ:Uniformity X} `{Ψ:Uniformity Y} `{Ξ:Uniformity Z}
  `{!UniformReflection f, !UniformReflection g}
  : UniformReflection (g ∘ f).
Proof. intros U.
  pose proof ufm_reflection f U as [V PV].
  pose proof ufm_reflection g V as [W PW].
  exists W. intros x y. rew (PW (f x) (f y)). exact (PV x y).
Qed.
#[global] Hint Extern 2 (UniformReflection (func_op (_ ∘ _))) => simple notypeclasses refine compose_ufm_reflect : typeclass_instances.

Lemma compose_ufm_reflecting@{u} `{@UniformlyReflecting@{u} X Y Φ Ψ f} `{@UniformlyReflecting@{u} Y Z Ψ Ξ g}
  : UniformlyReflecting (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (UniformlyReflecting (_ ∘ _)) => simple notypeclasses refine compose_ufm_reflecting : typeclass_instances.

Lemma ufm_refl_factor@{u} {X Y Z:set@{u}}
  {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z} (f: X ⇾ Y) (g: Y ⇾ Z)
  `{!UniformlyContinuous g}
  : UniformlyReflecting (g ∘ f) → UniformlyReflecting f.
Proof. intros Hgf. split; try exact _. intros U.
  pose proof (ufm_reflection (g ∘ f) U) as [W PW].
  now exists (ufm_preimage g W).
Qed.

Lemma ufm_cont_factor@{u} {X Y Z:set@{u}}
  {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z} (f: X ⇾ Y) (g: Y ⇾ Z)
  `{!UniformlyReflecting g}
  : UniformlyContinuous (g ∘ f) → UniformlyContinuous f.
Proof. intros Hgf. split; try exact _. intros V.
  pose proof (ufm_reflection g V) as [W PW].
  pose proof (ufm_continuity (g ∘ f) W) as [U PU].
  exists U. intros x y. rew (PU x y). exact (PW (f x) (f y)).
Qed.

Lemma compose_ufm_initial@{u} `{@UniformlyInitial@{u} X Y Φ Ψ f} `{@UniformlyInitial@{u} Y Z Ψ Ξ g}
  : UniformlyInitial (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (UniformlyInitial (_ ∘ _)) => simple notypeclasses refine compose_ufm_initial : typeclass_instances.

Lemma compose_ufm_emb@{u} `{@UniformlyEmbedding@{u} X Y Φ Ψ f} `{@UniformlyEmbedding@{u} Y Z Ψ Ξ g}
  : UniformlyEmbedding (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding (_ ∘ _)) => simple notypeclasses refine compose_ufm_emb : typeclass_instances.

(** Abstract reflection pair instance *)

Inductive 𝐔𝐧𝐢𝐟 :=.
#[global] Hint Extern 0 (Fiber 𝐔𝐧𝐢𝐟) => exact Uniformity : typeclass_instances.
#[global] Hint Extern 0 (ObjClass 𝐔𝐧𝐢𝐟) => exact @UniformSpace : typeclass_instances.
#[global] Hint Extern 0 (HomClass 𝐔𝐧𝐢𝐟) => exact @UniformlyContinuous_fun : typeclass_instances.
#[global] Hint Extern 0 (RflClass 𝐔𝐧𝐢𝐟) => exact @UniformlyReflecting_fun : typeclass_instances.
#[global] Hint Extern 0 (IniClass 𝐔𝐧𝐢𝐟) => exact @UniformlyInitial_fun : typeclass_instances.
#[global] Hint Extern 0 (EmbClass 𝐔𝐧𝐢𝐟) => exact @UniformlyEmbedding_fun : typeclass_instances.
#[global] Hint Extern 2 (Fib 𝐔𝐧𝐢𝐟 ?X) => change (Uniformity X) : typeclass_instances.

Definition unif_classes@{u} : ReflectionPairClasses@{u} 𝐔𝐧𝐢𝐟.  Proof. now esplit. Defined.
#[global] Hint Extern 2 (ReflectionPairClasses 𝐔𝐧𝐢𝐟) => exact unif_classes : typeclass_instances.

Lemma unif_construct: Construct 𝐔𝐧𝐢𝐟.
Proof. split.
+ now change (∀ `{@UniformSpace X Φ}, UniformlyContinuous (id_fun X)).
+ now change (∀ `{@UniformlyContinuous X Y Φ Ψ f}, UniformSpace X).
+ now change (∀ `{@UniformlyContinuous X Y Φ Ψ f}, UniformSpace Y).
+ now change (∀ X Y Z Φ Ψ Ξ f g, @UniformlyContinuous X Y Φ Ψ f → @UniformlyContinuous Y Z Ψ Ξ g
                                → UniformlyContinuous (g ∘ f)).
Qed.
#[global] Hint Extern 0 (Construct 𝐔𝐧𝐢𝐟) => exact unif_construct : typeclass_instances.

Lemma unif_rfl_construct: RflConstruct 𝐔𝐧𝐢𝐟.
Proof. split.
+ now change (∀ `{@UniformSpace X Φ}, UniformlyReflecting (id_fun X)).
+ now change (∀ `{@UniformlyReflecting X Y Φ Ψ f}, UniformSpace X).
+ now change (∀ `{@UniformlyReflecting X Y Φ Ψ f}, UniformSpace Y).
+ now change (∀ X Y Z Φ Ψ Ξ f g, @UniformlyReflecting X Y Φ Ψ f → @UniformlyReflecting Y Z Ψ Ξ g
                                → UniformlyReflecting (g ∘ f)).
Qed.
#[global] Hint Extern 0 (RflConstruct 𝐔𝐧𝐢𝐟) => exact unif_rfl_construct : typeclass_instances.

Lemma unif_ini_spec : IniClassSpec 𝐔𝐧𝐢𝐟.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (IniClassSpec 𝐔𝐧𝐢𝐟) => exact unif_ini_spec : typeclass_instances.

Lemma unif_emb_spec : EmbClassSpec 𝐔𝐧𝐢𝐟.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (EmbClassSpec 𝐔𝐧𝐢𝐟) => exact unif_emb_spec : typeclass_instances.

Lemma unif_rfl_pair : ReflectionPair 𝐔𝐧𝐢𝐟.
Proof. esplit; try exact _.
+ change (∀ X Y Z Φ Ψ Ξ f g, @UniformlyReflecting Y Z Ψ Ξ g → @UniformlyContinuous X Z Φ Ξ (g ∘ f)
                            → @UniformlyContinuous X Y Φ Ψ f).
  intros. now apply (ufm_cont_factor f g).
+ change (∀ X Y Z Φ Ψ Ξ f g, @UniformlyContinuous Y Z Ψ Ξ g → @UniformlyReflecting X Z Φ Ξ (g ∘ f)
                            → @UniformlyReflecting X Y Φ Ψ f).
  intros. now apply (ufm_refl_factor f g).
Qed.
#[global] Hint Extern 0 (ReflectionPair 𝐔𝐧𝐢𝐟) => exact unif_rfl_pair : typeclass_instances.


#[global] Hint Extern 0 (FiberMap 𝐔𝐧𝐢𝐟 𝐀𝐓𝐨𝐩) => exact @UniformNeighborhood : typeclass_instances.
Lemma unif_atop_pair_map@{u} : PairMorphism@{u} 𝐔𝐧𝐢𝐟 𝐀𝐓𝐨𝐩 (U:=@UniformNeighborhood@{u}).
Proof. split; try exact _.
+ now change (∀ X Y Φ Ψ f, @UniformlyContinuous X Y Φ Ψ f → Continuous f).
+ now change (∀ X Y Φ Ψ f, @UniformlyReflecting X Y Φ Ψ f → ContinuouslyReflecting f).
Qed.
#[global] Hint Extern 0 (PairMorphism 𝐔𝐧𝐢𝐟 𝐀𝐓𝐨𝐩) => exact unif_atop_pair_map : typeclass_instances.

(** Inverses flip classes *)

Local Open Scope fun_inv_scope.
Lemma invert_ufm_cont `{@UniformlyContinuous X Y Φ Ψ f} `{!Inverse f, !Bijective f}
  : UniformlyReflecting f⁻¹.
Proof. exact (invert_hom (C:=𝐔𝐧𝐢𝐟) (f:=f)). Qed.
#[global] Hint Extern 4 (UniformlyReflecting _⁻¹) => simple notypeclasses refine invert_ufm_cont : typeclass_instances.

Lemma invert_ufm_refl `{@UniformlyReflecting X Y Φ Ψ f} `{!Inverse f, !Bijective f}
  : UniformlyContinuous f⁻¹.
Proof. exact (invert_rfl (C:=𝐔𝐧𝐢𝐟) (f:=f)). Qed.
#[global] Hint Extern 4 (UniformlyContinuous _⁻¹) => simple notypeclasses refine invert_ufm_refl : typeclass_instances.

Lemma invert_ufm_initial `{@UniformlyInitial X Y Φ Ψ f} `{!Inverse f, !Bijective f}
  : UniformlyEmbedding (inverse f).
Proof. exact (invert_ini (C:=𝐔𝐧𝐢𝐟) (f:=f)). Qed.
#[global] Hint Extern 4 (UniformlyEmbedding _⁻¹) => simple notypeclasses refine invert_ufm_initial : typeclass_instances.
#[global] Hint Extern 4 (UniformlyInitial _⁻¹) => simple notypeclasses refine invert_ufm_initial : typeclass_instances.
Local Close Scope fun_inv_scope.

Section ufm_preimage.
  Context `{H:@UniformlyContinuous X Y Φ Ψ f}.
  
  Let inst : UniformSpace Y.  Proof. exact _. Qed.

  Lemma ufm_preimage_lat_mor : Lattice_Morphism (ufm_preimage f).
  Proof. apply alt_Build_Lattice_Morphism; intros U V.
  + exact (preserves_meet (preimage ⟨f, f⟩) _ _).
  + exact (preserves_join (preimage ⟨f, f⟩) _ _).
  Qed.

  Let inst2 : Lattice_Morphism (ufm_preimage f).  Proof. exact ufm_preimage_lat_mor. Qed.
  
  Lemma ufm_preimage_order_preserving : OrderPreserving (ufm_preimage f).
  Proof. exact (meet_sl_mor_preserving _). Qed.

  Lemma ufm_preimage_inv U : ufm_preimage f (U⁻¹) = (ufm_preimage f U)⁻¹.
  Proof. refl. Qed.

  Lemma ufm_preimage_compose U V : ufm_preimage f U ∙ ufm_preimage f V ≤ ufm_preimage f (U ∙ V).
  Proof. intros [a c].
    change ((∐ b, (f a, f b) ∊ U ⊠ (f b, f c) ∊ V) ⊸ ∐ y, (f a, y) ∊ U ⊠ (y, f c) ∊ V).
    rew <-aex_adj; intros b. now rew <-(aex_ub _ (f b)).
  Qed.

End ufm_preimage.
Arguments ufm_preimage_inv {_ _ _ _} f {_} U.
Arguments ufm_preimage_compose {_ _ _ _} f {_} U V.
#[global] Hint Extern 2 (Lattice_Morphism (ufm_preimage _)) => simple notypeclasses refine ufm_preimage_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (ufm_preimage _)) => simple notypeclasses refine ufm_preimage_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (MeetSemiLattice_Morphism (ufm_preimage _)) => simple notypeclasses refine ufm_preimage_lat_mor : typeclass_instances.
#[global] Hint Extern 2 (OrderPreserving (ufm_preimage _)) => simple notypeclasses refine ufm_preimage_order_preserving : typeclass_instances.


(** Topological notions *)
Lemma uniform_interior `{Φ:Uniformity X}
  : interior = set:(λ A:𝒫 X, { x:X | ∐ (U:Φ), ∏ y, near U x y ⊸ y ∊ A}).
Proof. refl. Qed.

Definition uniform_interior_applied `{Φ:Uniformity X} {A}
  : interior A = { x:X | ∐ (U:Φ), ∏ y, near U x y ⊸ y ∊ A}
:= uniform_interior A.

Definition uniform_interior_applied2 `{Φ:Uniformity X} {A} {x}
  : x ∊ interior A ⧟ ∐ (U:Φ), ∏ y, near U x y ⊸ y ∊ A
:= uniform_interior A x.


Lemma uniform_closure `{Φ:Uniformity X}
  : closure = set:(λ A:𝒫 X, { x:X | ∏ (U:Φ), ∐ y, near U x y ⊠ y ∊ A}).
Proof. refl. Qed.

Definition uniform_closure_applied `{Φ:Uniformity X} {A}
  : closure A = { x:X | ∏ (U:Φ), ∐ y, near U x y ⊠ y ∊ A}
:= uniform_closure A.

Definition uniform_closure_applied2 `{Φ:Uniformity X} {A} {x}
  : x ∊ closure A ⧟ ∏ (U:Φ), ∐ y, near U x y ⊠ y ∊ A
:= uniform_closure A x.


Lemma uniform_dense `{Φ:Uniformity X}
  : dense = { A : 𝒫 X | ∏ (x:X) (U:Φ), ∐ y, near U x y ⊠ y ∊ A }.
Proof. intros A.
  change ((∏ (x:X), (∏ (U:Φ), ∐ y, near U x y ⊠ y ∊ A) ⧟ 𝐓)
         ⧟ ∏ (x:X) (U:Φ), ∐ y, near U x y ⊠ y ∊ A).
  now simplify.
Qed.

Definition uniform_dense_applied `{Φ:Uniformity X} A
  : dense A ⧟ ∏ (x:X) (U:Φ), ∐ y, near U x y ⊠ y ∊ A
:= uniform_dense A.

Lemma uniform_Dense_iff@{u} {X Y:set@{u}} `{@UniformSpace Y Φ} {f:X ⇾ Y}
  : Dense f ↔ ∏ (y:Y) (U:Φ), ∐ x, near U y (f x).
Proof. rew (Dense_alt _), (uniform_dense_applied _). split.
  * intros P y U. pose proof (P y U) as [y' [Py' [x Ex]]]. exists x. now rew Ex.
  * intros P y U. pose proof (P y U) as [x Px]. now exists (f x).
Qed.

Lemma uniform_dense_range@{u} {X Y:set@{u}} `{@UniformSpace Y Φ} (f:X ⇾ Y) : ∀ `{!Dense f} (y:Y) (U:Φ), ∐ x, near U y (f x).
Proof. apply uniform_Dense_iff. Qed.

(** Thicken *)

Section thicken.
  Import thicken_notation.
  Context `{@UniformSpace X Φ}.
  
  Lemma closure_sub_thicken (U:Φ) (A:𝒫 X) : closure A ⊆ U.[A].
  Proof. intros x. rew uniform_closure_applied2.
    rew (all_lb _ U⁻¹). rew <-aex_adj; intros y.
    change ((y, x) ∊ U ⊠ y ∊ A ⊸ ∐ y, y ∊ A ⊠ (y, x) ∊ U).
    rew <-(aex_ub _ y). tautological.
  Qed.
  
  Lemma thicken_sub_interior (U:Φ) (A B:𝒫 X) : U.[A] ⊆ B ⊸ A ⊆ interior B.
  Proof. change (?a ≤ ?b) with (∏ x, x ∊ a ⊸ x ∊ b).
    rew <-all_adj; intros x.
    rew uniform_interior_applied2. rew <-(aex_ub _ U).
    rew <-(aprod_adj _ _ _). rew <-all_adj; intros y.
    rew (all_lb _ y). change (y ∊ U.[A]) with (∐ x, x ∊ A ⊠ (x, y) ∊ U).
    rew <-(aex_ub _ x). tautological.
  Qed.
End thicken.

Section image_thicken.
  Import thicken_notation.

  Lemma image_thicken_le@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X ⇾ Y)
    (U:Φ) (V:Ψ) (K : 𝒫 X) : U ⊆ ⟨f,f⟩* V ⊸ f⁎ (U.[K]) ⊆ V.[f⁎ K].
  Proof. change ( (∏ p, p ∊ U ⊸ ⟨f,f⟩ p ∊ V) ⊸
      ∏ z, (∐ y', f y' = z ⊠ (∐ k', k' ∊ K ⊠ (k', y') ∊ U)) ⊸ ∐ w, w ∊ f⁎ K ⊠ (w, z) ∊ V).
    rew <-all_adj; intros z. rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj; intros y'.
    rew aex_frob_l, aex_frob_l, <-aex_adj; intros k'.
    rew <-(aex_ub _ (f k')), <-(image_el f _ _).
    rew (all_lb _ (k', y')). change ( ⟨f,f⟩ (k', y') ) with ((f k', f y')).
    rew (is_fun set:(λ y, (f k', y) ∊ V) (f y') z : f y' = z ⊸ (f k', f y') ∊ V ⧟ (f k', z) ∊ V ).
    tautological.
  Qed.
  
  Lemma image_thicken_uc_le `{@UniformlyContinuous X Y Φ Ψ f} (V:Ψ) (K:𝒫 X)
    : f⁎ (ufm_preimage f V).[K] ⊆ V.[f⁎ K].
  Proof. now apply image_thicken_le. Qed.

  (** Dually, thickened preimages land in preimages of thickenings. *)
  Lemma preimage_thicken_le@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X ⇾ Y)
    (U:Φ) (V:Ψ) (B : 𝒫 Y) : U ⊆ ⟨f,f⟩* V ⊸ U.[f* B] ⊆ f* (V.[B]).
  Proof. change ( (∏ p, p ∊ U ⊸ ⟨f,f⟩ p ∊ V) ⊸
      ∏ y, (∐ x, f x ∊ B ⊠ (x, y) ∊ U) ⊸ ∐ w, w ∊ B ⊠ (w, f y) ∊ V).
    rew <-all_adj; intros y. rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj; intros x.
    rew <-(aex_ub _ (f x)). rew (all_lb _ (x, y)).
    change ( ⟨f,f⟩ (x, y) ) with ((f x, f y)).
    tautological.
  Qed.

  Lemma preimage_thicken_uc_le `{@UniformlyContinuous X Y Φ Ψ f} (V:Ψ) (B:𝒫 Y)
    : (ufm_preimage f V).[f* B] ⊆ f* (V.[B]).
  Proof. now apply preimage_thicken_le. Qed.

  (** With a reflection certificate instead, preimages of thickened images
      land in thickenings ([ufm_reflection_alt] provides a certificate for
      every [U] when [f] is uniformly reflecting). *)
  Lemma preimage_thicken_image_le@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X ⇾ Y)
    (U:Φ) (W:Ψ) (B : 𝒫 X) : ⟨f,f⟩* W ⊆ U ⊸ f* (W.[f⁎ B]) ⊆ U.[B].
  Proof. change ( (∏ p, ⟨f,f⟩ p ∊ W ⊸ p ∊ U) ⊸
      ∏ x, (∐ y', (∐ b, f b = y' ⊠ b ∊ B) ⊠ (y', f x) ∊ W) ⊸ ∐ b, b ∊ B ⊠ (b, x) ∊ U).
    rew <-all_adj; intros x. rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj; intros y'.
    rew aex_frob_r, aex_frob_l, <-aex_adj; intros b. rew <-(aex_ub _ b).
    rew (all_lb _ (b, x)). change ( ⟨f,f⟩ (b, x) ) with ((f b, f x)).
    rew (is_fun set:(λ z, (z, f x) ∊ W) (f b) y' : f b = y' ⊸ (f b, f x) ∊ W ⧟ (y', f x) ∊ W ).
    tautological.
  Qed.

  Local Open Scope subset_scope.

  (** Uniform reflection transports a margin along the image. *)
  Lemma image_reflect_apart@{u} `{@UniformlyReflecting@{u} X Y Φ Ψ f} (U : Φ) (K B : 𝒫 X)
    : U.[K] ⊆ B ᗮ ⊸ ∐ W:Ψ, W.[f⁎ K] ⊆ (f⁎ B)ᗮ.
  Proof.
    pose proof ufm_reflection_alt f (U⁻¹) as [W PW].
    rew <-(aex_ub _ (W⁻¹)).
    rew [(thicken_apart_swap U K B) | (thicken_apart_swap_alt W _ _)].
    rew (image_preimage_adj f K _).
    change (K ⊆ U⁻¹.[B] ᗮ ⊸ K ⊆ (f* (W.[f⁎ B]))ᗮ).
    rew (preimage_thicken_image_le f U⁻¹ W B) in PW.
    now rew <-PW.
  Qed.
End image_thicken.
Arguments image_thicken_uc_le {_ _ _ _} f {_} V K.
Arguments preimage_thicken_uc_le {_ _ _ _} f {_} V B.
Arguments image_reflect_apart {_ _ _ _} f {_} U K B.

Local Open Scope subset_scope.

Local Abbreviation cl := closure.
Local Abbreviation int := interior.

Lemma dense_interior_closure_unit@{u} {X Y:set@{u}}
  `{@UniformSpace Y Ψ} (f:X ⇾ Y) `{!Dense f} (A:𝒫 Y)
  : int A ⊆ cl (f⁎ (f* A)).
Proof. intros y. rew uniform_interior_applied2.
  rew <-aex_adj; intros U.
  rew uniform_closure_applied2, <-all_adj; intros V.
  pose proof uniform_dense_range f y (U ⊓ V) as [x Hx].
  rew [(all_lb _ (f x)) | <-(aex_ub _ (f x))].
  rew <-(image_el _ _ _); change (x ∊ f* A) with (f x ∊ A).
  enough (near U y (f x) ⊠ near V y (f x)) as G by (revert G; tautological).
  now rew [<-(meet_lb_l U V)|<-(meet_lb_r U V)].
Qed.

Lemma dense_open_restriction@{u} {X Y:set@{u}} `{@UniformSpace Y Ψ} (f:X ⇾ Y) `{!Dense f}
  (S:𝒫 Y) {HS:open S} : cl (f⁎ (f* S)) = cl S.
Proof. apply le_antisym; split.
+ now rew (image_preimage_counit _ _).
+ rew <-(idempotent_alt closure (f⁎ (f* S))).
  rew <-(order_preserving closure _ _), <-(dense_interior_closure_unit _ _).
  now rew (HS : int S = S).
Qed.

Import thicken_notation.

Lemma dense_image_preimage_unit@{u}  {X Y:set@{u}} `{@UniformSpace Y Ψ} (f:X ⇾ Y) `{!Dense f}
  (S:𝒫 Y) U : S ⊆ cl (f⁎ (f* U.[S])).
Proof. now rew <-(dense_interior_closure_unit _ _), <-(thicken_sub_interior U _ _). Qed.


Lemma ufm_dense_image_closure_test@{u} {X Y:set@{u}} `{@UniformSpace Y Ψ} (f:X ⇾ Y) `{!Dense f}
  (V:Ψ) (P:Ω) (S:𝒫 X) (y:Y) : (∀ x, near V y (f x) → (P ⊸ x ∊ S)) → (P ⊸ y ∊ cl (f⁎ S)) .
Proof. intros Hy. rew uniform_closure_applied2. rew <-all_adj; intros W.
  pose proof (uniform_dense_range f y (V ⊓ W)) as [x Hx].
  rew <-(aex_ub _ (f x)).
  rew [<-(meet_lb_r V W)|<-(image_el f _ _)].
  rew (aprod_true_l Hx).
  apply Hy.
  now rew <-(meet_lb_l V W).
Qed.

