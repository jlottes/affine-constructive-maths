Require Import abstract_algebra theory.common_props theory.groups.
Require Import sprop logic.aprop.
Require Import easy rewrite quote.base.


(** [Ω] is a [BoundedDistributiveLattice] *)
Global Hint Extern 2 (Bottom AProp_set) => exact afalse : typeclass_instances.
Global Hint Extern 2 (Top AProp_set) => exact atrue : typeclass_instances.
Global Hint Extern 2 (Meet AProp_set) => eexact (aand_fun ∘ tensor_to_prod _ _) : typeclass_instances.
Global Hint Extern 2 (Join AProp_set) => eexact (aor_fun ∘ tensor_to_prod _ _) : typeclass_instances.

Lemma AProp_lattice : BoundedDistributiveLattice Ω.
Proof. tautological. Qed.
Global Hint Extern 2 (BoundedDistributiveLattice AProp_set) => refine AProp_lattice : typeclass_instances.
Global Hint Extern 2 (BoundedLattice AProp_set) => refine AProp_lattice : typeclass_instances.
Global Hint Extern 2 (DistributiveLattice AProp_set) => refine AProp_lattice : typeclass_instances.
Global Hint Extern 2 (Lattice AProp_set) => refine AProp_lattice : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice AProp_set) => refine AProp_lattice : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice AProp_set) => refine AProp_lattice : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice AProp_set) => refine AProp_lattice : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice AProp_set) => refine AProp_lattice : typeclass_instances.

Lemma anot_lat_mor : BoundedLattice_Flip_Morphism anot.
Proof. split; try exact _; tautological. Qed.
Global Hint Extern 2 (BoundedLattice_Flip_Morphism anot) => refine anot_lat_mor : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice_Flip_Morphism anot) => refine anot_lat_mor : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice_Flip_Morphism anot) => refine anot_lat_mor : typeclass_instances.
Global Hint Extern 2 (Lattice_Flip_Morphism anot) => refine anot_lat_mor : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice_Flip_Morphism anot) => refine anot_lat_mor : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Flip_Morphism anot) => refine anot_lat_mor : typeclass_instances.


Definition alt_Build_MeetSemiLattice : ∀ `{Meet L},
   @Associative L (⊓)
 → Commutative (X:=L) (⊓)
 → @BinaryIdempotent L (⊓)
 → MeetSemiLattice L
:= @alt_Build_SemiLattice.

Definition alt_Build_JoinSemiLattice : ∀ `{Join L},
   @Associative L (⊔)
 → Commutative (X:=L) (⊔)
 → @BinaryIdempotent L (⊔)
 → JoinSemiLattice L
:= @alt_Build_SemiLattice.

Definition meet_ass `{MeetSemiLattice L} : Associative (X:=L) (⊓) := _.
Definition join_ass `{JoinSemiLattice L} : Associative (X:=L) (⊔) := _.
Definition meet_com `{MeetSemiLattice L} : Commutative (X:=L) (⊓) := _.
Definition join_com `{JoinSemiLattice L} : Commutative (X:=L) (⊔) := _.
Definition meet_idm `{MeetSemiLattice L} : BinaryIdempotent (X:=L) (⊓) := _.
Definition join_idm `{JoinSemiLattice L} : BinaryIdempotent (X:=L) (⊔) := _.
Global Hint Extern 2 (Associative (⊓)) => simple notypeclasses refine meet_ass : typeclass_instances.
Global Hint Extern 2 (Associative (⊔)) => simple notypeclasses refine join_ass : typeclass_instances.
Global Hint Extern 2 (Commutative (⊓)) => simple notypeclasses refine meet_com : typeclass_instances.
Global Hint Extern 2 (Commutative (⊔)) => simple notypeclasses refine join_com : typeclass_instances.
Global Hint Extern 2 (BinaryIdempotent (⊓)) => simple notypeclasses refine meet_idm : typeclass_instances.
Global Hint Extern 2 (BinaryIdempotent (⊔)) => simple notypeclasses refine join_idm : typeclass_instances.

Definition alt_Build_BoundedMeetSemiLattice : ∀ `{Meet L} `{Top L},
   @Associative L (⊓)
 → Commutative (X:=L) (⊓)
 → @BinaryIdempotent L (⊓)
 → LeftIdentity  (X:=L) (⊓) ⊤
 → BoundedMeetSemiLattice L
:= @alt_Build_BoundedSemiLattice.

Definition alt_Build_BoundedJoinSemiLattice : ∀ `{Join L} `{Bottom L},
   @Associative L (⊔)
 → Commutative (X:=L) (⊔)
 → @BinaryIdempotent L (⊔)
 → LeftIdentity  (X:=L) (⊔) ⊥
 → BoundedJoinSemiLattice L
:= @alt_Build_BoundedSemiLattice.

Definition meet_top_l `{BoundedMeetSemiLattice L} : LeftIdentity (X:=L) (⊓) ⊤ := _.
Definition meet_top_r `{BoundedMeetSemiLattice L} : RightIdentity (X:=L) (⊓) ⊤ := _.
Definition join_bot_l `{BoundedJoinSemiLattice L} : LeftIdentity (X:=L) (⊔) ⊥ := _.
Definition join_bot_r `{BoundedJoinSemiLattice L} : RightIdentity (X:=L) (⊔) ⊥ := _.
Global Hint Extern 2 (LeftIdentity  (⊓) _) => simple notypeclasses refine meet_top_l : typeclass_instances.
Global Hint Extern 2 (RightIdentity (⊓) _) => simple notypeclasses refine meet_top_r : typeclass_instances.
Global Hint Extern 2 (LeftIdentity  (⊔) _) => simple notypeclasses refine join_bot_l : typeclass_instances.
Global Hint Extern 2 (RightIdentity (⊔) _) => simple notypeclasses refine join_bot_r : typeclass_instances.

Definition bounded_meet_sl_is_sl `{BoundedMeetSemiLattice L} : MeetSemiLattice L := _.
Definition bounded_join_sl_is_sl `{BoundedJoinSemiLattice L} : JoinSemiLattice L := _.
Coercion bounded_meet_sl_is_sl : BoundedMeetSemiLattice >-> MeetSemiLattice.
Coercion bounded_join_sl_is_sl : BoundedJoinSemiLattice >-> JoinSemiLattice.

Coercion top_inhabited `{Top M} : Inhabited M.  Proof. now exists ⊤. Defined.
Coercion bounded_meet_sl_inhabited `{BoundedMeetSemiLattice M} : Inhabited M := _.
Coercion bottom_inhabited `{Bottom M} : Inhabited M.  Proof. now exists ⊥. Defined.
Coercion bounded_join_sl_inhabited `{BoundedMeetSemiLattice M} : Inhabited M := _.

Definition join_meet_distr_r `{DistributiveLattice L} : RightDistribute (X:=L) (⊔) (⊓) := right_distr_from_left.
Definition meet_join_distr_r `{DistributiveLattice L} : RightDistribute (X:=L) (⊓) (⊔) := right_distr_from_left.
Global Hint Extern 2 (RightDistribute (⊔) (⊓)) => simple notypeclasses refine join_meet_distr_r : typeclass_instances.
Global Hint Extern 2 (RightDistribute (⊓) (⊔)) => simple notypeclasses refine meet_join_distr_r : typeclass_instances.

Local Notation "X 'ᵒᵖ'" := (Order_op X) (at level 1, format "X 'ᵒᵖ'").
Definition MeetSemiLattice_op `{H:JoinSemiLattice L} : MeetSemiLattice (L ᵒᵖ) := H.
Definition JoinSemiLattice_op `{H:MeetSemiLattice L} : JoinSemiLattice (L ᵒᵖ) := H.
Global Hint Extern 2 (MeetSemiLattice (_ ᵒᵖ)) => simple notypeclasses refine MeetSemiLattice_op : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice (_ ᵒᵖ)) => simple notypeclasses refine JoinSemiLattice_op : typeclass_instances.
Definition BoundedMeetSemiLattice_op `{H:BoundedJoinSemiLattice L} : BoundedMeetSemiLattice (L ᵒᵖ) := H.
Definition BoundedJoinSemiLattice_op `{H:BoundedMeetSemiLattice L} : BoundedJoinSemiLattice (L ᵒᵖ) := H.
Global Hint Extern 2 (BoundedMeetSemiLattice (_ ᵒᵖ)) => simple notypeclasses refine BoundedMeetSemiLattice_op : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice (_ ᵒᵖ)) => simple notypeclasses refine BoundedJoinSemiLattice_op : typeclass_instances.
Lemma Lattice_op `{H : Lattice L} : Lattice (L ᵒᵖ).  Proof. destruct H. now split. Qed.
Global Hint Extern 2 (Lattice (_ ᵒᵖ)) => simple notypeclasses refine Lattice_op : typeclass_instances.
Lemma DistributiveLattice_op `{H : DistributiveLattice L} : DistributiveLattice (L ᵒᵖ).  Proof. destruct H. now split. Qed.
Global Hint Extern 2 (DistributiveLattice (_ ᵒᵖ)) => simple notypeclasses refine DistributiveLattice_op : typeclass_instances.

Lemma BoundedLattice_op `{H : BoundedLattice L} : BoundedLattice (L ᵒᵖ).  Proof. destruct H. now split. Qed.
Global Hint Extern 2 (BoundedLattice (_ ᵒᵖ)) => simple notypeclasses refine BoundedLattice_op : typeclass_instances.
Lemma BoundedDistributiveLattice_op `{H : BoundedDistributiveLattice L} : BoundedDistributiveLattice (L ᵒᵖ).  Proof. destruct H. now split. Qed.
Global Hint Extern 2 (BoundedDistributiveLattice (_ ᵒᵖ)) => simple notypeclasses refine BoundedDistributiveLattice_op : typeclass_instances.

Lemma alt_Build_BoundedLattice `{Lattice L} `{Top L} `{Bottom L} :
  LeftIdentity (X:=L) (⊓) ⊤ → LeftIdentity (X:=L) (⊔) ⊥ → BoundedLattice L.
Proof. intros. split; try exact _; [ now apply alt_Build_BoundedMeetSemiLattice | now apply alt_Build_BoundedJoinSemiLattice ]. Qed.

Lemma alt_Build_DistributiveLattice `{Lattice L} :
  LeftDistribute (X:=L) (⊔) (⊓) → DistributiveLattice L.
Proof. intro. pose proof right_distr_from_left : RightDistribute (X:=L) (⊔) (⊓).
  split; trivial; hnf; intros x y z.
  rew (distribute_l _ _ _ x z).
  rew (distribute_r _ _ x y x).
  rew (binary_idempotency _ x).
  rew (commutativity (⊔) y x).
  rew (meet_join_absorption _ _).
  rew <-(meet_join_absorption x z) at 1.
  rew <-(associativity _ _ _ _).
  now rew <-(distribute_r _ _ _ _ _).
Qed.

Lemma alt_Build_BoundedDistributiveLattice `{BoundedLattice L} :
  LeftDistribute (X:=L) (⊔) (⊓) → BoundedDistributiveLattice L.
Proof. intro. split; [now apply alt_Build_DistributiveLattice | exact _]. Qed.

Lemma distribute_alt `{DistributiveLattice L} (x y z : L) :
  (x ⊓ y) ⊔ (x ⊓ z) ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) ⊓ (y ⊔ z).
Proof.
  rew (distribute_r _ _ x y (x ⊓ z)), (join_meet_absorption _ _).
  rew (distribute_r _ _ _ _ (y ⊓ z)).
  rew (distribute_l _ _ x y z).
  rew (commutativity _ y (x ⊓ z)), <-(associativity _ _ y _).
  rew (join_meet_absorption _ _).
  rew (distribute_r _ _ x z y).
  rew (commutativity (⊔) z y).
  rew (commutativity _ (x ⊔ y) (x ⊔ z)).
  rew (associativity _ _ _ _).
  rew <-(associativity _ (x ⊔ z) _ _) at 1.
  now rew (binary_idempotency _ _).
Qed.


Canonical Structure MeetSemiLattice_Morphism_fun {X Y mX mY}
  := make_fun_alt (@MeetSemiLattice_Morphism X Y mX mY) (@SemiGroup_Morphism_fun X Y mX mY).

Canonical Structure JoinSemiLattice_Morphism_fun {X Y jX jY}
  := make_fun_alt (@JoinSemiLattice_Morphism X Y jX jY) (@SemiGroup_Morphism_fun X Y jX jY).

Canonical Structure BoundedMeetSemiLattice_Morphism_fun {X Y mX tX mY tY}
  := make_fun_alt (@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY) (@Monoid_Morphism_fun X Y mX tX mY tY).

Canonical Structure BoundedJoinSemiLattice_Morphism_fun {X Y jX bX jY bY}
  := make_fun_alt (@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY) (@Monoid_Morphism_fun X Y jX bX jY bY).

Lemma Lattice_Morphism_proper_impl {X Y mX jX mY jY} (f g : X ⇾ Y)
  : f = g → impl (@Lattice_Morphism X Y mX jX mY jY f, Lattice_Morphism g).
Proof. intros E H; split; try exact _; now rew <-E. Qed.
Canonical Structure Lattice_Morphism_fun {X Y mX jX mY jY} :=
  make_weak_spred (@Lattice_Morphism X Y mX jX mY jY) Lattice_Morphism_proper_impl.

Lemma BoundedLattice_Morphism_proper_impl {X Y mX jX tX bX mY jY tY bY} (f g : X ⇾ Y)
  : f = g → impl (@BoundedLattice_Morphism X Y mX jX tX bX mY jY tY bY f, BoundedLattice_Morphism g).
Proof. intros E H; split; try exact _; now rew <-E. Qed.
Canonical Structure BoundedLattice_Morphism_fun {X Y mX jX tX bX mY jY tY bY} :=
  make_weak_spred (@BoundedLattice_Morphism X Y mX jX tX bX mY jY tY bY) BoundedLattice_Morphism_proper_impl.


Coercion bounded_msl_mor_msl_mor `{H:@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY f} : MeetSemiLattice_Morphism f := H.
Coercion bounded_jsl_mor_jsl_mor `{H:@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY f} : JoinSemiLattice_Morphism f := H.
Coercion bounded_latmor_latmor `{H:@BoundedLattice_Morphism X Y mX jX tX bX mY jY tY bY f} : Lattice_Morphism f.
Proof. split; try exact _. exact (bounded_latmor_b _ H). Qed.

Coercion bounded_msl_flip_mor_msl_flip_mor `{H:@BoundedMeetSemiLattice_Flip_Morphism X Y mX tX jY bY f} : MeetSemiLattice_Flip_Morphism f := H.
Coercion bounded_jsl_flip_mor_jsl_flip_mor `{H:@BoundedJoinSemiLattice_Flip_Morphism X Y jX bX mY tY f} : JoinSemiLattice_Flip_Morphism f := H.
Coercion bounded_latmor_flip_latmor_flip `{H:@BoundedLattice_Flip_Morphism X Y mX jX tX bX mY jY tY bY f} : Lattice_Flip_Morphism f.
Proof. split; try exact _. exact (bounded_latmor_b _ H). Qed.

Definition preserves_meet `{@MeetSemiLattice_Morphism X Y mX mY f} : ∀ x y, f (x ⊓ y) = f x ⊓ f y := preserves_sg_op (f:MeetSemigroupOps _ ⇾ MeetSemigroupOps _).
Definition preserves_join `{@JoinSemiLattice_Morphism X Y jX jY f} : ∀ x y, f (x ⊔ y) = f x ⊔ f y := preserves_sg_op (f:JoinSemigroupOps _ ⇾ JoinSemigroupOps _).
Arguments preserves_meet {_ _ _ _} f {_} x y.
Arguments preserves_join {_ _ _ _} f {_} x y.

Definition preserves_meet_flip `{@MeetSemiLattice_Flip_Morphism X Y mX jY f} : ∀ x y, f (x ⊓ y) = f x ⊔ f y := preserves_sg_op (f:MeetSemigroupOps _ ⇾ JoinSemigroupOps _).
Definition preserves_join_flip `{@JoinSemiLattice_Flip_Morphism X Y jX mY f} : ∀ x y, f (x ⊔ y) = f x ⊓ f y := preserves_sg_op (f:JoinSemigroupOps _ ⇾ MeetSemigroupOps _).
Arguments preserves_meet_flip {_ _ _ _} f {_} x y.
Arguments preserves_join_flip {_ _ _ _} f {_} x y.

Coercion BoundedMeetSemiLattice_Morphism_pointed `{@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY f}
  : Top_Pointed_Morphism f := monmor_pointed f _.
Coercion BoundedJoinSemiLattice_Morphism_pointed `{@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY f}
  : Bottom_Pointed_Morphism f := monmor_pointed f _.


Coercion latmor_meet_sl_mor_flip `{H:@Lattice_Flip_Morphism X Y mX jX mY jY f} : MeetSemiLattice_Flip_Morphism f := latmor_meet_sl_mor _ _.
Coercion latmor_join_sl_mor_flip `{H:@Lattice_Flip_Morphism X Y mX jX mY jY f} : JoinSemiLattice_Flip_Morphism f := latmor_join_sl_mor _ _.
Coercion bounded_latmor_meet_flip `{H:@BoundedLattice_Flip_Morphism X Y mX jX tX bX mY jY tY bY f} : BoundedMeetSemiLattice_Flip_Morphism f := bounded_latmor_meet _ _.
Coercion bounded_latmor_join_flip `{H:@BoundedLattice_Flip_Morphism X Y mX jX tX bX mY jY tY bY f} : BoundedJoinSemiLattice_Flip_Morphism f := bounded_latmor_join _ _.

Definition id_meetsl_mor `{MeetSemiLattice L} : MeetSemiLattice_Morphism (id_fun L) := id_semigroup_mor (G:=MeetSemigroupOps L).
Definition id_joinsl_mor `{JoinSemiLattice L} : JoinSemiLattice_Morphism (id_fun L) := id_semigroup_mor (G:=JoinSemigroupOps L).
Global Hint Extern 2 (MeetSemiLattice_Morphism (id_fun _)) => simple notypeclasses refine id_meetsl_mor : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Morphism (id_fun _)) => simple notypeclasses refine id_joinsl_mor : typeclass_instances.

Definition id_bounded_meetsl_mor `{BoundedMeetSemiLattice L} : BoundedMeetSemiLattice_Morphism (id_fun L) := id_monoid_mor (M:=MeetSemigroupOps L).
Definition id_bounded_joinsl_mor `{BoundedJoinSemiLattice L} : BoundedJoinSemiLattice_Morphism (id_fun L) := id_monoid_mor (M:=JoinSemigroupOps L).
Global Hint Extern 2 (BoundedMeetSemiLattice_Morphism (id_fun _)) => simple notypeclasses refine id_bounded_meetsl_mor : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice_Morphism (id_fun _)) => simple notypeclasses refine id_bounded_joinsl_mor : typeclass_instances.

Lemma id_lattice_mor `{Lattice L} : Lattice_Morphism (id_fun L).  Proof. now split. Qed.
Global Hint Extern 2 (Lattice_Morphism (id_fun _)) => simple notypeclasses refine id_lattice_mor : typeclass_instances.

Lemma id_bounded_lattice_mor `{BoundedLattice L} : BoundedLattice_Morphism (id_fun L).  Proof. now split. Qed.
Global Hint Extern 2 (BoundedLattice_Morphism (id_fun _)) => simple notypeclasses refine id_bounded_lattice_mor : typeclass_instances.

Definition compose_meetsl_mor@{u} : ∀ {X Y Z:set@{u}} {op₁ op₂ op₃} {g f},
  @MeetSemiLattice_Morphism X Y op₁ op₂ f → @MeetSemiLattice_Morphism Y Z op₂ op₃ g
  → MeetSemiLattice_Morphism (g ∘ f)
:= @compose_semigroup_mor.
Global Hint Extern 2 (MeetSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_meetsl_mor _ _) : typeclass_instances.

Definition compose_joinsl_mor@{u} : ∀ {X Y Z:set@{u}} {op₁ op₂ op₃} {g f},
  @JoinSemiLattice_Morphism X Y op₁ op₂ f → @JoinSemiLattice_Morphism Y Z op₂ op₃ g
  → JoinSemiLattice_Morphism (g ∘ f)
:= @compose_semigroup_mor.
Global Hint Extern 2 (JoinSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_joinsl_mor _ _) : typeclass_instances.

Definition compose_bounded_meetsl_mor@{u} : ∀ {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedMeetSemiLattice_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedMeetSemiLattice_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedMeetSemiLattice_Morphism (g ∘ f)
:= @compose_monoid_mor.
Global Hint Extern 2 (BoundedMeetSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_meetsl_mor _ _) : typeclass_instances.

Definition compose_bounded_joinsl_mor@{u} : ∀ {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedJoinSemiLattice_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedJoinSemiLattice_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedJoinSemiLattice_Morphism (g ∘ f)
:= @compose_monoid_mor.
Global Hint Extern 2 (BoundedJoinSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_joinsl_mor _ _) : typeclass_instances.

Lemma compose_lattice_mor@{u} {X Y Z:set@{u}} {m₁ j₁} {m₂ j₂} {m₃ j₃} {g f} :
  @Lattice_Morphism X Y m₁ j₁ m₂ j₂ f → @Lattice_Morphism Y Z m₂ j₂ m₃ j₃ g
  → Lattice_Morphism (g ∘ f).
Proof. now split. Qed.
Global Hint Extern 2 (Lattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_lattice_mor _ _) : typeclass_instances.

Lemma compose_bounded_lattice_mor@{u} {X Y Z:set@{u}} {m₁ j₁ t₁ b₁} {m₂ j₂ t₂ b₂} {m₃ j₃ t₃ b₃} {g f} :
  @BoundedLattice_Morphism X Y m₁ j₁ t₁ b₁ m₂ j₂ t₂ b₂ f → @BoundedLattice_Morphism Y Z m₂ j₂ t₂ b₂ m₃ j₃ t₃ b₃ g
  → BoundedLattice_Morphism (g ∘ f).
Proof. now split. Qed.
Global Hint Extern 2 (BoundedLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_lattice_mor _ _) : typeclass_instances.

(** Composition with contravariant (flip) morphisms — the lattice mirror of
    the OrderPreservingFlip composition table in orders/maps.v.  The flip
    classes are the straight classes at the op-order codomain, so each
    semilattice entry is the semigroup/monoid composition read at the
    transported instances. *)

Definition compose_meetsl_mor_flip@{u} : ∀ {X Y Z:set@{u}} {op₁ op₂ op₃} {g f},
  @MeetSemiLattice_Flip_Morphism X Y op₁ op₂ f → @JoinSemiLattice_Flip_Morphism Y Z op₂ op₃ g
  → MeetSemiLattice_Morphism (g ∘ f)
:= @compose_semigroup_mor.

Definition compose_joinsl_mor_flip@{u} : ∀ {X Y Z:set@{u}} {op₁ op₂ op₃} {g f},
  @JoinSemiLattice_Flip_Morphism X Y op₁ op₂ f → @MeetSemiLattice_Flip_Morphism Y Z op₂ op₃ g
  → JoinSemiLattice_Morphism (g ∘ f)
:= @compose_semigroup_mor.

Definition compose_meetsl_flip_mor_l@{u} : ∀ {X Y Z:set@{u}} {op₁ op₂ op₃} {g f},
  @MeetSemiLattice_Morphism X Y op₁ op₂ f → @MeetSemiLattice_Flip_Morphism Y Z op₂ op₃ g
  → MeetSemiLattice_Flip_Morphism (g ∘ f)
:= @compose_semigroup_mor.

Definition compose_meetsl_flip_mor_r@{u} : ∀ {X Y Z:set@{u}} {op₁ op₂ op₃} {g f},
  @MeetSemiLattice_Flip_Morphism X Y op₁ op₂ f → @JoinSemiLattice_Morphism Y Z op₂ op₃ g
  → MeetSemiLattice_Flip_Morphism (g ∘ f)
:= @compose_semigroup_mor.

Definition compose_joinsl_flip_mor_l@{u} : ∀ {X Y Z:set@{u}} {op₁ op₂ op₃} {g f},
  @JoinSemiLattice_Morphism X Y op₁ op₂ f → @JoinSemiLattice_Flip_Morphism Y Z op₂ op₃ g
  → JoinSemiLattice_Flip_Morphism (g ∘ f)
:= @compose_semigroup_mor.

Definition compose_joinsl_flip_mor_r@{u} : ∀ {X Y Z:set@{u}} {op₁ op₂ op₃} {g f},
  @JoinSemiLattice_Flip_Morphism X Y op₁ op₂ f → @MeetSemiLattice_Morphism Y Z op₂ op₃ g
  → JoinSemiLattice_Flip_Morphism (g ∘ f)
:= @compose_semigroup_mor.

Definition compose_bounded_meetsl_mor_flip@{u} : ∀ {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedMeetSemiLattice_Flip_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedJoinSemiLattice_Flip_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedMeetSemiLattice_Morphism (g ∘ f)
:= @compose_monoid_mor.

Definition compose_bounded_joinsl_mor_flip@{u} : ∀ {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedJoinSemiLattice_Flip_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedMeetSemiLattice_Flip_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedJoinSemiLattice_Morphism (g ∘ f)
:= @compose_monoid_mor.

Definition compose_bounded_meetsl_flip_mor_l@{u} : ∀ {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedMeetSemiLattice_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedMeetSemiLattice_Flip_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedMeetSemiLattice_Flip_Morphism (g ∘ f)
:= @compose_monoid_mor.

Definition compose_bounded_meetsl_flip_mor_r@{u} : ∀ {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedMeetSemiLattice_Flip_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedJoinSemiLattice_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedMeetSemiLattice_Flip_Morphism (g ∘ f)
:= @compose_monoid_mor.

Definition compose_bounded_joinsl_flip_mor_l@{u} : ∀ {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedJoinSemiLattice_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedJoinSemiLattice_Flip_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedJoinSemiLattice_Flip_Morphism (g ∘ f)
:= @compose_monoid_mor.

Definition compose_bounded_joinsl_flip_mor_r@{u} : ∀ {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedJoinSemiLattice_Flip_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedMeetSemiLattice_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedJoinSemiLattice_Flip_Morphism (g ∘ f)
:= @compose_monoid_mor.

Lemma compose_lattice_mor_flip@{u} {X Y Z:set@{u}} {m₁ j₁} {m₂ j₂} {m₃ j₃} {g f} :
  @Lattice_Flip_Morphism X Y m₁ j₁ m₂ j₂ f → @Lattice_Flip_Morphism Y Z m₂ j₂ m₃ j₃ g
  → Lattice_Morphism (g ∘ f).
Proof. intros Hf Hg. split.
+ exact Hf.
+ exact (Lattice_op (L:=Z ᵒᵖ) (H:=latmor_b g Hg)).
+ exact (compose_meetsl_mor_flip Hf Hg).
+ exact (compose_joinsl_mor_flip Hf Hg).
Qed.

Lemma compose_lattice_flip_mor_l@{u} {X Y Z:set@{u}} {m₁ j₁} {m₂ j₂} {m₃ j₃} {g f} :
  @Lattice_Morphism X Y m₁ j₁ m₂ j₂ f → @Lattice_Flip_Morphism Y Z m₂ j₂ m₃ j₃ g
  → Lattice_Flip_Morphism (g ∘ f).
Proof. intros Hf Hg. split.
+ exact Hf.
+ exact (latmor_b g Hg).
+ exact (compose_meetsl_flip_mor_l Hf Hg).
+ exact (compose_joinsl_flip_mor_l Hf Hg).
Qed.

Lemma compose_lattice_flip_mor_r@{u} {X Y Z:set@{u}} {m₁ j₁} {m₂ j₂} {m₃ j₃} {g f} :
  @Lattice_Flip_Morphism X Y m₁ j₁ m₂ j₂ f → @Lattice_Morphism Y Z m₂ j₂ m₃ j₃ g
  → Lattice_Flip_Morphism (g ∘ f).
Proof. intros Hf Hg. split.
+ exact Hf.
+ exact (Lattice_op (L:=Z) (H:=latmor_b g Hg)).
+ exact (compose_meetsl_flip_mor_r Hf Hg).
+ exact (compose_joinsl_flip_mor_r Hf Hg).
Qed.

Lemma compose_bounded_lattice_mor_flip@{u} {X Y Z:set@{u}} {m₁ j₁ t₁ b₁} {m₂ j₂ t₂ b₂} {m₃ j₃ t₃ b₃} {g f} :
  @BoundedLattice_Flip_Morphism X Y m₁ j₁ t₁ b₁ m₂ j₂ t₂ b₂ f → @BoundedLattice_Flip_Morphism Y Z m₂ j₂ t₂ b₂ m₃ j₃ t₃ b₃ g
  → BoundedLattice_Morphism (g ∘ f).
Proof. intros Hf Hg. split.
+ exact Hf.
+ exact (BoundedLattice_op (L:=Z ᵒᵖ) (H:=bounded_latmor_b g Hg)).
+ exact (compose_bounded_meetsl_mor_flip Hf Hg).
+ exact (compose_bounded_joinsl_mor_flip Hf Hg).
Qed.

Lemma compose_bounded_lattice_flip_mor_l@{u} {X Y Z:set@{u}} {m₁ j₁ t₁ b₁} {m₂ j₂ t₂ b₂} {m₃ j₃ t₃ b₃} {g f} :
  @BoundedLattice_Morphism X Y m₁ j₁ t₁ b₁ m₂ j₂ t₂ b₂ f → @BoundedLattice_Flip_Morphism Y Z m₂ j₂ t₂ b₂ m₃ j₃ t₃ b₃ g
  → BoundedLattice_Flip_Morphism (g ∘ f).
Proof. intros Hf Hg. split.
+ exact Hf.
+ exact (bounded_latmor_b g Hg).
+ exact (compose_bounded_meetsl_flip_mor_l Hf Hg).
+ exact (compose_bounded_joinsl_flip_mor_l Hf Hg).
Qed.

Lemma compose_bounded_lattice_flip_mor_r@{u} {X Y Z:set@{u}} {m₁ j₁ t₁ b₁} {m₂ j₂ t₂ b₂} {m₃ j₃ t₃ b₃} {g f} :
  @BoundedLattice_Flip_Morphism X Y m₁ j₁ t₁ b₁ m₂ j₂ t₂ b₂ f → @BoundedLattice_Morphism Y Z m₂ j₂ t₂ b₂ m₃ j₃ t₃ b₃ g
  → BoundedLattice_Flip_Morphism (g ∘ f).
Proof. intros Hf Hg. split.
+ exact Hf.
+ exact (BoundedLattice_op (L:=Z) (H:=bounded_latmor_b g Hg)).
+ exact (compose_bounded_meetsl_flip_mor_r Hf Hg).
+ exact (compose_bounded_joinsl_flip_mor_r Hf Hg).
Qed.

Global Hint Extern 3 (MeetSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_meetsl_mor_flip _ _) : typeclass_instances.
Global Hint Extern 3 (JoinSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_joinsl_mor_flip _ _) : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_meetsl_flip_mor_l _ _) : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_meetsl_flip_mor_r _ _) : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_joinsl_flip_mor_l _ _) : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_joinsl_flip_mor_r _ _) : typeclass_instances.

Global Hint Extern 3 (BoundedMeetSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_meetsl_mor_flip _ _) : typeclass_instances.
Global Hint Extern 3 (BoundedJoinSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_joinsl_mor_flip _ _) : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_meetsl_flip_mor_l _ _) : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_meetsl_flip_mor_r _ _) : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_joinsl_flip_mor_l _ _) : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_joinsl_flip_mor_r _ _) : typeclass_instances.

Global Hint Extern 3 (Lattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_lattice_mor_flip _ _) : typeclass_instances.
Global Hint Extern 2 (Lattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_lattice_flip_mor_l _ _) : typeclass_instances.
Global Hint Extern 2 (Lattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_lattice_flip_mor_r _ _) : typeclass_instances.
Global Hint Extern 3 (BoundedLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_lattice_mor_flip _ _) : typeclass_instances.
Global Hint Extern 2 (BoundedLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_lattice_flip_mor_l _ _) : typeclass_instances.
Global Hint Extern 2 (BoundedLattice_Flip_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_lattice_flip_mor_r _ _) : typeclass_instances.


Definition invert_meetsl_mor `{@MeetSemiLattice_Morphism X Y mX mY f} `{!Inverse f, !Bijective f} : MeetSemiLattice_Morphism (inverse f) := invert_semigroup_mor.
Definition invert_joinsl_mor `{@JoinSemiLattice_Morphism X Y jX jY f} `{!Inverse f, !Bijective f} : JoinSemiLattice_Morphism (inverse f) := invert_semigroup_mor.
Global Hint Extern 2 (MeetSemiLattice_Morphism (inverse _)) => simple notypeclasses refine invert_meetsl_mor : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Morphism (inverse _)) => simple notypeclasses refine invert_joinsl_mor : typeclass_instances.

Definition invert_bounded_meetsl_mor `{@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY f} `{!Inverse f, !Bijective f} : BoundedMeetSemiLattice_Morphism (inverse f) := invert_monoid_mor.
Definition invert_bounded_joinsl_mor `{@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY f} `{!Inverse f, !Bijective f} : BoundedJoinSemiLattice_Morphism (inverse f) := invert_monoid_mor.
Global Hint Extern 2 (BoundedMeetSemiLattice_Morphism (inverse _)) => simple notypeclasses refine invert_bounded_meetsl_mor : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice_Morphism (inverse _)) => simple notypeclasses refine invert_bounded_joinsl_mor : typeclass_instances.

Lemma invert_lattice_mor `{@Lattice_Morphism X Y mX jX mY jY f} `{!Inverse f, !Bijective f} : Lattice_Morphism (inverse f).
Proof. now split. Qed.
Global Hint Extern 2 (Lattice_Morphism (inverse _)) => simple notypeclasses refine invert_lattice_mor : typeclass_instances.

Lemma invert_bounded_lattice_mor `{@BoundedLattice_Morphism X Y mX jX tX bX mY jY tY bY f} `{!Inverse f, !Bijective f} : BoundedLattice_Morphism (inverse f).
Proof. now split. Qed.
Global Hint Extern 2 (BoundedLattice_Morphism (inverse _)) => simple notypeclasses refine invert_bounded_lattice_mor : typeclass_instances.


Definition Build_MeetSemiLattice_Morphism@{u} {X Y:set@{u}} 
  `{MeetSemiLattice X} `{MeetSemiLattice Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x ⊓ y) = f x ⊓ f y)
 → MeetSemiLattice_Morphism f
:= Build_SemiGroup_Morphism (f:MeetSemigroupOps X ⇾ MeetSemigroupOps Y).

Definition Build_JoinSemiLattice_Morphism@{u} {X Y:set@{u}}
  `{JoinSemiLattice X} `{JoinSemiLattice Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x ⊔ y) = f x ⊔ f y)
 → JoinSemiLattice_Morphism f
:= Build_SemiGroup_Morphism (f:JoinSemigroupOps X ⇾ JoinSemigroupOps Y).

Definition alt_Build_BoundedMeetSemiLattice_Morphism@{u} :
  ∀ {X Y:set@{u}} `{BoundedMeetSemiLattice X} `{BoundedMeetSemiLattice Y} {f : X ⇾ Y},
  (∀ x y : X, f (x ⊓ y) = f x ⊓ f y)
 → f ⊤ = ⊤
 → BoundedMeetSemiLattice_Morphism f
:= @alt_Build_Monoid_Morphism.

Definition alt_Build_BoundedJoinSemiLattice_Morphism@{u} :
  ∀ {X Y:set@{u}} `{BoundedJoinSemiLattice X} `{BoundedJoinSemiLattice Y} {f : X ⇾ Y},
  (∀ x y : X, f (x ⊔ y) = f x ⊔ f y)
 → f ⊥ = ⊥
 → BoundedJoinSemiLattice_Morphism f
:= @alt_Build_Monoid_Morphism.

Definition Build_MeetSemiLattice_Flip_Morphism@{u}
  {X Y:set@{u}} `{MeetSemiLattice X} `{JoinSemiLattice Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x ⊓ y) = f x ⊔ f y)
 → MeetSemiLattice_Flip_Morphism f
:= Build_SemiGroup_Morphism (f:MeetSemigroupOps X ⇾ JoinSemigroupOps Y).

Definition Build_JoinSemiLattice_Flip_Morphism@{u}
  {X Y:set@{u}} `{JoinSemiLattice X} `{MeetSemiLattice Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x ⊔ y) = f x ⊓ f y)
 → JoinSemiLattice_Flip_Morphism f
:= Build_SemiGroup_Morphism (f:JoinSemigroupOps X ⇾ MeetSemigroupOps Y).

Lemma alt_Build_Lattice_Morphism@{u} {X Y:set@{u}}
  `{Lattice X} `{Lattice Y} {f : X ⇾ Y} :
   (∀ x y : X, f (x ⊓ y) = f x ⊓ f y)
 → (∀ x y : X, f (x ⊔ y) = f x ⊔ f y)
 → Lattice_Morphism f.
Proof. intros. split; try exact _.
+ now apply Build_MeetSemiLattice_Morphism.
+ now apply Build_JoinSemiLattice_Morphism.
Qed.

Lemma Build_Lattice_Flip_Morphism@{u} {X Y:set@{u}}
  `{Lattice X} `{Lattice Y} {f : X ⇾ Y} :
   (∀ x y : X, f (x ⊓ y) = f x ⊔ f y)
 → (∀ x y : X, f (x ⊔ y) = f x ⊓ f y)
 → Lattice_Flip_Morphism f.
Proof. intros. split; try exact _.
+ now apply Build_MeetSemiLattice_Flip_Morphism.
+ now apply Build_JoinSemiLattice_Flip_Morphism.
Qed.

Lemma alt_Build_BoundedLattice_Morphism@{u} {X Y:set@{u}}
  `{BoundedLattice X} `{BoundedLattice Y} {f : X ⇾ Y} :
   (∀ x y : X, f (x ⊓ y) = f x ⊓ f y)
 → (∀ x y : X, f (x ⊔ y) = f x ⊔ f y)
 → f ⊤ = ⊤
 → f ⊥ = ⊥
 → BoundedLattice_Morphism f.
Proof. intros. split; try exact _.
+ now apply alt_Build_BoundedMeetSemiLattice_Morphism.
+ now apply alt_Build_BoundedJoinSemiLattice_Morphism.
Qed.

Lemma Build_BoundedLattice_Flip_Morphism@{u} {X Y:set@{u}}
  `{BoundedLattice X} `{BoundedLattice Y} {f : X ⇾ Y} :
   (∀ x y : X, f (x ⊓ y) = f x ⊔ f y)
 → (∀ x y : X, f (x ⊔ y) = f x ⊓ f y)
 → f ⊤ = ⊥
 → f ⊥ = ⊤
 → BoundedLattice_Flip_Morphism f.
Proof. intros. split; try exact _.
+ now apply alt_Build_BoundedMeetSemiLattice_Morphism.
+ now apply alt_Build_BoundedJoinSemiLattice_Morphism.
Qed.


Definition projected_meet_sl@{u} :
  ∀ {X L:set@{u}} `{MeetSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X},
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → MeetSemiLattice X
  := @projected_semilattice.

Definition projected_join_sl@{u} :
  ∀ {X L:set@{u}} `{JoinSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{Join X},
   (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → JoinSemiLattice X
  := @projected_semilattice.

Lemma projected_lattice@{u} {X L:set@{u}} `{Lattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X} `{Join X} :
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → Lattice X.
Proof. intros Em Ej. pose proof projected_meet_sl f _. pose proof projected_join_sl f _.
  split; trivial.
+ intros x y. rew <-(injective f _ _), (Ej _ _), (Em _ _). now apply absorption.
+ intros x y. rew <-(injective f _ _), (Em _ _), (Ej _ _). now apply absorption.
Qed.

Lemma projected_distr_lattice@{u} {X L:set@{u}} `{DistributiveLattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X} `{Join X} :
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → DistributiveLattice X.
Proof. intros Em Ej. pose proof projected_lattice f _ _. split; trivial.
+ intros x y z. rew <-(injective f _ _).
  rew [ (Ej _ _) | (Em _ _) ]. rew [ (Em _ _) | (Ej _ _) ].
  now apply distribute_l.
+ intros x y z. rew <-(injective f _ _).
  rew [ (Em _ _) | (Ej _ _) ]. rew [ (Ej _ _) | (Em _ _) ].
  now apply distribute_l.
Qed.


Definition projected_bounded_meet_sl@{u} :
  ∀ {X L:set@{u}} `{BoundedMeetSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X} `{Top X},
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → f ⊤ = ⊤
   → BoundedMeetSemiLattice X
:= @projected_bounded_semilattice.

Definition projected_bounded_join_sl@{u} :
  ∀ {X L:set@{u}} `{BoundedJoinSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{Join X} `{Bottom X},
   (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → f ⊥ = ⊥
   → BoundedJoinSemiLattice X
:= @projected_bounded_semilattice.


Lemma projected_bounded_lattice@{u} {X L:set@{u}} `{BoundedLattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X} `{Join X} `{Top X} `{Bottom X} :
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → f ⊤ = ⊤
   → f ⊥ = ⊥
   → BoundedLattice X.
Proof. intros. pose proof projected_lattice f _ _.
  pose proof projected_bounded_meet_sl f _ _.
  pose proof projected_bounded_join_sl f _ _.
  now split.
Qed.

Lemma projected_bounded_distr_lattice@{u} {X L:set@{u}} `{BoundedDistributiveLattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X} `{Join X} `{Top X} `{Bottom X} :
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → f ⊤ = ⊤
   → f ⊥ = ⊥
   → BoundedDistributiveLattice X.
Proof. intros. pose proof projected_bounded_lattice f _ _ _ _.
  pose proof projected_distr_lattice f _.
  now split.
Qed.


(** Quote *)

Lemma quote_meet_alt `(f:X ⇾ Y) `{@MeetSemiLattice_Morphism X Y mX mY f}
  {x₁ y₁ x₂ y₂} : quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ ⊓ x₂) (y₁ ⊓ y₂).
Proof. exact ( quote_sg_op_alt (f:MeetSemigroupOps _ ⇾ MeetSemigroupOps _) ). Qed.

Lemma quote_join_alt `(f:X ⇾ Y) `{@JoinSemiLattice_Morphism X Y jX jY f}
  {x₁ y₁ x₂ y₂} : quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ ⊔ x₂) (y₁ ⊔ y₂).
Proof. exact ( quote_sg_op_alt (f:JoinSemigroupOps _ ⇾ JoinSemigroupOps _) ). Qed.

Global Hint Extern 4 (quote _ (_ ⊓ _) _) => quote_hint_strip (fun f => refine (quote_meet_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ ⊓ _)) => quote_hint_strip (fun f => refine (quote_meet_alt f _ _)) : quote.

Global Hint Extern 4 (quote _ (_ ⊔ _) _) => quote_hint_strip (fun f => refine (quote_join_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ ⊔ _)) => quote_hint_strip (fun f => refine (quote_join_alt f _ _)) : quote.

