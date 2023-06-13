Require Import abstract_algebra theory.common_props theory.groups.
Require Import sprop.
Require Import easy rewrite quote.base.

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


Definition join_meet_distr_r `{DistributiveLattice L} : RightDistribute (X:=L) (⊔) (⊓) := right_distr_from_left.
Definition meet_join_distr_r `{DistributiveLattice L} : RightDistribute (X:=L) (⊓) (⊔) := right_distr_from_left.
Global Hint Extern 2 (RightDistribute (⊔) (⊓)) => simple notypeclasses refine join_meet_distr_r : typeclass_instances.
Global Hint Extern 2 (RightDistribute (⊓) (⊔)) => simple notypeclasses refine meet_join_distr_r : typeclass_instances.

Local Notation "X 'ᵒᵖ'" := (order_op X) (at level 1, format "X 'ᵒᵖ'").
Definition MeetSemiLattice_op `{H:JoinSemiLattice L} : MeetSemiLattice (L ᵒᵖ) := H.
Definition JoinSemiLattice_op `{H:MeetSemiLattice L} : JoinSemiLattice (L ᵒᵖ) := H.
Global Hint Extern 2 (MeetSemiLattice (_ ᵒᵖ)) => simple notypeclasses refine MeetSemiLattice_op : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice (_ ᵒᵖ)) => simple notypeclasses refine MeetSemiLattice_op : typeclass_instances.
Lemma Lattice_op `{H : Lattice L} : Lattice (L ᵒᵖ).  Proof. destruct H. now split. Qed.
Global Hint Extern 2 (Lattice (_ ᵒᵖ)) => simple notypeclasses refine Lattice_op : typeclass_instances.
Lemma DistributiveLattice_op `{H : DistributiveLattice L} : DistributiveLattice (L ᵒᵖ).  Proof. destruct H. now split. Qed.
Global Hint Extern 2 (DistributiveLattice (_ ᵒᵖ)) => simple notypeclasses refine DistributiveLattice_op : typeclass_instances.

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
  rew (associativity _ _ _ _), <-(associativity _ (x ⊔ z) _ _).
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
  : f = g → impl (@Lattice_Morphism X Y mX jX mY jY f) (Lattice_Morphism g).
Proof. intros E H; split; try exact _; now rew <-E. Qed.
Canonical Structure Lattice_Morphism_fun {X Y mX jX mY jY} :=
  make_weak_spred (@Lattice_Morphism X Y mX jX mY jY) Lattice_Morphism_proper_impl.


Coercion bounded_msl_mor_msl_mor `{H:@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY f} : MeetSemiLattice_Morphism f := H.
Coercion bounded_jsl_mor_jsl_mor `{H:@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY f} : JoinSemiLattice_Morphism f := H.

Definition preserves_meet `{@MeetSemiLattice_Morphism X Y mX mY f} : ∀ x y, f (x ⊓ y) = f x ⊓ f y := preserves_sg_op (f:MeetSemigroupOps _ ⇾ MeetSemigroupOps _).
Definition preserves_join `{@JoinSemiLattice_Morphism X Y jX jY f} : ∀ x y, f (x ⊔ y) = f x ⊔ f y := preserves_sg_op (f:JoinSemigroupOps _ ⇾ JoinSemigroupOps _).
Arguments preserves_meet {_ _ _ _} f {_} x y.
Arguments preserves_join {_ _ _ _} f {_} x y.

Coercion BoundedMeetSemiLattice_Morphism_pointed `{@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY f}
  : Top_Pointed_Morphism f := monmor_pointed f _.
Coercion BoundedJoinSemiLattice_Morphism_pointed `{@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY f}
  : Bottom_Pointed_Morphism f := monmor_pointed f _.

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

Definition compose_meetsl_mor : ∀ {X Y Z} {op₁ op₂ op₃} {g f},
  @MeetSemiLattice_Morphism X Y op₁ op₂ f → @MeetSemiLattice_Morphism Y Z op₂ op₃ g
  → MeetSemiLattice_Morphism (g ∘ f)
:= @compose_semigroup_mor.
Global Hint Extern 2 (MeetSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_meetsl_mor _ _) : typeclass_instances.

Definition compose_joinsl_mor : ∀ {X Y Z} {op₁ op₂ op₃} {g f},
  @JoinSemiLattice_Morphism X Y op₁ op₂ f → @JoinSemiLattice_Morphism Y Z op₂ op₃ g
  → JoinSemiLattice_Morphism (g ∘ f)
:= @compose_semigroup_mor.
Global Hint Extern 2 (JoinSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_joinsl_mor _ _) : typeclass_instances.

Definition compose_bounded_meetsl_mor : ∀ {X Y Z} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedMeetSemiLattice_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedMeetSemiLattice_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedMeetSemiLattice_Morphism (g ∘ f)
:= @compose_monoid_mor.
Global Hint Extern 2 (BoundedMeetSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_meetsl_mor _ _) : typeclass_instances.

Definition compose_bounded_joinsl_mor : ∀ {X Y Z} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @BoundedJoinSemiLattice_Morphism X Y op₁ e₁ op₂ e₂ f → @BoundedJoinSemiLattice_Morphism Y Z op₂ e₂ op₃ e₃ g
  → BoundedJoinSemiLattice_Morphism (g ∘ f)
:= @compose_monoid_mor.
Global Hint Extern 2 (BoundedJoinSemiLattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_bounded_joinsl_mor _ _) : typeclass_instances.

Lemma compose_lattice_mor {X Y Z} {m₁ j₁} {m₂ j₂} {m₃ j₃} {g f} :
  @Lattice_Morphism X Y m₁ j₁ m₂ j₂ f → @Lattice_Morphism Y Z m₂ j₂ m₃ j₃ g
  → Lattice_Morphism (g ∘ f).
Proof. now split. Qed.
Global Hint Extern 2 (Lattice_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_lattice_mor _ _) : typeclass_instances.


Definition invert_meetsl_mor `{@MeetSemiLattice_Morphism X Y mX mY f} `{!Inverse f} `{!Bijective f} : MeetSemiLattice_Morphism (inverse f) := invert_semigroup_mor.
Definition invert_joinsl_mor `{@JoinSemiLattice_Morphism X Y jX jY f} `{!Inverse f} `{!Bijective f} : JoinSemiLattice_Morphism (inverse f) := invert_semigroup_mor.
Global Hint Extern 2 (MeetSemiLattice_Morphism (inverse _)) => simple notypeclasses refine invert_meetsl_mor : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Morphism (inverse _)) => simple notypeclasses refine invert_joinsl_mor : typeclass_instances.

Definition invert_bounded_meetsl_mor `{@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY f} `{!Inverse f} `{!Bijective f} : BoundedMeetSemiLattice_Morphism (inverse f) := invert_monoid_mor.
Definition invert_bounded_joinsl_mor `{@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY f} `{!Inverse f} `{!Bijective f} : BoundedJoinSemiLattice_Morphism (inverse f) := invert_monoid_mor.
Global Hint Extern 2 (BoundedMeetSemiLattice_Morphism (inverse _)) => simple notypeclasses refine invert_bounded_meetsl_mor : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice_Morphism (inverse _)) => simple notypeclasses refine invert_bounded_joinsl_mor : typeclass_instances.

Lemma invert_lattice_mor `{@Lattice_Morphism X Y mX jX mY jY f} `{!Inverse f} `{!Bijective f} : Lattice_Morphism (inverse f).
Proof. now split. Qed.
Global Hint Extern 2 (Lattice_Morphism (inverse _)) => simple notypeclasses refine invert_lattice_mor : typeclass_instances.


Definition Build_MeetSemiLattice_Morphism 
  `{MeetSemiLattice X} `{MeetSemiLattice Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x ⊓ y) = f x ⊓ f y)
 → MeetSemiLattice_Morphism f
:= Build_SemiGroup_Morphism (f:MeetSemigroupOps X ⇾ MeetSemigroupOps Y).

Definition Build_JoinSemiLattice_Morphism 
  `{JoinSemiLattice X} `{JoinSemiLattice Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x ⊔ y) = f x ⊔ f y)
 → JoinSemiLattice_Morphism f
:= Build_SemiGroup_Morphism (f:JoinSemigroupOps X ⇾ JoinSemigroupOps Y).

Definition alt_Build_BoundedMeetSemiLattice_Morphism :
  ∀ `{BoundedMeetSemiLattice X} `{BoundedMeetSemiLattice Y} {f : X ⇾ Y},
  (∀ x y : X, f (x ⊓ y) = f x ⊓ f y)
 → f ⊤ = ⊤
 → BoundedMeetSemiLattice_Morphism f
:= @alt_Build_Monoid_Morphism.

Definition alt_Build_BoundedJoinSemiLattice_Morphism :
  ∀ `{BoundedJoinSemiLattice X} `{BoundedJoinSemiLattice Y} {f : X ⇾ Y},
  (∀ x y : X, f (x ⊔ y) = f x ⊔ f y)
 → f ⊥ = ⊥
 → BoundedJoinSemiLattice_Morphism f
:= @alt_Build_Monoid_Morphism.


Definition projected_meet_sl :
  ∀ `{MeetSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X},
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → MeetSemiLattice X
  := @projected_semilattice.

Definition projected_join_sl :
  ∀ `{JoinSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{Join X},
   (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → JoinSemiLattice X
  := @projected_semilattice.

Lemma projected_lattice `{Lattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X} `{Join X} :
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → Lattice X.
Proof. intros Em Ej. pose proof projected_meet_sl f _. pose proof projected_join_sl f _.
  split; trivial.
+ intros x y. rew <-(injective f _ _), (Ej _ _), (Em _ _). now apply absorption.
+ intros x y. rew <-(injective f _ _), (Em _ _), (Ej _ _). now apply absorption.
Qed.

Lemma projected_distr_lattice `{DistributiveLattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X} `{Join X} :
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → DistributiveLattice X.
Proof. intros Em Ej. pose proof projected_lattice f _ _. split; trivial.
+ intros x y z. rew <-(injective f _ _).
  rew [ (Ej _ _) | (Em _ _) ]. rew [ (Em _ _) | (Ej _ _) | (Ej _ _) ].
  now apply distribute_l.
+ intros x y z. rew <-(injective f _ _).
  rew [ (Em _ _) | (Ej _ _) ]. rew [ (Ej _ _) | (Em _ _) | (Em _ _) ].
  now apply distribute_l.
Qed.


Definition projected_bounded_meet_sl :
  ∀ `{BoundedSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{Meet X} `{Top X},
   (∀ x y, f (x ⊓ y) = f x ⊓ f y)
   → f ⊤ = ⊤
   → BoundedMeetSemiLattice X
:= @projected_bounded_semilattice.

Definition projected_bounded_join_sl :
  ∀ `{BoundedJoinSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{Join X} `{Bottom X},
   (∀ x y, f (x ⊔ y) = f x ⊔ f y)
   → f ⊥ = ⊥
   → BoundedJoinSemiLattice X
:= @projected_bounded_semilattice.


(** Quote *)

Lemma quote_meet_alt `(f:X ⇾ Y) `{@MeetSemiLattice_Morphism X Y mX mY f}
  {x₁ y₁ x₂ y₂} : quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ ⊓ x₂) (y₁ ⊓ y₂).
Proof quote_sg_op_alt (f:MeetSemigroupOps _ ⇾ MeetSemigroupOps _).

Lemma quote_join_alt `(f:X ⇾ Y) `{@JoinSemiLattice_Morphism X Y jX jY f}
  {x₁ y₁ x₂ y₂} : quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ ⊔ x₂) (y₁ ⊔ y₂).
Proof quote_sg_op_alt (f:JoinSemigroupOps _ ⇾ JoinSemigroupOps _).

Global Hint Extern 4 (quote _ (_ ⊓ _) _) => quote_hint_strip (fun f => refine (quote_meet_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ ⊓ _)) => quote_hint_strip (fun f => refine (quote_meet_alt f _ _)) : quote.

Global Hint Extern 4 (quote _ (_ ⊔ _) _) => quote_hint_strip (fun f => refine (quote_join_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ ⊔ _)) => quote_hint_strip (fun f => refine (quote_join_alt f _ _)) : quote.

