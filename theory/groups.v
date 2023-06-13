Require Import interfaces.sprop abstract_algebra.
Require Import logic.aprop relations.
Require Import easy rewrite tactics.misc.
Require Export theory.common_props theory.pointed.
Require Import quote.base.

Local Open Scope grp_scope.
Local Notation e := mon_unit.
Local Notation "X 'ᵒᵖ'" := (semigroup_op X) (at level 1, format "X 'ᵒᵖ'").

Definition alt_Build_CommutativeSemiGroup : ∀ `{SgOp G},
   @Associative G (∙)
 → Commutative (X:=G) (∙)
 → CommutativeSemiGroup G
:= @Build_CommutativeSemiGroup.

Definition alt_Build_SemiLattice : ∀ `{SgOp L},
   @Associative L (∙)
 → Commutative (X:=L) (∙)
 → @BinaryIdempotent L (∙)
 → SemiLattice L.
Proof. repeat (split; trivial). Defined.

Definition alt_Build_Monoid : ∀ `{SgOp M} `{MonUnit M},
   @Associative M (∙)
 → LeftIdentity  (X:=M) (∙) e
 → RightIdentity (X:=M) (∙) e
 → Monoid M
:= @Build_Monoid.

Definition alt_Build_CommutativeMonoid `{SgOp M} `{MonUnit M} :
   @Associative M (∙)
 → Commutative (X:=M) (∙)
 → LeftIdentity  (X:=M) (∙) e
 → CommutativeMonoid M.
Proof. intros; repeat (split; trivial). exact right_id_from_left. Defined.

Definition alt_Build_BoundedSemiLattice `{SgOp L} `{MonUnit L} :
   @Associative L (∙)
 → Commutative (X:=L) (∙)
 → @BinaryIdempotent L (∙)
 → LeftIdentity  (X:=L) (∙) e
 → BoundedSemiLattice L.
Proof. intros; split.
+ now apply alt_Build_SemiLattice.
+ now apply alt_Build_CommutativeMonoid.
Defined.

Definition alt_Build_Group `{SgOp G} `{MonUnit G} `{Inv G} :
   @Associative G (∙)
 → LeftIdentity  (X:=G) (∙) e
 → RightIdentity (X:=G) (∙) e
 → LeftInverse  (X:=G) (∙) (⁻¹) e
 → RightInverse (X:=G) (∙) (⁻¹) e
 → Group G.
Proof. intros; split; trivial. now apply alt_Build_Monoid. Defined.

Definition alt_Build_AbGroup `{SgOp G} `{MonUnit G} `{Inv G} :
   @Associative G (∙)
 → Commutative (X:=G) (∙)
 → LeftIdentity  (X:=G) (∙) e
 → LeftInverse  (X:=G) (∙) (⁻¹) e
 → AbGroup G.
Proof. intros; split; trivial. apply alt_Build_Group; trivial.
+ exact right_id_from_left.
+ exact right_inverse_from_left.
Defined.

Definition commonoid_comsg `(CommutativeMonoid M) : CommutativeSemiGroup M.
Proof. now split. Defined.
Coercion commonoid_comsg : CommutativeMonoid >-> CommutativeSemiGroup.

Definition abgroup_common `(AbGroup G) : CommutativeMonoid G.
Proof. now split. Defined.
Coercion abgroup_common : AbGroup >-> CommutativeMonoid.

Definition strong_op_mon_strong_op_sg `(StrongOpMonoid M) : StrongOpSemiGroup M.
Proof. now split. Defined.
Coercion strong_op_mon_strong_op_sg : StrongOpMonoid >-> StrongOpSemiGroup.

Section opposite.
  Ltac go := first [ split | red ]; try exact _; change (@sg_op (semigroup_op _) ?f) with f; unfold semigroup_op; exact _.
  Instance SemiGroup_op            `{SemiGroup G}            : SemiGroup (G ᵒᵖ).             Proof. go. Defined.
  Instance CommutativeSemiGroup_op `{CommutativeSemiGroup G} : CommutativeSemiGroup (G ᵒᵖ).  Proof. go. Defined.
  Instance SemiLattice_op          `{SemiLattice L}          : SemiLattice (L ᵒᵖ).           Proof. go. Defined.
  Instance Monoid_op               `{Monoid M}               : Monoid (M ᵒᵖ).                Proof. go. Defined.
  Instance CommutativeMonoid_op    `{CommutativeMonoid M}    : CommutativeMonoid (M ᵒᵖ).     Proof. go. Defined.
  Instance BoundedSemiLattice_op   `{BoundedSemiLattice L}   : BoundedSemiLattice (L ᵒᵖ).    Proof. go. Defined.
  Instance Group_op                `{Group G}                : Group (G ᵒᵖ).                 Proof. go. Defined.
  Instance AbGroup_op              `{AbGroup G}              : AbGroup (G ᵒᵖ).               Proof. go. Defined.
End opposite.
Global Hint Extern 2 (SemiGroup            (_ ᵒᵖ)) => simple notypeclasses refine SemiGroup_op            : typeclass_instances.
Global Hint Extern 2 (CommutativeSemiGroup (_ ᵒᵖ)) => simple notypeclasses refine CommutativeSemiGroup_op : typeclass_instances.
Global Hint Extern 2 (SemiLattice          (_ ᵒᵖ)) => simple notypeclasses refine SemiLattice_op          : typeclass_instances.
Global Hint Extern 2 (Monoid               (_ ᵒᵖ)) => simple notypeclasses refine Monoid_op               : typeclass_instances.
Global Hint Extern 2 (CommutativeMonoid    (_ ᵒᵖ)) => simple notypeclasses refine CommutativeMonoid_op    : typeclass_instances.
Global Hint Extern 2 (BoundedSemiLattice   (_ ᵒᵖ)) => simple notypeclasses refine BoundedSemiLattice_op   : typeclass_instances.
Global Hint Extern 2 (Group                (_ ᵒᵖ)) => simple notypeclasses refine Group_op                : typeclass_instances.
Global Hint Extern 2 (AbGroup              (_ ᵒᵖ)) => simple notypeclasses refine AbGroup_op              : typeclass_instances.

Lemma monoid_unit_unique_l `{Monoid M} (x:M) : LeftIdentity (∙) x → x = e.
Proof. intro. rew <-(right_identity (∙) x). exact (left_identity (∙) _). Qed.

Lemma monoid_unit_unique_r `{Monoid M} (x:M) : RightIdentity (∙) x → x = e.
Proof monoid_unit_unique_l (M:=M ᵒᵖ) x.

(** a simple group simplification tactic *)
Ltac group_basic :=
  repeat match goal with
  | |- context [ e ∙ ?x ] => rew (left_identity  (∙) (x:=e) x)
  | |- context [ ?x ∙ e ] => rew (right_identity (∙) (y:=e) x)
  | |- context [ ?x⁻¹ ∙ ?x ] => rew (inverse_l x)
  | |- context [ ?x ∙ ?x⁻¹ ] => rew (inverse_r x)
  end.
Ltac group_simplify := group_basic; repeat rew (associativity (∙) _ _ _); group_basic.

Lemma group_assoc_inv_l_3 `{Group G} (x y : G) : y ∙ x⁻¹ ∙ x = y.
Proof. rew <-(associativity (∙) _ _ _). now group_simplify. Qed.

Lemma group_assoc_inv_l_4 `{Group G} (x y z : G) : y ∙ z ∙ x⁻¹ ∙ x = y ∙ z.
Proof. rew <-(associativity (∙) _ _ x). now group_simplify. Qed.

Lemma group_assoc_inv_r_3 `{Group G} (x y : G) : y ∙ x ∙ x⁻¹ = y.
Proof. rew <-(associativity (∙) _ _ _). now group_simplify. Qed.

Lemma group_assoc_inv_r_4 `{Group G} (x y z : G) : y ∙ z ∙ x ∙ x⁻¹ = y ∙ z.
Proof. rew <-(associativity (∙) _ x _). now group_simplify. Qed.

Ltac group_basic ::=
  repeat match goal with
  | |- context [ e ∙ ?x ] => rew (left_identity  (∙) (x:=e) x)
  | |- context [ ?x ∙ e ] => rew (right_identity (∙) (y:=e) x)
  | |- context [ ?x⁻¹ ∙ ?x ] => rew (inverse_l x)
  | |- context [ ?x ∙ ?x⁻¹ ] => rew (inverse_r x)
  | |- context [ ?y ∙ ?x⁻¹ ∙ ?x ] => rew (group_assoc_inv_l_3 x y)
  | |- context [ ?y ∙ ?x ∙ ?x⁻¹ ] => rew (group_assoc_inv_r_3 x y)
  | |- context [ ?y ∙ ?z ∙ ?x⁻¹ ∙ ?x ] => rew (group_assoc_inv_l_4 x y z)
  | |- context [ ?y ∙ ?z ∙ ?x ∙ ?x⁻¹ ] => rew (group_assoc_inv_r_4 x y z)
  end.

Global Hint Extern 2 (Inverse (@inv ?G ?f)) => notypeclasses refine (@inv G f) : typeclass_instances.

Lemma inverse_involutive `{Group G} : Involutive (X:=G) (⁻¹).
Proof. intros x.
  rew <-(left_identity (∙) x) at 2.
  rew <-(inverse_l x⁻¹).
  now rew (group_assoc_inv_l_3 _ _).
Qed.
Coercion inverse_involutive : Group >-> Involutive.
Global Hint Extern 4 (Involutive (⁻¹)) => simple notypeclasses refine inverse_involutive : typeclass_instances.
Global Hint Extern 4 (Bijective  (⁻¹)) => simple notypeclasses refine inverse_involutive : typeclass_instances.
Global Hint Extern 4 (Injective  (⁻¹)) => simple notypeclasses refine inverse_involutive : typeclass_instances.
Global Hint Extern 4 (Surjective (⁻¹)) => simple notypeclasses refine inverse_involutive : typeclass_instances.

Lemma inverse_unit `{Group G} : e⁻¹ = e :> G.
Proof. rew <-(inverse_l e) at 2. now group_simplify. Qed.

Lemma inverse_distr `{Group G} (x y : G) : (x ∙ y)⁻¹ = y⁻¹ ∙ x⁻¹.
Proof. rew <-(left_identity (∙) (y⁻¹ ∙ x⁻¹)), <-(inverse_l (x ∙ y)).
  do 2 rew <-(associativity (∙) _ _ _). now group_simplify.
Qed.

Lemma inverse_distr_ab `{AbGroup G} (x y : G) : (x ∙ y)⁻¹ = x⁻¹ ∙ y⁻¹.
Proof. rew (commutativity (∙) x⁻¹_ ). exact (inverse_distr _ _). Qed.

Ltac group_basic ::=
  repeat match goal with
  | |- context [ e⁻¹ ] => rew inverse_unit
  | |- context [ e ∙ ?x ] => rew (left_identity  (∙) (x:=e) x)
  | |- context [ ?x ∙ e ] => rew (right_identity (∙) (y:=e) x)
  | |- context [ ?x⁻¹ ∙ ?x ] => rew (inverse_l x)
  | |- context [ ?x ∙ ?x⁻¹ ] => rew (inverse_r x)
  | |- context [ (?x⁻¹)⁻¹ ] => rew (inverse_involutive x)
  | |- context [ ?y ∙ ?x⁻¹ ∙ ?x ] => rew (group_assoc_inv_l_3 x y)
  | |- context [ ?y ∙ ?x ∙ ?x⁻¹ ] => rew (group_assoc_inv_r_3 x y)
  | |- context [ ?y ∙ ?z ∙ ?x⁻¹ ∙ ?x ] => rew (group_assoc_inv_l_4 x y z)
  | |- context [ ?y ∙ ?z ∙ ?x ∙ ?x⁻¹ ] => rew (group_assoc_inv_r_4 x y z)
  | |- context [ (?x ∙ ?y)⁻¹ ] => rew (inverse_distr x y)
  end.

Lemma inverse_swap_r `{Group G} (x y : G) : x ∙ y⁻¹ = (y ∙ x⁻¹)⁻¹.
Proof. now group_simplify. Qed.

Lemma inverse_swap_l_ab `{AbGroup G} (x y : G) : x⁻¹ ∙ y = (x ∙ y⁻¹)⁻¹.
Proof. rew (inverse_distr_ab _ _). now group_simplify. Qed.

Lemma group_left_op_inj `{Group G} (z:G) : Injective (z ∙).
Proof. intros x y. change (z ∙ x = z ∙ y ⊸ x = y).
  rew <-(left_identity (∙) x) at 2.
  rew <-(left_identity (∙) y) at 2.
  rew <-(inverse_l z).
  rew <-!2(associativity (∙) _ _ _).
  exact (is_fun (z⁻¹ ∙) _ _).
Qed.
Global Hint Extern 5 (Injective (_ ∙)) => simple notypeclasses refine (group_left_op_inj _) : typeclass_instances.

Lemma group_right_op_inj `{Group G} (z:G) : Injective (∙ z).
Proof group_left_op_inj (G := G ᵒᵖ) z.
Global Hint Extern 5 (Injective (∙ _)) => simple notypeclasses refine (group_right_op_inj _) : typeclass_instances.

Lemma equal_by_inverse `{Group G} (x y : G) : x ∙ y⁻¹ = e ⧟ x = y.
Proof. rew (right_cancellation (∙) y _ e). now group_simplify. Qed.

Lemma flip_inverse `{Group G} (x y : G) : x⁻¹ = y ⧟ x = y⁻¹.
Proof. rew (injective_iff (⁻¹) _ y). now group_simplify. Qed.

Lemma flip_inverse_unit `{Group G} (x y : G) : x⁻¹ = e ⧟ x = e.
Proof. rew (injective_iff (⁻¹) x _). now group_simplify. Qed.

Lemma group_op_strong `{Group G} `{!StrongOp (X:=G) (∙)} : StrongSet G.
Proof. intros x y z.
  rew (right_cancellation (∙) y⁻¹ x y); group_simplify.
  rew (ltac:(now group_simplify) : x = (x ∙ y⁻¹) ∙ y) at 2.
  rew (ltac:(now group_simplify) : z = e ∙ z) at 2.
  exact (is_fun (strong_op (∙)) (_, _) (_, _)).
Qed.

(** Morphisms *)

Lemma SemiGroup_Morphism_proper_impl {X Y} {Xop:SgOp X} {Yop:SgOp Y} {f g : X ⇾ Y}
  : f = g → impl (SemiGroup_Morphism f) (SemiGroup_Morphism g).
Proof. intros E H; split; try exact _. rew <-E. apply H. Qed.
Canonical Structure SemiGroup_Morphism_fun {X Y Xop Yop} :=
  make_weak_spred (@SemiGroup_Morphism X Y Xop Yop) (@SemiGroup_Morphism_proper_impl _ _ _ _).

Lemma Monoid_Morphism_proper_impl {X Y} {Xop:SgOp X} {Xunit:MonUnit X} {Yop:SgOp Y} {Yunit:MonUnit Y} {f g : X ⇾ Y}
  : f = g → impl (Monoid_Morphism f) (Monoid_Morphism g).
Proof. intros E H; split; try exact _; now rew <-E. Qed.
Canonical Structure Monoid_Morphism_fun {X Y Xop Xunit Yop Yunit} :=
  make_weak_spred (@Monoid_Morphism X Y Xop Xunit Yop Yunit) (@Monoid_Morphism_proper_impl _ _ _ _ _ _).


Lemma alt_Build_Monoid_Morphism `{Monoid (X:=X)} `{Monoid (X:=Y)} (f:X ⇾ Y):
   (∀ x y, f (x ∙ y) = f x ∙ f y)
→  (f e = e)
→ Monoid_Morphism f.
Proof. now split. Qed.

Lemma id_semigroup_mor `{SemiGroup G} : SemiGroup_Morphism (id_fun G).
Proof. now split. Qed.
Global Hint Extern 2 (SemiGroup_Morphism (id_fun _)) => simple notypeclasses refine id_semigroup_mor : typeclass_instances.

Lemma id_monoid_mor `{Monoid M} : Monoid_Morphism (id_fun M).
Proof. now apply alt_Build_Monoid_Morphism. Qed.
Global Hint Extern 2 (Monoid_Morphism (id_fun _)) => simple notypeclasses refine id_monoid_mor : typeclass_instances.

Lemma compose_semigroup_mor {X Y Z} {op₁ op₂ op₃} {g f}
  : @SemiGroup_Morphism X Y op₁ op₂ f → @SemiGroup_Morphism Y Z op₂ op₃ g
  → SemiGroup_Morphism (g ∘ f).
Proof. intros. split; try exact _. intros x y.
  change (g (f (x ∙ y)) = g (f x) ∙ g (f y)).
  rew (preserves_sg_op f _ _). exact (preserves_sg_op g _ _).
Qed.
Global Hint Extern 2 (SemiGroup_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_semigroup_mor _ _) : typeclass_instances.

Lemma compose_monoid_mor {X Y Z} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f}
  : @Monoid_Morphism X Y op₁ e₁ op₂ e₂ f → @Monoid_Morphism Y Z op₂ e₂ op₃ e₃ g
  → Monoid_Morphism (g ∘ f).
Proof. intros. now split. Qed.
Global Hint Extern 2 (Monoid_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_monoid_mor _ _) : typeclass_instances.

Lemma invert_semigroup_mor `{SemiGroup_Morphism (f:=f)} `{!Inverse f} `{!Bijective f}
  : SemiGroup_Morphism (inverse f).
Proof. split; try exact _. intros x y.
  rew (injective_iff f _ _), (preserves_sg_op f _ _).
  now rew !3(surjective_applied f _).
Qed.
Global Hint Extern 2 (SemiGroup_Morphism (inverse _)) => simple notypeclasses refine invert_semigroup_mor : typeclass_instances.

Lemma invert_monoid_mor `{Monoid_Morphism (f:=f)} `{!Inverse f} `{!Bijective f}
  : Monoid_Morphism (inverse f).
Proof. now split. Qed.
Global Hint Extern 2 (Monoid_Morphism (inverse _)) => simple notypeclasses refine invert_monoid_mor : typeclass_instances.

Section groupmor_props.
  Universes i.
  Context `{Group@{i} G₁} `{Group G₂} (f : G₁ ⇾ G₂) `{!SemiGroup_Morphism f}.

  Instance group_mor: Monoid_Morphism f.
  Proof. split; try exact _. change (f e = e).
    apply (right_cancellation (∙) (f e)).
    rew <-(preserves_sg_op f _ _).
    now group_simplify.
  Qed.
  Let inst := group_mor.

  Lemma preserves_inverse x : f x⁻¹ = (f x)⁻¹.
  Proof.
    apply (left_cancellation (∙) (f x)).
    rew <-(preserves_sg_op f _ _).
    group_simplify.
    exact (preserves_unit _).
  Qed.

  Lemma preserves_op_inverse_r x y : f (x ∙ y⁻¹) = (f x) ∙ (f y)⁻¹.
  Proof. now rew (preserves_sg_op f _ _), (preserves_inverse _). Qed.

  Lemma preserves_op_inverse_l x y : f (x⁻¹ ∙ y) = (f x)⁻¹ ∙ (f y).
  Proof. now rew (preserves_sg_op f _ _), (preserves_inverse _). Qed.
End groupmor_props.
Global Hint Extern 10 (Monoid_Morphism _) => simple notypeclasses refine (group_mor _) : typeclass_instances.

Lemma grp_inverse_mor `{Group G} : Monoid_Morphism (X:=G) (Y:=G ᵒᵖ) (@inv G _).
Proof. refine (group_mor _). split; try exact _. exact inverse_distr. Qed.
Global Hint Extern 8 (Monoid_Morphism (⁻¹)) => simple notypeclasses refine grp_inverse_mor : typeclass_instances.

Lemma abgrp_inverse_mor `{AbGroup G} : Monoid_Morphism (@inv G _).
Proof. refine (group_mor _). split; try exact _. exact inverse_distr_ab. Qed.
Global Hint Extern 4 (Monoid_Morphism (⁻¹)) => simple notypeclasses refine abgrp_inverse_mor : typeclass_instances.

Lemma projected_semigroup
  `{SemiGroup S} `(f:X ⇾ S) `{!Injective f} `{SgOp X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → SemiGroup X.
Proof. intro op_correct. intros x y z.
  rew (injective_iff f _ _). rew ?(op_correct _ _).
  now apply associativity.
Qed.

Lemma projected_commutative_semigroup
  `{CommutativeSemiGroup S} `(f:X ⇾ S) `{!Injective f} `{SgOp X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → CommutativeSemiGroup X.
Proof. intro op_correct. pose proof projected_semigroup f op_correct.
  split; trivial. intros x y.
  rew (injective_iff f _ _). rew ?(op_correct _ _). now apply commutativity.
Qed.

Lemma projected_semilattice
  `{SemiLattice L} `(f:X ⇾ L) `{!Injective f} `{SgOp X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → SemiLattice X.
Proof. intro op_correct. pose proof projected_commutative_semigroup f op_correct.
  split; trivial. intros x.
  rew (injective_iff f _ _). rew ?(op_correct _ _). now apply binary_idempotency.
Qed.

Lemma projected_monoid
  `{Monoid M} `(f:X ⇾ M) `{!Injective f} `{SgOp X} `{MonUnit X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → f e = e
   → Monoid X.
Proof. intros op_correct unit_correct. pose proof projected_semigroup f op_correct.
  split; trivial; intros x; rew (injective_iff f _ _); rew ?(op_correct _ _);
  rew unit_correct.
  + now apply left_identity.
  + now apply right_identity.
Qed.

Lemma projected_commutative_monoid
  `{CommutativeMonoid M} `(f:X ⇾ M) `{!Injective f} `{SgOp X} `{MonUnit X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → f e = e
   → CommutativeMonoid X.
Proof. intros op_correct unit_correct.
  pose proof projected_commutative_semigroup f op_correct.
  pose proof projected_monoid f op_correct unit_correct.
  now split.
Qed.

Lemma projected_bounded_semilattice
  `{BoundedSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{SgOp X} `{MonUnit X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → f e = e
   → BoundedSemiLattice X.
Proof. intros op_correct unit_correct.
  pose proof projected_commutative_monoid f op_correct unit_correct.
  pose proof projected_semilattice f op_correct.
  now split.
Qed.

Lemma projected_group
  `{Group G} `(f:X ⇾ G) `{!Injective f} `{SgOp X} `{MonUnit X} `{Inv X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → f e = e
   → (∀ x, f x⁻¹ = (f x)⁻¹)
   → Group X.
Proof. intros op_correct unit_correct inv_correct.
  pose proof projected_monoid f op_correct unit_correct.
  split; trivial; intros x; rew (injective_iff f _ _); rew ?(op_correct _ _);
  rew unit_correct; rew (inv_correct _).
  + now apply left_inverse.
  + now apply right_inverse.
Qed.

Lemma projected_abgroup
  `{AbGroup G} `(f:X ⇾ G) `{!Injective f} `{SgOp X} `{MonUnit X} `{Inv X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → f e = e
   → (∀ x, f x⁻¹ = (f x)⁻¹)
   → AbGroup X.
Proof. intros op_correct unit_correct inv_correct.
  pose proof projected_group f op_correct unit_correct inv_correct.
  pose proof projected_commutative_monoid f op_correct unit_correct.
  now split.
Qed.

(** Quote *)

Lemma quote_sg_op_alt `(f:X ⇾ Y) `{SemiGroup_Morphism (X:=X) (Y:=Y) (f:=f)}
  {x₁ y₁ x₂ y₂} : quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ ∙ x₂) (y₁ ∙ y₂).
Proof. unfold quote. intros P Q. now rew (preserves_sg_op f _ _), P, Q. Qed.

Lemma quote_inverse_alt `{Group G₁} `{Group G₂} (f : G₁ ⇾ G₂) `{!SemiGroup_Morphism f}
  {x y} : quote f x y → quote f x⁻¹ y⁻¹.
Proof. unfold quote. intros P. now rew (preserves_inverse f _), P. Qed.

Global Hint Extern 4 (quote _ (_ ∙ _) _) => quote_hint_strip (fun f => refine (quote_sg_op_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ ∙ _)) => quote_hint_strip (fun f => refine (quote_sg_op_alt f _ _)) : quote.

Global Hint Extern 4 (quote _ (_⁻¹) _) => quote_hint_strip (fun f => refine (quote_inverse_alt f _)) : quote.
Global Hint Extern 4 (quote _ _ (_⁻¹)) => quote_hint_strip (fun f => refine (quote_inverse_alt f _)) : quote.



