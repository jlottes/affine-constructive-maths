Require Import interfaces.sprop abstract_algebra.
Require Import logic.aprop relations.
Require Import easy rewrite tactics.misc simplify.
Require Export theory.common_props theory.pointed.
Require Import quote.base.

Local Open Scope sg_op_scope.
Local Abbreviation e := mon_unit.
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

Definition alt_Build_StarSemiGroup `{SgOp G} `{Inv G} :
   @Associative G (∙)
 → Involutive (X:=G) inv
 → AntiDistribute (X:=G) inv (∙)
 → StarSemiGroup G.
Proof. now split. Defined.

Definition alt_Build_StarMonoid `{SgOp G} `{MonUnit G} `{Inv G} :
   @Associative G (∙)
 → LeftIdentity  (X:=G) (∙) e
 → RightIdentity (X:=G) (∙) e
 → Involutive (X:=G) inv
 → AntiDistribute (X:=G) inv (∙)
 → StarMonoid G.
Proof. intros; repeat (split; trivial). Defined.
 
Local Open Scope grp_scope.
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
Local Close Scope grp_scope.

Coercion monunit_inhabited `{MonUnit M} : Inhabited M.  Proof. now exists e. Defined.
Coercion monoid_inhabited `{Monoid M} : Inhabited M := _.

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
  Instance StarSemiGroup_op        `{StarSemiGroup G}        : StarSemiGroup (G ᵒᵖ).         Proof. go. Defined.
  Instance StarMonoid_op           `{StarMonoid G}           : StarMonoid (G ᵒᵖ).            Proof. go. Defined.
  Instance Group_op                `{Group G}                : Group (G ᵒᵖ).                 Proof. go. Defined.
  Instance AbGroup_op              `{AbGroup G}              : AbGroup (G ᵒᵖ).               Proof. go. Defined.
End opposite.
Global Hint Extern 2 (SemiGroup            (_ ᵒᵖ)) => simple notypeclasses refine SemiGroup_op            : typeclass_instances.
Global Hint Extern 2 (CommutativeSemiGroup (_ ᵒᵖ)) => simple notypeclasses refine CommutativeSemiGroup_op : typeclass_instances.
Global Hint Extern 2 (SemiLattice          (_ ᵒᵖ)) => simple notypeclasses refine SemiLattice_op          : typeclass_instances.
Global Hint Extern 2 (Monoid               (_ ᵒᵖ)) => simple notypeclasses refine Monoid_op               : typeclass_instances.
Global Hint Extern 2 (CommutativeMonoid    (_ ᵒᵖ)) => simple notypeclasses refine CommutativeMonoid_op    : typeclass_instances.
Global Hint Extern 2 (BoundedSemiLattice   (_ ᵒᵖ)) => simple notypeclasses refine BoundedSemiLattice_op   : typeclass_instances.
Global Hint Extern 2 (StarSemiGroup        (_ ᵒᵖ)) => simple notypeclasses refine StarSemiGroup_op        : typeclass_instances.
Global Hint Extern 2 (StarMonoid           (_ ᵒᵖ)) => simple notypeclasses refine StarMonoid_op           : typeclass_instances.
Global Hint Extern 2 (Group                (_ ᵒᵖ)) => simple notypeclasses refine Group_op                : typeclass_instances.
Global Hint Extern 2 (AbGroup              (_ ᵒᵖ)) => simple notypeclasses refine AbGroup_op              : typeclass_instances.

Lemma monoid_unit_unique_l `{Monoid M} (x:M) : LeftIdentity (∙) x → x = e.
Proof. intro. rew <-(right_identity (∙) x). exact (left_identity (∙) _). Qed.

Lemma monoid_unit_unique_r `{Monoid M} (x:M) : RightIdentity (∙) x → x = e.
Proof. exact (monoid_unit_unique_l (M:=M ᵒᵖ) x). Qed.

(** a simple group simplification tactic *)
Lemma simplify_mon_unit_identity_l `{MonUnit M} `{SgOp M} {P:LeftIdentity (X:=M) (∙) e} {x x':M} `{!SimplifiesTo x x'} : SimplifiesTo (e ∙ x) x'.
Proof. split. rew (simplify x). apply P. Qed.
Global Hint Extern 2 (SimplifiesTo (e ∙ _) _) => notypeclasses refine simplify_mon_unit_identity_l : typeclass_instances.

Lemma simplify_mon_unit_identity_r `{MonUnit M} `{SgOp M} {P:RightIdentity (X:=M) (∙) e} {x x':M} `{!SimplifiesTo x x'} : SimplifiesTo (x ∙ e) x'.
Proof. split. rew (simplify x). apply P. Qed.
Global Hint Extern 2 (SimplifiesTo (_ ∙ e) _) => notypeclasses refine simplify_mon_unit_identity_r : typeclass_instances.

Local Open Scope grp_scope.
Global Hint Extern 4 (SimplifiesTo (?x⁻¹ ∙ ?y) _) => match x with y => solve_simplify (inverse_l x) end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (?x ∙ ?y⁻¹) _) => match x with y => solve_simplify (inverse_r x) end : typeclass_instances.

Ltac group_basic :=
  repeat match goal with
  | |- context [ e ∙ ?x ] => rew (left_identity  (∙) (x:=e) x)
  | |- context [ ?x ∙ e ] => rew (right_identity (∙) (y:=e) x)
  | |- context [ ?x⁻¹ ∙ ?y ] => match x with y => rew (inverse_l x) end
  | |- context [ ?x ∙ ?y⁻¹ ] => match x with y => rew (inverse_r x) end
  end.
Ltac group_simplify := group_basic; repeat rew (associativity (∙) _ _ _); group_basic.


Lemma group_assoc_inv_l_3 `{Group G} (x y : G) : y ∙ x⁻¹ ∙ x = y.
Proof. rew <-(associativity (∙) _ _ _); now simplify. Qed.

Lemma group_assoc_inv_l_4 `{Group G} (x y z : G) : y ∙ z ∙ x⁻¹ ∙ x = y ∙ z.
Proof. rew <-(associativity (∙) _ _ x); now simplify. Qed.

Lemma group_assoc_inv_r_3 `{Group G} (x y : G) : y ∙ x ∙ x⁻¹ = y.
Proof. rew <-(associativity (∙) _ _ _); now simplify. Qed.

Lemma group_assoc_inv_r_4 `{Group G} (x y z : G) : y ∙ z ∙ x ∙ x⁻¹ = y ∙ z.
Proof. rew <-(associativity (∙) _ x _); now simplify. Qed.

Ltac group_basic ::=
  repeat match goal with
  | |- context [ e ∙ ?x ] => rew (left_identity  (∙) (x:=e) x)
  | |- context [ ?x ∙ e ] => rew (right_identity (∙) (y:=e) x)
  | |- context [ ?x⁻¹ ∙ ?y ] => match x with y => rew (inverse_l x) end
  | |- context [ ?x ∙ ?y⁻¹ ] => match x with y => rew (inverse_r x) end
  | |- context [ ?y ∙ ?x⁻¹ ∙ ?z ] => match x with z => rew (group_assoc_inv_l_3 x y) end
  | |- context [ ?y ∙ ?x ∙ ?z⁻¹ ] => match x with z => rew (group_assoc_inv_r_3 x y) end
  | |- context [ ?y ∙ ?z ∙ ?x⁻¹ ∙ ?w ] => match x with w => rew (group_assoc_inv_l_4 x y z) end
  | |- context [ ?y ∙ ?z ∙ ?x ∙ ?w⁻¹ ] => match x with w => rew (group_assoc_inv_r_4 x y z) end
  end.

Local Ltac simplify_chain tm := match goal with |- SimplifiesTo ?x ?y => change (SimplifiesToR (x,y)); trans tm end.
Lemma simplify_group_inv_l_3 `{Group G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (y ∙ x⁻¹ ∙ x) y'.
Proof. simplify_chain y; trivial; split. apply group_assoc_inv_l_3. Qed.
Lemma simplify_group_inv_r_3 `{Group G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (y ∙ x ∙ x⁻¹) y'.
Proof. simplify_chain y; trivial; split. apply group_assoc_inv_r_3. Qed.
Lemma simplify_group_assoc_inv_l_3 `{Group G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x⁻¹ ∙ (x ∙ y)) y'.
Proof. simplify_chain y; trivial; split. now group_simplify. Qed.
Lemma simplify_group_assoc_inv_r_3 `{Group G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x ∙ (x⁻¹ ∙ y)) y'.
Proof. simplify_chain y; trivial; split. now group_simplify. Qed.
Lemma simplify_abgroup_inv_l_3 `{AbGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x⁻¹ ∙ y ∙ x) y'.
Proof. simplify_chain y; trivial; split. rew (commutativity (∙) _ y). apply group_assoc_inv_l_3. Qed.
Lemma simplify_abgroup_inv_r_3 `{AbGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x ∙ y ∙ x⁻¹) y'.
Proof. simplify_chain y; trivial; split. rew (commutativity (∙) _ y). apply group_assoc_inv_r_3. Qed.
Lemma simplify_abgroup_assoc_inv_l_3 `{AbGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x⁻¹ ∙ (y ∙ x)) y'.
Proof. split. rew (associativity (∙) _ _ _). apply simplify_abgroup_inv_l_3. Qed.
Lemma simplify_abgroup_assoc_inv_r_3 `{AbGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x ∙ (y ∙ x⁻¹)) y'.
Proof. split. rew (associativity (∙) _ _ _). apply simplify_abgroup_inv_r_3. Qed.
Global Hint Extern 4 (SimplifiesTo (_ ∙ (?x)⁻¹ ∙ ?y) _) => match x with y => notypeclasses refine simplify_group_inv_l_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (_ ∙ ?x ∙ (?y)⁻¹) _) => match x with y => notypeclasses refine simplify_group_inv_r_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo ((?x)⁻¹ ∙ (?y ∙ _)) _) => match x with y => notypeclasses refine simplify_group_assoc_inv_l_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (?x ∙ ((?y)⁻¹ ∙ _)) _) => match x with y => notypeclasses refine simplify_group_assoc_inv_r_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo ((?x)⁻¹ ∙ _ ∙ ?y) _) => match x with y => notypeclasses refine simplify_abgroup_inv_l_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (?x ∙ _ ∙ (?y)⁻¹) _) => match x with y => notypeclasses refine simplify_abgroup_inv_r_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo ((?x)⁻¹ ∙ (_ ∙ ?y)) _) => match x with y => notypeclasses refine simplify_abgroup_assoc_inv_l_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (?x ∙ (_ ∙ (?y)⁻¹)) _) => match x with y => notypeclasses refine simplify_abgroup_assoc_inv_r_3 end : typeclass_instances.



Global Hint Extern 2 (Inverse (@inv ?G ?f)) => notypeclasses refine (@inv G f) : typeclass_instances.

Global Hint Extern 4 (Bijective  (⁻¹)) => simple notypeclasses refine inv_involutive : typeclass_instances.
Global Hint Extern 4 (Injective  (⁻¹)) => simple notypeclasses refine inv_involutive : typeclass_instances.
Global Hint Extern 4 (Surjective (⁻¹)) => simple notypeclasses refine inv_involutive : typeclass_instances.

Coercion group_star_mon `{Group G} : StarMonoid G.
Proof. apply alt_Build_StarMonoid; try exact _.
+ intros x; simplify.
  rew <-(left_identity (∙) x) at 2.
  rew <-(inverse_l x⁻¹).
  now rew (group_assoc_inv_l_3 _ _).
+ intros x y.
  rew <-(left_identity (∙) (y⁻¹ ∙ x⁻¹)), <-(inverse_l (x ∙ y)).
  do 2 rew <-(associativity (∙) _ _ _). now group_simplify.
Qed.

Lemma simplify_inv_involutive `{StarSemiGroup G} {x x' : G} `{!SimplifiesTo x x'} : SimplifiesTo ((x⁻¹)⁻¹) (x').
Proof. split. rew (simplify x). exact (involutive_alt _ _). Qed.
Global Hint Extern 4 (SimplifiesTo (((_)⁻¹)⁻¹) _) => notypeclasses refine simplify_inv_involutive : typeclass_instances.

Definition inv_distr `{StarSemiGroup G} : ∀ x y : G, (x ∙ y)⁻¹ = y⁻¹ ∙ x⁻¹ := anti_distribute _ _.

Lemma inv_com_distr `{StarSemiGroup G} `{!Commutative (X:=G) (∙)} : Distribute (X:=G) inv (∙).
Proof. intros x y. rew (commutativity (∙) x⁻¹_ ). now apply anti_distribute. Qed.

Definition inv_distr_ab `{StarSemiGroup G} `{!Commutative (X:=G) (∙)}
  : ∀ x y : G, (x ∙ y)⁻¹ = x⁻¹ ∙ y⁻¹ := inv_com_distr.

Lemma inv_unit `{StarMonoid G} : e⁻¹ = e :> G.
Proof. apply monoid_unit_unique_l. intros y.
  rew <-(involutive_alt inv y) at 1.
  rew <-(inv_distr _ _).
  rew (right_identity _ _).
  exact (involutive_alt _ _).
Qed.
Global Hint Extern 4 (SimplifiesTo (e⁻¹) _) => solve_simplify inv_unit : typeclass_instances.

Ltac group_basic ::=
  repeat match goal with
  | |- context [ e⁻¹ ] => rew inv_unit
  | |- context [ e ∙ ?x ] => rew (left_identity  (∙) (x:=e) x)
  | |- context [ ?x ∙ e ] => rew (right_identity (∙) (y:=e) x)
  | |- context [ ?x⁻¹ ∙ ?y ] => match x with y => rew (inverse_l x) end
  | |- context [ ?x ∙ ?y⁻¹ ] => match x with y => rew (inverse_r x) end
  | |- context [ (?x⁻¹)⁻¹ ] => rew (involutive_alt (⁻¹) x)
  | |- context [ ?y ∙ ?x⁻¹ ∙ ?z ] => match x with z => rew (group_assoc_inv_l_3 x y) end
  | |- context [ ?y ∙ ?x ∙ ?z⁻¹ ] => match x with z => rew (group_assoc_inv_r_3 x y) end
  | |- context [ ?y ∙ ?z ∙ ?x⁻¹ ∙ ?w ] => match x with w => rew (group_assoc_inv_l_4 x y z) end
  | |- context [ ?y ∙ ?z ∙ ?x ∙ ?w⁻¹ ] => match x with w => rew (group_assoc_inv_r_4 x y z) end
  | |- context [ (?x ∙ ?y)⁻¹ ] => rew (inv_distr x y)
  end.

Lemma inv_swap_r `{StarSemiGroup G} (x y : G) : x ∙ y⁻¹ = (y ∙ x⁻¹)⁻¹.
Proof. now group_simplify. Qed.

Lemma inv_swap_l_ab `{StarSemiGroup G} `{!Commutative (X:=G) (∙)} (x y : G) : x⁻¹ ∙ y = (x ∙ y⁻¹)⁻¹.
Proof. rew (inv_distr_ab _ _). now group_simplify. Qed.

Lemma group_left_op_inj `{Group G} (z:G) : Injective (z ∙).
Proof. intros x y; simplify.
  rew <-(left_identity (∙) x) at 2.
  rew <-(left_identity (∙) y) at 2.
  rew <-(inverse_l z).
  rew <-(associativity (∙) _ _ _).
  exact (is_fun (z⁻¹ ∙) _ _).
Qed.
Global Hint Extern 5 (Injective (_ ∙)) => simple notypeclasses refine (group_left_op_inj _) : typeclass_instances.

Lemma group_right_op_inj `{Group G} (z:G) : Injective (∙ z).
Proof. exact (group_left_op_inj (G := G ᵒᵖ) z). Qed.
Global Hint Extern 5 (Injective (∙ _)) => simple notypeclasses refine (group_right_op_inj _) : typeclass_instances.

Lemma equal_by_inverse `{Group G} (x y : G) : x ∙ y⁻¹ = e ⧟ x = y.
Proof. now rew (injective_iff_simp (∙y) _ e). Qed.

Lemma flip_inv `{StarSemiGroup G} (x y : G) : x⁻¹ = y ⧟ x = y⁻¹.
Proof. now rew (injective_iff_simp (⁻¹) _ y). Qed.

Lemma flip_inv_unit `{StarMonoid G} (x y : G) : x⁻¹ = e ⧟ x = e.
Proof. now rew (injective_iff_simp (⁻¹) x _). Qed.

Lemma group_op_strong `{Group G} `{!StrongOp (X:=G) (∙)} : StrongSet G.
Proof. intros x y z.
  rew (injective_iff_simp (∙ y⁻¹) x y).
  (* FIX ME *)
  assert (x = (x ∙ y⁻¹) ∙ y) as E by now group_simplify. rew E at 2. clear E.
  assert (z = e ∙ z) as E by now group_simplify. rew E at 2. clear E.
  exact (is_fun (strong_op (∙)) (_, _) (_, _)).
Qed.

(** Morphisms *)

Lemma SemiGroup_Morphism_proper_impl@{u} {X Y:set@{u}} {Xop:SgOp X} {Yop:SgOp Y} {f g : X ⇾ Y}
  : f = g → impl (SemiGroup_Morphism f, SemiGroup_Morphism g).
Proof. intros E H; split; try exact _. rew <-E. apply H. Qed.
Canonical Structure SemiGroup_Morphism_fun {X Y Xop Yop} :=
  make_weak_spred (@SemiGroup_Morphism X Y Xop Yop) (@SemiGroup_Morphism_proper_impl _ _ _ _).

Lemma Monoid_Morphism_proper_impl@{u} {X Y:set@{u}} {Xop:SgOp X} {Xunit:MonUnit X} {Yop:SgOp Y} {Yunit:MonUnit Y} {f g : X ⇾ Y}
  : f = g → impl (Monoid_Morphism f, Monoid_Morphism g).
Proof. intros E H; split; try exact _; now rew <-E. Qed.
Canonical Structure Monoid_Morphism_fun {X Y Xop Xunit Yop Yunit} :=
  make_weak_spred (@Monoid_Morphism X Y Xop Xunit Yop Yunit) (@Monoid_Morphism_proper_impl _ _ _ _ _ _).

Lemma StarSemiGroup_Morphism_proper_impl@{u} {X Y:set@{u}} {Xop:SgOp X} {Yop:SgOp Y} {Xinv:Inv X} {Yinv:Inv Y} {f g : X ⇾ Y}
  : f = g → impl (StarSemiGroup_Morphism f, StarSemiGroup_Morphism g).
Proof. intros E H; split; try exact _; intros; rew <-E; apply H. Qed.
Canonical Structure StarSemiGroup_Morphism_fun {X Y Xop Yop Xinv Yinv} :=
  make_weak_spred (@StarSemiGroup_Morphism X Y Xop Yop Xinv Yinv) (@StarSemiGroup_Morphism_proper_impl _ _ _ _ _ _).

Lemma StarMonoid_Morphism_proper_impl@{u} {X Y:set@{u}} {Xop:SgOp X} {Yop:SgOp Y} {Xunit:MonUnit X} {Yunit:MonUnit Y} {Xinv:Inv X} {Yinv:Inv Y} {f g : X ⇾ Y}
  : f = g → impl (StarMonoid_Morphism f, StarMonoid_Morphism g).
Proof. intros E H; split; try exact _; rew <-E; apply H. Qed.
Canonical Structure StarMonoid_Morphism_fun {X Y Xop Yop Xunit Yunit Xinv Yinv} :=
  make_weak_spred (@StarMonoid_Morphism X Y Xop Yop Xunit Yunit Xinv Yinv) (@StarMonoid_Morphism_proper_impl _ _ _ _ _ _ _ _).


Lemma alt_Build_Monoid_Morphism@{u} {X Y:set@{u}} `{Monoid (X:=X)} `{Monoid (X:=Y)} (f:X ⇾ Y):
   (∀ x y, f (x ∙ y) = f x ∙ f y)
→  (f e = e)
→ Monoid_Morphism f.
Proof. now split. Qed.

Lemma alt_Build_StarSemiGroup_Morphism@{u} {X Y:set@{u}} `{StarSemiGroup X} `{StarSemiGroup Y} (f:X ⇾ Y):
   (∀ x y, f (x ∙ y) = f x ∙ f y)
→  (∀ x, f x⁻¹ = (f x)⁻¹)
→ StarSemiGroup_Morphism f.
Proof. intros; split; trivial. now split. Qed.

Lemma alt_Build_StarMonoid_Morphism@{u} {X Y:set@{u}} `{StarMonoid X} `{StarMonoid Y} (f:X ⇾ Y):
   (∀ x y, f (x ∙ y) = f x ∙ f y)
→  (f e = e)
→  (∀ x, f x⁻¹ = (f x)⁻¹)
→ StarMonoid_Morphism f.
Proof. intros; split; trivial.
+ now apply alt_Build_Monoid_Morphism.
+ now apply alt_Build_StarSemiGroup_Morphism.
Qed.


Lemma id_semigroup_mor `{SemiGroup G} : SemiGroup_Morphism (id_fun G).
Proof. now split. Qed.
Global Hint Extern 2 (SemiGroup_Morphism (id_fun _)) => simple notypeclasses refine id_semigroup_mor : typeclass_instances.

Lemma id_monoid_mor `{Monoid M} : Monoid_Morphism (id_fun M).
Proof. now apply alt_Build_Monoid_Morphism. Qed.
Global Hint Extern 2 (Monoid_Morphism (id_fun _)) => simple notypeclasses refine id_monoid_mor : typeclass_instances.

Lemma id_star_semigroup_mor `{StarSemiGroup G} : StarSemiGroup_Morphism (id_fun G).
Proof. now apply alt_Build_StarSemiGroup_Morphism. Qed.
Global Hint Extern 2 (StarSemiGroup_Morphism (id_fun _)) => simple notypeclasses refine id_star_semigroup_mor : typeclass_instances.

Lemma id_star_monoid_mor `{StarMonoid M} : StarMonoid_Morphism (id_fun M).
Proof. now apply alt_Build_StarMonoid_Morphism. Qed.
Global Hint Extern 2 (StarMonoid_Morphism (id_fun _)) => simple notypeclasses refine id_star_monoid_mor : typeclass_instances.

Lemma compose_semigroup_mor@{u} {X Y Z:set@{u}} {op₁ op₂ op₃} {g f}
  : @SemiGroup_Morphism X Y op₁ op₂ f → @SemiGroup_Morphism Y Z op₂ op₃ g
  → SemiGroup_Morphism (g ∘ f).
Proof. intros. split; try exact _. intros x y.
  change (g (f (x ∙ y)) = g (f x) ∙ g (f y)).
  rew (preserves_sg_op f _ _). exact (preserves_sg_op g _ _).
Qed.
Global Hint Extern 2 (SemiGroup_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_semigroup_mor _ _) : typeclass_instances.

Lemma compose_monoid_mor@{u} {X Y Z:set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f}
  : @Monoid_Morphism X Y op₁ e₁ op₂ e₂ f → @Monoid_Morphism Y Z op₂ e₂ op₃ e₃ g
  → Monoid_Morphism (g ∘ f).
Proof. intros. now split. Qed.
Global Hint Extern 2 (Monoid_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_monoid_mor _ _) : typeclass_instances.

Lemma compose_star_semigroup_mor@{u} {X Y Z:set@{u}} {op₁ op₂ op₃} {inv₁ inv₂ inv₃} {g f}
  : @StarSemiGroup_Morphism X Y op₁ op₂ inv₁ inv₂ f → @StarSemiGroup_Morphism Y Z op₂ op₃ inv₂ inv₃ g
  → StarSemiGroup_Morphism (g ∘ f).
Proof. intros. split; try exact _. intros x.
  change (g (f x⁻¹) = (g (f x))⁻¹).
  rew (preserves_inv f _). exact (preserves_inv g _).
Qed.
Global Hint Extern 2 (StarSemiGroup_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_star_semigroup_mor _ _) : typeclass_instances.

Lemma compose_star_monoid_mor@{u} {X Y Z:set@{u}} {op₁ e₁ inv₁} {op₂ e₂ inv₂} {op₃ e₃ inv₃} {g f}
  : @StarMonoid_Morphism X Y op₁ op₂ e₁ e₂ inv₁ inv₂ f → @StarMonoid_Morphism Y Z op₂ op₃ e₂ e₃ inv₂ inv₃ g
  → StarMonoid_Morphism (g ∘ f).
Proof. intros. now split. Qed.
Global Hint Extern 2 (StarMonoid_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_star_monoid_mor _ _) : typeclass_instances.

Lemma invert_semigroup_mor `{SemiGroup_Morphism (f:=f)} `{!Inverse f, !Bijective f}
  : SemiGroup_Morphism (inverse f).
Proof. split; try exact _. intros x y.
  rew (injective_iff f _ _), (preserves_sg_op f _ _).
  now rew (surjective_applied f _).
Qed.
Global Hint Extern 2 (SemiGroup_Morphism (inverse _)) => simple notypeclasses refine invert_semigroup_mor : typeclass_instances.

Lemma invert_monoid_mor `{Monoid_Morphism (f:=f)} `{!Inverse f, !Bijective f}
  : Monoid_Morphism (inverse f).
Proof. now split. Qed.
Global Hint Extern 2 (Monoid_Morphism (inverse _)) => simple notypeclasses refine invert_monoid_mor : typeclass_instances.

Lemma invert_star_semigroup_mor `{StarSemiGroup_Morphism (f:=f)} `{!Inverse f, !Bijective f}
  : StarSemiGroup_Morphism (inverse f).
Proof. split; try exact _. intros x.
  rew (injective_iff f _ _), (preserves_inv f _).
  now rew !(surjective_applied f _).
Qed.
Global Hint Extern 2 (StarSemiGroup_Morphism (inverse _)) => simple notypeclasses refine invert_star_semigroup_mor : typeclass_instances.

Lemma invert_star_monoid_mor `{StarMonoid_Morphism (f:=f)} `{!Inverse f, !Bijective f}
  : StarMonoid_Morphism (inverse f).
Proof. now split. Qed.
Global Hint Extern 2 (StarMonoid_Morphism (inverse _)) => simple notypeclasses refine invert_star_monoid_mor : typeclass_instances.


Lemma preserves_op_inv_r `{StarSemiGroup_Morphism (f:=f)} x y : f (x ∙ y⁻¹) = (f x) ∙ (f y)⁻¹.
Proof. now rew (preserves_sg_op f _ _), (preserves_inv f _). Qed.
Arguments preserves_op_inv_r {_ _ _ _ _ _} f {_} x y.

Lemma preserves_op_inv_l `{StarSemiGroup_Morphism (f:=f)} x y : f (x⁻¹ ∙ y) = (f x)⁻¹ ∙ (f y).
Proof. now rew (preserves_sg_op f _ _), (preserves_inv f _). Qed.
Arguments preserves_op_inv_l {_ _ _ _ _ _} f {_} x y.

Section groupmor_props.
  Universes u.
  Context `{Group@{u} G₁} `{Group@{u} G₂} (f : G₁ ⇾ G₂) `{!SemiGroup_Morphism f}.

  Local Instance: MonUnit_Pointed_Morphism f.
  Proof. change (f e = e).
    rew (injective_iff_simp (∙ f e) _ _).
    rew <-(preserves_sg_op f _ _).
    now simplify.
  Qed.
  
  Instance group_mor: StarMonoid_Morphism f.
  Proof. apply alt_Build_StarMonoid_Morphism.
  + exact (preserves_sg_op f).
  + exact (preserves_unit f).
  + intros x. rew (injective_iff_simp (f x ∙) _ _).
    rew <-(preserves_sg_op f _ _).
    simplify.
    exact (preserves_unit _).
  Qed.
End groupmor_props.
Global Hint Extern 10 (Monoid_Morphism _) => simple notypeclasses refine (group_mor _) : typeclass_instances.
Global Hint Extern 10 (StarSemiGroup_Morphism _) => simple notypeclasses refine (group_mor _) : typeclass_instances.
Global Hint Extern 10 (StarMonoid_Morphism _) => simple notypeclasses refine (group_mor _) : typeclass_instances.

Lemma inv_sg_mor `{StarSemiGroup G} : SemiGroup_Morphism (X:=G) (Y:=G ᵒᵖ) (@inv G _).
Proof. split; try exact _. exact inv_distr. Qed.
Global Hint Extern 8 (SemiGroup_Morphism (⁻¹)) => simple notypeclasses refine inv_sg_mor : typeclass_instances.

Lemma inv_mon_mor `{StarMonoid G} : Monoid_Morphism (X:=G) (Y:=G ᵒᵖ) (@inv G _).
Proof. split; try exact _. exact inv_unit. Qed.
Global Hint Extern 8 (Monoid_Morphism (⁻¹)) => simple notypeclasses refine inv_mon_mor : typeclass_instances.
Global Hint Extern 4 (MonUnit_Pointed_Morphism (⁻¹)) => simple notypeclasses refine inv_mon_mor : typeclass_instances.

Lemma inv_com_sg_mor `{StarSemiGroup G} `{!Commutative (X:=G) (∙)} : SemiGroup_Morphism (@inv G _).
Proof. split; try exact _. exact inv_distr_ab. Qed.
Global Hint Extern 4 (SemiGroup_Morphism (⁻¹)) => simple notypeclasses refine inv_com_sg_mor : typeclass_instances.

Lemma inv_com_mon_mor `{StarMonoid G} `{!Commutative (X:=G) (∙)} : Monoid_Morphism (@inv G _).
Proof. now split. Qed.
Global Hint Extern 4 (Monoid_Morphism (⁻¹)) => simple notypeclasses refine inv_com_mon_mor : typeclass_instances.

Lemma inv_star_sg_mor `{StarSemiGroup G} : StarSemiGroup_Morphism (X:=G) (Y:=G ᵒᵖ) (@inv G _).
Proof. split; try exact _. intros x. exact (reflexivity (=) _). Qed.
Global Hint Extern 8 (StarSemiGroup_Morphism (⁻¹)) => simple notypeclasses refine inv_star_sg_mor : typeclass_instances.

Lemma inv_star_mon_mor `{StarMonoid G} : StarMonoid_Morphism (X:=G) (Y:=G ᵒᵖ) (@inv G _).
Proof. now split. Qed.
Global Hint Extern 8 (StarMonoid_Morphism (⁻¹)) => simple notypeclasses refine inv_star_mon_mor : typeclass_instances.

Lemma inv_com_star_sg_mor `{StarSemiGroup G} `{!Commutative (X:=G) (∙)} : StarSemiGroup_Morphism (@inv G _).
Proof. split; try exact _. Qed.
Global Hint Extern 4 (StarSemiGroup_Morphism (⁻¹)) => simple notypeclasses refine inv_com_star_sg_mor : typeclass_instances.

Lemma inv_com_star_mon_mor `{StarMonoid G} `{!Commutative (X:=G) (∙)} : StarMonoid_Morphism (@inv G _).
Proof. now split. Qed.
Global Hint Extern 4 (StarMonoid_Morphism (⁻¹)) => simple notypeclasses refine inv_com_star_mon_mor : typeclass_instances.


Lemma projected_semigroup@{u} {X S:set@{u}}
  `{SemiGroup S} `(f:X ⇾ S) `{!Injective f} `{SgOp X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → SemiGroup X.
Proof. intro op_correct. intros x y z.
  rew (injective_iff f _ _). rew ?(op_correct _ _).
  now apply associativity.
Qed.

Lemma projected_commutative_semigroup@{u} {X S:set@{u}}
  `{CommutativeSemiGroup S} `(f:X ⇾ S) `{!Injective f} `{SgOp X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → CommutativeSemiGroup X.
Proof. intro op_correct. pose proof projected_semigroup f op_correct.
  split; trivial. intros x y.
  rew (injective_iff f _ _). rew ?(op_correct _ _). now apply commutativity.
Qed.

Lemma projected_semilattice@{u} {X L:set@{u}}
  `{SemiLattice L} `(f:X ⇾ L) `{!Injective f} `{SgOp X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → SemiLattice X.
Proof. intro op_correct. pose proof projected_commutative_semigroup f op_correct.
  split; trivial. intros x.
  rew (injective_iff f _ _). rew ?(op_correct _ _). now apply binary_idempotency.
Qed.

Lemma projected_monoid@{u} {X M:set@{u}}
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

Lemma projected_commutative_monoid@{u} {X M:set@{u}}
  `{CommutativeMonoid M} `(f:X ⇾ M) `{!Injective f} `{SgOp X} `{MonUnit X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → f e = e
   → CommutativeMonoid X.
Proof. intros op_correct unit_correct.
  pose proof projected_commutative_semigroup f op_correct.
  pose proof projected_monoid f op_correct unit_correct.
  now split.
Qed.

Lemma projected_bounded_semilattice@{u} {X L:set@{u}}
  `{BoundedSemiLattice L} `(f:X ⇾ L) `{!Injective f} `{SgOp X} `{MonUnit X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → f e = e
   → BoundedSemiLattice X.
Proof. intros op_correct unit_correct.
  pose proof projected_commutative_monoid f op_correct unit_correct.
  pose proof projected_semilattice f op_correct.
  now split.
Qed.

Lemma projected_star_semigroup@{u} {X G:set@{u}}
  `{StarSemiGroup G} `(f:X ⇾ G) `{!Injective f} `{SgOp X} `{Inv X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → (∀ x, f x⁻¹ = (f x)⁻¹)
   → StarSemiGroup X.
Proof. intros op_correct inv_correct.
  pose proof projected_semigroup f op_correct.
  apply alt_Build_StarSemiGroup; trivial.
  + intros x. rew (injective_iff f _ _). simplify. rew !(inv_correct _).
    exact (involutive_alt _ _).
  + intros x y. rew (injective_iff f _ _).
    rew (inv_correct _), (op_correct _ _), (inv_correct _).
    now apply anti_distribute.
Qed.

Lemma projected_star_monoid@{u} {X G:set@{u}}
  `{StarMonoid G} `(f:X ⇾ G) `{!Injective f} `{SgOp X} `{MonUnit X} `{Inv X} :
   (∀ x y, f (x ∙ y) = f x ∙ f y)
   → f e = e
   → (∀ x, f x⁻¹ = (f x)⁻¹)
   → StarMonoid X.
Proof. intros op_correct unit_correct inv_correct.
  pose proof projected_star_semigroup f op_correct inv_correct.
  pose proof projected_monoid f op_correct unit_correct.
  now split.
Qed.

Lemma projected_group@{u} {X G:set@{u}}
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

Lemma projected_abgroup@{u} {X G:set@{u}}
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

Lemma quote_inv_alt `(f:X ⇾ Y) `{StarSemiGroup_Morphism (X:=X) (Y:=Y) (f:=f)}
  {x y} : quote f x y → quote f x⁻¹ y⁻¹.
Proof. unfold quote. intros P. now rew (preserves_inv f _), P. Qed.

Global Hint Extern 4 (quote _ (_ ∙ _) _) => quote_hint_strip (fun f => refine (quote_sg_op_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ ∙ _)) => quote_hint_strip (fun f => refine (quote_sg_op_alt f _ _)) : quote.

Global Hint Extern 4 (quote _ (_⁻¹) _) => quote_hint_strip (fun f => refine (quote_inv_alt f _)) : quote.
Global Hint Extern 4 (quote _ _ (_⁻¹)) => quote_hint_strip (fun f => refine (quote_inv_alt f _)) : quote.

