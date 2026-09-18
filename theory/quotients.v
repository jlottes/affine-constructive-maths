Require Import logic.aprop easy.
Require Import theory.set interfaces.subset.
Require Import theory.product_algebras.
Require Import theory.subgroups.
Require Import theory.additive_groups.
Require Import rewrite.

Definition quotient_set (X:set) (R:𝒫 (X ⊗ X)) `{!Equivalence  R}: set := @set_make X R _.

Module quotient_set_notation.
  Notation "X / R" := (quotient_set X R) (at level 40) : set_scope.
End quotient_set_notation.
Import quotient_set_notation.

Section to_quotient.
  Context {X:set} (R:𝒫 (X ⊗ X)) `{!Equivalence R}.

  Lemma quotient_subrel : Subrelation (@equiv X _) (@equiv (X/R) _).
  Proof. intros [x y]. change (x = y ⊸ (x, y) ∊ R).
    rew <-(equal_element R (x, x) (x, y)).
    rew (aprod_true_r (reflexivity R x : (x, x) ∊ R)).
    change (x = y ⊸ x = x ⊠ x = y).
    now rew (aprod_true_l (reflexivity (=) x)).
  Qed.

  Lemma to_quotient_is_fun : @IsFun X (X/R) id.
  Proof. intros x y. apply quotient_subrel. Qed.
  Definition to_quotient := @func_make _ _ _ to_quotient_is_fun.
End to_quotient.

Global Hint Extern 2 (Subrelation (@equiv (set_T ?X) _) (@equiv (set_T (?X / _)) _)) => simple notypeclasses refine (quotient_subrel _) : typeclass_instances.

Section lift_op.
  Universes u.
  Context {X:set@{u}} {R:𝒫 (X ⊗ X)} `{!Equivalence R}.
  Context {Y:set@{u}} {S:𝒫 (Y ⊗ Y)} `{!Equivalence S}.
  Context (f:X ⇾ Y) `{!MapsTo (tensor_map f f) R S}.

  Definition quotient_lift_op_is_fun : @IsFun (X/R) (Y/S) f
  := λ x₁ x₂, maps_to (tensor_map f f) R S (x₁, x₂).

  Definition quotient_lift_op := @func_make _ _ _ quotient_lift_op_is_fun.
End lift_op.

Section lift_op2.
  Universes u.
  Context {X:set@{u}} {R:𝒫 (X ⊗ X)} `{!Equivalence R}.
  Context {Y:set@{u}} {S:𝒫 (Y ⊗ Y)} `{!Equivalence S}.
  Context {Z:set@{u}} {T:𝒫 (Z ⊗ Z)} `{!Equivalence T}.
  Context (f:X ⊗ Y ⇾ Z) `{!MapsTo (tensor_map2 (f, f)) (R ⊗ S) T}.

  Lemma quotient_lift_op2_is_fun : @IsFun ((X/R)⊗(Y/S)) (Z/T) f.
  Proof. intros [x₁ y₁][x₂ y₂]. exact (maps_to (tensor_map2 (f, f)) (R ⊗ S) T ((x₁, x₂), (y₁, y₂))). Qed.

  Definition quotient_lift_op2 := @func_make _ _ _ quotient_lift_op2_is_fun.
End lift_op2.

Section props.
  Universes u.
  Context {X:set@{u}} {R:𝒫 (X ⊗ X)} `{!Equivalence R}.
  Context {Y:set@{u}} {S:𝒫 (Y ⊗ Y)} `{!Equivalence S}.
  Context {Z:set@{u}} {T:𝒫 (Z ⊗ Z)} `{!Equivalence T}.

  Local Ltac doit := intros H; hnf; intros; apply (quotient_subrel _ _), H.

  Lemma quotient_associative       {f}     `{!MapsTo (tensor_map2 (f, f)) (R ⊗ R) R}                                           : @Associative      X     f   → Associative      (quotient_lift_op2 f).  Proof. doit. Qed.
  Lemma quotient_commutative       {f}     `{!MapsTo (tensor_map2 (f, f)) (R ⊗ R) S}                                           : @Commutative      X Y   f   → Commutative      (quotient_lift_op2 f).  Proof. doit. Qed.
  Lemma quotient_binary_idempotent {f}     `{!MapsTo (tensor_map2 (f, f)) (R ⊗ R) R}                                           : @BinaryIdempotent X     f   → BinaryIdempotent (quotient_lift_op2 f).  Proof. doit. Qed.
  (*Lemma quotient_involutive        {f}     `{!MapsTo (tensor_map   f f  )  R      R}                                           : @Involutive       X     f   → Involutive       (quotient_lift_op  f).  Proof. doit. Qed.*)
  Lemma quotient_absorption        {f g}   `{!MapsTo (tensor_map2 (f, f)) (R ⊗ T) R, !MapsTo (tensor_map2 (g, g)) (R ⊗ S) T} : @Absorption       X Y Z f g → Absorption       (quotient_lift_op2 f) (quotient_lift_op2 g).  Proof. doit. Qed.
  Lemma quotient_left_distribute   {f g}   `{!MapsTo (tensor_map2 (f, f)) (R ⊗ R) R, !MapsTo (tensor_map2 (g, g)) (R ⊗ R) R} : @LeftDistribute   X     f g → LeftDistribute   (quotient_lift_op2 f) (quotient_lift_op2 g).  Proof. doit. Qed.
  Lemma quotient_right_distribute  {f g}   `{!MapsTo (tensor_map2 (f, f)) (R ⊗ R) R, !MapsTo (tensor_map2 (g, g)) (R ⊗ R) R} : @RightDistribute  X     f g → RightDistribute  (quotient_lift_op2 f) (quotient_lift_op2 g).  Proof. doit. Qed.

  Lemma quotient_left_identity     {f   x} `{!MapsTo (tensor_map2 (f, f)) (R ⊗ S) S}                                           : @LeftIdentity     X Y   f x → LeftIdentity     (quotient_lift_op2 f) (to_quotient R x).  Proof. doit. Qed.
  Lemma quotient_right_identity    {f   y} `{!MapsTo (tensor_map2 (f, f)) (R ⊗ S) R}                                           : @RightIdentity    X Y   f y → RightIdentity    (quotient_lift_op2 f) (to_quotient S y).  Proof. doit. Qed.
  Lemma quotient_left_absorb       {f   x} `{!MapsTo (tensor_map2 (f, f)) (R ⊗ S) R}                                           : @LeftAbsorb       X Y   f x → LeftAbsorb       (quotient_lift_op2 f) (to_quotient R x).  Proof. doit. Qed.
  Lemma quotient_right_absorb      {f   y} `{!MapsTo (tensor_map2 (f, f)) (R ⊗ S) S}                                           : @RightAbsorb      X Y   f y → RightAbsorb      (quotient_lift_op2 f) (to_quotient S y).  Proof. doit. Qed.

  Lemma quotient_left_inverse      {f g z} `{!MapsTo (tensor_map2 (f, f)) (R ⊗ S) T, !MapsTo (tensor_map  g g   )  S      R} : @LeftInverse      X Y Z f g z → LeftInverse    (quotient_lift_op2 f) (quotient_lift_op g) (to_quotient T z).  Proof. doit. Qed.
  Lemma quotient_right_inverse     {f g z} `{!MapsTo (tensor_map2 (f, f)) (R ⊗ S) T, !MapsTo (tensor_map  g g   )  R      S} : @RightInverse     X Y Z f g z → RightInverse   (quotient_lift_op2 f) (quotient_lift_op g) (to_quotient T z).  Proof. doit. Qed.
End props.

Local Instance quotient_sg_op_closed `{H1:SemiGroup (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:SubSemiGroup R}
  : MapsTo (tensor_map2 (sg_op, sg_op)) (R ⊗ R) R.
Proof. intros [p q]. exact (sub_sg_closed R p q). Qed.

Local Instance quotient_inv_closed `{H1:Group (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:SubGroup R}
  : MapsTo (tensor_map inv inv) R R.
Proof. exact (sub_inv_closed R). Qed.

Local Instance quotient_plus_closed@{u}: ∀ {X:set@{u}} `{H1:AdditiveNonComSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:AdditiveSubSemiGroup R},
  MapsTo (tensor_map2 (plus, plus)) (R ⊗ R) R := @quotient_sg_op_closed.

Local Instance quotient_mult_closed@{u}: ∀ {X:set@{u}} `{H1:MultiplicativeSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:MultiplicativeSubSemiGroup R},
  MapsTo (tensor_map2 (mult, mult)) (R ⊗ R) R := @quotient_sg_op_closed.

Local Instance quotient_negate_closed@{u}: ∀ {X:set@{u}} `{H1:AdditiveNonComGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:AdditiveSubGroup R},
  MapsTo (tensor_map negate negate) R R := @quotient_inv_closed.

Definition quotient_sg_op `{H1:SemiGroup (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:SubSemiGroup R} : SgOp (X / R) := quotient_lift_op2 sg_op.
Definition quotient_inv   `{H1:Group (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:SubGroup R} : Inv (X / R) := quotient_lift_op inv.

Definition quotient_plus   `{H1:AdditiveNonComSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:AdditiveSubSemiGroup R} : Plus (X / R) := quotient_lift_op2 plus.
Definition quotient_mult   `{H1:MultiplicativeSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:MultiplicativeSubSemiGroup R} : Mult (X / R) := quotient_lift_op2 mult.
Definition quotient_negate `{H1:AdditiveNonComGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {H:AdditiveSubGroup R} : Negate (X / R) := quotient_lift_op negate.

Global Hint Extern 2 (SgOp   (_ / _)) => simple notypeclasses refine quotient_sg_op  : typeclass_instances.
Global Hint Extern 2 (Inv    (_ / _)) => simple notypeclasses refine quotient_inv    : typeclass_instances.
Global Hint Extern 2 (Plus   (_ / _)) => simple notypeclasses refine quotient_plus   : typeclass_instances.
Global Hint Extern 2 (Mult   (_ / _)) => simple notypeclasses refine quotient_mult   : typeclass_instances.
Global Hint Extern 2 (Negate (_ / _)) => simple notypeclasses refine quotient_negate : typeclass_instances.

Global Hint Extern 2 (MonUnit (?X / _)) => change (MonUnit X) : typeclass_instances.
Global Hint Extern 2 (Zero    (?X / _)) => change (Zero X) : typeclass_instances.
Global Hint Extern 2 (One     (?X / _)) => change (One X) : typeclass_instances.


Lemma quotient_semigroup `{SemiGroup (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R} : SemiGroup (X / R).
Proof. red. now apply quotient_associative. Qed.
Global Hint Extern 2 (SemiGroup (_ / _)) => simple notypeclasses refine quotient_semigroup : typeclass_instances.

Lemma quotient_com_semigroup `{CommutativeSemiGroup (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R} : CommutativeSemiGroup (X / R).
Proof. split; try exact _. now apply quotient_commutative. Qed.
Global Hint Extern 2 (CommutativeSemiGroup (_ / _)) => simple notypeclasses refine quotient_com_semigroup : typeclass_instances.

Lemma quotient_semilattice `{SemiLattice (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R} : SemiLattice (X / R).
Proof. split; try exact _. now apply quotient_binary_idempotent. Qed.
Global Hint Extern 2 (SemiLattice (_ / _)) => simple notypeclasses refine quotient_semilattice : typeclass_instances.

Lemma quotient_monoid `{Monoid (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R} : Monoid (X / R).
Proof. split; try exact _.
* now apply quotient_left_identity.
* now apply quotient_right_identity.
Qed.
Global Hint Extern 2 (Monoid (_ / _)) => simple notypeclasses refine quotient_monoid : typeclass_instances.

Lemma quotient_com_monoid `{CommutativeMonoid (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R} : CommutativeMonoid (X / R).
Proof. split; try exact _. now apply quotient_commutative. Qed.
Global Hint Extern 2 (CommutativeMonoid (_ / _)) => simple notypeclasses refine quotient_com_monoid : typeclass_instances.

Local Instance quotient_bounded_sl `{BoundedSemiLattice (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R} : BoundedSemiLattice (X / R).
Proof. now split. Qed.
Global Hint Extern 2 (BoundedSemiLattice (_ / _)) => simple notypeclasses refine quotient_bounded_sl : typeclass_instances.

Lemma quotient_group `{Group (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubGroup R} : Group (X / R).
Proof. split; try exact _.
* now apply quotient_left_inverse.
* now apply quotient_right_inverse.
Qed.
Global Hint Extern 2 (Group (_ / _)) => simple notypeclasses refine quotient_group : typeclass_instances.

Lemma quotient_abgroup `{AbGroup (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubGroup R} : AbGroup (X / R).
Proof. split; try exact _. now apply quotient_commutative. Qed.
Global Hint Extern 2 (AbGroup (_ / _)) => simple notypeclasses refine quotient_abgroup : typeclass_instances.


Definition quotient_add_nc_sg  `{AdditiveNonComSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubSemiGroup R} : AdditiveNonComSemiGroup (X / R) := quotient_semigroup.
Definition quotient_add_nc_mon `{AdditiveNonComMonoid    (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubSemiGroup R} : AdditiveNonComMonoid    (X / R) := quotient_monoid.
Definition quotient_add_mon    `{AdditiveMonoid          (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubSemiGroup R} : AdditiveMonoid          (X / R) := quotient_com_monoid.
Definition quotient_add_nc_grp `{AdditiveNonComGroup     (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubGroup     R} : AdditiveNonComGroup     (X / R) := quotient_group.
Definition quotient_add_grp    `{AdditiveGroup           (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubGroup     R} : AdditiveGroup           (X / R) := quotient_abgroup.

Definition quotient_mult_sg     `{MultiplicativeSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !MultiplicativeSubSemiGroup R} : MultiplicativeSemiGroup (X / R) := quotient_semigroup.
Definition quotient_mult_mon    `{MultiplicativeMonoid    (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !MultiplicativeSubSemiGroup R} : MultiplicativeMonoid    (X / R) := quotient_monoid.
Definition quotient_mult_com_mon`{MultiplicativeComMonoid (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !MultiplicativeSubSemiGroup R} : MultiplicativeComMonoid (X / R) := quotient_com_monoid.

Global Hint Extern 2 (AdditiveNonComSemiGroup (_ / _)) => simple notypeclasses refine quotient_add_nc_sg : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComMonoid    (_ / _)) => simple notypeclasses refine quotient_add_nc_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid          (_ / _)) => simple notypeclasses refine quotient_add_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComGroup     (_ / _)) => simple notypeclasses refine quotient_add_nc_grp : typeclass_instances.
Global Hint Extern 2 (AdditiveGroup           (_ / _)) => simple notypeclasses refine quotient_add_grp : typeclass_instances.

Global Hint Extern 2 (MultiplicativeSemiGroup (_ / _)) => simple notypeclasses refine quotient_mult_sg : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid    (_ / _)) => simple notypeclasses refine quotient_mult_mon : typeclass_instances.
Global Hint Extern 2 (MultiplicativeComMonoid (_ / _)) => simple notypeclasses refine quotient_mult_com_mon : typeclass_instances.


Lemma to_quotient_pointed {X:set} {R:𝒫 (X ⊗ X)} `{!Equivalence R} {x:X} : Pointed_Morphism x (to_quotient R x) (to_quotient R).
Proof. exact (reflexivity (=) (to_quotient R x)). Qed.
Global Hint Extern 2 (Pointed_Morphism _ _ (to_quotient _)) => simple notypeclasses refine to_quotient_pointed : typeclass_instances.

Definition to_quotient_mon_unit_pointed {X:set} {R:𝒫 (X ⊗ X)} `{!Equivalence R} `{MonUnit X} : MonUnit_Pointed_Morphism (to_quotient R) := to_quotient_pointed.
Definition to_quotient_top_pointed {X:set} {R:𝒫 (X ⊗ X)} `{!Equivalence R} `{Top X} : Top_Pointed_Morphism (to_quotient R) := to_quotient_pointed.
Definition to_quotient_bottom_pointed {X:set} {R:𝒫 (X ⊗ X)} `{!Equivalence R} `{Bottom X} : Bottom_Pointed_Morphism (to_quotient R) := to_quotient_pointed.
Definition to_quotient_zero_pointed {X:set} {R:𝒫 (X ⊗ X)} `{!Equivalence R} `{Zero X} : Zero_Pointed_Morphism (to_quotient R) := to_quotient_pointed.
Definition to_quotient_one_pointed {X:set} {R:𝒫 (X ⊗ X)} `{!Equivalence R} `{One X} : One_Pointed_Morphism (to_quotient R) := to_quotient_pointed.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_mon_unit_pointed : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_top_pointed : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_zero_pointed : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_one_pointed : typeclass_instances.

Lemma to_quotient_sg_mor `{SemiGroup (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R} : SemiGroup_Morphism (to_quotient R).
Proof. split; try exact _. now intros x y. Qed.
Global Hint Extern 2 (SemiGroup_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_sg_mor : typeclass_instances.

Lemma to_quotient_mon_mor `{Monoid (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R} : Monoid_Morphism (to_quotient R).
Proof. now split. Qed.
Global Hint Extern 2 (Monoid_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_mon_mor : typeclass_instances.

Definition to_quotient_add_sg_mor  `{AdditiveNonComSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubSemiGroup R} : AdditiveSemiGroup_Morphism (to_quotient R) := to_quotient_sg_mor.
Definition to_quotient_add_mon_mor `{AdditiveNonComMonoid    (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubSemiGroup R} : AdditiveMonoid_Morphism (to_quotient R) := to_quotient_mon_mor.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_add_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_add_mon_mor : typeclass_instances.

Definition to_quotient_mult_sg_mor  `{MultiplicativeSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !MultiplicativeSubSemiGroup R} : MultiplicativeSemiGroup_Morphism (to_quotient R) := to_quotient_sg_mor.
Definition to_quotient_mult_mon_mor `{MultiplicativeMonoid    (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !MultiplicativeSubSemiGroup R} : MultiplicativeMonoid_Morphism (to_quotient R) := to_quotient_mon_mor.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_mult_sg_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (to_quotient _)) => simple notypeclasses refine to_quotient_mult_mon_mor : typeclass_instances.


Lemma quotient_lift_op_pointed@{u} {X Y:set@{u}}
  `{R:𝒫 (X ⊗ X)} `{!Equivalence R} {x:X}
  `{S:𝒫 (Y ⊗ Y)} `{!Equivalence S} {y:Y}
  {f:X ⇾ Y} `{!MapsTo (tensor_map f f) R S}
  {H:Pointed_Morphism x y f}
  : Pointed_Morphism (to_quotient R x) (to_quotient S y) (quotient_lift_op f).
Proof. red. apply quotient_subrel. apply H. Qed.
Global Hint Extern 2 (Pointed_Morphism _ _ (quotient_lift_op _)) => simple notypeclasses refine quotient_lift_op_pointed : typeclass_instances.

Definition quotient_lift_op_mon_unit_pointed@{u} {X Y:set@{u}}
  `{R:𝒫 (X ⊗ X)} `{!Equivalence R} `{MonUnit X}
  `{S:𝒫 (Y ⊗ Y)} `{!Equivalence S} `{MonUnit Y}
  {f:X ⇾ Y} `{!MapsTo (tensor_map f f) R S}
  `{!MonUnit_Pointed_Morphism f}
  : MonUnit_Pointed_Morphism (quotient_lift_op f)
:= quotient_lift_op_pointed.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (quotient_lift_op _)) => simple notypeclasses refine quotient_lift_op_mon_unit_pointed : typeclass_instances.

Definition quotient_lift_op_zero_pointed@{u} {X Y:set@{u}}
  `{R:𝒫 (X ⊗ X)} `{!Equivalence R} `{Zero X}
  `{S:𝒫 (Y ⊗ Y)} `{!Equivalence S} `{Zero Y}
  {f:X ⇾ Y} `{!MapsTo (tensor_map f f) R S}
  `{!Zero_Pointed_Morphism f}
  : Zero_Pointed_Morphism (quotient_lift_op f)
:= quotient_lift_op_pointed.
Global Hint Extern 2 (Zero_Pointed_Morphism (quotient_lift_op _)) => simple notypeclasses refine quotient_lift_op_zero_pointed : typeclass_instances.

Lemma quotient_lift_op_sg_mor@{u} {X Y:set@{u}}
  `{SemiGroup (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R}
  `{SemiGroup (X:=Y)} {S:𝒫 (Y ⊗ Y)} `{!Equivalence S, !SubSemiGroup S}
  {f:X ⇾ Y} `{!MapsTo (tensor_map f f) R S}
  `{!SemiGroup_Morphism f}
  : SemiGroup_Morphism (quotient_lift_op f).
Proof. split; try exact _. intros x y. apply quotient_subrel. exact (preserves_sg_op f _ _). Qed.
Global Hint Extern 2 (SemiGroup_Morphism (quotient_lift_op _)) => simple notypeclasses refine quotient_lift_op_sg_mor : typeclass_instances.

Lemma quotient_lift_op_mon_mor@{u} {X Y:set@{u}}
  `{Monoid (X:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !SubSemiGroup R}
  `{Monoid (X:=Y)} {S:𝒫 (Y ⊗ Y)} `{!Equivalence S, !SubSemiGroup S}
  {f:X ⇾ Y} `{!MapsTo (tensor_map f f) R S}
  `{!Monoid_Morphism f}
  : Monoid_Morphism (quotient_lift_op f).
Proof. now split. Qed.
Global Hint Extern 2 (Monoid_Morphism (quotient_lift_op _)) => simple notypeclasses refine quotient_lift_op_mon_mor : typeclass_instances.

Definition quotient_lift_op_add_sg_mor@{u} {X Y:set@{u}}
  `{AdditiveNonComSemiGroup (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubSemiGroup R}
  `{AdditiveNonComSemiGroup (R:=Y)} {S:𝒫 (Y ⊗ Y)} `{!Equivalence S, !AdditiveSubSemiGroup S}
  {f:X ⇾ Y} `{!MapsTo (tensor_map f f) R S}
  `{!AdditiveSemiGroup_Morphism f}
  : AdditiveSemiGroup_Morphism (quotient_lift_op f)
:= quotient_lift_op_sg_mor.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (quotient_lift_op _)) => simple notypeclasses refine quotient_lift_op_add_sg_mor : typeclass_instances.

Definition quotient_lift_op_add_mon_mor@{u} {X Y:set@{u}}
  `{AdditiveNonComMonoid (R:=X)} {R:𝒫 (X ⊗ X)} `{!Equivalence R, !AdditiveSubSemiGroup R}
  `{AdditiveNonComMonoid (R:=Y)} {S:𝒫 (Y ⊗ Y)} `{!Equivalence S, !AdditiveSubSemiGroup S}
  {f:X ⇾ Y} `{!MapsTo (tensor_map f f) R S}
  `{!AdditiveMonoid_Morphism f}
  : AdditiveMonoid_Morphism (quotient_lift_op f)
:= quotient_lift_op_mon_mor.
Global Hint Extern 2 (AdditiveMonoid_Morphism (quotient_lift_op _)) => simple notypeclasses refine quotient_lift_op_add_mon_mor : typeclass_instances.


