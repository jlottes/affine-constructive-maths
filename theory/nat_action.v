Require Import theory.set abstract_algebra interfaces.pointwise.
Require Import interfaces.bundled_algebra interfaces.subset.
Require Import logic.aprop.
Require Import theory.bundled_groups.
Require Import theory.projected_set.
Require Import theory.rings theory.subrings.
Require Import theory.naturals.
Require Import theory.pointwise theory.of_course_set.
Require Import easy rewrite rewrite_preserves.
Require Import set_lambda.


Definition EndFun (X:set) : set := X ⇾ X.

Global Hint Extern 1 (One (EndFun ?X)) => refine (id_fun X) : typeclass_instances.
Global Hint Extern 1 (Mult (EndFun ?X)) => refine (@scompose_fun X X X) : typeclass_instances.

Global Hint Extern 1 (Zero (EndFun _)) => refine (const 0) : typeclass_instances.
Global Hint Extern 1 (Plus (EndFun ?X)) => notypeclasses refine (pointwise_op (+) X) : typeclass_instances.


Local Open Scope mult_scope.

Lemma EndFun_mult_mon {X:set} : MultiplicativeMonoid (EndFun X).
Proof. apply alt_Build_MultiplicativeMonoid; hnf; now intros. Qed.
Global Hint Extern 2 (MultiplicativeMonoid    (EndFun _)) => simple notypeclasses refine EndFun_mult_mon : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup (EndFun _)) => simple notypeclasses refine EndFun_mult_mon : typeclass_instances.


Lemma EndFun_NearRig `{AdditiveNonComMonoid X} `{!PointwiseOp (X:=X) (+) X} : NearRig (EndFun X).
Proof. apply alt_Build_NearRig.
+ exact (pointwise_add_nc_mon _).
+ exact EndFun_mult_mon.
+ now intros f g h.
+ now intros f.
Qed.
Global Hint Extern 2 (NearRig    (EndFun _)) => simple notypeclasses refine EndFun_NearRig : typeclass_instances.
Global Hint Extern 2 (NearRg     (EndFun _)) => simple notypeclasses refine EndFun_NearRig : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComMonoid (EndFun _)) => simple notypeclasses refine EndFun_NearRig : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComSemiGroup (EndFun _)) => simple notypeclasses refine EndFun_NearRig : typeclass_instances.

Definition EndFun_AdditiveMonoid `{AdditiveMonoid X} `{!PointwiseOp (X:=X) (+) X} : AdditiveMonoid (EndFun X) := pointwise_add_mon _.
Global Hint Extern 2 (AdditiveMonoid (EndFun _)) => simple notypeclasses refine EndFun_AdditiveMonoid : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup (EndFun _)) => simple notypeclasses refine EndFun_AdditiveMonoid : typeclass_instances.


Import of_course_set_notation.

Definition Additive_Monoid_EndFun `{AdditiveMonoid X} `{!PointwiseOp (X:=X) (+) X} := { f: !(EndFun X) | of_course (AdditiveMonoid_Morphism f) } .
Arguments Additive_Monoid_EndFun X {_ _ _ _}.
Local Notation "E₊" := Additive_Monoid_EndFun.

Lemma Additive_Monoid_EndFun_SubNearRig `{AdditiveMonoid X} `{!PointwiseOp (X:=X) (+) X} : SubNearRig (E₊ X).
Proof. apply alt_Build_SubNearRig2.
  1, 2 : intros f g; change (set_T (X ⇾ X)) in f, g.
  all: change (?f ∊ E₊ X) with (of_course (AdditiveMonoid_Morphism f)).
  1, 2 : apply affirmative_aimpl.
  all: simpl.
  1, 2: intros [Hf Hg].
  2: now change (AdditiveMonoid_Morphism (f ∘ g)).
  all: apply alt_Build_AdditiveMonoid_Morphism; intros; simpl; unfold id;
    rewrite_preserves g; rewrite_preserves f.
  4,5,6: refl.
  + rew ?(associativity (+) _ _ _). apply (is_fun (+ g y) _ _).
    rew <-?(associativity (+) _ _ _). apply (is_fun (f x +) _ _).
    exact (commutativity (+) _ _).
  + exact (plus_0_l _).
  + sym. exact (plus_0_l _).
Qed.

Global Hint Extern 2 (SubNearRig (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRig : typeclass_instances.
Global Hint Extern 2 (SubNearRg (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRig : typeclass_instances.
Global Hint Extern 2 (AdditiveSubMonoid (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRig : typeclass_instances.
Global Hint Extern 2 (AdditiveSubSemiGroup (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRig : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubMonoid (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRig : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubSemiGroup (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRig : typeclass_instances.

Lemma Additive_Monoid_EndFun_Rig `{AdditiveMonoid X} `{!PointwiseOp (X:=X) (+) X} : Rig (E₊ X).
Proof. apply alt_Build_Rig; try exact _.
+ (* LeftDistribute (·) (+) *)
  intros [f elf] [g elg] [h elh]; revert elf elg elh; simpl; intros ???; change (set_T (X ⇾ X)) in f,g,h.
  intros x. now rewrite_preserves f.
+ (* RightAbsorb (·) 0 *)
  intros [f elf]; revert elf; simpl; intros ?; change (set_T (X ⇾ X)) in f.
  intros x. exact (preserves_0 f).
Qed.
Global Hint Extern 1 (Rig (subset_to_set (E₊ _))) => simple notypeclasses refine Additive_Monoid_EndFun_Rig : typeclass_instances.
Global Hint Extern 1 (Rg (subset_to_set (E₊ _))) => simple notypeclasses refine Additive_Monoid_EndFun_Rig : typeclass_instances.
Global Hint Extern 1 (LeftNearRg (subset_to_set (E₊ _))) => simple notypeclasses refine Additive_Monoid_EndFun_Rig : typeclass_instances.
Global Hint Extern 1 (LeftNearRig (subset_to_set (E₊ _))) => simple notypeclasses refine Additive_Monoid_EndFun_Rig : typeclass_instances.

Section add_nat_act.
  Universes i.
  Context (ℕ:naturals@{i}).
  Context `{AdditiveNonComMonoid@{i} X} `{!PointwiseOp (X:=X) (+) X} .

  Local Notation ϕ := (naturals_to_mon (near_rig_car (nats_near_rig ℕ)) (EndFun X)).

  Definition add_nat_act : ℕ ⊗ X ⇾ X := uncurry ϕ.
  Local Notation "x ∙ y" := (func_op add_nat_act (x, y)).

  Lemma add_nat_act_strong : StrongOp add_nat_act.
  Proof dec_strong_op_l _.

  Lemma add_nat_act_0_l : ∏ x, 0 ∙ x = 0 .
  Proof preserves_0 ϕ .

  Lemma add_nat_act_1_l : ∏ x, 1 ∙ x = x .
  Proof preserves_1 ϕ .

  Lemma add_nat_act_plus_l m n : ∏ x, (m + n) ∙ x = m ∙ x + n ∙ x.
  Proof preserves_plus ϕ m n.

  Local Open Scope mult_scope.

  Lemma add_nat_act_mult_l m n : ∏ x, (m · n) ∙ x = m ∙ (n ∙ x).
  Proof preserves_mult ϕ m n.

  Lemma add_nat_act_add_mon2 {x} : AdditiveMonoid_Morphism (ap2 add_nat_act x).
  Proof. apply alt_Build_AdditiveMonoid_Morphism.
  + intros m n. apply add_nat_act_plus_l.
  + apply add_nat_act_0_l.
  Qed.

  Local Notation E₀ := (ZeroSymmetricPart (EndFun X)).

  Lemma add_nat_act_0_r n : n ∙ 0 = 0 .
  Proof. change (ϕ n 0 = 0).
    rew <-exact:( naturals_initial (from_subset _ ∘ naturals_to_mon ℕ E₀) ).
    change ((?f ∘ ?g) ?x) with (f (g x)).
    destruct (naturals_to_mon ℕ E₀ n) as [f Hf]. exact (Hf 0).
  Qed.
End add_nat_act.
Arguments add_nat_act_add_mon2 {_ X _ _ _ _ _}.
Global Hint Extern 2 (AdditiveMonoid_Morphism (func_op (func_op ap2 (add_nat_act _)) _) ) => simple notypeclasses refine add_nat_act_add_mon2 : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (func_op (func_op ap2 (add_nat_act _)) _) ) => simple notypeclasses refine add_nat_act_add_mon2 : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (func_op (func_op ap2 (add_nat_act _)) _) ) => simple notypeclasses refine add_nat_act_add_mon2 : typeclass_instances.

Section add_nat_act.
  Universes i.
  Context {ℕ:naturals@{i}}.
  Context `{AdditiveMonoid X} `{!PointwiseOp (X:=X) (+) X} .
  Local Notation "x ∙ y" := (func_op (add_nat_act ℕ (X:=X)) (x, y)).
  Local Notation "( n ∙)" := (func_op2 ap1 (add_nat_act ℕ (X:=X)) n).
  Local Notation ϕ := (naturals_to_mon (near_rig_car (nats_near_rig ℕ)) (EndFun X)).
  Local Notation ε := (of_course_counit (EndFun X)).
  Local Notation i := (from_subset _).
  Local Notation ψ := (naturals_to_mon ℕ (E₊ X)).

  Lemma add_nat_act_add_mon1 {n} : AdditiveMonoid_Morphism (n∙).
  Proof. change (AdditiveMonoid_Morphism (ϕ n)).
    rew <-(naturals_initial (ε ∘ i ∘ ψ)).
    change (AdditiveMonoid_Morphism (ε (i (ψ n)))).
    destruct (ψ n) as [f Hf]. exact Hf.
  Qed.

  Lemma add_nat_act_plus_r n : ∏ x y, n ∙ (x + y) = n ∙ x + n ∙ y.
  Proof.
    refine (preserves_plus (n∙)).
    exact add_nat_act_add_mon1.
  Qed.
End add_nat_act.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (func_op (func_op ap1 (add_nat_act _)) _) ) => simple notypeclasses refine add_nat_act_add_mon1 : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (func_op (func_op ap1 (add_nat_act _)) _) ) => simple notypeclasses refine add_nat_act_add_mon1 : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (func_op (func_op ap1 (add_nat_act _)) _) ) => simple notypeclasses refine add_nat_act_add_mon1 : typeclass_instances.


