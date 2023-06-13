Require Import theory.set abstract_algebra interfaces.pointwise.
Require Import interfaces.bundled_algebra interfaces.subset.
Require Import logic.aprop.
Require Import theory.bundled_groups.
Require Import theory.projected_set.
Require Import theory.rings theory.subrings.
Require Import theory.naturals theory.integers.
Require Import theory.pointwise theory.of_course_set.
Require Import theory.nat_action.
Require Import easy rewrite rewrite_preserves.
Require Import set_lambda.

Global Hint Extern 1 (Negate (EndFun ?X)) => notypeclasses refine (pointwise_func (-) X) : typeclass_instances.

Import of_course_set_notation.
Local Open Scope mult_scope.
Local Notation "E₊" := Additive_Monoid_EndFun.

Lemma EndFun_NearRing `{AdditiveNonComGroup X} `{!PointwiseOp (X:=X) (+) X} : NearRing (EndFun X).
Proof. apply alt_Build_NearRing; try exact _. exact (pointwise_add_nc_grp _). Qed.
Global Hint Extern 2 (NearRing (EndFun _)) => simple notypeclasses refine EndFun_NearRing : typeclass_instances.
Global Hint Extern 2 (NearRng (EndFun _)) => simple notypeclasses refine EndFun_NearRing : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComGroup (EndFun _)) => simple notypeclasses refine EndFun_NearRing : typeclass_instances.
Global Hint Extern 2 (AdditiveCancellation (EndFun _)) => simple notypeclasses refine EndFun_NearRing : typeclass_instances.

Definition EndFun_AdditiveGroup `{AdditiveGroup X} `{!PointwiseOp (X:=X) (+) X} : AdditiveGroup (EndFun X) := pointwise_add_grp _.
Global Hint Extern 2 (AdditiveGroup (EndFun _)) => simple notypeclasses refine EndFun_AdditiveGroup : typeclass_instances.

Lemma Additive_Monoid_EndFun_SubNearRing `{AdditiveGroup X} `{!PointwiseOp (X:=X) (+) X} : SubNearRing (E₊ X).
Proof. pose proof _ : (SubNearRig (E₊ X)) as P. apply alt_Build_SubNearRing2; try apply P.
  intros f; change (set_T (X ⇾ X)) in f.
  change (?f ∊ E₊ X) with (of_course (AdditiveMonoid_Morphism f)).
  apply affirmative_aimpl; simpl; intro.
  now change (AdditiveMonoid_Morphism ((-) ∘ f)).
Qed.
Global Hint Extern 2 (SubNearRing (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRing : typeclass_instances.
Global Hint Extern 2 (SubNearRng (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRing : typeclass_instances.
Global Hint Extern 2 (AdditiveSubGroup (E₊ _)) => simple notypeclasses refine Additive_Monoid_EndFun_SubNearRing : typeclass_instances.


Lemma Additive_Monoid_EndFun_Ring `{AdditiveGroup X} `{!PointwiseOp (X:=X) (+) X} : Ring (E₊ X).
Proof. now apply alt_Build_Ring. Qed.
Global Hint Extern 1 (Ring (subset_to_set (E₊ _))) => simple notypeclasses refine Additive_Monoid_EndFun_Ring : typeclass_instances.
Global Hint Extern 1 (Rng (subset_to_set (E₊ _))) => simple notypeclasses refine Additive_Monoid_EndFun_Ring : typeclass_instances.
Global Hint Extern 1 (LeftNearRing (subset_to_set (E₊ _))) => simple notypeclasses refine Additive_Monoid_EndFun_Ring : typeclass_instances.
Global Hint Extern 1 (LeftNearRng (subset_to_set (E₊ _))) => simple notypeclasses refine Additive_Monoid_EndFun_Ring : typeclass_instances.


Section add_int_act.
  Universes i.
  Context (ℤ:integers@{i}).
  Context `{AdditiveNonComGroup@{i} X} `{!PointwiseOp (X:=X) (+) X} .

  Local Notation ϕ := (integers_to_group (ring_car (ints_ring ℤ)) (EndFun X)).

  Definition add_int_act : ℤ ⊗ X ⇾ X := uncurry ϕ.
  Local Notation "x ∙ y" := (func_op add_int_act (x, y)).

  Lemma add_int_act_strong : StrongOp add_int_act.
  Proof dec_strong_op_l _.

  Lemma add_int_act_0_l : ∏ x, 0 ∙ x = 0 .
  Proof preserves_0 ϕ .

  Lemma add_int_act_1_l : ∏ x, 1 ∙ x = x .
  Proof preserves_1 ϕ .

  Lemma add_int_act_plus_l m n : ∏ x, (m + n) ∙ x = m ∙ x + n ∙ x.
  Proof preserves_plus ϕ m n.

  Lemma add_int_act_negate_l n : ∏ x, (-n) ∙ x = -(n ∙ x).
  Proof preserves_negate ϕ n.

  Lemma add_int_act_minus_l m n : ∏ x, (m - n) ∙ x = m ∙ x - n ∙ x.
  Proof preserves_minus ϕ m n.

  Local Open Scope mult_scope.

  Lemma add_int_act_mult_l m n : ∏ x, (m · n) ∙ x = m ∙ (n ∙ x).
  Proof preserves_mult ϕ m n.

  Lemma add_int_act_add_mon2 {x} : AdditiveMonoid_Morphism (ap2 add_int_act x).
  Proof. apply alt_Build_AdditiveMonoid_Morphism.
  + intros m n. apply add_int_act_plus_l.
  + apply add_int_act_0_l.
  Qed.

  Local Notation E₀ := (ZeroSymmetricPart (EndFun X)).

  Lemma add_int_act_0_r n : n ∙ 0 = 0 .
  Proof. change (ϕ n 0 = 0).
    rew <-exact:( integers_initial (from_subset _ ∘ integers_to_group ℤ E₀) ).
    change ((?f ∘ ?g) ?x) with (f (g x)).
    destruct (integers_to_group ℤ E₀ n) as [f Hf]. exact (Hf 0).
  Qed.
End add_int_act.
Arguments add_int_act_add_mon2 {_ X _ _ _ _ _ x}.
Global Hint Extern 2 (AdditiveMonoid_Morphism (func_op (func_op ap2 (add_int_act _)) _) ) => simple notypeclasses refine add_int_act_add_mon2 : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (func_op (func_op ap2 (add_int_act _)) _) ) => simple notypeclasses refine add_int_act_add_mon2 : typeclass_instances.


Section add_int_act.
  Universes i.
  Context (ℤ:integers@{i}).
  Context `{AdditiveGroup@{i} X} `{!PointwiseOp (X:=X) (+) X} .

  Local Notation "x ∙ y" := (func_op (add_int_act ℤ (X:=X)) (x, y)).
  Local Notation "( n ∙)" := (func_op2 ap1 (add_int_act ℤ (X:=X)) n).
  Local Notation ϕ := (integers_to_group (ring_car (ints_ring ℤ)) (EndFun X)).
  Local Notation ε := (of_course_counit (EndFun X)).
  Local Notation i := (from_subset _).
  Local Notation ψ := (integers_to_group ℤ (E₊ X)).

  Lemma add_int_act_add_mon1 {n} : AdditiveMonoid_Morphism (n∙).
  Proof. change (AdditiveMonoid_Morphism (ϕ n)).
    rew <-(integers_initial (ε ∘ i ∘ ψ)).
    change (AdditiveMonoid_Morphism (ε (i (ψ n)))).
    destruct (ψ n) as [f Hf]. exact Hf.
  Qed.

  Lemma add_int_act_plus_r n : ∏ x y, n ∙ (x + y) = n ∙ x + n ∙ y.
  Proof.
    refine (preserves_plus (n∙)).
    exact add_int_act_add_mon1.
  Qed.
End add_int_act.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (func_op (func_op ap1 (add_int_act _)) _) ) => simple notypeclasses refine add_int_act_add_mon1 : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (func_op (func_op ap1 (add_int_act _)) _) ) => simple notypeclasses refine add_int_act_add_mon1 : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (func_op (func_op ap1 (add_int_act _)) _) ) => simple notypeclasses refine add_int_act_add_mon1 : typeclass_instances.


Section nat_to_int.
  Universes i.
  Context {ℕ:naturals@{i}} {ℤ:integers@{i}} (f:ℕ ⇾ ℤ) `{!Rig_Morphism f}.
  Context `{AdditiveNonComGroup@{i} X} `{!PointwiseOp (X:=X) (+) X} .

  Local Notation ϕ := (naturals_to_mon (near_rig_car (near_rig ℕ)) (EndFun X)).
  Local Notation ψ := (integers_to_group (ring_car (ints_ring ℤ)) (EndFun X)).

  Lemma int_act_nat_act n x : add_int_act ℤ (f n, x) = add_nat_act ℕ (n, x) .
  Proof naturals_initial (ψ ∘ f) n x.
End nat_to_int.

