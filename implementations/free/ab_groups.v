Require Import abstract_algebra bundled_algebra interfaces.integers.
Require Export interfaces.free.generators interfaces.free.groups.
Require Import theory.bundled_rings.
Require Import theory.int_action.
Require Import finite_sequences.
Require Import free.com_monoids.
Require Import easy.

Local Definition int_action (ℤ:integers) (G:additive_group) (x:G) : additive_group_morphism ℤ G
  := @make_additive_non_com_monoid_morphism ℤ G
     (of_course_counit _ ∘ ap2 (add_int_act ℤ (X:=of_course_set G)) x) _.

Local Lemma int_action_1_r {ℤ G} x : @int_action ℤ G x 1 = x.
Proof add_int_act_1_l ℤ (X:=of_course_set G) x.

Definition free_add_group@{u} (ℤ:integers@{u}) `{!IsDecEq ℤ (d:=d)} : free_additive_group@{u}.
Proof. unshelve esplit.
+ unshelve esplit.
  - exact (make_additive_group (FinSeq ℤ)).
  - split. now change (Dec (A:=FinSeq ℤ) (=)).
  - split. exact (eval.v (M:=ℤ)).
  - now change (IsDecEq (FinSeq ℤ)).
+ intros G Γ. unshelve esplit.
  - simple refine (make_additive_non_com_monoid_morphism _).
    * exact (eval.eval (int_action ℤ G) Γ).
    * change (AdditiveMonoid_Morphism (eval.eval (int_action ℤ G) Γ)).
      refine (eval.eval_addmon_mor _ _).
  - exact ( eval.eval_var (X:=G) (int_action ℤ G) int_action_1_r Γ ).
Defined.

