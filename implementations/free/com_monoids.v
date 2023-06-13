Require Import abstract_algebra bundled_algebra interfaces.free_monoid interfaces.naturals.
Require Import interfaces.sprop relations.
Require Import logic.aprop.
Require Import list nat.
Require Export interfaces.free.generators interfaces.free.groups.
Require Import theory.set theory.groups theory.bundled_groups theory.rings theory.bundled_rings.
Require Import theory.nno theory.naturals theory.nat_action.
Require Import easy replc tactics.misc rewrite_preserves.
Require Import set_lambda.

Require Import finite_sequences.

Module eval.

Local Notation "x ,, s" := (func_op FinSeq_cons (x, s)) (at level 60, right associativity).
Import finite_sequences.index_notation.
Local Notation "[ x ]" := (func_op ProdList_unit x).
Local Notation e := mon_unit.
Local Open Scope grp_scope.

Import projection_notation.

Section contents.
  Universes u.
  Context {M:additive_monoid@{u}} `{!DecidableEquality M}.
  Notation "M*" := (FinSeq (additive_monoid_car M)).
  Local Hint Extern 1 (AffirmativeEquality M*) => exact (_ : DecidableEquality M*) : typeclass_instances.

  Context {X:additive_monoid@{u}}.

  Context (act:X → additive_monoid_morphism M X).

  Local Infix "·" := act.
  Local Notation "x :: l" := (func_op TensorCons (x, l)) (at level 60, right associativity).
  Local Notation "X*" := (TensorList (additive_monoid_car X)).

  Fixpoint act_map_op (Γ : list X) : TensorList M ⇾ X* :=
  match Γ with
  | nil => const e
  | cons x Γ' =>
      TensorList_match (X:=M) (Y:=X*) (
      0 :: ProdList_map (const 0) Γ',
      set:((λ '(n, s), x · n :: act_map_op Γ' s) : M ⊗ TensorList M → X* )
      )
  end.

  Lemma act_map_nil : ∀ (Γ : list X), act_map_op Γ nil = ProdList_map (const 0) Γ.
  Proof. now intros [| x Γ]. Qed.

  Local Notation tl := FinSeq_tail.

  Lemma act_map_spec : ∀ x (Γ : list X) (s:M*), act_map_op (cons x Γ) s = x · [s]_0 :: act_map_op Γ (tl s).
  Proof. intros x Γ. refine (ProdList_sdestruct _ _ _).
  + change (act_map_op (cons x Γ) e) with (0 :: ProdList_map (const (Y:=X) 0) Γ).
    change (tl _) with (@nil M). rew (act_map_nil _).
    change (_ :: ?b = _) with (0 = x · 0 ⊠ b = b :> X*).
    rew (preserves_0 _); now split.
  + intros α s. change (x · α = x · α ⊠ act_map_op Γ s = act_map_op Γ s). now split.
  Qed.

  Lemma act_map_is_fun : ∀ (Γ : list X), @IsFun M* X* (act_map_op Γ).
  Proof. refine (list_sinduction _ _ _) .
  + exact (is_fun (const e)).
  + intros x Γ' IH s t. apply affirmative_aimpl. intros E.
    rew [ (act_map_spec x Γ' s) | (act_map_spec x Γ' t) ].
    change (x · [s]_0 = x · [t]_0 ⊠ act_map_op Γ' (tl s) = act_map_op Γ' (tl t)).
    rew <-(IH _ _). rew <-E; now split.
  Qed.

  Definition act_map (Γ:list X) : M* ⇾ X* := @make_fun _ _ _ (act_map_is_fun Γ).

  Local Definition sum : X* ⇾ X := TensorList_to_monoid (id_fun (additive_monoid_as_com_monoid X)).
  Definition eval (Γ:list X) := sum ∘ act_map Γ.

  Lemma eval_spec : ∀ x (Γ : list X) (s:M*), eval (cons x Γ) s = x · [s]_0 + eval Γ (tl s).
  Proof. intros x Γ s. now rew (FinSeq_tail_spec s) at 1. Qed.

  Lemma eval_pres_0 : ∀ Γ, eval Γ 0 = 0.
  Proof. refine (list_sinduction _ _ _); [ refl | intros x Γ IH ]. rew (eval_spec _ _ _).
    change (x · 0 + eval Γ 0 = 0). rew [ (preserves_0 _) | IH ]. exact (plus_0_l _).
  Qed.

  Lemma eval_addmon_mor (Γ:list X) : AdditiveMonoid_Morphism (eval Γ).
  Proof. apply alt_Build_AdditiveMonoid_Morphism; [| exact (eval_pres_0 _) ]; revert Γ.
    refine (list_sinduction _ _ _).
  + intros s t. sym. exact (plus_0_l _).
  + intros x Γ IH s t.
    rew ?(eval_spec _ _ _).
    rewrite_preserves (tl (X:=M)).
    rewrite_preserves (FinSeq_index (X:=M) 0).
    rewrite_preserves (act x).
    rew (IH _ _).
    rew ?(associativity (+) _ _ _). apply (is_fun (+ eval Γ (tl t))).
    rew <-?(associativity (+) _ _ _). apply (is_fun (x · [s]_0 +)).
    exact (commutativity (+) _ _).
  Qed.

  Context {Mone:One M}.
  Local Hint Extern 1 (One (additive_non_com_monoid_car (additive_monoid_as_add_nc_monoid M))) => exact Mone : typeclass_instances.
  Definition v : Nat ⇾ M* := set:(λ n, nno_rec Nat set:(λ y:M*, 0,, y) (FinSeq_unit 1, n)).
  Local Hint Extern 1 (Var M*) => refine v : typeclass_instances.
  Context (act_1_r : ∀ x, x · 1 = x).

  Lemma eval_var : ∀ (Γ:list@{u} X), Var_Morphism Γ (eval Γ).
  Proof. unfold Var_Morphism.
    refine (list_sinduction@{u} _ _ _); [ easy | intros x Γ IH [| n ] ].
    + intros []. change ((x · 1) + eval Γ 0 = x).
      rew [ (act_1_r x) | (eval_pres_0 _) ]. exact (plus_0_r _).
    + intro b. change (ListInBounds Γ n) in b. specialize (IH n b).
      change ((x · 0) + eval Γ (var n) = list_nth Γ n).
      now rew (preserves_0 (act x)), (plus_0_l _).
  Qed.
End contents.
End eval.

Definition nat_action (ℕ:naturals) (M:additive_monoid) (x:M) : additive_monoid_morphism ℕ M
  := make_additive_non_com_monoid_morphism (of_course_counit _ ∘ ap2 (add_nat_act ℕ (X:=of_course_set M)) x).

Lemma nat_action_1_r {ℕ M} x : @nat_action ℕ M x 1 = x.
Proof add_nat_act_1_l ℕ (X:=of_course_set M) x.

Definition free_add_mon@{u} (ℕ:naturals@{u}) `{!IsDecEq ℕ (d:=d)} : free_additive_monoid@{u}.
Proof. unshelve esplit.
+ unshelve esplit.
  - exact (make_additive_monoid (FinSeq ℕ)).
  - split. now change (Dec (A:=FinSeq ℕ) (=)).
  - split. exact (eval.v (M:=ℕ)).
  - now change (IsDecEq (FinSeq ℕ)).
+ intros M Γ. unshelve esplit.
  - simple refine (make_additive_non_com_monoid_morphism _).
    * exact (eval.eval (nat_action ℕ M) Γ).
    * change (AdditiveMonoid_Morphism (eval.eval (nat_action ℕ M) Γ)).
      refine (eval.eval_addmon_mor _ _).
  - exact ( eval.eval_var (X:=M) (nat_action ℕ M) nat_action_1_r Γ ).
Defined.

Definition free_additive_monoid_as_free_com_mon (F:free_additive_monoid) : free_commutative_monoid.
Proof. unshelve esplit.
+ unshelve esplit; [ exact (additive_monoid_as_com_monoid F) | exact F .. ].
+ intros M Γ. change (list (com_monoid_as_additive_monoid M)) in Γ. unshelve esplit.
  - exact (additive_non_com_monoid_morphism_as_mon_mor (free_additive_monoid.eval F Γ)).
  - exact (free_additive_monoid.eval F Γ).
Defined.

Definition free_com_mon@{u} (ℕ:naturals@{u}) `{!IsDecEq ℕ (d:=d)} : free_commutative_monoid@{u}
  := free_additive_monoid_as_free_com_mon (free_add_mon ℕ).
