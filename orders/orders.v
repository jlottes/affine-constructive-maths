Require Export interfaces.orders.
Require Import logic.aprop relations easy rewrite tactics.misc.

Local Notation "X 'ᵒᵖ'" := (order_op X) (at level 1, format "X 'ᵒᵖ'").

Definition le_dual `{Le A} {x:A} {y} : DeMorganDual (x ≤ y) (y < x) := demorgan_dual_base.
Definition lt_dual `{Le A} {x:A} {y} : DeMorganDual (x < y) (y ≤ x) := anot_dual.
Global Hint Extern 2 (DeMorganDual (_ ≤ _) _) => notypeclasses refine le_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ < _) _) => notypeclasses refine lt_dual : typeclass_instances.

Global Hint Extern 2 (apos (aimpl (_ ≤ _) _)) => sapply_2 (Transitive_rel_proper_aimpl (≤)) : proper.
Global Hint Extern 2 (apos (aiff (_ ≤ _) _)) => sapply_2 (Transitive_Antisymmetric_rel_proper_aiff (≤) (=)) : proper.

Lemma lt_proper_aimpl `{WeakPoset P} {x₁ x₂ y₁ y₂ : P} : x₂ ≤ x₁ → y₁ ≤ y₂ → (x₁ < y₁ ⊸ x₂ < y₂).
Proof. intros E1 E2. apply by_contrapositive. now rew E1, E2. Qed.
Lemma lt_proper_aiff `{WeakPoset P} {x₁ x₂ y₁ y₂ : P} : x₁ = x₂ → y₁ = y₂ → (x₁ < y₁ ⧟ x₂ < y₂).
Proof. intros E1 E2. apply by_contrapositive_iff. now rew E1, E2. Qed.

Global Hint Extern 2 (apos (aimpl (_ < _) _)) => sapply_2 lt_proper_aimpl : proper.
Global Hint Extern 2 (apos (aiff (_ < _) _)) => sapply_2 lt_proper_aiff : proper.

Global Hint Extern 10 (apos (_ ≤ _)) => sapply_1 (aimpl_impl_pos (eq_le _ _)) : proper.


Lemma dec_order_aff `{DecidableOrder P} : AffirmativeOrder P.  Proof. now split. Qed.
Lemma dec_order_ref `{DecidableOrder P} : RefutativeOrder  P.  Proof. now split. Qed.
Coercion dec_order_aff : DecidableOrder >-> AffirmativeOrder.
Coercion dec_order_ref : DecidableOrder >-> RefutativeOrder.


Section opposite.
  Ltac go := first [ red | split ]; try exact _; change (@le (set_T (order_op _)) ?R) with R; unfold order_op; exact _.
  Instance PreOrder_op         {X:set} `{PreOrder         X} : PreOrder         (X ᵒᵖ).  Proof. go. Defined.

  Instance WeakPoset_op        `{WeakPoset X} : WeakPoset (X ᵒᵖ).  Proof. go. Defined.
  Instance Poset_op            `{Poset X} : Poset (X ᵒᵖ).  Proof. go. Defined.
  Instance StrongPoset_op      `{StrongPoset      X} : StrongPoset      (X ᵒᵖ).  Proof. go. Defined.
  Instance DecidableOrder_op   `{DecidableOrder   X} : DecidableOrder   (X ᵒᵖ).  Proof. go. Defined.
  Instance AffirmativeOrder_op `{AffirmativeOrder X} : AffirmativeOrder (X ᵒᵖ).  Proof. go. Defined.
  Instance RefutativeOrder_op  `{RefutativeOrder  X} : RefutativeOrder  (X ᵒᵖ).  Proof. go. Defined.
  Instance TotalOrder_op       `{TotalOrder       X} : TotalOrder       (X ᵒᵖ).  Proof. go. Defined.
  Instance LinearOrder_op      `{LinearOrder X}      : LinearOrder      (X ᵒᵖ).  Proof. go. Defined.
End opposite.
Global Hint Extern 2 (PreOrder         (_ ᵒᵖ)) => simple notypeclasses refine PreOrder_op         : typeclass_instances.
Global Hint Extern 2 (WeakPoset (_ ᵒᵖ)) => simple notypeclasses refine WeakPoset_op : typeclass_instances.
Global Hint Extern 2 (Poset (_ ᵒᵖ)) => simple notypeclasses refine Poset_op : typeclass_instances.
Global Hint Extern 2 (StrongPoset      (_ ᵒᵖ)) => simple notypeclasses refine StrongPoset_op      : typeclass_instances.
Global Hint Extern 2 (DecidableOrder   (_ ᵒᵖ)) => simple notypeclasses refine DecidableOrder_op   : typeclass_instances.
Global Hint Extern 2 (AffirmativeOrder (_ ᵒᵖ)) => simple notypeclasses refine AffirmativeOrder_op : typeclass_instances.
Global Hint Extern 2 (RefutativeOrder  (_ ᵒᵖ)) => simple notypeclasses refine RefutativeOrder_op  : typeclass_instances.
Global Hint Extern 2 (TotalOrder       (_ ᵒᵖ)) => simple notypeclasses refine TotalOrder_op       : typeclass_instances.
Global Hint Extern 2 (LinearOrder      (_ ᵒᵖ)) => simple notypeclasses refine LinearOrder_op      : typeclass_instances.


Lemma alt_Build_Poset {X : set} {Xle : Le X} :
   Reflexive (A:=X) (≤)
 → Transitive (A:=X) (≤)
 → Subrelation (A:=X) (=) (≤)
 → Antisymmetric (A:=X) (≤) (=)
 → Poset X.
Proof. intros. repeat ( split; try exact _ ). Qed.

Section induced_poset.
  Universes i.
  Context {A:Type@{i}} `{PreOrder A} `{Equiv A}.
  Context (eq_correct : ∀ x y : A, x = y ⧟ x ≤ y ∧ y ≤ x).

  Local Instance preorder_is_set : IsSet A.
  Proof. split; hnf; intros; rew ?(eq_correct _ _).
  + now split.
  + refine (aand_intro (aandr _ _) (aandl _ _)).
  + refine (aand_intro _ _).
    * rew !2(aandl _ _). now apply transitivity.
    * rew !2(aandr _ _). rew (aprod_com _ _). now apply transitivity.
  Qed.
  Definition induced_poset := set_make A.
  Local Hint Extern 1 (Le (set_T induced_poset)) => change (Le A) : typeclass_instances.
  Lemma induced_poset_poset : Poset induced_poset.
  Proof. apply alt_Build_Poset; try exact _; hnf; change (set_T induced_poset) with A; intros; now rew ?(eq_correct _ _). Qed.
End induced_poset.


Lemma le_is_fun `{WeakPoset P} : @IsFun (P ⊗ P) Ω (tuncurry le).
Proof.
  enough (∀ x₁ x₂ y₁ y₂ : P, x₁ = x₂ ⊠ y₁ = y₂ ⊸ x₁ ≤ y₁ ⊸ x₂ ≤ y₂) as Q.
  * intros [x₁ y₁] [x₂ y₂]. change (x₁ = x₂ ⊠ y₁ = y₂ ⊸ x₁ ≤ y₁ ⧟ x₂ ≤ y₂).
    apply aand_intro; [ now apply Q |].
    rew [ (symmetry_iff (=) x₁ x₂) | (symmetry_iff (=) y₁ y₂) ]; now apply Q.
  * intros. rew <-(transitivity (≤) x₂ x₁ y₂), <-(transitivity (≤) x₁ y₁ y₂).
    rew (symmetry_iff (=) x₁ x₂).
    rew [ (subrelation (=)) | (subrelation (=)) ].
    tautological.
Qed.
Canonical Structure le_fun `{WeakPoset P} := make_fun_alt (eval_tuncurry (@le P _)) le_is_fun.
Canonical Structure lt_fun `{WeakPoset P} := make_fun_alt (eval_tuncurry (@lt P _)) (anot ∘ le_fun ∘ tensor_swap _ _).


Definition eq_le_flip `{WeakPoset P} : ∀ x y : P, x = y ⊸ y ≤ x := eq_le (X:=P ᵒᵖ).

Lemma lt_ne `{WeakPoset P} (x y : P) : x < y ⊸ x ≠ y.
Proof. apply by_contrapositive, eq_le_flip. Qed.

Definition lt_ne_flip `{WeakPoset P} (x y : P) : x < y ⊸ y ≠ x := lt_ne (P:=P ᵒᵖ) _ _.

Lemma le_antisym_iff `{Poset P} (x y : P) : x ≤ y ∧ y ≤ x ⧟ x = y.
Proof. split.
+ now apply antisymmetry.
+ exact (aand_intro (eq_le _ _) (eq_le_flip _ _)).
Qed.

Lemma ne_iff_lt `{Poset P} (x y : P) : x ≠ y ⧟ x < y ∨ y < x.
Proof. apply by_contrapositive_iff. sym. exact (le_antisym_iff (P:=P ᵒᵖ) _ _). Qed.

Lemma le_lt_par_eq `{WeakPoset P} (x y : P) : x ≤ y ⊸ x < y ⊞ x = y.
Proof. rew <-(le_pseudo_antisym _ _). change (x < y) with ((y ≤ x)ᗮ).
  set (Q:=x ≤ y). set (R:=y ≤ x). tautological.
Qed.

Lemma le_prod_ne_lt `{WeakPoset P} (x y : P) : x ≤ y ⊠ x ≠ y ⊸ x < y .
Proof. apply by_contrapositive. exact (le_lt_par_eq (P:=P ᵒᵖ) _ _). Qed.

Lemma le_lt_trans `{WeakPoset P} (x y z : P) : x ≤ y ⊠ y < z ⊸ x < z.
Proof. rew exact:(contrapositive (transitivity (≤) z x y)), (apar_com _ _). exact (aprod_mp_r _ _). Qed.

Lemma lt_le_trans `{WeakPoset P} (x y z : P) : x < y ⊠ y ≤ z ⊸ x < z.
Proof. rew exact:(contrapositive (transitivity (≤) y z x)). exact (aprod_mp_l _ _). Qed.

Definition StrongPoset_StrongSet `{StrongPoset P} : StrongSet P.
Proof. intros x y z.
  rew <-!3(le_antisym_iff (P:=P) _ _).
  rew <-(strong_transitivity (≤) x y z).
  rew <-(strong_transitivity (≤) z y x).
  tautological.
Qed.
Coercion StrongPoset_StrongSet : StrongPoset >-> StrongSet.

Definition DecidableOrder_DecidableEquality `{DecidableOrder P} : DecidableEquality P.
Proof. intros x y. now rew <-(le_antisym_iff (P:=P) _ _). Qed.
Coercion DecidableOrder_DecidableEquality : DecidableOrder >-> DecidableEquality.

Definition RefutativeOrder_RefutativeEquality `{RefutativeOrder P} : RefutativeEquality P.
Proof. intros x y. now rew <-(le_antisym_iff (P:=P) _ _). Qed.
Coercion RefutativeOrder_RefutativeEquality : RefutativeOrder >-> RefutativeEquality.

Lemma DecidableOrder_DecidableLt    `{DecidableOrder   P} : DecidableRelation   (A:=P) (<).  Proof. now unfold lt. Qed.
Lemma RefutativeOrder_AffirmativeLt `{RefutativeOrder  P} : AffirmativeRelation (A:=P) (<).  Proof. now unfold lt. Qed.
Lemma AffirmativeOrder_RefutativeLt `{AffirmativeOrder P} : RefutativeRelation  (A:=P) (<).  Proof. now unfold lt. Qed.

Global Hint Extern 2 (DecidableRelation   (<)) => simple notypeclasses refine DecidableOrder_DecidableLt    : typeclass_instances.
Global Hint Extern 2 (AffirmativeRelation (<)) => simple notypeclasses refine RefutativeOrder_AffirmativeLt : typeclass_instances.
Global Hint Extern 2 (RefutativeRelation  (<)) => simple notypeclasses refine AffirmativeOrder_RefutativeLt : typeclass_instances.


Lemma TotalOrder_is_Linear `{TotalOrder X} : LinearOrder X.
Proof. now split. Qed.
Coercion TotalOrder_is_Linear : TotalOrder >-> LinearOrder.

Definition lt_le `{LinearOrder P} : Subrelation (A:=P) (<) (≤) := λ x y, pseudo_total (≤) _ _.
Global Hint Extern 2 (Subrelation (<) (≤)) => simple notypeclasses refine lt_le : typeclass_instances.

Definition lt_trans `{LinearOrder P} : Transitive (A:=P) (<).
Proof. intros x y z. rew (lt_le x y). exact (le_lt_trans _ _ _). Qed.
Global Hint Extern 2 (Transitive (<)) => simple notypeclasses refine lt_trans : typeclass_instances.

Definition lt_str_trans `{TotalOrder P} : StronglyTransitive (A:=P) (<).
Proof. intros x y z. pose proof total (≤) x y as [E|E].
+ now rew <-E at 2.
+ apply by_contrapositive. now rew (aor_is_true_l E).
Qed.
Global Hint Extern 2 (StronglyTransitive (<)) => simple notypeclasses refine lt_str_trans : typeclass_instances.

Lemma lt_or_eq_le `{LinearOrder P} (x y : P) : x < y ∨ x = y ⊸ x ≤ y.
Proof aor_elim (lt_le _ _) (eq_le _ _).

Lemma lt_le_and_ne `{LinearOrder P} (x y : P) : x < y ⊸ x ≤ y ∧ x ≠ y .
Proof. apply by_contrapositive. exact (lt_or_eq_le (P:=P ᵒᵖ) _ _). Qed.



Lemma lt_par_eq_le `{LinearOrder P} `{!RefutativeOrder P} (x y : P) : x < y ⊞ x = y ⊸ x ≤ y.
Proof. apply aor_apar_refutative. exact (lt_or_eq_le _ _). Qed. 

Lemma le_iff_lt_par_eq `{LinearOrder P} `{!RefutativeOrder P} (x y : P) : x ≤ y ⧟ x < y ⊞ x = y.
Proof. split. exact (le_lt_par_eq _ _). exact (lt_par_eq_le _ _). Qed.

Lemma lt_iff_le_prod_ne `{LinearOrder P} `{!RefutativeOrder P} (x y : P) : x < y ⧟ x ≤ y ⊠ x ≠ y.
Proof. apply by_contrapositive_iff. exact (le_iff_lt_par_eq (P:=P ᵒᵖ) _ _). Qed.

(** Products *)
Import projection_notation.

Definition tensor_le (X Y:set) {Xle:Le X} {Yle:Le Y} : Le (X ⊗ Y) := λ p q, π₁ p ≤ π₁ q ⊠ π₂ p ≤ π₂ q.
Definition prod_le   (X Y:set) {Xle:Le X} {Yle:Le Y} : Le (X ⊗ Y) := λ p q, π₁ p ≤ π₁ q ∧ π₂ p ≤ π₂ q.
Global Hint Extern 2 (Le (set_T (?X ⊗ ?Y))) => refine (tensor_le X Y) : typeclass_instances.
Global Hint Extern 2 (Le (set_T (?X × ?Y))) => refine (prod_le   X Y) : typeclass_instances.

Ltac unfold_pair_le :=
  try change ( (?a, ?b) ≤ (?c, ?d) :> set_T (_ × _) ) with (aand (a ≤ c) (b ≤ d));
  try change ( (?a, ?b) ≤ (?c, ?d) :> set_T (_ ⊗ _) ) with (a ≤ c ⊠ b ≤ d).

Lemma tensor_weak_poset `{WeakPoset X} `{WeakPoset Y} : WeakPoset (X ⊗ Y).
Proof.
  pose proof (tautology : ∀ P Q R S : Ω, (P ⊠ Q) ⊠ (R ⊠ S) ⊸ (P ⊠ R) ⊠ (Q ⊠ S)) as swap.
  split; [ split |..].
+ intros [x y]. now split.
+ intros [x₁ y₁][x₂ y₂][x₃ y₃]. unfold_pair_le.
  rew (swap _ _ _ _). refine (aprod_proper_aimpl _ _); now apply transitivity.
+ intros [x₁ y₁][x₂ y₂]. unfold_pair_eq; unfold_pair_le.
  refine (aprod_proper_aimpl _ _); now apply subrelation.
+ intros [x₁ y₁][x₂ y₂]. unfold_pair_eq; unfold_pair_le.
  rew (swap _ _ _ _). refine (aprod_proper_aimpl _ _); now apply pseudo_antisymmetry.
Qed.
Global Hint Extern 2 (WeakPoset (_ ⊗ _)) => simple notypeclasses refine tensor_weak_poset : typeclass_instances.

Lemma tensor_le_proper {X Y:set} {Xle:Le X} {Yle:Le Y} {x₁ y₁} {x₂ y₂}
  : x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁, y₁) ≤ (x₂, y₂) :> X ⊗ Y.
Proof. tautological. Qed.

Lemma prod_le_proper {X Y:set} {Xle:Le X} {Yle:Le Y} {x₁ y₁} {x₂ y₂}
  : x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁, y₁) ≤ (x₂, y₂) :> X × Y.
Proof. tautological. Qed.

Global Hint Extern 2 (apos (pair _ _ ≤ _ :> set_T (_ × _) )) => sapply_2 prod_le_proper : proper.
Global Hint Extern 2 (apos (pair _ _ ≤ _ :> set_T (_ ⊗ _) )) => sapply_2 tensor_le_proper : proper.
Global Hint Extern 2 (apos (pair _ _ ≤ _ :> _ * _ ))
  => first [ sapply_2 tensor_le_proper
           | sapply_2 prod_le_proper ] : proper.


