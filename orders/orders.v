Require Export interfaces.orders.
Require Import logic.aprop relations easy rewrite tactics.misc.

Local Notation "X 'ᵒᵖ'" := (order_op X) (at level 1, format "X 'ᵒᵖ'").

Definition le_dual `{Le A} {x:A} {y} : DeMorganDual (x ≤ y) (y < x) := demorgan_dual_base.
Definition lt_dual `{Le A} {x:A} {y} : DeMorganDual (x < y) (y ≤ x) := anot_dual.
Global Hint Extern 2 (DeMorganDual (_ ≤ _) _) => notypeclasses refine le_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ < _) _) => notypeclasses refine lt_dual : typeclass_instances.

Global Hint Extern 2 (apos (aimpl (_ ≤ _, _))) => sapply_2 (Transitive_rel_proper_aimpl (≤)) : proper.
Global Hint Extern 2 (apos (aiff (_ ≤ _, _))) => sapply_2 (Transitive_Antisymmetric_rel_proper_aiff (≤) (=)) : proper.

Lemma lt_proper_aimpl `{WeakPoset P} {x₁ x₂ y₁ y₂ : P} : x₂ ≤ x₁ → y₁ ≤ y₂ → (x₁ < y₁ ⊸ x₂ < y₂).
Proof. intros E1 E2. apply by_contrapositive. now rew [ E1 | E2 ]. Qed.
Lemma lt_proper_aiff `{WeakPoset P} {x₁ x₂ y₁ y₂ : P} : x₁ = x₂ → y₁ = y₂ → (x₁ < y₁ ⧟ x₂ < y₂).
Proof. intros E1 E2. apply by_contrapositive_iff. now rew [ E1 | E2 ]. Qed.

Global Hint Extern 2 (apos (aimpl (_ < _, _))) => sapply_2 lt_proper_aimpl : proper.
Global Hint Extern 2 (apos (aiff (_ < _, _))) => sapply_2 lt_proper_aiff : proper.

#[global] Hint Extern 3 (Subrelation (≤) (≤)) => simple notypeclasses refine (Subrelation_refl_applied _) : typeclass_instances.

Global Hint Extern 20 (apos (_ ≤ _)) => sapply_1 (aimpl_impl_pos (eq_le_sub _)) : proper.

Coercion IsDecLe_DecidableRelation `{H:IsDecLe X} : DecidableLe X := IsDec_Decidable.

Coercion dec_le_aff_eq `{H:DecidableLe X} : AffirmativeLe X := H.
Coercion dec_le_ref_eq `{H:DecidableLe X} : RefutativeLe X := H.

Definition dec_le_strong `{PreOrder (X:=X)} {H:DecidableLe X} : StrongLe X := dec_trans_strong (≤).

Coercion dec_order_aff `{DecidableOrder P} : AffirmativeOrder P.  Proof. now split. Qed.
Coercion dec_order_ref `{DecidableOrder P} : RefutativeOrder  P.  Proof. now split. Qed.
Coercion dec_order_strong `{DecidableOrder P} : StrongPoset P.
Proof. split; try exact _. exact dec_le_strong. Qed.


Section opposite.
  Ltac go := first [ red | split ]; try exact _; change (@le (order_op _) ?R) with R; unfold order_op; exact _.
  Instance PreOrder_op         {X:Type} `{PreOrder         X} : PreOrder         (X ᵒᵖ).  Proof. go. Defined.
  Instance StrongLe_op         {X:Type} `{StrongLe      X} : StrongLe      (X ᵒᵖ).  Proof. go. Defined.
  Instance DecidableLe_op      {X:Type} `{DecidableLe   X} : DecidableLe   (X ᵒᵖ).  Proof. go. Defined.
  Instance AffirmativeLe_op    {X:Type} `{AffirmativeLe X} : AffirmativeLe (X ᵒᵖ).  Proof. go. Defined.
  Instance RefutativeLe_op     {X:Type} `{RefutativeLe  X} : RefutativeLe  (X ᵒᵖ).  Proof. go. Defined.
End opposite.
Global Hint Extern 2 (PreOrder         (_ ᵒᵖ)) => simple notypeclasses refine PreOrder_op      : typeclass_instances.
Global Hint Extern 2 (StrongLe         (_ ᵒᵖ)) => simple notypeclasses refine StrongLe_op      : typeclass_instances.
Global Hint Extern 2 (DecidableLe      (_ ᵒᵖ)) => simple notypeclasses refine DecidableLe_op   : typeclass_instances.
Global Hint Extern 2 (AffirmativeLe    (_ ᵒᵖ)) => simple notypeclasses refine AffirmativeLe_op : typeclass_instances.
Global Hint Extern 2 (RefutativeLe     (_ ᵒᵖ)) => simple notypeclasses refine RefutativeLe_op  : typeclass_instances.
Global Hint Extern 2 (PreOrder         (set_T (Order_op _))) => simple notypeclasses refine PreOrder_op      : typeclass_instances.
Global Hint Extern 2 (StrongLe         (set_T (Order_op _))) => simple notypeclasses refine StrongLe_op      : typeclass_instances.
Global Hint Extern 2 (DecidableLe      (set_T (Order_op _))) => simple notypeclasses refine DecidableLe_op   : typeclass_instances.
Global Hint Extern 2 (AffirmativeLe    (set_T (Order_op _))) => simple notypeclasses refine AffirmativeLe_op : typeclass_instances.
Global Hint Extern 2 (RefutativeLe     (set_T (Order_op _))) => simple notypeclasses refine RefutativeLe_op  : typeclass_instances.

Section opposite.
  Ltac go := first [ red | split ]; try exact _; change (@le (set_T (Order_op _)) ?R) with R; exact _.
  Instance WeakPoset_op        `{WeakPoset X} : WeakPoset (X ᵒᵖ).  Proof. go. Defined.
  Instance Poset_op            `{Poset X} : Poset (X ᵒᵖ).  Proof. go. Defined.
  Instance StrongPoset_op      `{StrongPoset      X} : StrongPoset      (X ᵒᵖ).  Proof. go. Defined.
  Instance DecidableOrder_op   `{DecidableOrder   X} : DecidableOrder   (X ᵒᵖ).  Proof. go. Defined.
  Instance AffirmativeOrder_op `{AffirmativeOrder X} : AffirmativeOrder (X ᵒᵖ).  Proof. go. Defined.
  Instance RefutativeOrder_op  `{RefutativeOrder  X} : RefutativeOrder  (X ᵒᵖ).  Proof. go. Defined.
  Instance TotalOrder_op       `{TotalOrder       X} : TotalOrder       (X ᵒᵖ).  Proof. go. Defined.
  Instance LinearOrder_op      `{LinearOrder X}      : LinearOrder      (X ᵒᵖ).  Proof. go. Defined.
End opposite.
Global Hint Extern 2 (WeakPoset        (Order_op _)) => simple notypeclasses refine WeakPoset_op : typeclass_instances.
Global Hint Extern 2 (Poset            (Order_op _)) => simple notypeclasses refine Poset_op : typeclass_instances.
Global Hint Extern 2 (StrongPoset      (Order_op _)) => simple notypeclasses refine StrongPoset_op      : typeclass_instances.
Global Hint Extern 2 (DecidableOrder   (Order_op _)) => simple notypeclasses refine DecidableOrder_op   : typeclass_instances.
Global Hint Extern 2 (AffirmativeOrder (Order_op _)) => simple notypeclasses refine AffirmativeOrder_op : typeclass_instances.
Global Hint Extern 2 (RefutativeOrder  (Order_op _)) => simple notypeclasses refine RefutativeOrder_op  : typeclass_instances.
Global Hint Extern 2 (TotalOrder       (Order_op _)) => simple notypeclasses refine TotalOrder_op       : typeclass_instances.
Global Hint Extern 2 (LinearOrder      (Order_op _)) => simple notypeclasses refine LinearOrder_op      : typeclass_instances.


Lemma alt_Build_WeakPoset {X : set} {Xle : Le X} :
   Reflexive (A:=X) (≤)
 → Transitive (A:=X) (≤)
 → Subrelation (A:=X∗X) (=) (≤)
 → PseudoAntisymmetric (A:=X) (≤) (=)
 → WeakPoset X.
Proof. intros. repeat ( split; try exact _ ). Qed.

Lemma alt_Build_Poset {X : set} {Xle : Le X} :
   Reflexive (A:=X) (≤)
 → Transitive (A:=X) (≤)
 → Subrelation (A:=X∗X) (=) (≤)
 → Antisymmetric (A:=X) (≤) (=)
 → Poset X.
Proof. intros. repeat ( split; try exact _ ). Qed.

Section induced_poset.
  Universes u.
  Context {A:Type@{u}} `{PreOrder A} `{Equiv A}.
  Context (eq_correct : ∀ x y : A, x = y ⧟ x ≤ y ∧ y ≤ x).

  Local Instance preorder_is_set : IsSet A.
  Proof. split; hnf; intros; rew ?(eq_correct _ _).
  + now split.
  + refine (aand_intro (aandr _ _) (aandl _ _)).
  + refine (aand_intro _ _).
    * rew (aandl _ _). now apply transitivity.
    * rew (aandr _ _). rew (aprod_com _ _) at 1. now apply transitivity.
  Qed.
  Definition induced_poset := set_make A.
  Local Hint Extern 1 (Le (set_T induced_poset)) => change (Le A) : typeclass_instances.
  Lemma induced_poset_poset : Poset induced_poset.
  Proof. apply alt_Build_Poset; try exact _; hnf; unfold induced_poset, set_T, set_eq;
    [ intros [??] | intros ]; now rew ?(eq_correct _ _).
  Qed.
End induced_poset.

(*
Lemma le_is_fun `{WeakPoset P} : @IsFun (P ⊗ P) Ω le.
Proof.
  enough (∀ x₁ x₂ y₁ y₂ : P, x₁ = x₂ ⊠ y₁ = y₂ ⊸ x₁ ≤ y₁ ⊸ x₂ ≤ y₂) as Q.
  * intros [x₁ y₁] [x₂ y₂]. change (x₁ = x₂ ⊠ y₁ = y₂ ⊸ x₁ ≤ y₁ ⧟ x₂ ≤ y₂).
    apply aand_intro; [ now apply Q |].
    rew [ (symmetry_iff (=) x₁ x₂) | (symmetry_iff (=) y₁ y₂) ]; now apply Q.
  * intros. rew <-(transitivity (≤) x₂ x₁ y₂), <-(transitivity (≤) x₁ y₁ y₂).
    rew (symmetry_iff (=) x₁ x₂).
    rew (subrelation (=) _).
    tautological.
Qed.
Canonical Structure le_fun `{WeakPoset P} : _ ⇾ _ := @func_make _ _ _ le_is_fun.

Lemma lt_is_fun `{WeakPoset P} : @IsFun (P ⊗ P) Ω lt.
Proof. exact (anot ∘ le ∘ tensor_swap _ _). Qed.
Canonical Structure lt_fun `{WeakPoset P} : _ ⇾ _ := @func_make _ _ _ lt_is_fun.
*)

Lemma AProp_is_preorder : PreOrder Ω.
Proof. split; now unfold le. Qed.
Global Hint Extern 2 (PreOrder Ω) => eexact AProp_is_preorder : typeclass_instances.

Lemma AProp_is_poset : Poset Ω.
Proof. now refine (induced_poset_poset _). Qed.
Global Hint Extern 2 (Poset AProp_set) => eexact AProp_is_poset : typeclass_instances.
Global Hint Extern 2 (WeakPoset AProp_set) => notypeclasses refine AProp_is_poset : typeclass_instances.

Global Hint Extern 15 (apos (func_op ?f ?x ⊸ func_op ?g ?y)) =>
  change (apos (@le Ω aimpl (func_op f x) (func_op g y))) : proper.

Lemma anot_order_embedding_flip : OrderEmbeddingFlip anot.
Proof. tautological. Qed.
Global Hint Extern 2 (OrderEmbeddingFlip  anot_fun) => refine anot_order_embedding_flip : typeclass_instances.
Global Hint Extern 2 (OrderPreservingFlip anot_fun) => refine anot_order_embedding_flip : typeclass_instances.
Global Hint Extern 2 (OrderReflectingFlip anot_fun) => refine anot_order_embedding_flip : typeclass_instances.

Definition eq_le      `{WeakPoset P} (x y : P) : x = y ⊸ x ≤ y := eq_le_sub (_, _).
Definition eq_le_flip `{WeakPoset P} : ∀ x y : P, x = y ⊸ y ≤ x := eq_le (P:=P ᵒᵖ).

Lemma lt_ne `{WeakPoset P} (x y : P) : x < y ⊸ x ≠ y.
Proof. apply by_contrapositive, eq_le_flip. Qed.

Definition lt_ne_flip `{WeakPoset P} (x y : P) : x < y ⊸ y ≠ x := lt_ne (P:=P ᵒᵖ) _ _.

Global Hint Extern 8 (apos (?x ≠ ?y)) =>
  match goal with
  | H : apos (x < y) |- _ => refine (aimpl_impl_pos (lt_ne _ _) H)
  | H : apos (y < x) |- _ => refine (aimpl_impl_pos (lt_ne_flip _ _) H)
  end  : typeclass_instances.

Lemma le_antisym_iff `{Poset P} (x y : P) : x ≤ y ∧ y ≤ x ⧟ x = y.
Proof. split.
+ now apply antisymmetry.
+ exact (aand_intro (eq_le _ _) (eq_le_flip _ _)).
Qed.

Lemma ne_iff_lt `{Poset P} (x y : P) : x ≠ y ⧟ x < y ∨ y < x.
Proof. apply by_contrapositive_iff. sym. exact (le_antisym_iff (P:=P ᵒᵖ) _ _). Qed.

Lemma le_lt_par_eq `{WeakPoset P} (x y : P) : x ≤ y ⊸ x < y ⊞ x = y.
Proof. rew <-(le_pseudo_antisym _ _). change (x < y) with ((y ≤ x)ᗮ).
  tautological.
Qed.

Lemma le_prod_ne_lt `{WeakPoset P} (x y : P) : x ≤ y ⊠ x ≠ y ⊸ x < y .
Proof. apply by_contrapositive. exact (le_lt_par_eq (P:=P ᵒᵖ) _ _). Qed.

Lemma le_lt_trans `{WeakPoset P} (x y z : P) : x ≤ y ⊠ y < z ⊸ x < z.
Proof. rew (contrapositive (transitivity (≤) z x y)), (apar_com _ _). exact (aprod_mp_r _ _). Qed.

Lemma lt_le_trans `{WeakPoset P} (x y z : P) : x < y ⊠ y ≤ z ⊸ x < z.
Proof. rew (contrapositive (transitivity (≤) y z x)). exact (aprod_mp_l _ _). Qed.

Definition StrongPoset_StrongSet `{StrongPoset P} : StrongSet P.
Proof. intros x y z.
  rew <-(le_antisym_iff _ _).
  rew <-(strong_transitivity (≤) x y z).
  rew <-(strong_transitivity (≤) z y x).
  tautological.
Qed.
Coercion StrongPoset_StrongSet : StrongPoset >-> StrongSet.

Definition DecidableOrder_DecidableEquality `{DecidableOrder P} : DecidableEquality P.
Proof. intros [x y]. now rew <-(le_antisym_iff _ _). Qed.
Coercion DecidableOrder_DecidableEquality : DecidableOrder >-> DecidableEquality.

Definition RefutativeOrder_RefutativeEquality `{RefutativeOrder P} : RefutativeEquality P.
Proof. intros [x y]. now rew <-(le_antisym_iff _ _). Qed.
Coercion RefutativeOrder_RefutativeEquality : RefutativeOrder >-> RefutativeEquality.

Lemma DecidableOrder_DecidableLt    `{DecidableOrder   P} : DecidableRelation   (A:=P∗P) (<).  Proof. now unfold lt. Qed.
Lemma RefutativeOrder_AffirmativeLt `{RefutativeOrder  P} : AffirmativeRelation (A:=P∗P) (<).  Proof. now unfold lt. Qed.
Lemma AffirmativeOrder_RefutativeLt `{AffirmativeOrder P} : RefutativeRelation  (A:=P∗P) (<).  Proof. now unfold lt. Qed.

Global Hint Extern 2 (DecidableRelation   (<)) => simple notypeclasses refine DecidableOrder_DecidableLt    : typeclass_instances.
Global Hint Extern 2 (AffirmativeRelation (<)) => simple notypeclasses refine RefutativeOrder_AffirmativeLt : typeclass_instances.
Global Hint Extern 2 (RefutativeRelation  (<)) => simple notypeclasses refine AffirmativeOrder_RefutativeLt : typeclass_instances.


Lemma TotalOrder_is_Linear `{TotalOrder X} : LinearOrder X.
Proof. now split. Qed.
Coercion TotalOrder_is_Linear : TotalOrder >-> LinearOrder.

Definition lt_le_sub `{LinearOrder P} : Subrelation (A:=P∗P) (<) (≤) := λ p, pseudo_total (≤) _ _.
Global Hint Extern 2 (Subrelation (<) (≤)) => simple notypeclasses refine lt_le_sub : typeclass_instances.
Definition lt_le `{LinearOrder P} (x y : P) : x < y ⊸ x ≤ y := lt_le_sub (_, _).

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
Proof. exact ( aor_elim (lt_le _ _) (eq_le _ _) ). Qed.

Lemma lt_le_and_ne `{LinearOrder P} (x y : P) : x < y ⊸ x ≤ y ∧ x ≠ y .
Proof. apply by_contrapositive. exact (lt_or_eq_le (P:=P ᵒᵖ) _ _). Qed.



Lemma lt_par_eq_le `{LinearOrder P} `{!RefutativeOrder P} (x y : P) : x < y ⊞ x = y ⊸ x ≤ y.
Proof. apply aor_apar_refutative. exact (lt_or_eq_le _ _). Qed. 

Lemma le_iff_lt_par_eq `{LinearOrder P} `{!RefutativeOrder P} (x y : P) : x ≤ y ⧟ x < y ⊞ x = y.
Proof. split. exact (le_lt_par_eq _ _). exact (lt_par_eq_le _ _). Qed.

Lemma lt_iff_le_prod_ne `{LinearOrder P} `{!RefutativeOrder P} (x y : P) : x < y ⧟ x ≤ y ⊠ x ≠ y.
Proof. apply by_contrapositive_iff. exact (le_iff_lt_par_eq (P:=P ᵒᵖ) _ _). Qed.


Global Hint Extern 8 (apos (?x ≤ ?y)) =>
  match goal with
  | H : apos (x = y) |- _ => refine (aimpl_impl_pos (eq_le _ _) H)
  | H : apos (y = x) |- _ => refine (aimpl_impl_pos (eq_le_flip _ _) H)
  | H : apos (x < y) |- _ => refine (aimpl_impl_pos (lt_le _ _) H)
  end : typeclass_instances.


(** Products *)
Import projection_notation.

Definition tensor_le@{u} (X Y:set@{u}) {Xle:Le X} {Yle:Le Y} : Le (X ⊗ Y) := λ '(p, q), π₁ p ≤ π₁ q ⊠ π₂ p ≤ π₂ q.
Definition prod_le@{u}   (X Y:set@{u}) {Xle:Le X} {Yle:Le Y} : Le (X × Y) := λ '(p, q), π₁ p ≤ π₁ q ∧ π₂ p ≤ π₂ q.
Global Hint Extern 2 (Le (set_T (?X ⊗ ?Y))) => refine (tensor_le X Y) : typeclass_instances.
Global Hint Extern 2 (Le (set_T (?X × ?Y))) => refine (prod_le   X Y) : typeclass_instances.

Ltac unfold_pair_le :=
  try change ( (?a, ?b) ≤ (?c, ?d) :> set_T (_ × _) ) with (aand (a ≤ c, b ≤ d));
  try change ( (?a, ?b) ≤ (?c, ?d) :> set_T (_ ⊗ _) ) with (a ≤ c ⊠ b ≤ d).

Lemma tensor_preorder@{u} {X Y:set@{u}} `{PreOrder X} `{PreOrder Y} : PreOrder (X ⊗ Y).
Proof. split.
+ intros [x y]. now split.
+ intros [x₁ y₁][x₂ y₂][x₃ y₃]. unfold_pair_le.
  now rew (aprod_medial _ _ _ _), (transitivity le _ _ _).
Qed.
#[global] Hint Extern 2 (PreOrder (set_T (_ ⊗ _))) => simple notypeclasses refine tensor_preorder : typeclass_instances.

Lemma prod_preorder@{u} {X Y:set@{u}} `{PreOrder X} `{PreOrder Y} : PreOrder (X × Y).
Proof. split.
+ intros [x y]. now split.
+ intros [x₁ y₁][x₂ y₂][x₃ y₃]. unfold_pair_le.
  now rew (aand_aprod_swap _ _ _ _), (transitivity le _ _ _).
Qed.
#[global] Hint Extern 2 (PreOrder (set_T (_ × _))) => simple notypeclasses refine prod_preorder : typeclass_instances.

Lemma tensor_weak_poset@{u} {X Y:set@{u}} `{WeakPoset X} `{WeakPoset Y} : WeakPoset (X ⊗ Y).
Proof. split; try exact _.
+ intros [[x₁ y₁][x₂ y₂]]. unfold_pair_eq; unfold_pair_le.
  refine (aprod_proper_aimpl _ _); now apply subrelation.
+ intros [x₁ y₁][x₂ y₂]. unfold_pair_eq; unfold_pair_le.
  rew (aprod_medial _ _ _ _). refine (aprod_proper_aimpl _ _); now apply pseudo_antisymmetry.
Qed.
Global Hint Extern 2 (WeakPoset (_ ⊗ _)) => simple notypeclasses refine tensor_weak_poset : typeclass_instances.

Lemma prod_weak_poset@{u} {X Y:set@{u}} `{WeakPoset X} `{WeakPoset Y} : WeakPoset (X × Y).
Proof. split; try exact _.
+ intros [[x₁ y₁][x₂ y₂]]. unfold_pair_eq; unfold_pair_le.
  refine (aand_proper_aimpl _ _); now apply subrelation.
+ intros [x₁ y₁][x₂ y₂]. unfold_pair_eq; unfold_pair_le.
  rew (aand_aprod_swap _ _ _ _). refine (aand_proper_aimpl _ _); now apply pseudo_antisymmetry.
Qed.
Global Hint Extern 2 (WeakPoset (_ × _)) => simple notypeclasses refine prod_weak_poset : typeclass_instances.

Lemma prod_poset@{u} {X Y:set@{u}} `{Poset X} `{Poset Y} : Poset (X × Y).
Proof. split; [exact _|]. intros [x₁ y₁][x₂ y₂]. unfold_pair_eq; unfold_pair_le.
  apply aand_intro.
  + rew [(aandl (x₁ ≤ x₂) _)|(aandl (x₂ ≤ x₁) _)]. now apply antisymmetry.
  + rew [(aandr _ (y₁ ≤ y₂))|(aandr _ (y₂ ≤ y₁))]. now apply antisymmetry.
Qed.
Global Hint Extern 2 (Poset (_ × _)) => simple notypeclasses refine prod_poset : typeclass_instances.

Lemma tensor_le_proper@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} {x₁ y₁} {x₂ y₂}
  : x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁, y₁) ≤ (x₂, y₂) :> X ⊗ Y.
Proof. full_tautological. Qed.

Lemma prod_le_proper@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} {x₁ y₁} {x₂ y₂}
  : x₁ ≤ x₂ → y₁ ≤ y₂ → (x₁, y₁) ≤ (x₂, y₂) :> X × Y.
Proof. full_tautological. Qed.

Global Hint Extern 2 (apos (pair _ _ ≤ _ :> set_T (_ × _) )) => sapply_2 prod_le_proper : proper.
Global Hint Extern 2 (apos (pair _ _ ≤ _ :> set_T (_ ⊗ _) )) => sapply_2 tensor_le_proper : proper.
Global Hint Extern 2 (apos (pair _ _ ≤ _ :> _ ∗ _ ))
  => first [ sapply_2 tensor_le_proper
           | sapply_2 prod_le_proper ] : proper.


(** Effective trichotomoy *)

Definition trich_le_dec `{Trich X} : @Dec (X∗X) (≤) := λ p, match trich p with
  | is_lt => true
  | is_eq => true
  | is_gt => false
end.
Global Hint Extern 10 (Dec (≤)) => simple refine trich_le_dec : typeclass_instances.


Coercion trich_le_dec_correct `{IsTrich X} : IsDecLe X.
Proof. intros [x y]. unfold dec, trich_le_dec. generalize (trich_spec x y); destruct (trich (x, y)).
+ apply lt_le.
+ apply eq_le.
+ now intro.
Qed.
Global Hint Extern 2 (IsDecLe _ (d:=trich_le_dec)) => simple notypeclasses refine trich_le_dec_correct : typeclass_instances.

Coercion trich_decidable `{IsTrich X} : DecidableOrder X.  Proof. now split. Qed.
Coercion trich_total     `{IsTrich X} : TotalOrder X.
Proof. split; try exact _. intros x y.
  generalize (trich_spec x y); destruct (trich (x, y)).
+ intro. left. now apply lt_le.
+ intro. left. now apply eq_le.
+ intro. right. now apply lt_le.
Qed.


Definition trich_eq_dec `{Trich X} : @Dec (X∗X) (=) := λ p, match trich p with
  | is_lt => false
  | is_eq => true
  | is_gt => false
end.
Global Hint Extern 20 (Dec (=)) => simple refine trich_eq_dec : typeclass_instances.


Coercion trich_eq_dec_correct `{IsTrich X} : IsDecEq X.
Proof. intros [x y]. unfold dec, trich_eq_dec. generalize (trich_spec x y); destruct (trich (x, y)).
+ apply lt_ne.
+ easy.
+ apply lt_ne_flip.
Qed.
Global Hint Extern 2 (IsDecEq _ (d:=trich_eq_dec)) => simple notypeclasses refine trich_eq_dec_correct : typeclass_instances.

(** of course set *)

Import of_course_set_notation.

Typeclasses Opaque of_course_set.
#[global] Hint Extern 0 (Le (set_T (of_course_set ?X))) => simple notypeclasses refine (of_course_rel (λ p, @le X _ p)) : typeclass_instances.

Lemma of_course_aff_le {X:set} {Xle:Le X} : AffirmativeLe !X.
Proof. red; now change (@le !X ?R) with R. Qed.
#[global] Hint Extern 2 (AffirmativeLe (set_T !_)) => simple notypeclasses refine of_course_aff_le : typeclass_instances.

Lemma of_course_preorder@{u} {X:set@{u}} {Xle:Le X} `{!PreOrder X} : PreOrder !X.
Proof. split; now change (@le !X ?R) with R. Qed.
#[global] Hint Extern 2 (PreOrder (set_T !_)) => simple notypeclasses refine of_course_preorder : typeclass_instances.

Lemma of_course_weak_poset `{WeakPoset X} : WeakPoset !X.
Proof. split; try exact _.
+ intros [x y]. apply affirmative_aimpl.
  change (x = y :> X → x ≤ y :> X). apply eq_le.
+ intros x y. apply affirmative_aimpl.
  change (x ≤ y :> X ⊠ y ≤ x :> X → x = y :> X). apply le_pseudo_antisym.
Qed.
#[global] Hint Extern 2 (WeakPoset !_) => simple notypeclasses refine of_course_weak_poset : typeclass_instances.

(** terminal object *)

#[global] Hint Extern 1 (Le unit) => exact (λ _, 𝐓) : typeclass_instances.
#[global] Hint Extern 1 (Le (set_T 𝟏)) => exact (λ _, 𝐓) : typeclass_instances.
Lemma unit_dec_order   : DecidableOrder 𝟏.  Proof. tautological. Qed.
Lemma unit_total_order : TotalOrder 𝟏.      Proof. tautological. Qed.
#[global] Hint Extern 1 (DecidableOrder 𝟏) => simple notypeclasses refine unit_dec_order : typeclass_instances.
#[global] Hint Extern 1 (WeakPoset 𝟏) => simple notypeclasses refine unit_dec_order : typeclass_instances.
#[global] Hint Extern 1 (Poset 𝟏) => simple notypeclasses refine unit_dec_order : typeclass_instances.
#[global] Hint Extern 1 (StrongPoset 𝟏) => simple notypeclasses refine unit_dec_order : typeclass_instances.
#[global] Hint Extern 1 (PreOrder unit) => simple notypeclasses refine unit_dec_order : typeclass_instances.
#[global] Hint Extern 1 (PreOrder (set_T 𝟏)) => simple notypeclasses refine unit_dec_order : typeclass_instances.

#[global] Hint Extern 1 (TotalOrder 𝟏) => simple notypeclasses refine unit_total_order : typeclass_instances.
#[global] Hint Extern 1 (LinearOrder 𝟏) => simple notypeclasses refine unit_total_order : typeclass_instances.

Lemma unit_order_terminal `{f:X ⇾ 𝟏} `{WeakPoset X} : OrderPreserving f.
Proof. split; [ now split | tautological ]. Qed.
#[global] Hint Extern 2 (@OrderPreserving _ 𝟏 _ _ _) => simple notypeclasses refine unit_order_terminal : typeclass_instances.

Lemma from_unit_order_embed `{f:𝟏 ⇾ X} `{WeakPoset X} : OrderEmbedding f.
Proof. split; [ split; [ split; try exact _ |] ..]; intros [][]; refine (aimpl_true_r _). Qed.
#[global] Hint Extern 2 (@OrderEmbedding 𝟏 _ _ _ _) => simple notypeclasses refine from_unit_order_embed : typeclass_instances.
#[global] Hint Extern 2 (@OrderPreserving 𝟏 _ _ _ _) => simple notypeclasses refine from_unit_order_embed : typeclass_instances.
#[global] Hint Extern 2 (@OrderReflecting 𝟏 _ _ _ _) => simple notypeclasses refine from_unit_order_embed : typeclass_instances.

