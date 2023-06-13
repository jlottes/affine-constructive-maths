Require Import interfaces.notation sprop tauto tactics.misc easy rewrite.proper.

Lemma spartially_refl_l `{@sPartialEquivalence A R} {x y} : R x y → R x x.
Proof. intros E. now trans y. Qed.

Lemma spartially_refl_r `{@sPartialEquivalence A R} {x y} : R x y → R y y.
Proof. intros E. now trans x. Qed.

Lemma flip_sReflexive     `{!@sReflexive     A R}    : sReflexive   (sflip R).  Proof. firstorder. Qed.
Lemma flip_sIrreflexive   `{!@sIrreflexive   A R}    : sIrreflexive (sflip R).  Proof. firstorder. Qed.
Lemma flip_sSymmetric     `{!@sSymmetric     A R}    : sSymmetric   (sflip R).  Proof. firstorder. Qed.
Lemma flip_sTransitive    `{!@sTransitive    A R}    : sTransitive  (sflip R).  Proof. firstorder. Qed.
Lemma flip_sAntisymmetric `{!@sAntisymmetric A R R'} : sAntisymmetric R (sflip R').  Proof. firstorder. Qed.
Lemma flip_sSubrelation   `{!@sSubrelation   A R R'} : sSubrelation (sflip R) (sflip R').  Proof. firstorder. Qed.
Lemma flip_sSubrelation_symmetric `{!@sSymmetric A R} `{!sSubrelation R R'} : sSubrelation R (sflip R').
Proof. intros x y E. red. now apply ssubrelation. Qed.

Global Hint Extern 2 (sReflexive       (sflip _)) => eapply @flip_sReflexive     : typeclass_instances.
Global Hint Extern 2 (sIrreflexive     (sflip _)) => eapply @flip_sIrreflexive   : typeclass_instances.
Global Hint Extern 2 (sSymmetric       (sflip _)) => eapply @flip_sSymmetric     : typeclass_instances.
Global Hint Extern 2 (sTransitive      (sflip _)) => eapply @flip_sTransitive    : typeclass_instances.
Global Hint Extern 2 (sAntisymmetric _ (sflip _)) => eapply @flip_sAntisymmetric : typeclass_instances.
Global Hint Extern 2 (sSubrelation   (sflip _) (sflip _)) => eapply @flip_sSubrelation : typeclass_instances.
Global Hint Extern 4 (sSubrelation   _ (sflip _)) => eapply @flip_sSubrelation_symmetric : typeclass_instances.

Lemma flip_sPartialEquivalence `{!@sPartialEquivalence A R} : sPartialEquivalence (sflip R).  Proof. now split. Qed.
Lemma flip_sEquivalence `{!@sEquivalence A R} : sEquivalence (sflip R).  Proof. now split. Qed.
Global Hint Extern 2 (sPartialEquivalence (sflip _)) => simple notypeclasses refine flip_sPartialEquivalence : typeclass_instances.
Global Hint Extern 2 (sEquivalence (sflip _)) => simple notypeclasses refine flip_sEquivalence : typeclass_instances.

Lemma complement_sReflexive   `{!@sIrreflexive A R} : sReflexive   (scomplement R).  Proof. firstorder. Qed.
Lemma complement_sIrreflexive `{!@sReflexive   A R} : sIrreflexive (scomplement R).  Proof. firstorder. Qed.
Lemma complement_sSymmetric   `{!@sSymmetric   A R} : sSymmetric   (scomplement R).  Proof. firstorder. Qed.
Lemma complement_sSubrelation `{!@sSubrelation A R R'} : sSubrelation (scomplement R') (scomplement R).  Proof. firstorder. Qed.
Global Hint Extern 2 (sReflexive   (scomplement _)) => eapply @complement_sReflexive   : typeclass_instances.
Global Hint Extern 2 (sIrreflexive (scomplement _)) => eapply @complement_sIrreflexive : typeclass_instances.
Global Hint Extern 2 (sSymmetric   (scomplement _)) => eapply @complement_sSymmetric   : typeclass_instances.
Global Hint Extern 2 (sSubrelation _ (scomplement _)) => eapply @complement_sSubrelation : typeclass_instances.

Lemma seq_sEquivalence {A} : sEquivalence (@seq A).
Proof. split.
+ intros x; constructor.
+ intros x y []; constructor.
+ intros x y z [] []; constructor.
Qed.
Global Hint Extern 2 (sEquivalence seq) => simple notypeclasses refine seq_sEquivalence  : typeclass_instances.
Global Hint Extern 2 (sPartialEquivalence seq) => simple notypeclasses refine seq_sEquivalence  : typeclass_instances.
Global Hint Extern 2 (sReflexive   seq) => simple notypeclasses refine seq_sEquivalence : typeclass_instances.
Global Hint Extern 2 (sSymmetric   seq) => simple notypeclasses refine seq_sEquivalence : typeclass_instances.
Global Hint Extern 2 (sTransitive  seq) => simple notypeclasses refine seq_sEquivalence : typeclass_instances.

Lemma seq_sSubrelation `(R:srelation A) `{!sReflexive R} : sSubrelation seq R.
Proof. now intros x y []. Qed.
Global Hint Extern 2 (sSubrelation seq _) => simple notypeclasses refine (seq_sSubrelation _) : typeclass_instances.

Lemma impl_sReflexive  : sReflexive  impl.  Proof. firstorder. Qed.
Lemma impl_sTransitive : sTransitive impl.  Proof. firstorder. Qed.
Lemma impl_sAntisymmetric : sAntisymmetric iff impl.  Proof. firstorder. Qed.
Lemma impl_sSubrelation_iff : sSubrelation iff impl.  Proof. firstorder. Qed.
Global Hint Extern 2 (sReflexive  impl) => eapply impl_sReflexive  : typeclass_instances.
Global Hint Extern 2 (sTransitive impl) => eapply impl_sTransitive : typeclass_instances.
Global Hint Extern 2 (sAntisymmetric _ impl) => eapply impl_sAntisymmetric : typeclass_instances.
Global Hint Extern 2 (sAntisymmetric iff _) => eapply impl_sAntisymmetric : typeclass_instances.
Global Hint Extern 2 (sSubrelation iff impl) => eapply impl_sSubrelation_iff : typeclass_instances.

Lemma iff_refl  (P :SProp)    : P ↔ P.                  Proof. firstorder. Qed.
Lemma iff_sym   (P Q:SProp)   : P ↔ Q → Q ↔ P.          Proof. firstorder. Qed.
Lemma iff_trans (P Q R:SProp) : P ↔ Q → Q ↔ R → P ↔ R.  Proof. firstorder. Qed.

Lemma iff_sEquivalence : sEquivalence iff.    Proof. firstorder. Qed.
Global Hint Extern 2 (sEquivalence iff) => exact iff_sEquivalence : typeclass_instances.
Global Hint Extern 2 (sPartialEquivalence iff) => exact iff_sEquivalence : typeclass_instances.
Global Hint Extern 2 (sReflexive   iff) => exact iff_sEquivalence  : typeclass_instances.
Global Hint Extern 2 (sSymmetric   iff) => exact iff_sEquivalence  : typeclass_instances.
Global Hint Extern 2 (sTransitive  iff) => exact iff_sEquivalence : typeclass_instances.

Lemma sAntisymmetric_refl_applied `(R:srelation A) : sAntisymmetric R R.  Proof. red. tauto. Qed.
Global Hint Extern 1 (sAntisymmetric ?R ?R) => eapply @sAntisymmetric_refl_applied : typeclass_instances.

Lemma sSubrelation_refl_applied `(R:srelation A) : sSubrelation R R.  Proof. firstorder. Qed.
Global Hint Extern 1 (sSubrelation ?R ?R) => eapply @sSubrelation_refl_applied : typeclass_instances.

Lemma sSubrelation_refl    {A} : sReflexive  (@sSubrelation A).     Proof sSubrelation_refl_applied.
Lemma sSubrelation_trans   {A} : sTransitive (@sSubrelation A).     Proof. firstorder. Qed.
Global Hint Extern 2 (sReflexive  sSubrelation) => simple notypeclasses refine sSubrelation_refl  : typeclass_instances.
Global Hint Extern 2 (sTransitive sSubrelation) => simple notypeclasses refine sSubrelation_trans : typeclass_instances.

Lemma srespectful_sSymmetric {A B} (R:srelation A) (R':srelation B)
  `{!sSymmetric R} `{!sSymmetric R'} : sSymmetric (R ++> R')%ssignature.
Proof. intros f g Ef x y Ex. sym. now apply Ef. Qed.
Global Hint Extern 2 (sSymmetric (_ ++> _)%ssignature) => simple notypeclasses refine (srespectful_sSymmetric _ _) : typeclass_instances.
Global Hint Extern 2 (sSymmetric (_ --> _)%ssignature) => simple notypeclasses refine (srespectful_sSymmetric _ _) : typeclass_instances.

Lemma srespectful_sTransitive {A B} (R:srelation A) (R':srelation B)
  `{!sPartialEquivalence R} `{!sTransitive R'} : sTransitive (R ++> R')%ssignature.
Proof. intros f g h E1 E2 x y Ex. trans (g x).
+ apply E1. exact (spartially_refl_l Ex).
+ now apply E2.
Qed.
Global Hint Extern 2 (sTransitive (_ ++> _)%ssignature) => simple notypeclasses refine (srespectful_sTransitive _ _) : typeclass_instances.
Global Hint Extern 2 (sTransitive (_ --> _)%ssignature) => simple notypeclasses refine (srespectful_sTransitive _ _) : typeclass_instances.

Lemma srespectful_PER {A B} (R:srelation A) (R':srelation B)
  `{!sPartialEquivalence R} `{!sPartialEquivalence R'} : sPartialEquivalence (R ++> R')%ssignature.
Proof. now split. Qed.
Global Hint Extern 2 (sPartialEquivalence (_ ++> _)%ssignature) => simple notypeclasses refine (srespectful_PER _ _) : typeclass_instances.
Global Hint Extern 2 (sPartialEquivalence (_ --> _)%ssignature) => simple notypeclasses refine (srespectful_PER _ _) : typeclass_instances.

Lemma srespectful_subrel {A B}
  {R1 S1 : srelation A} `{!sSubrelation S1 R1}
  {R2 S2 : srelation B} `{!sSubrelation S2 R2}
  : sSubrelation (R1++>S2)%ssignature (S1++>R2)%ssignature .
Proof. intros f g Ef x y Ex. now apply ssubrelation, Ef, ssubrelation. Qed.
Global Hint Extern 2 (sSubrelation _ (_ ++> _)%ssignature) => simple notypeclasses refine srespectful_subrel : typeclass_instances.
Global Hint Extern 2 (sSubrelation _ (_ --> _)%ssignature) => simple notypeclasses refine srespectful_subrel : typeclass_instances.

Lemma srespectful_antisym {A B}
  {R1 S1 : srelation A} `{!sAntisymmetric S1 R1} `{!sSubrelation S1 R1} `{!sSymmetric S1}
  {R2 S2 : srelation B} `{!sAntisymmetric S2 R2}
  : sAntisymmetric (S1==>S2)%ssignature (R1++>R2)%ssignature .
Proof. intros f g E1 E2 x y E.
  apply santisymmetry; [ apply E1 | apply E2 ]; now apply ssubrelation.
Qed.
Global Hint Extern 2 (sAntisymmetric _ (_ ++> _)%ssignature) => simple notypeclasses refine srespectful_antisym : typeclass_instances.
Global Hint Extern 2 (sAntisymmetric _ (_ --> _)%ssignature) => simple notypeclasses refine srespectful_antisym : typeclass_instances.

Lemma sproper_antisym `{H:@sAntisymmetric A R R'} {m} : sProper R' m → sProper R m.
Proof. intro. red. now apply santisymmetry. Qed.

Lemma sproper_antisym_applied_p {A B m} {R₁ S₁ : srelation A} {R₂ S₂ : srelation B}
  {H:sAntisymmetric (S₁==>S₂)%ssignature (R₁++>R₂)%ssignature}
    : (∀ x y : A, R₁ x y → R₂ (m x) (m y))
    → (∀ x y : A, S₁ x y → S₂ (m x) (m y)).
Proof sproper_antisym (R:=(S₁==>S₂)%ssignature) (R':=(R₁++>R₂)%ssignature).

Lemma sproper_antisym_applied_f {A B m} {R₁ S₁ : srelation A} {R₂ S₂ : srelation B}
  {H:sAntisymmetric (S₁==>S₂)%ssignature (R₁-->R₂)%ssignature}
    : (∀ x y : A, R₁ y x → R₂ (m x) (m y))
    → (∀ x y : A, S₁ x y → S₂ (m x) (m y)).
Proof sproper_antisym (R:=(S₁==>S₂)%ssignature) (R':=(R₁-->R₂)%ssignature).

Local Ltac prove_proper_antisym_applied m :=
  let P := fresh "P" in intro P;
  match goal with H : sAntisymmetric ?S ?R |- _ =>
    let H2 := fresh "H" in
    enough (sProper S m) as H2 by (intros; now apply H2);
    apply (sproper_antisym (H:=H));
    repeat (hnf; intros); now apply P
  end.

Lemma sproper_antisym_applied_pp {A B C m} {R₁ S₁ : srelation A} {R₂ S₂ : srelation B} {R₃ S₃ : srelation C}
  {H:sAntisymmetric (S₁==>S₂==>S₃)%ssignature (R₁++>R₂++>R₃)%ssignature}
    : (∀ x₁ y₁ x₂ y₂, R₁ x₁ y₁ → R₂ x₂ y₂ → R₃ (m x₁ x₂) (m y₁ y₂))
    → (∀ x₁ y₁ x₂ y₂, S₁ x₁ y₁ → S₂ x₂ y₂ → S₃ (m x₁ x₂) (m y₁ y₂)).
Proof. prove_proper_antisym_applied m. Qed.

Lemma sproper_antisym_applied_fp {A B C m} {R₁ S₁ : srelation A} {R₂ S₂ : srelation B} {R₃ S₃ : srelation C}
  `{!sAntisymmetric (S₁==>S₂==>S₃)%ssignature (R₁-->R₂++>R₃)%ssignature}
    : (∀ x₁ y₁ x₂ y₂, R₁ y₁ x₁ → R₂ x₂ y₂ → R₃ (m x₁ x₂) (m y₁ y₂))
    → (∀ x₁ y₁ x₂ y₂, S₁ x₁ y₁ → S₂ x₂ y₂ → S₃ (m x₁ x₂) (m y₁ y₂)).
Proof. prove_proper_antisym_applied m. Qed.

Lemma sproper_antisym_applied_pf {A B C m} {R₁ S₁ : srelation A} {R₂ S₂ : srelation B} {R₃ S₃ : srelation C}
  `{!sAntisymmetric (S₁==>S₂==>S₃)%ssignature (R₁++>R₂-->R₃)%ssignature}
    : (∀ x₁ y₁ x₂ y₂, R₁ x₁ y₁ → R₂ y₂ x₂ → R₃ (m x₁ x₂) (m y₁ y₂))
    → (∀ x₁ y₁ x₂ y₂, S₁ x₁ y₁ → S₂ x₂ y₂ → S₃ (m x₁ x₂) (m y₁ y₂)).
Proof. prove_proper_antisym_applied m. Qed.

Lemma sproper_antisym_applied_ff {A B C m} {R₁ S₁ : srelation A} {R₂ S₂ : srelation B} {R₃ S₃ : srelation C}
  `{!sAntisymmetric (S₁==>S₂==>S₃)%ssignature (R₁-->R₂-->R₃)%ssignature}
    : (∀ x₁ y₁ x₂ y₂, R₁ y₁ x₁ → R₂ y₂ x₂ → R₃ (m x₁ x₂) (m y₁ y₂))
    → (∀ x₁ y₁ x₂ y₂, S₁ x₁ y₁ → S₂ x₂ y₂ → S₃ (m x₁ x₂) (m y₁ y₂)).
Proof. prove_proper_antisym_applied m. Qed.


Lemma sTransitive_rel_proper_impl {A} R {H:@sTransitive A R}
  {x₁ x₂ y₁ y₂} : R x₂ x₁ → R y₁ y₂ → impl (R x₁ y₁) (R x₂ y₂).
Proof. intros; intro. trans x₁; trivial. now trans y₁. Qed.

Lemma sPER_rel_proper_impl {A} R `{@sPartialEquivalence A R}
  {x₁ x₂ y₁ y₂} : R x₁ x₂ → R y₁ y₂ → impl (R x₁ y₁) (R x₂ y₂).
Proof. intros; intro. trans x₁; [ now sym | now trans y₁ ]. Qed.

Lemma sPER_rel_proper_iff {A} R `{@sPartialEquivalence A R}
  {x₁ x₂ y₁ y₂} : R x₁ x₂ → R y₁ y₂ → iff (R x₁ y₁) (R x₂ y₂).
Proof. split; fold_impl; now apply (sPER_rel_proper_impl R). Qed.

Lemma impl_proper_impl     {P₁ P₂ Q₁ Q₂}: impl P₂ P₁ → impl Q₁ Q₂ → impl (impl P₁ Q₁) (impl P₂ Q₂).  Proof sTransitive_rel_proper_impl impl.
Lemma impl_proper_iff  : ∀ {P₁ P₂ Q₁ Q₂}, iff  P₁ P₂ → iff  Q₁ Q₂ → iff  (impl P₁ Q₁) (impl P₂ Q₂).  Proof sproper_antisym_applied_fp (@impl_proper_impl).
Lemma iff_proper_impl      {P₁ P₂ Q₁ Q₂}: iff  P₁ P₂ → iff  Q₁ Q₂ → impl (iff  P₁ Q₁) (iff  P₂ Q₂).  Proof sPER_rel_proper_impl iff.
Lemma iff_proper_iff   : ∀ {P₁ P₂ Q₁ Q₂}, iff  P₁ P₂ → iff  Q₁ Q₂ → iff  (iff  P₁ Q₁) (iff  P₂ Q₂).  Proof sproper_antisym_applied_pp (@iff_proper_impl).
Lemma not_proper_impl      {P₁ P₂}      : impl P₂ P₁ → impl (not P₁) (not P₂).  Proof. unfold impl. tauto. Qed.
Lemma not_proper_iff   : ∀ {P₁ P₂}      , iff  P₁ P₂ → iff  (not P₁) (not P₂).  Proof sproper_antisym_applied_f (@not_proper_impl).
Lemma or_proper_impl       {P₁ P₂ Q₁ Q₂}: impl P₁ P₂ → impl Q₁ Q₂ → impl (or  P₁ Q₁) (or  P₂ Q₂).  Proof. unfold impl. tauto. Qed.
Lemma or_proper_iff    : ∀ {P₁ P₂ Q₁ Q₂}, iff  P₁ P₂ → iff  Q₁ Q₂ → iff  (or  P₁ Q₁) (or  P₂ Q₂).  Proof sproper_antisym_applied_pp (@or_proper_impl).
Lemma and_proper_impl      {P₁ P₂ Q₁ Q₂}: impl P₁ P₂ → impl Q₁ Q₂ → impl (and P₁ Q₁) (and P₂ Q₂).  Proof. unfold impl. tauto. Qed.
Lemma and_proper_iff   : ∀ {P₁ P₂ Q₁ Q₂}, iff  P₁ P₂ → iff  Q₁ Q₂ → iff  (and P₁ Q₁) (and P₂ Q₂).  Proof sproper_antisym_applied_pp (@and_proper_impl).

Global Hint Extern 1 ((sflip ?R) ?a ?b) => change (R b a) : proper.
Global Hint Extern 10 => lazymatch goal with |- (forall _ : ?P, ?Q) => change (impl P Q) end : proper.

Global Hint Extern 2 (impl (impl _ _)         _) => sapply_2 impl_proper_impl : proper.
Global Hint Extern 2 (iff  (impl _ _)         _) => sapply_2 impl_proper_iff  : proper.
Global Hint Extern 2 (impl (iff  _ _)         _) => sapply_2 iff_proper_impl  : proper.
Global Hint Extern 2 (iff  (iff  _ _)         _) => sapply_2 iff_proper_iff   : proper.
Global Hint Extern 2 (impl (not _)            _) => sapply_1 not_proper_impl  : proper.
Global Hint Extern 2 (iff  (not _)            _) => sapply_1 not_proper_iff   : proper.
Global Hint Extern 2 (impl (or  _ _)          _) => sapply_2 or_proper_impl   : proper.
Global Hint Extern 2 (iff  (or  _ _)          _) => sapply_2 or_proper_iff    : proper.
Global Hint Extern 2 (impl (and _ _)          _) => sapply_2 and_proper_impl  : proper.
Global Hint Extern 2 (iff  (and _ _)          _) => sapply_2 and_proper_iff   : proper.


Ltac forall_proper_impl_tac :=
  first [ simple refine (impl_proper_impl _ _)
        | let H := fresh "H" in let x := fresh "x" in intros H x;
          specialize (H x); revert H; fold_impl ].

Ltac forall_proper_iff_tac :=
  first [ simple refine (impl_proper_iff _ _)
        | simple refine ((λ H : (∀ x, iff _ _), conj (λ P x, andl (H x) (P x)) (λ P x, andr (H x) (P x))) (λ _, _)) ].

Global Hint Extern 2 (impl (∀ x, _) _) => forall_proper_impl_tac : proper.
Global Hint Extern 2 (iff  (∀ x, _) _) => forall_proper_iff_tac : proper.

Ltac ex_proper_impl_tac :=
  refine ((λ H : (∀ x, impl _ _), λ '(exists _ x p), exists _ x (H x p)) (λ _, _)).

Ltac ex_proper_iff_tac :=
  refine ((λ H : (∀ x, iff _ _), conj (λ '(exists _ x p), exists _ x (andl (H x) p))
                                      (λ '(exists _ x p), exists _ x (andr (H x) p)) ) (λ _, _)).

Global Hint Extern 2 (impl (ex _) _) => ex_proper_impl_tac : proper.
Global Hint Extern 2 (iff  (ex _) _) => ex_proper_iff_tac : proper.


