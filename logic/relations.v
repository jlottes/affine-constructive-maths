Require Export logic.aprop.
Require Import interfaces.notation tauto easy rewrite sprop.

Global Hint Extern 4 (apos (?R (?x, ?y))) => match x with y => refl end : typeclass_instances.

Lemma symmetry_iff {A} R `{!@Symmetric A R} x y : R (x, y) ⧟ R (y, x).  Proof. now split. Qed.
Lemma transitivity_alt {A} R `{!@Transitive A R} x y z : R (x, y) ⊸ R (y, z) ⊸ R (x, z).
Proof. rew <-(aprod_adj _ _ _). now apply transitivity. Qed.

Lemma IsDec_Decidable `{IsDec (R:=R)} : DecidableRelation R.
Proof. intros x. red. generalize (dec_spec R x).
  destruct (dec R x); intro; [ now left | now right ].
Qed.
Coercion IsDec_Decidable : IsDec >-> DecidableRelation.

Coercion dec_rel_aff_rel `(R:A → Ω) (H:DecidableRelation R) : AffirmativeRelation R := H.
Coercion dec_rel_ref_rel `(R:A → Ω) (H:DecidableRelation R) : RefutativeRelation R := H.

Lemma StronglyTransitive_Transitive `(R:A ∗ A → Ω) : StronglyTransitive R → Transitive R.
Proof. intros H x y z. eapply aimpl_trans. split; [refine (aprod_aand _ _) | eapply H]. Qed.
Coercion StronglyTransitive_Transitive : StronglyTransitive >-> Transitive.

Lemma dec_trans_strong `(R:A ∗ A → Ω) `{!DecidableRelation R, !Transitive R} : StronglyTransitive R.
Proof. intros x y z. rew (aand_aprod_dec_l (R (x, y)) _). now apply transitivity. Qed.

Lemma Antisymmetric_PseudoAntisymmetric {A} (R eq : A ∗ A → Ω) : Antisymmetric R eq → PseudoAntisymmetric R eq.
Proof. intros H x y. rew (aprod_aand _ _). now apply antisymmetry. Qed.
Coercion Antisymmetric_PseudoAntisymmetric : Antisymmetric >-> PseudoAntisymmetric.

Lemma dec_pseudo_antisym {A} (R eq:A ∗ A → Ω) `{!DecidableRelation R, !PseudoAntisymmetric R eq}
  : Antisymmetric R eq.
Proof. intros x y. rew (aand_aprod_dec_l _ _). now apply pseudo_antisymmetry. Qed.

Lemma Total_PseudoTotal `(R:A ∗ A → Ω) : TotalRelation R → PseudoTotalRelation R.
Proof. intros H x y. apply aor_apar, H. Qed.
Coercion Total_PseudoTotal : TotalRelation >-> PseudoTotalRelation.

Lemma dec_pseudo_total `(R:A ∗ A → Ω) `{!DecidableRelation R, !PseudoTotalRelation R} : TotalRelation R.
Proof. intros x y. rew <-(apar_aor_dec_l (R (x, y)) (R (y, x))). now apply pseudo_total. Qed.

Lemma flip_Reflexive          `{H:@Reflexive          A R} : Reflexive          (flip R).  Proof. exact H. Qed.
Lemma flip_Symmetric          `{H:@Symmetric          A R} : Symmetric          (flip R).  Proof. intros x y. unfold flip. apply H. Qed.
Lemma flip_Transitive         `{H:@Transitive         A R} : Transitive         (flip R).  Proof. intros x y z. unfold flip. rew (aprod_com _ _). apply H. Qed.
Lemma flip_StronglyTransitive `{H:@StronglyTransitive A R} : StronglyTransitive (flip R).  Proof. intros x y z. unfold flip. rew (aand_com _ _). apply H. Qed.
Lemma flip_PseudoAntisymmetric `{H:@PseudoAntisymmetric A R R'} : PseudoAntisymmetric (flip R) R'.  Proof. intros x y. unfold flip. generalize (pseudo_antisymmetry R x y). tautological.  Qed.
Lemma flip_Antisymmetric `{H:@Antisymmetric A R R'} : Antisymmetric (flip R) R'.  Proof. intros x y. unfold flip. generalize (antisymmetry R x y). tautological.  Qed.
Lemma flip_Subrelation   `{H:@Subrelation   (A∗A) R R'} : Subrelation (flip R) (flip R').  Proof. intros [x y]. unfold flip. apply H. Qed.
Lemma flip_Subrelation_symmetric `{!@Symmetric A R, !Subrelation R R'} : Subrelation R (flip R').
Proof. intros [x y]. unfold flip. rew (symmetry R x y). now apply subrelation. Qed.
Lemma flip_DecidableRelation   `{H:@DecidableRelation   (A∗A) R} : DecidableRelation   (flip R).  Proof. hnf; intros; apply H. Qed.
Lemma flip_AffirmativeRelation `{H:@AffirmativeRelation (A∗A) R} : AffirmativeRelation (flip R).  Proof. hnf; intros; apply H. Qed.
Lemma flip_RefutativeRelation  `{H:@RefutativeRelation  (A∗A) R} : RefutativeRelation  (flip R).  Proof. hnf; intros; apply H. Qed.
Lemma flip_PseudoTotalRelation `{H:@PseudoTotalRelation A R} : PseudoTotalRelation (flip R).  Proof. hnf; intros; apply H. Qed.
Lemma flip_TotalRelation       `{H:@TotalRelation       A R} : TotalRelation       (flip R).  Proof. hnf; intros; apply H. Qed.

Global Hint Extern 2 (Reflexive          (flip _)) => eapply @flip_Reflexive          : typeclass_instances.
Global Hint Extern 2 (Symmetric          (flip _)) => eapply @flip_Symmetric          : typeclass_instances.
Global Hint Extern 2 (Transitive         (flip _)) => eapply @flip_Transitive         : typeclass_instances.
Global Hint Extern 2 (StronglyTransitive (flip _)) => eapply @flip_StronglyTransitive : typeclass_instances.
Global Hint Extern 2 (PseudoAntisymmetric (flip _) _) => eapply @flip_PseudoAntisymmetric : typeclass_instances.
Global Hint Extern 2 (Antisymmetric (flip _) _) => eapply @flip_Antisymmetric : typeclass_instances.
Global Hint Extern 2 (Subrelation   (flip _) (flip _)) => eapply @flip_Subrelation : typeclass_instances.
Global Hint Extern 4 (Subrelation   _ (flip _)) => eapply @flip_Subrelation_symmetric : typeclass_instances.
Global Hint Extern 2 (DecidableRelation   (flip _)) => eapply @flip_DecidableRelation : typeclass_instances.
Global Hint Extern 2 (AffirmativeRelation (flip _)) => eapply @flip_AffirmativeRelation : typeclass_instances.
Global Hint Extern 2 (RefutativeRelation  (flip _)) => eapply @flip_RefutativeRelation  : typeclass_instances.
Global Hint Extern 2 (PseudoTotalRelation (flip _)) => eapply @flip_PseudoTotalRelation : typeclass_instances.
Global Hint Extern 2 (TotalRelation       (flip _)) => eapply @flip_TotalRelation       : typeclass_instances.

Lemma flip_PartialEquivalence `{!@PartialEquivalence A R} : PartialEquivalence (flip R).  Proof. now split. Qed.
Lemma flip_Equivalence `{!@Equivalence A R} : Equivalence (flip R).  Proof. now split. Qed.
Global Hint Extern 2 (PartialEquivalence (flip _)) => simple notypeclasses refine flip_PartialEquivalence : typeclass_instances.
Global Hint Extern 2 (Equivalence (flip _)) => simple notypeclasses refine flip_Equivalence : typeclass_instances.

Global Hint Extern 1 (apos ((flip ?R) (?a, ?b))) => change (apos (R (b, a))) : proper.
Global Hint Extern 1 (apos ((complement ?R) ?x)) => change (apos (anot (R x))) : proper.

Lemma complement_Symmetric   `{H:@Symmetric   A R} : Symmetric   (complement R).  Proof. intros x y. refine (acontra _). apply H. Qed.
Global Hint Extern 2 (Symmetric   (complement _)) => eapply @complement_Symmetric   : typeclass_instances.

Lemma complement_DecidableRelation   `{H:@DecidableRelation   A R} : DecidableRelation   (complement R).  Proof. hnf; now unfold complement. Qed.
Lemma complement_RefutativeRelation  `{H:@AffirmativeRelation A R} : RefutativeRelation  (complement R).  Proof. hnf; now unfold complement. Qed.
Lemma complement_AffirmativeRelation `{H:@RefutativeRelation  A R} : AffirmativeRelation (complement R).  Proof. hnf; now unfold complement. Qed.
Global Hint Extern 2 (DecidableRelation   (complement _)) => eapply @complement_DecidableRelation   : typeclass_instances.
Global Hint Extern 2 (RefutativeRelation  (complement _)) => eapply @complement_RefutativeRelation  : typeclass_instances.
Global Hint Extern 2 (AffirmativeRelation (complement _)) => eapply @complement_AffirmativeRelation : typeclass_instances.

Lemma Antisymmetric_refl_applied `(R:A ∗ A → Ω) : Antisymmetric R R.  Proof. tautological. Qed.
Global Hint Extern 1 (Antisymmetric ?R ?R) => eapply @Antisymmetric_refl_applied : typeclass_instances.

Lemma Subrelation_refl_applied `(R:A → Ω) : Subrelation R R.  Proof. now intros x. Qed.
Global Hint Extern 1 (Subrelation ?R ?R) => simple notypeclasses refine (Subrelation_refl_applied _) : typeclass_instances.

(*
Lemma Subrelation_refl    {A} : sprop.sReflexive  (@Subrelation A).     Proof Subrelation_refl_applied.
Lemma Subrelation_trans   {A} : sprop.sTransitive (@Subrelation A).
Proof. intros R₁ R₂ R₃ H ? x y. rew (H x y). now apply subrelation. Qed.
Global Hint Extern 2 (sprop.sReflexive  Subrelation) => simple notypeclasses refine Subrelation_refl  : typeclass_instances.
Global Hint Extern 2 (sprop.sTransitive Subrelation) => simple notypeclasses refine Subrelation_trans : typeclass_instances.
*)

Lemma Transitive_rel_proper_aimpl {A} R {H:@Transitive A R}
  {x₁ x₂} {y₁ y₂} : R (x₂, x₁) → R (y₁, y₂) → R (x₁, y₁) ⊸ R (x₂, y₂).
Proof. intros Ex Ey.
  rew <-(transitivity R x₂ x₁ y₂), (aprod_true_l Ex).
  rew <-(transitivity R x₁ y₁ y₂), (aprod_true_r Ey).
  refl.
Qed.

Lemma Transitive_Antisymmetric_rel_proper_aiff {A} R R' `{!@Transitive A R, !Subrelation R' R, !Symmetric R'}
  {x₁ x₂} {y₁ y₂} : R' (x₁, x₂) → R' (y₁, y₂) → R (x₁, y₁) ⧟ R (x₂, y₂).
Proof. split; refine (Transitive_rel_proper_aimpl R _ _); now apply (andl (subrelation R' _)). Qed.

Lemma PER_rel_proper_aimpl {A} R `{@PartialEquivalence A R}
  {x₁ x₂} {y₁ y₂} : R (x₁, x₂) → R (y₁, y₂) → R (x₁, y₁) ⊸ R (x₂, y₂).
Proof. intros. now apply (Transitive_rel_proper_aimpl _). Qed.

Lemma PER_rel_proper_aiff {A} R `{@PartialEquivalence A R}
  {x₁ x₂} {y₁ y₂} : R (x₁, x₂) → R (y₁, y₂) → R (x₁, y₁) ⧟ R (x₂, y₂).
Proof. split; now apply (PER_rel_proper_aimpl _). Qed.


Definition trivial_Equivalence A : Equivalence (λ _ : A∗A, 𝐓) := tautology.
Global Hint Extern 2 (Equivalence (λ _, atrue)) => simple notypeclasses refine (trivial_Equivalence _) : typeclass_instances.
Global Hint Extern 2 (PartialEquivalence (λ _, atrue)) => simple notypeclasses refine (trivial_Equivalence _) : typeclass_instances.
Global Hint Extern 2 (Reflexive (λ _, atrue)) => simple notypeclasses refine (trivial_Equivalence _) : typeclass_instances.
Global Hint Extern 2 (Symmetric (λ _, atrue)) => simple notypeclasses refine (trivial_Equivalence _) : typeclass_instances.
Global Hint Extern 2 (Transitive (λ _, atrue)) => simple notypeclasses refine (trivial_Equivalence _) : typeclass_instances.


Lemma of_course_rel_Affirmative `(R:A → SProp) : AffirmativeRelation (of_course_rel R).
Proof. now red. Qed.
Global Hint Extern 2 (AffirmativeRelation (of_course_rel _)) => simple notypeclasses refine (of_course_rel_Affirmative _) : typeclass_instances.

Lemma of_course_rel_Reflexive `(R:srelation A) `{!sReflexive R} : Reflexive (of_course_rel R).
Proof. intros x. now simpl. Qed.
Global Hint Extern 2 (Reflexive (of_course_rel _)) => simple notypeclasses refine (of_course_rel_Reflexive _) : typeclass_instances.

Lemma of_course_rel_Symmetric `(R:srelation A) `{!sSymmetric R} : Symmetric (of_course_rel R).
Proof. intros x y. apply affirmative_aimpl. exact (ssymmetry x y). Qed.
Global Hint Extern 2 (Symmetric (of_course_rel _)) => simple notypeclasses refine (of_course_rel_Symmetric _) : typeclass_instances.

Lemma of_course_rel_Transitive `(R:srelation A) `{!sTransitive R} : Transitive (of_course_rel R).
Proof. intros x y z. apply affirmative_aimpl. simpl. intros [??]. now trans y. Qed.
Global Hint Extern 2 (Transitive (of_course_rel _)) => simple notypeclasses refine (of_course_rel_Transitive _) : typeclass_instances.

Lemma of_course_rel_Equivalence `(R:srelation A) `{!sEquivalence R} : Equivalence (of_course_rel R).  Proof. now split. Qed.
Global Hint Extern 2 (Equivalence (of_course_rel _)) => simple notypeclasses refine (of_course_rel_Equivalence _) : typeclass_instances.

Definition leq_equiv A : Equivalence (@leq A) := of_course_rel_Equivalence _.
Global Hint Extern 2 (Equivalence leq) => simple notypeclasses refine (leq_equiv _) : typeclass_instances.


Lemma of_course_rel_Reflexive_back `{R:A ∗ A → Ω} `{!Reflexive R} : sReflexive R.
Proof. full_tautological. Qed.
Global Hint Extern 2 (sReflexive (λ x, apos (_ x))) => simple notypeclasses refine of_course_rel_Reflexive_back : typeclass_instances.

Lemma of_course_rel_Symmetric_back `{R:A ∗ A → Ω} `{!Symmetric R} : sSymmetric R.
Proof. intros x y ?. now apply symmetry. Qed.
Global Hint Extern 2 (sSymmetric (λ x, apos (_ x))) => simple notypeclasses refine of_course_rel_Symmetric_back : typeclass_instances.

Lemma of_course_rel_Transitive_back `{R:A ∗ A → Ω} `{!Transitive R} : sTransitive R.
Proof. intros x y z ? ?. apply (transitivity R x y z); now split. Qed.
Global Hint Extern 2 (sTransitive (λ x, apos (_ x))) => simple notypeclasses refine of_course_rel_Transitive_back : typeclass_instances.

Lemma of_course_rel_Equivalence_back `{R:A ∗ A → Ω} `{!Equivalence R} : sEquivalence R.
Proof. now split. Qed.
Global Hint Extern 2 (sEquivalence (λ x, apos (_ x))) => simple notypeclasses refine of_course_rel_Equivalence_back : typeclass_instances.


