Require Import interfaces.notation sprop tauto easy srelations logic.aprop rewrite.

Import modality_notation.

Definition apar_LEM (P:Ω) : P ⊞ P ᗮ := tautology.
Definition apar_LEM_dual (P:Ω) `{DeMorganDual P Pd} : P ⊞ Pd := tautology.

Definition why_not_LEM (P : Ω) : ? (P ∨ P ᗮ) := tautology.
Global Hint Extern 2 (apos (why_not (aor ?P (?P)ᗮ))) => notypeclasses refine (why_not_LEM P) : typeclass_instances.
Global Hint Extern 20 (apos (why_not (aor ?P _))) => notypeclasses refine (why_not_LEM P) : typeclass_instances.

Lemma refutative_by_why_not P {H:? P} `{Refutative Q} : (P ⊸ Q) → Q.
Proof. intro. rew <-(aimpl_true_l H). now apply whynot_aimpl_refutative. Qed.

Lemma refutative_apar_aor {P Q R} `{Refutative R} : (P ⊞ Q) → (P ∨ Q ⊸ R) → R.
Proof. rew (apar_aor _ _). intro. now apply refutative_by_why_not. Qed.

Lemma refutative_apar_elim {P Q R} `{Refutative R} : (P ⊞ Q) → (P ⊸ R) → (Q ⊸ R) → R.
Proof. intros PorQ ??. apply (refutative_apar_aor PorQ). now apply aor_elim. Qed.

Lemma refutative_apar_elim_alt_l {P Q R} {HP:Refutative P} {HR:Refutative R} : (P ⊞ Q) → (P → R) → (Q → R) → R.
Proof. intros PorQ. assert (Affirmative (P ∨ Q)) by (clear R HR; tautological).
  intros a b. apply (refutative_apar_aor (PorQ)), affirmative_aimpl.
  intros [?|?]; [ apply a | apply b ]; assumption.
Qed.

Lemma refutative_apar_elim_alt_r {P Q R} {HQ:Refutative Q} {HR:Refutative R} : (P ⊞ Q) → (P → R) → (Q → R) → R.
Proof. rew (apar_com _ _); intros QorP ??. now apply (refutative_apar_elim_alt_l QorP). Qed.


Lemma refutative_by_LEM (P:Ω) `{Refutative Q} : ((P ∨ P ᗮ) ⊸ Q) → Q.
Proof refutative_apar_aor (apar_LEM P).

Lemma refutative_by_cases P `{DeMorganDual P Pd} `{Refutative Q} : ((P ∨ Pd) ⊸ Q) → Q.
Proof refutative_apar_aor (apar_LEM_dual P).

Lemma refutative_by_cases_alt P `{DeMorganDual P Pd} `{Refutative Q} : (P ⊸ Q) → (Pd ⊸ Q) → Q.
Proof refutative_apar_elim (apar_LEM_dual P).

Lemma refutative_by_contradiction P `{DeMorganDual P Pd} `{DeMorganDual Q Qd} `{Refutative Q} : (Qd → (P ∧ Pd)) → Q.
Proof. rew <-(demorgan_dual Q). rew <- exact:(demorgan_dual P). clear H H0. intro.
  apply (refutative_by_LEM P). apply by_contrapositive. apply affirmative_aimpl. tautological.
Qed.

Definition Affirmative_Decidability (P : Ω) := Affirmative (P ∨ P ᗮ).
Existing Class Affirmative_Decidability.

Lemma refutative_decidability_decidable (P : Ω) : Refutative (P ∨ P ᗮ) → P ∨ P ᗮ.
Proof. unfold Refutative. now rew ( aiff_is_true (why_not_LEM P) ), (aiff_true _). Qed.

Lemma refutative_by_aff_cases P `{Affirmative_Decidability P} `{DeMorganDual P Pd} `{Refutative Q} : ((P ∨ Pd) → Q) → Q.
Proof. intro E. apply (refutative_by_cases P). apply @affirmative_aimpl; trivial.
  now rew <-(@demorgan_dual P Pd _).
Qed.

Lemma affirmative_decidability_alt P : Affirmative_Decidability P ↔ (¬ (apos P) → ¬ (aneg P) → False).
Proof. unfold Affirmative_Decidability. rew (affirmative_alt _). tautological. Qed.

Local Ltac doit := repeat match goal with
  | H : Affirmative_Decidability ?P |- _ => revert H
  | H : Affirmative ?P |- _ => revert H
  | H : Refutative ?P |- _ => revert H
end; rew ?(affirmative_decidability_alt _); rew ?(affirmative_alt _); rew ?(refutative_alt _); tautological.

Lemma affirmative_affirmative_dec {P} : Affirmative P → Affirmative_Decidability P.  Proof. doit. Qed.
Lemma refutative_affirmative_dec {P} : Refutative P → Affirmative_Decidability P.  Proof. doit. Qed.
Coercion affirmative_affirmative_dec : Affirmative >-> Affirmative_Decidability.
Coercion refutative_affirmative_dec : Refutative >-> Affirmative_Decidability.
Global Hint Extern 20 (Affirmative_Decidability _) => apply affirmative_affirmative_dec : typeclass_instances.
Global Hint Extern 20 (Affirmative_Decidability _) => apply refutative_affirmative_dec : typeclass_instances.

Definition of_course_affirmative_dec {P} : Affirmative_Decidability (! P) := _.
Definition why_not_affirmative_dec {P} : Affirmative_Decidability (? P) := _.
Global Hint Extern 2 (Affirmative_Decidability (! _)) => eapply of_course_affirmative_dec : typeclass_instances.
Global Hint Extern 2 (Affirmative_Decidability (? _)) => eapply why_not_affirmative_dec : typeclass_instances.

Lemma anot_affirmative_dec  `{Affirmative_Decidability P} : Affirmative_Decidability P ᗮ.  Proof. doit. Qed.
Lemma aand_affirmative_dec  `{Affirmative_Decidability P} `{Affirmative_Decidability Q} : Affirmative_Decidability (P ∧ Q).  Proof. doit. Qed.
Lemma aor_affirmative_dec   `{Affirmative_Decidability P} `{Affirmative_Decidability Q} : Affirmative_Decidability (P ∨ Q).  Proof. doit. Qed.
Lemma aprod_affirmative_dec `{Affirmative_Decidability P} `{Affirmative_Decidability Q} : Affirmative_Decidability (P ⊠ Q).  Proof. doit. Qed.
Lemma apar_affirmative_dec  `{Affirmative_Decidability P} `{Affirmative_Decidability Q} : Affirmative_Decidability (P ⊞ Q).  Proof. doit. Qed.
Global Hint Extern 2 (Affirmative_Decidability (_ ᗮ))      => simple notypeclasses refine anot_affirmative_dec  : typeclass_instances.
Global Hint Extern 2 (Affirmative_Decidability (aand _ _)) => simple notypeclasses refine aand_affirmative_dec  : typeclass_instances.
Global Hint Extern 2 (Affirmative_Decidability (aor _ _))  => simple notypeclasses refine aor_affirmative_dec   : typeclass_instances.
Global Hint Extern 2 (Affirmative_Decidability (_ ⊠ _))    => simple notypeclasses refine aprod_affirmative_dec : typeclass_instances.
Global Hint Extern 2 (Affirmative_Decidability (_ ⊞ _))    => simple notypeclasses refine apar_affirmative_dec  : typeclass_instances.


