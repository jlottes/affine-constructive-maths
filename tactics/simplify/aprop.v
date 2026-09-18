Require Import interfaces.sprop theory.set logic.aprop logic.relations.
Require Import rewrite easy tactics.misc.
Require Export simplify.base.

Lemma simplify_impl (P Q : SProp) {P' Q': SProp} : ∀ `{!SimplifiesTo P P', !SimplifiesTo Q Q'}, SimplifiesTo (P → Q) (P' → Q').
Proof. intros [E1][E2]; split; revert E1 E2; lazy; tautological. Qed.
Global Hint Extern 104 (SimplifiesTo (?P → ?Q) _) => simplify_progress constr:(simplify_impl P Q) : typeclass_instances.

Definition simplify_thm {P P':Ω} (H:P) {E:SimplifiesTo P P'} : P' := aimpl_impl_pos (sprop.andl E.(simplify _)) H.
Definition full_simplify_thm {P P':Ω} (H:P) {E:FullSimplifiesTo P P'} : P' := simplify_thm _ (E:=E).

Global Hint Extern 4 (SimplifiesTo (func_op anot_fun  ?P) ?out) => change (SimplifiesTo (anot  P) out)  : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (func_op aand_fun  ?P) ?out) => change (SimplifiesTo (aand  P) out) : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (func_op aprod_fun ?P) ?out) => change (SimplifiesTo (aprod P) out) : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (func_op aor_fun   ?P) ?out) => change (SimplifiesTo (aor   P) out) : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (func_op apar_fun  ?P) ?out) => change (SimplifiesTo (apar  P) out) : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (func_op aimpl_fun ?P) ?out) => change (SimplifiesTo (aimpl P) out) : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (func_op aiff_fun  ?P) ?out) => change (SimplifiesTo (aiff  P) out) : typeclass_instances.


Global Hint Extern 4 (SimplifiesTo (anot atrue) _) => exact (simplify_base (x:=afalse)) : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (anot afalse) _) => exact (simplify_base (x:=atrue)) : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (anot (anot ?P)) ?out) => change (SimplifiesTo P out) : typeclass_instances.

Import modality_notation.

Lemma simplify_anot_aimpl `{@SimplifiesTo Ω P P'} `{@SimplifiesTo Ω (anot Q) Qd} : SimplifiesTo (P ⊸ Q)ᗮ (P' ⊠ Qd).
Proof. split. rew (simplify P). rew <-exact:(simplify (Q ᗮ)). apply aimpl_dual. Qed.
Lemma simplify_anot_of_course `{@SimplifiesTo Ω (anot P) Pd} : SimplifiesTo (! P)ᗮ (? Pd).
Proof. split. rew <-exact:(simplify (P ᗮ)). exact of_course_dual. Qed.
Lemma simplify_anot_why_not `{@SimplifiesTo Ω (anot P) Pd} : SimplifiesTo (? P)ᗮ (! Pd).
Proof. split. rew <-exact:(simplify (P ᗮ)). exact why_not_dual. Qed.

Global Hint Extern 4 (SimplifiesTo (_ ⊸ _)ᗮ _) => notypeclasses refine simplify_anot_aimpl : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (! _)ᗮ _) => notypeclasses refine simplify_anot_of_course : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (? _)ᗮ _) => notypeclasses refine simplify_anot_why_not : typeclass_instances.

Local Ltac chain tm := match goal with |- SimplifiesTo ?x ?y => change (SimplifiesToR (x,y)); trans tm end.

Definition simplify_aimpl_true {P} := Build_SimplifiesTo _ (P ⊸ atrue) atrue tautology.
Definition simplify_false_aimpl {P} := Build_SimplifiesTo _ (afalse ⊸ P) atrue tautology.
Global Hint Extern 4 (SimplifiesTo (_ ⊸ atrue) _) => notypeclasses refine simplify_aimpl_true : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (afalse ⊸ _) _) => notypeclasses refine simplify_false_aimpl : typeclass_instances.

Lemma simplify_true_aimpl `{@SimplifiesTo Ω P P'} : SimplifiesTo (atrue ⊸ P) P'.
Proof. split. rew (simplify P). apply true_aimpl. Qed.
Global Hint Extern 4 (SimplifiesTo (atrue ⊸ _) _) => notypeclasses refine simplify_true_aimpl : typeclass_instances.

Lemma simplify_aimpl_false `{@SimplifiesTo Ω (anot P) Pd} : SimplifiesTo (P ⊸ afalse) Pd.
Proof. change (SimplifiesToR (P ⊸ 𝐅, Pd)). trans (anot P); trivial. split. apply aimpl_false. Qed.
Global Hint Extern 4 (SimplifiesTo (_ ⊸ afalse) _) => notypeclasses refine simplify_aimpl_false : typeclass_instances.

Lemma simplify_aiff_true `{@SimplifiesTo Ω P P'} : SimplifiesTo (P ⧟ atrue) P'.
Proof. split. rew (simplify P). apply aiff_true. Qed.
Global Hint Extern 4 (SimplifiesTo (_ ⧟ atrue) _) => notypeclasses refine simplify_aiff_true : typeclass_instances.

Lemma simplify_true_aiff `{@SimplifiesTo Ω P P'} : SimplifiesTo (atrue ⧟ P) P'.
Proof. split. rew (simplify P). exact tautology. Qed.
Global Hint Extern 4 (SimplifiesTo (atrue ⧟ _) _) => notypeclasses refine simplify_true_aiff : typeclass_instances.

Lemma simplify_aiff_false `{@SimplifiesTo Ω (anot P) Pd} : SimplifiesTo (P ⧟ afalse) Pd.
Proof. chain (anot P); trivial. split. exact tautology. Qed.
Global Hint Extern 4 (SimplifiesTo (_ ⧟ afalse) _) => notypeclasses refine simplify_aiff_false : typeclass_instances.

Lemma simplify_false_aiff `{@SimplifiesTo Ω (anot P) Pd} : SimplifiesTo (afalse ⧟ P) Pd.
Proof. chain (anot P); trivial. split. exact tautology. Qed.
Global Hint Extern 4 (SimplifiesTo (afalse ⧟ _) _) => notypeclasses refine simplify_false_aiff : typeclass_instances.

Definition simplify_aimpl_refl {P} := Build_SimplifiesTo _ (P ⊸ P) atrue tautology.
Definition simplify_aiff_refl {P} := Build_SimplifiesTo _ (P ⧟ P) atrue tautology.
Global Hint Extern 2 (SimplifiesTo (?P ⊸ ?P) _) => notypeclasses refine simplify_aimpl_refl : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (?P ⧟ ?P) _) => notypeclasses refine simplify_aiff_refl : typeclass_instances.


Definition simplify_aandl {P Q} := Build_SimplifiesTo _ (P ∧ Q ⊸ P) atrue tautology.
Global Hint Extern 4 (SimplifiesTo (?P ∧ _ ⊸ ?P) _) => notypeclasses refine simplify_aandl : typeclass_instances.
Definition simplify_aandr {P Q} := Build_SimplifiesTo _ (P ∧ Q ⊸ Q) atrue tautology.
Global Hint Extern 4 (SimplifiesTo (_ ∧ ?P ⊸ ?P) _) => notypeclasses refine simplify_aandr : typeclass_instances.

Lemma simplify_true_aand `{@SimplifiesTo Ω P P'} : SimplifiesTo (𝐓 ∧ P) P'.
Proof. chain P; trivial. split. apply aand_unit_l. Qed.
Global Hint Extern 4 (SimplifiesTo (𝐓 ∧ _) _) => notypeclasses refine simplify_true_aand : typeclass_instances.

Lemma simplify_aand_true `{@SimplifiesTo Ω P P'} : SimplifiesTo (P ∧ 𝐓) P'.
Proof. chain P; trivial. split. apply aand_unit_r. Qed.
Global Hint Extern 4 (SimplifiesTo (_ ∧ 𝐓) _) => notypeclasses refine simplify_aand_true : typeclass_instances.

Definition simplify_false_aand {P} := Build_SimplifiesTo _ (𝐅 ∧ P) 𝐅 (aand_false_l _).
Definition simplify_aand_false {P} := Build_SimplifiesTo _ (P ∧ 𝐅) 𝐅 (aand_false_r _).
Global Hint Extern 4 (SimplifiesTo (𝐅 ∧ _) _) => notypeclasses refine simplify_false_aand : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (_ ∧ 𝐅) _) => notypeclasses refine simplify_aand_false : typeclass_instances.

Lemma simplify_aand_idem `{@SimplifiesTo Ω P P'} : SimplifiesTo (P ∧ P) P'.
Proof. chain P; trivial. split. apply aand_idem. Qed.
Global Hint Extern 4 (SimplifiesTo (?P ∧ ?Q) _) => lazymatch P with Q => notypeclasses refine simplify_aand_idem end : typeclass_instances.


Definition simplify_aorl {P Q} := Build_SimplifiesTo _ (P ⊸ P ∨ Q) 𝐓 tautology.
Global Hint Extern 4 (SimplifiesTo (?P ⊸ ?P ∨ _) _) => notypeclasses refine simplify_aorl : typeclass_instances.
Definition simplify_aorr {P Q} := Build_SimplifiesTo _ (Q ⊸ P ∨ Q) 𝐓 tautology.
Global Hint Extern 4 (SimplifiesTo (?P ⊸ _ ∨ ?P) _) => notypeclasses refine simplify_aorr : typeclass_instances.

Lemma simplify_false_aor `{@SimplifiesTo Ω P P'} : SimplifiesTo (𝐅 ∨ P) P'.
Proof. chain P; trivial. split. apply aor_unit_l. Qed.
Global Hint Extern 4 (SimplifiesTo (𝐅 ∨ _) _) => notypeclasses refine simplify_false_aor : typeclass_instances.

Lemma simplify_aor_false `{@SimplifiesTo Ω P P'} : SimplifiesTo (P ∨ 𝐅) P'.
Proof. chain P; trivial. split. apply aor_unit_r. Qed.
Global Hint Extern 4 (SimplifiesTo (_ ∨ 𝐅) _) => notypeclasses refine simplify_aor_false : typeclass_instances.

Definition simplify_true_aor {P} := Build_SimplifiesTo _ (𝐓 ∨ P) 𝐓 (aor_true_l _).
Definition simplify_aor_true {P} := Build_SimplifiesTo _ (P ∨ 𝐓) 𝐓 (aor_true_r _).
Global Hint Extern 4 (SimplifiesTo (𝐓 ∨ _) _) => notypeclasses refine simplify_true_aor : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (_ ∨ 𝐓) _) => notypeclasses refine simplify_aor_true : typeclass_instances.

Lemma simplify_aor_idem `{@SimplifiesTo Ω P P'} : SimplifiesTo (P ∨ P) P'.
Proof. chain P; trivial. split. apply aor_idem. Qed.
Global Hint Extern 4 (SimplifiesTo (?P ∨ ?Q) _) => lazymatch P with Q => notypeclasses refine simplify_aor_idem end : typeclass_instances.


Lemma simplify_true_aprod `{@SimplifiesTo Ω P P'} : SimplifiesTo (𝐓 ⊠ P) P'.
Proof. chain P; trivial. split. apply aprod_unit_l. Qed.
Global Hint Extern 4 (SimplifiesTo (𝐓 ⊠ _) _) => notypeclasses refine simplify_true_aprod : typeclass_instances.

Lemma simplify_aprod_true `{@SimplifiesTo Ω P P'} : SimplifiesTo (P ⊠ 𝐓) P'.
Proof. chain P; trivial. split. apply aprod_unit_r. Qed.
Global Hint Extern 4 (SimplifiesTo (_ ⊠ 𝐓) _) => notypeclasses refine simplify_aprod_true : typeclass_instances.

Definition simplify_false_aprod {P} := Build_SimplifiesTo _ (𝐅 ⊠ P) 𝐅 (aprod_false_l _).
Definition simplify_aprod_false {P} := Build_SimplifiesTo _ (P ⊠ 𝐅) 𝐅 (aprod_false_r _).
Global Hint Extern 4 (SimplifiesTo (𝐅 ⊠ _) _) => notypeclasses refine simplify_false_aprod : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (_ ⊠ 𝐅) _) => notypeclasses refine simplify_aprod_false : typeclass_instances.


Lemma simplify_false_apar `{@SimplifiesTo Ω P P'} : SimplifiesTo (𝐅 ⊞ P) P'.
Proof. chain P; trivial. split. apply apar_unit_l. Qed.
Global Hint Extern 4 (SimplifiesTo (𝐅 ⊞ _) _) => notypeclasses refine simplify_false_apar : typeclass_instances.

Lemma simplify_apar_false `{@SimplifiesTo Ω P P'} : SimplifiesTo (P ⊞ 𝐅) P'.
Proof. chain P; trivial. split. apply apar_unit_r. Qed.
Global Hint Extern 4 (SimplifiesTo (_ ⊞ 𝐅) _) => notypeclasses refine simplify_apar_false : typeclass_instances.

Definition simplify_true_apar {P} : SimplifiesTo (𝐓 ⊞ P) 𝐓 := ltac:(solve_simplify (apar_true_l _)).
Definition simplify_apar_true {P} : SimplifiesTo (P ⊞ 𝐓) 𝐓 := ltac:(solve_simplify (apar_true_r _)).
Global Hint Extern 4 (SimplifiesTo (𝐓 ⊞ _) _) => notypeclasses refine simplify_true_apar : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (_ ⊞ 𝐓) _) => notypeclasses refine simplify_apar_true : typeclass_instances.

Definition simplify_of_course_true := Build_SimplifiesTo _ (of_course atrue) atrue tautology.
Definition simplify_of_course_false := Build_SimplifiesTo _ (of_course afalse) afalse tautology.
Global Hint Extern 4 (SimplifiesTo (of_course (apos atrue)) _) => notypeclasses refine simplify_of_course_true : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (of_course (apos afalse)) _) => notypeclasses refine simplify_of_course_false : typeclass_instances.

Lemma simplify_of_course_idem `{@SimplifiesTo Ω P P'} : SimplifiesTo (!(! P)) (! P').
Proof. split. rew (simplify P). apply of_course_idem. Qed.
Global Hint Extern 4 (SimplifiesTo (! (! _)) _) => notypeclasses refine simplify_of_course_idem : typeclass_instances.

Lemma simplify_why_not_idem `{@SimplifiesTo Ω P P'} : SimplifiesTo (?(? P)) (? P').
Proof. split. rew (simplify P). apply why_not_idem. Qed.
Global Hint Extern 4 (SimplifiesTo (? (? _)) _) => notypeclasses refine simplify_why_not_idem : typeclass_instances.


Definition simplify_true_prop {P:Ω} (H:P) : SimplifiesTo P atrue := ltac:(solve_simplify (aiff_is_true H)).
Global Hint Extern 8 (@SimplifiesTo AProp_set _ _) => refine (simplify_true_prop _) : typeclass_instances.


(** Quantifiers. *)
Global Hint Extern 2 (SimplifiesTo (all ?P) ?out) => 
      let t := constr:(ltac:(
        split; refine (aimpl_impl_pos (all_aiff _ _) _);
        let x := fresh "x" in intro x;
        let P := match goal with |- apos (?P ⧟ _) => P end in
        let t := constr:(simplify P) in
        refine t
      ) : SimplifiesTo (all P) _) in
      let t := lazymatch t with ?tm => tm end in
      simplify_progress t : typeclass_instances.

Global Hint Extern 2 (SimplifiesTo (aex ?P) ?out) => 
      let t := constr:(ltac:(
        split; refine (aimpl_impl_pos (aex_aiff _ _) _);
        let x := fresh "x" in intro x;
        let P := match goal with |- apos (?P ⧟ _) => P end in
        let t := constr:(simplify P) in
        refine t
      ) : SimplifiesTo (aex P) _) in
      let t := lazymatch t with ?tm => tm end in
      simplify_progress t : typeclass_instances.

Lemma simplify_all_true {X} : SimplifiesTo (∏ _ : X, atrue) atrue.
Proof. split; full_tautological. Qed.
Global Hint Extern 2 (SimplifiesTo (∏ _, atrue) _) => refine simplify_all_true : typeclass_instances.

Lemma simplify_aex_false {X} : SimplifiesTo (∐ _ : X, afalse) afalse.
Proof. split; full_tautological. Qed.
Global Hint Extern 2 (SimplifiesTo (∐ _, afalse) _) => refine simplify_aex_false : typeclass_instances.

