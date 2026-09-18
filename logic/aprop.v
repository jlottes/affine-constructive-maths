Require Import interfaces.notation sprop tauto easy srelations.
Require Export interfaces.aprop.
Require Import tactics.misc rewrite.proper.

Import props_notation.
Import modality_notation.

Ltac tautological_hook ::= unfold seq, Decidable, Affirmative, Refutative, DeMorganDual in *; simpl in *.

(** [atautological]: like [tautological], but first replace every maximal
    subterm that is *not* built from the affine connectives with a fresh
    opaque [_ : Ω], and clear the rest of the hypothesis context.  This stops
    [tautological]'s [simpl in *] from unfolding the atoms (and from churning
    over a large context), which is the usual cause of slowness.  It automates
    the manual [set (P := ..); ..; clearbody P ..; clear ..] idiom. *)

(** Syntactic head symbol of [t], peeling applications without any
    conversion/unfolding. *)
Ltac aprop_term_head t :=
  lazymatch t with ?g _ => aprop_term_head g | ?h => h end.

(** [A]'s outermost symbol is an affine connective.  This *must* be a syntactic
    head test, not an [lazymatch A with aprod _ => .. end]: Ltac constr patterns
    match up to conversion, and every Ω-valued atom reduces in whnf to a
    connective — a membership [x ∊ U] or equality [x = y] is refutative, so it
    unfolds to [not_of_course _].  A pattern match therefore classifies *every*
    atom as a connective, which silently makes [abstract_aprop_atoms] a no-op.
    Comparing the syntactic head against each connective constant with
    [constr_eq_nounivs] (universe-insensitive: [all]/[aex] are polymorphic)
    sidesteps conversion entirely. *)
Ltac aprop_connective_head A :=
  let h := aprop_term_head A in
  first
  [ constr_eq_nounivs h (@atrue)      | constr_eq_nounivs h (@afalse)
  | constr_eq_nounivs h (@aand)       | constr_eq_nounivs h (@aor)
  | constr_eq_nounivs h (@aprod)      | constr_eq_nounivs h (@apar)
  | constr_eq_nounivs h (@aimpl)      | constr_eq_nounivs h (@aiff)
  | constr_eq_nounivs h (@anot)
  | constr_eq_nounivs h (@of_course)  | constr_eq_nounivs h (@not_of_course)
  | constr_eq_nounivs h (@why_not) ].
  (* | constr_eq_nounivs h (@all)        | constr_eq_nounivs h (@aex) ]. *)

(** [T] is the type of an affine proposition.  By default this is just the
    bare constant [AProp]; once [theory.set] makes [Ω] into a set, equality and
    membership atoms are typed through the set's carrier [set_T AProp_set]
    instead, so [theory.set] extends this recognizer (via [::=]) to accept that
    form too.  Kept to [constr_eq] alternatives — a general [unify] convertibility
    test would be far more expensive across the many subterms scanned. *)
Ltac is_aprop_type T := constr_eq T AProp.

(** [A] is an atom worth abstracting: it has type [Ω], its head is not a
    connective, and it is not already an opaque variable. *)
Ltac is_aprop_atom A :=
  let T := type of A in is_aprop_type T;
  assert_fails (is_var A);
  assert_fails (aprop_connective_head A).

(** Before sealing an atom [A] under a fresh opaque [P], fold every occurrence
    that is *convertible* to [A] onto [A] itself, so they all abstract to the
    same [P].  This matters for universe-variant copies of one atom: the goal
    routinely contains several copies of, say, [w ⪽ W] at distinct (fresh,
    not-yet-collapsed) universe levels.  [set] only seals syntactically identical
    occurrences, so without this they would become *different* opaque atoms and a
    real tautology would no longer look like one.  [constr_eq_nounivs] is too
    weak here (the copies can differ in more than a head universe instance);
    [change B with A] is the honest test — it succeeds exactly when [B ≡ A],
    emitting the universe constraints that collapse the copies.  A same-head
    [constr_eq_nounivs] pre-filter keeps us from attempting [change] against every
    subterm. *)
Ltac abstract_aprop_atoms :=
  repeat match goal with
  | |- context [ ?A ] =>
      is_aprop_atom A;
      repeat (match goal with |- context [ ?B ] =>
        assert_fails (constr_eq A B);
        let hA := aprop_term_head A in let hB := aprop_term_head B in
        constr_eq_nounivs hA hB;
        change B with A end);
      let P := fresh "P" in set (P := A); clearbody P
  end.

Ltac clear_aprop_context :=
  repeat match goal with H : _ |- _ => clear H end.

Ltac tautological := abstract_aprop_atoms; clear_aprop_context; full_tautological.
Abbreviation tautology := ltac:(normalize_proof full_tautological) (only parsing).

(** Extensible typeclass mechanism for inferring the DeMorgan dual of a proposition P. *)
Definition demorgan_dual_base {P} : DeMorganDual P (P ᗮ) := tautology.
Global Hint Extern 100 (DeMorganDual _ _) => simple notypeclasses refine demorgan_dual_base : typeclass_instances.

Notation "'dual:(' P )" :=  ltac:( let t := constr:( _ : DeMorganDual P _ ) in
    lazymatch type of t with DeMorganDual _ ?Q => exact Q end) (only parsing).

Definition atrue_dual : DeMorganDual 𝐓 𝐅 := tautology.
Definition afalse_dual : DeMorganDual 𝐅 𝐓 := tautology.
Definition anot_dual {P} : DeMorganDual (P ᗮ) P := tautology.
Definition aand_dual  `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : DeMorganDual (P ∧ Q) (Pd ∨ Qd) := tautology.
Definition aor_dual   `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : DeMorganDual (P ∨ Q) (Pd ∧ Qd) := tautology.
Definition aprod_dual `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : DeMorganDual (P ⊠ Q) (Pd ⊞ Qd) := tautology.
Definition apar_dual  `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : DeMorganDual (P ⊞ Q) (Pd ⊠ Qd) := tautology.
Definition aimpl_dual  {P} `{DeMorganDual Q Qd} : DeMorganDual (P ⊸ Q) (P ⊠ Qd) := tautology.
Definition aiff_dual `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : DeMorganDual (P ⧟ Q) ((P ⊠ Qd) ∨ (Pd ⊠ Q)) := tautology.
Definition aimpl_dual_back1 {P Q} : DeMorganDual (P ᗮ ⊠ Q) (Q ⊸ P) := tautology.
Definition aimpl_dual_back2 {P Q} : DeMorganDual (P ⊠ Q ᗮ) (P ⊸ Q) := tautology.
Definition of_course_dual `{DeMorganDual P Pd} : DeMorganDual (!P) (? Pd) := tautology.
Definition why_not_dual `{DeMorganDual P Pd} : DeMorganDual (? P) (!Pd) := tautology.

Global Hint Extern 2 (DeMorganDual atrue _) => notypeclasses refine atrue_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual afalse _) => notypeclasses refine afalse_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ ᗮ) _) => notypeclasses refine anot_dual : typeclass_instances.
Global Hint Extern 10 (DeMorganDual (aand _) _) => notypeclasses refine aand_dual : typeclass_instances.
Global Hint Extern 10 (DeMorganDual (aor _) _) => notypeclasses refine aor_dual : typeclass_instances.
Global Hint Extern 10 (DeMorganDual (_ ⊠ _) _) => notypeclasses refine aprod_dual : typeclass_instances.
Global Hint Extern 10 (DeMorganDual (_ ⊞ _) _) => notypeclasses refine apar_dual : typeclass_instances.
Global Hint Extern 10 (DeMorganDual (_ ⊸ _) _) => notypeclasses refine aimpl_dual : typeclass_instances.
Global Hint Extern 10 (DeMorganDual (_ ⧟ _) _) => notypeclasses refine aiff_dual : typeclass_instances.
Global Hint Extern 5 (DeMorganDual (! _) _) => notypeclasses refine of_course_dual : typeclass_instances.
Global Hint Extern 5 (DeMorganDual (? _) _) => notypeclasses refine why_not_dual : typeclass_instances.


Definition contradiction {P:Ω} : P → P ᗮ → False := tautology.
Definition aimpl_by_contradiction `{DeMorganDual P Pd} {Q} : Pd → (P ⊸ Q) := tautology.
Definition by_contradiction `{DeMorganDual P Pd} {Q:Ω} : P → Pd → Q := tautology.

Definition acontra_eq (P Q : Ω) : (P ⊸ Q) ⧟ (Q ᗮ ⊸ P ᗮ) := tautology.
Definition acontra_iff_eq (P Q : Ω) : (P ⧟ Q) ⧟ (P ᗮ ⧟ Q ᗮ) := tautology.

Definition acontra : ∀ {P Q : Ω}, (P ⊸ Q) → (Q ᗮ ⊸ P ᗮ) := tautology.
Definition acontra_iff : ∀ {P Q : Ω}, (P ⧟ Q) → (P ᗮ ⧟ Q ᗮ) := tautology.

Definition contrapositive_eq     `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (P ⊸ Q) ⧟ (Qd ⊸ Pd) := tautology.
Definition contrapositive_iff_eq `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (P ⧟ Q) ⧟ (Pd ⧟ Qd) := tautology.
Definition contrapositive        `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (Q ⊸ P) → (Pd ⊸ Qd) := tautology.
Definition contrapositive_iff    `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (P ⧟ Q) → (Pd ⧟ Qd) := tautology.
Definition by_contrapositive     `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (Qd ⊸ Pd) → (P ⊸ Q) := tautology.
Definition by_contrapositive_iff `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (Pd ⧟ Qd) → (P ⧟ Q) := tautology.

Definition aimpl_split_dual `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (P → Q) → (Qd → Pd) → (P ⊸ Q) := tautology.
Definition apar_split_dual `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (Pd → Q) → (Qd → P) → (P ⊞ Q) := tautology.

Definition why_not_by_dual `{DeMorganDual P Pd} : (¬Pd) → ? P := tautology.

Definition decidable_dual P `{DeMorganDual P Pd} `{Decidable P} : P ∨ Pd := tautology.
Definition decidable_by_dual `{DeMorganDual P Pd} : P ∨ Pd → Decidable P := tautology.

Section tautologies.
  Context (P Q R S : Ω).

  Definition aimpl_true : P ⊸ 𝐓 := tautology.
  Definition false_aimpl: 𝐅 ⊸ P := tautology.
  Definition true_aimpl : (𝐓 ⊸ P) ⧟ P := tautology.
  Definition aimpl_false: (P ⊸ 𝐅) ⧟ P ᗮ := tautology.
  Definition aiff_true  : (P ⧟ 𝐓) ⧟ P := tautology.
  Definition aiff_false : (P ⧟ 𝐅) ⧟ P ᗮ := tautology.

  Definition aandl : P ∧ Q ⊸ P := tautology.
  Definition aandr : P ∧ Q ⊸ Q := tautology.
  Definition aand_lub : (R ⊸ P) ∧ (R ⊸ Q) ⊸ (R ⊸ P ∧ Q) := tautology.
  Definition aand_intro : (R ⊸ P) → (R ⊸ Q) → (R ⊸ P ∧ Q) := tautology.
  Definition aand_assoc : (P ∧ Q) ∧ R ⧟ P ∧ (Q ∧ R) := tautology.
  Definition aand_com : P ∧ Q ⧟ Q ∧ P := tautology.
  Definition aand_unit_l : 𝐓 ∧ P ⧟ P := tautology.
  Definition aand_unit_r : P ∧ 𝐓 ⧟ P := tautology.
  Definition aand_false_l : 𝐅 ∧ P ⧟ 𝐅 := tautology.
  Definition aand_false_r : P ∧ 𝐅 ⧟ 𝐅 := tautology.
  Definition aand_idem : P ∧ P ⧟ P := tautology.

  Definition aorl : P ⊸ P ∨ Q := tautology.
  Definition aorr : Q ⊸ P ∨ Q := tautology.
  Definition aor_glb : (P ⊸ R) ∧ (Q ⊸ R) ⊸ (P ∨ Q ⊸ R) := tautology.
  Definition aor_elim : (P ⊸ R) → (Q ⊸ R) → (P ∨ Q ⊸ R) := tautology.
  Definition aor_assoc : (P ∨ Q) ∨ R ⧟ P ∨ (Q ∨ R) := tautology.
  Definition aor_com : P ∨ Q ⧟ Q ∨ P := tautology.
  Definition aor_unit_l : 𝐅 ∨ P ⧟ P := tautology.
  Definition aor_unit_r : P ∨ 𝐅 ⧟ P := tautology.
  Definition aor_true_l : 𝐓 ∨ P ⧟ 𝐓 := tautology.
  Definition aor_true_r : P ∨ 𝐓 ⧟ 𝐓 := tautology.
  Definition aor_idem : P ∨ P ⧟ P := tautology.

  Definition aand_aor_distr : P ∨ (Q ∧ R) ⧟ (P ∨ Q) ∧ (P ∨ R) := tautology.
  Definition aor_aand_distr : P ∧ (Q ∨ R) ⧟ (P ∧ Q) ∨ (P ∧ R) := tautology.

  Definition aprod_adj : (P ⊠ Q ⊸ R) ⧟ (P ⊸ Q ⊸ R) := tautology.
  Definition apar_adj : (R ⊸ P ⊞ Q) ⧟ (R ⊠ P ᗮ ⊸ Q) := tautology.
  Definition apar_adj_dual `{DeMorganDual P Pd} : (R ⊸ P ⊞ Q) ⧟ (R ⊠ Pd ⊸ Q) := tautology.

  Definition aprod_assoc : (P ⊠ Q) ⊠ R ⧟ P ⊠ (Q ⊠ R) := tautology.
  Definition aprod_com : P ⊠ Q ⧟ Q ⊠ P := tautology.
  Definition aprod_medial : (P ⊠ Q) ⊠ (R ⊠ S) ⧟ (P ⊠ R) ⊠ (Q ⊠ S) := tautology.
  Definition aprod_unit_l : 𝐓 ⊠ P ⧟ P := tautology.
  Definition aprod_unit_r : P ⊠ 𝐓 ⧟ P := tautology.
  Definition aprod_false_l : 𝐅 ⊠ P ⧟ 𝐅 := tautology.
  Definition aprod_false_r : P ⊠ 𝐅 ⧟ 𝐅 := tautology.
  Definition aprod_mp_l : (P ⊸ Q) ⊠ P ⊸ Q := tautology.
  Definition aprod_mp_r : P ⊠ (P ⊸ Q) ⊸ Q := tautology.
  Definition aprod_of_course : P ⊠ P ⧟ !P := tautology.
  Definition of_course_aprod : !(P ⊠ Q) ⧟ !P ⊠ !Q := tautology.
  Definition why_not_aprod_aimpl : ? (P ⊠ Q) ⊸ (? P ⊠ ? Q) := tautology.

  Definition apar_assoc : (P ⊞ Q) ⊞ R ⧟ P ⊞ (Q ⊞ R) := tautology.
  Definition apar_com : P ⊞ Q ⧟ Q ⊞ P := tautology.
  Definition apar_unit_l : 𝐅 ⊞ P ⧟ P := tautology.
  Definition apar_unit_r : P ⊞ 𝐅 ⧟ P := tautology.
  Definition apar_true_l : 𝐓 ⊞ P ⧟ 𝐓 := tautology.
  Definition apar_true_r : P ⊞ 𝐓 ⧟ 𝐓 := tautology.
  Definition apar_why_not : P ⊞ P ⧟ ? P := tautology.
  Definition why_not_apar : ? (P ⊞ Q) ⧟ ? P ⊞ ? Q := tautology.
  Definition apar_of_course_aimpl : ! P ⊞ ! Q ⊸ ! (P ⊞ Q) := tautology.

  Definition aprodl : P ⊠ Q ⊸ P := tautology.
  Definition aprodr : P ⊠ Q ⊸ Q := tautology.
  Definition aprod_aand : P ⊠ Q ⊸ P ∧ Q := tautology.
  Definition aand_aprod : !(P ∧ Q) ⊸ P ⊠ Q := tautology.
  Definition aand_aprod_swap : (P ∧ Q) ⊠ (R ∧ S) ⊸ (P ⊠ R) ∧ (Q ⊠ S) := tautology.
  Definition aand_aprod_distr : (P ∧ Q) ⊠ R ⊸ (P ⊠ R) ∧ (Q ⊠ R) := tautology.

  Definition aparl : P ⊸ P ⊞ Q := tautology.
  Definition aparr : Q ⊸ P ⊞ Q := tautology.
  Definition aor_apar : P ∨ Q ⊸ P ⊞ Q := tautology.
  Definition apar_aor : P ⊞ Q ⊸ ?(P ∨ Q) := tautology.
  Definition aor_apar_swap : (P ⊞ Q) ∨ (R ⊞ S) ⊸ (P ∨ R) ⊞ (Q ∨ S) := tautology.
  Definition aor_apar_distr : (P ⊞ R) ∨ (Q ⊞ R) ⊸ (P ∨ Q) ⊞ R := tautology.
  Definition aimpl_aor_l : (P ⊸ Q ⊞ R) ⧟ ((P ⊸ Q) ⊞ R) := tautology.
  Definition aimpl_aor_r : (P ⊸ Q ⊞ R) ⧟ (Q ⊞ (P ⊸ R)) := tautology.

  Definition apar_aprod_distr_l : (P ⊠ Q) ⊠ (R ⊞ S) ⊸ (P ⊠ R) ⊞ (Q ⊠ S) := tautology.
  Definition apar_aprod_distr_r : (P ⊞ Q) ⊠ (R ⊠ S) ⊸ (P ⊠ R) ⊞ (Q ⊠ S) := tautology.

  Definition aprod_aimpl_apar : (P ⊸ R) ⊠ (Q ⊸ S) ⊸ (P ⊞ Q ⊸ R ⊞ S) := tautology.

  Definition of_course_aimpl : !P ⊸ P := tautology.
  Definition aimpl_why_not : P ⊸ ? P := tautology.

  Definition of_course_idem P : !(!P) ⧟ !P := tautology.
  Definition why_not_idem P : ? (? P) ⧟ ? P := tautology.
End tautologies.
Arguments aand_intro {P Q R} _ _.
Arguments aor_elim {P Q R} _ _.

Global Hint Extern 20 (apos (aand _)) => split : typeclass_instances.
Global Hint Extern 20 (apos (aprod _)) => split : typeclass_instances.

Global Hint Extern 2 (apos atrue) => refine sprop.I : typeclass_instances.

Global Hint Extern 2 (apos (_ ⊸ atrue)) => refine (aimpl_true _) : typeclass_instances.
Global Hint Extern 2 (apos (afalse ⊸ _)) => refine (false_aimpl _) : typeclass_instances.
Global Hint Extern 2 (apos (aand (?P, _) ⊸ ?Q)) => match P with Q => refine (aandl _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (aand (_, ?P) ⊸ ?Q)) => match P with Q => refine (aandr _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (?P ⊸ aor (?Q, _))) => match P with Q => refine (aorl _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (?P ⊸ aor (_, ?Q))) => match P with Q => refine (aorr _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (?P ⊠ _ ⊸ ?Q)) => match P with Q => refine (aprodl _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (_ ⊠ ?P ⊸ ?Q)) => match P with Q => refine (aprodr _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (?P ⊠ ?Q ⊸ aand (?P2, ?Q2))) => match P with P2 => match Q with Q2 => refine (aprod_aand _ _) end end : typeclass_instances.
Global Hint Extern 2 (apos (?P ⊸ ?Q ⊞ _)) => match P with Q => refine (aparl _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (?P ⊸ _ ⊞ ?Q)) => match P with Q => refine (aparr _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (aor (?P, ?Q) ⊸ ?P2 ⊞ ?Q2)) => match P with P2 => match Q with Q2 => refine (aor_apar _ _) end end : typeclass_instances.

Global Hint Extern 2 (apos (! apos ?P ⊸ ?Q)) => match P with Q => refine (of_course_aimpl _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (?P ⊸ ? ?Q)) => match P with Q => refine (aimpl_why_not _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (!apos (! ?P) ⧟ ! ?Q)) => match P with Q => refine (of_course_idem _ _) end : typeclass_instances.
Global Hint Extern 2 (apos (? (? ?P) ⧟ ? ?Q)) => match P with Q => refine (why_not_idem _ _) end : typeclass_instances.

Section tautologies.
  Context {P Q : Ω}.

  Definition aiff_is_true : P → (P ⧟ 𝐓) := tautology.
  Definition aiff_is_false  : P ᗮ → (P ⧟ 𝐅) := tautology.

  Definition aand_true_l   : P → (P ∧ Q ⧟ Q) := tautology.
  Definition aand_true_r   : Q → (P ∧ Q ⧟ P) := tautology.
  Definition aprod_true_l  : P → (P ⊠ Q ⧟ Q) := tautology.
  Definition aprod_true_r  : Q → (P ⊠ Q ⧟ P) := tautology.
  Definition aor_is_true_l : P → (P ∨ Q ⧟ 𝐓) := tautology.
  Definition aor_is_true_r : Q → (P ∨ Q ⧟ 𝐓) := tautology.
  Definition apar_is_true_l: P → (P ⊞ Q ⧟ 𝐓) := tautology.
  Definition apar_is_true_r: Q → (P ⊞ Q ⧟ 𝐓) := tautology.
  Definition apar_is_false_l : P → (P ᗮ ⊞ Q ⧟ Q) := tautology.
  Definition apar_is_false_r : Q → (P ⊞ Q ᗮ ⧟ P) := tautology.
  Definition aimpl_true_l  : P → ((P ⊸ Q) ⧟ Q) := tautology.
  Definition aimpl_true_r  : Q → (P ⊸ Q) := tautology.
  Definition aimpl_is_true_r  : Q → ((P ⊸ Q) ⧟ 𝐓) := tautology.
  Definition aiff_true_l   : P → ((P ⧟ Q) ⧟ Q) := tautology.
  Definition aiff_true_r   : Q → ((P ⧟ Q) ⧟ P) := tautology.

  Definition apar_is_false_l_dual `{DeMorganDual P Pd} : P → (Pd ⊞ Q ⧟ Q) := tautology.
  Definition apar_is_false_r_dual `{DeMorganDual Q Qd} : Q → (P ⊞ Qd ⧟ P) := tautology.
End tautologies.

Definition aimpl_refl  : Reflexive  aimpl := tautology.
Definition aimpl_trans : Transitive aimpl := tautology.
Global Hint Extern 0 (Reflexive aimpl) => exact aimpl_refl : typeclass_instances.
Global Hint Extern 0 (Transitive aimpl) => exact aimpl_trans : typeclass_instances.

Definition aiff_equiv : Equivalence aiff := tautology.
Global Hint Extern 0 (Equivalence aiff) => exact aiff_equiv : typeclass_instances.
Global Hint Extern 0 (Reflexive   aiff) => exact aiff_equiv : typeclass_instances.
Global Hint Extern 0 (Symmetric   aiff) => exact aiff_equiv : typeclass_instances.
Global Hint Extern 0 (Transitive  aiff) => exact aiff_equiv : typeclass_instances.

Definition aimpl_subrel_aiff : Subrelation aiff aimpl := tautology.
Global Hint Extern 0 (Subrelation aiff aimpl) => exact aimpl_subrel_aiff : typeclass_instances.

Lemma antisym_aimpl_aiff : Antisymmetric aimpl aiff.  Proof. easy. Qed.
Global Hint Extern 0 (Antisymmetric aimpl aiff) => exact antisym_aimpl_aiff : typeclass_instances.


Definition aex_adj `{P:A → Ω} {Q} : (∀ x, P x ⊸ Q) ↔ (aex P ⊸ Q) := tautology.
Definition all_adj `{P:A → Ω} {Q} : (∀ x, Q ⊸ P x) ↔ (Q ⊸ all P) := tautology.

Definition aex_ub `(P:A → Ω) x : P x ⊸ aex P := tautology.
Definition all_lb `(P:A → Ω) x : all P ⊸ P x := tautology.

Definition all_dual `{P:A → Ω} `{Pd:A → Ω} {H:∀ x, DeMorganDual (P x) (Pd x)} : DeMorganDual (all P) (aex Pd) := tautology.
Definition aex_dual `{P:A → Ω} `{Pd:A → Ω} {H:∀ x, DeMorganDual (P x) (Pd x)} : DeMorganDual (aex P) (all Pd) := tautology.

Global Hint Extern 10 (DeMorganDual (all _) _) => notypeclasses refine all_dual : typeclass_instances.
Global Hint Extern 10 (DeMorganDual (aex _) _) => notypeclasses refine aex_dual : typeclass_instances.

Definition all_aimpl {A} (P Q:A → Ω) : (∏ x, P x ⊸ Q x) ⊸ all P ⊸ all Q := tautology.
Definition all_aiff {A} (P Q:A → Ω) : (∏ x, P x ⧟ Q x) ⊸ all P ⧟ all Q := tautology.
Definition aex_aimpl {A} (P Q:A → Ω) : (∏ x, P x ⊸ Q x) ⊸ aex P ⊸ aex Q := tautology.
Definition aex_aiff {A} (P Q:A → Ω) : (∏ x, P x ⧟ Q x) ⊸ aex P ⧟ aex Q := tautology.

Definition aex_frob_l {P} `{Q:A → Ω} : P ⊠ aex Q ⧟ ∐ x, P ⊠ Q x := tautology.
Definition aex_frob_r `{P:A → Ω} {Q} : aex P ⊠ Q ⧟ ∐ x, P x ⊠ Q := tautology.
Definition all_frob_l {P} `{Q:A → Ω} : P ⊞ all Q ⧟ ∏ x, P ⊞ Q x := tautology.
Definition all_frob_r `{P:A → Ω} {Q} : all P ⊞ Q ⧟ ∏ x, P x ⊞ Q := tautology.

Definition of_course_aex `{P:A → Ω} : ! (aex P) ⧟ ∐ x, !(P x) := tautology.
Definition why_not_all `{P:A → Ω} : ? (all P) ⧟ ∏ x, ?(P x) := tautology.
Definition of_course_all_aimpl `{P:A → Ω} : ! (all P) ⊸ ∏ x, !(P x) := tautology.
Definition aex_why_not_aimpl `{P:A → Ω} : (∐ x, ?(P x)) ⊸ ? (aex P) := tautology.



Definition Affirmative_of_course P : Affirmative (!P) := tautology.
Definition Refutative_why_not P : Refutative (? P) := tautology.
Global Hint Extern 2 (Affirmative (!_)) => eapply Affirmative_of_course : typeclass_instances.
Global Hint Extern 2 (Refutative (? _)) => eapply Refutative_why_not : typeclass_instances.

Definition aimpl_impl_pos {P Q} : (P ⊸ Q) → (P → Q) := andl.
Definition aiff_iff_pos {P Q} : (P ⧟ Q) → (P ↔ Q) := tautology.
Global Hint Extern 1 (impl (apos _, apos _)) => sapply_1 aimpl_impl_pos : proper.
Global Hint Extern 1 (iff  (apos _, apos _)) => sapply_1 aiff_iff_pos   : proper.

Definition aimpl_impl_neg {P Q} : (P ⊸ Q) → (aneg Q → aneg P) := andr.
Definition aiff_iff_neg {P Q} : (P ⧟ Q) → (aneg P ↔ aneg Q) := tautology.
Global Hint Extern 1 (impl (aneg _, aneg _)) => sapply_1 aimpl_impl_neg : proper.
Global Hint Extern 1 (iff  (aneg _, aneg _)) => sapply_1 aiff_iff_neg   : proper.

Section propers.
  Context {P₁ P₂ Q₁ Q₂ : Ω}.
  Definition aimpl_proper_aimpl : (P₂ ⊸ P₁) → (Q₁ ⊸ Q₂) → (P₁ ⊸ Q₁) ⊸ (P₂ ⊸ Q₂) := tautology.
  Definition aimpl_proper_aiff  : (P₁ ⧟ P₂) → (Q₁ ⧟ Q₂) → (P₁ ⊸ Q₁) ⧟ (P₂ ⊸ Q₂) := tautology.
  Definition aiff_proper_aimpl  : (P₁ ⧟ P₂) → (Q₁ ⧟ Q₂) → (P₁ ⧟ Q₁) ⊸ (P₂ ⧟ Q₂) := tautology.
  Definition aiff_proper_aiff   : (P₁ ⧟ P₂) → (Q₁ ⧟ Q₂) → (P₁ ⧟ Q₁) ⧟ (P₂ ⧟ Q₂) := tautology.
  Definition anot_proper_aimpl  : (P₂ ⊸ P₁) → P₁ ᗮ ⊸ P₂ ᗮ := tautology.
  Definition anot_proper_aiff   : (P₁ ⧟ P₂) → P₁ ᗮ ⧟ P₂ ᗮ := tautology.
  Definition aand_proper_aimpl  : (P₁ ⊸ P₂) → (Q₁ ⊸ Q₂) → (P₁ ∧ Q₁) ⊸ (P₂ ∧ Q₂) := tautology.
  Definition aand_proper_aiff   : (P₁ ⧟ P₂) → (Q₁ ⧟ Q₂) → (P₁ ∧ Q₁) ⧟ (P₂ ∧ Q₂) := tautology.
  Definition aor_proper_aimpl   : (P₁ ⊸ P₂) → (Q₁ ⊸ Q₂) → (P₁ ∨ Q₁) ⊸ (P₂ ∨ Q₂) := tautology.
  Definition aor_proper_aiff    : (P₁ ⧟ P₂) → (Q₁ ⧟ Q₂) → (P₁ ∨ Q₁) ⧟ (P₂ ∨ Q₂) := tautology.
  Definition aprod_proper_aimpl : (P₁ ⊸ P₂) → (Q₁ ⊸ Q₂) → (P₁ ⊠ Q₁) ⊸ (P₂ ⊠ Q₂) := tautology.
  Definition aprod_proper_aiff  : (P₁ ⧟ P₂) → (Q₁ ⧟ Q₂) → (P₁ ⊠ Q₁) ⧟ (P₂ ⊠ Q₂) := tautology.
  Definition apar_proper_aimpl  : (P₁ ⊸ P₂) → (Q₁ ⊸ Q₂) → (P₁ ⊞ Q₁) ⊸ (P₂ ⊞ Q₂) := tautology.
  Definition apar_proper_aiff   : (P₁ ⧟ P₂) → (Q₁ ⧟ Q₂) → (P₁ ⊞ Q₁) ⧟ (P₂ ⊞ Q₂) := tautology.
End propers.

Global Hint Extern 2 (apos (aimpl (aimpl _, _))) => sapply_2 aimpl_proper_aimpl : proper.
Global Hint Extern 2 (apos (aiff  (aimpl _, _))) => sapply_2 aimpl_proper_aiff  : proper.
Global Hint Extern 2 (apos (aimpl (aiff  _, _))) => sapply_2 aiff_proper_aimpl  : proper.
Global Hint Extern 2 (apos (aiff  (aiff  _, _))) => sapply_2 aiff_proper_aiff   : proper.
Global Hint Extern 2 (apos (aimpl (anot  _, _))) => sapply_1 anot_proper_aimpl  : proper.
Global Hint Extern 2 (apos (aiff  (anot  _, _))) => sapply_1 anot_proper_aiff   : proper.
Global Hint Extern 2 (apos (aimpl (aand  _, _))) => sapply_2 aand_proper_aimpl  : proper.
Global Hint Extern 2 (apos (aiff  (aand  _, _))) => sapply_2 aand_proper_aiff   : proper.
Global Hint Extern 2 (apos (aimpl (aor   _, _))) => sapply_2 aor_proper_aimpl   : proper.
Global Hint Extern 2 (apos (aiff  (aor   _, _))) => sapply_2 aor_proper_aiff    : proper.
Global Hint Extern 2 (apos (aimpl (aprod _, _))) => sapply_2 aprod_proper_aimpl : proper.
Global Hint Extern 2 (apos (aiff  (aprod _, _))) => sapply_2 aprod_proper_aiff  : proper.
Global Hint Extern 2 (apos (aimpl (apar  _, _))) => sapply_2 apar_proper_aimpl  : proper.
Global Hint Extern 2 (apos (aiff  (apar  _, _))) => sapply_2 apar_proper_aiff   : proper.

Definition of_course_proper_aimpl {P Q} : (P ⊸ Q) → !P ⊸ !Q := tautology.
Definition of_course_proper_aiff {P Q} : (P ⧟ Q) → !P ⧟ !Q := tautology.
Definition why_not_proper_aimpl {P Q} : (P ⊸ Q) → ? P ⊸ ? Q := tautology.
Definition why_not_proper_aiff {P Q} : (P ⧟ Q) → ? P ⧟ ? Q := tautology.
Global Hint Extern 2 (apos (aimpl (of_course _, _))) => sapply_1 of_course_proper_aimpl : proper.
Global Hint Extern 2 (apos (aiff  (of_course _, _))) => sapply_1 of_course_proper_aiff : proper.
Global Hint Extern 2 (apos (aimpl (why_not _,   _))) => sapply_1 why_not_proper_aimpl : proper.
Global Hint Extern 2 (apos (aiff  (why_not _,   _))) => sapply_1 why_not_proper_aiff : proper.

Definition Decidable_proper_impl : ∀ `(P ⧟ Q), impl (Decidable P, Decidable Q) := tautology.
Definition Decidable_proper_iff : ∀ `(P ⧟ Q), iff (Decidable P, Decidable Q) := tautology.
Definition Affirmative_proper_impl : ∀ `(P ⧟ Q), impl (Affirmative P, Affirmative Q) := tautology.
Definition Affirmative_proper_iff : ∀ `(P ⧟ Q), iff (Affirmative P, Affirmative Q) := tautology.
Definition Refutative_proper_impl : ∀ `(P ⧟ Q), impl (Refutative P, Refutative Q) := tautology.
Definition Refutative_proper_iff : ∀ `(P ⧟ Q), iff (Refutative P, Refutative Q) := tautology.
Global Hint Extern 2 (impl (Decidable   _, _)) => sapply_1 Decidable_proper_impl   : proper.
Global Hint Extern 2 (iff  (Decidable   _, _)) => sapply_1 Decidable_proper_iff    : proper.
Global Hint Extern 2 (impl (Affirmative _, _)) => sapply_1 Affirmative_proper_impl : proper.
Global Hint Extern 2 (iff  (Affirmative _, _)) => sapply_1 Affirmative_proper_iff  : proper.
Global Hint Extern 2 (impl (Refutative  _, _)) => sapply_1 Refutative_proper_impl  : proper.
Global Hint Extern 2 (iff  (Refutative  _, _)) => sapply_1 Refutative_proper_iff   : proper.

Lemma all_proper_aimpl `{P:A → Ω} {Q:A → Ω} : (∀ x, P x ⊸ Q x) → all P ⊸ all Q.  Proof. apply all_aimpl. Qed.
Lemma all_proper_aiff  `{P:A → Ω} {Q:A → Ω} : (∀ x, P x ⧟ Q x) → all P ⧟ all Q.  Proof. apply all_aiff. Qed.
Lemma aex_proper_aimpl `{P:A → Ω} {Q:A → Ω} : (∀ x, P x ⊸ Q x) → aex P ⊸ aex Q.  Proof. apply aex_aimpl. Qed.
Lemma aex_proper_aiff  `{P:A → Ω} {Q:A → Ω} : (∀ x, P x ⧟ Q x) → aex P ⧟ aex Q.  Proof. apply aex_aiff. Qed.

Ltac proper_beta_reduce :=
  try match goal with |- apos(?R ((λ y, ?P) ?x, ?Q)) =>
    let t := constr:(match x with y => P end) in change (apos (R (t, Q)))
  end;
  try match goal with |- apos(?R (?P, (λ y, ?Q) ?x)) =>
    let t := constr:(match x with y => Q end) in change (apos (R (P, t)))
  end.

Global Hint Extern 2 (apos (all _ ⊸ _)) => sapply_1 all_proper_aimpl; intro; proper_beta_reduce : proper.
Global Hint Extern 2 (apos (all _ ⧟ _)) => sapply_1 all_proper_aiff; intro; proper_beta_reduce : proper.
Global Hint Extern 2 (apos (aex _ ⊸ _)) => sapply_1 aex_proper_aimpl; intro; proper_beta_reduce : proper.
Global Hint Extern 2 (apos (aex _ ⧟ _)) => sapply_1 aex_proper_aiff; intro; proper_beta_reduce : proper.

Definition aex_adj2 `{P₁:A → Ω} `{P₂:B → Ω} {Q} : (∀ x₁ x₂, P₁ x₁ ⊠ P₂ x₂ ⊸ Q) ↔ (aex P₁ ⊠ aex P₂ ⊸ Q).
Proof.
  sym. trans (apos ((∐ x₁, P₁ x₁ ⊠ aex P₂) ⊸ Q)). {
    refine (aiff_iff_pos _). refine (aimpl_proper_aiff _ _); [| easy ]. exact aex_frob_r.
  }
  trans (∀ x₁ : A, P₁ x₁ ⊠ (∐ y, P₂ y) ⊸ Q). sym; exact aex_adj.
  forall_proper_iff_tac.
  trans (apos ((∐ x₂, P₁ y ⊠ P₂ x₂) ⊸ Q)). {
    refine (aiff_iff_pos _). refine (aimpl_proper_aiff _ _); [| easy ]. exact aex_frob_l.
  }
  sym; exact aex_adj.
Qed.

Lemma all_adj2 `{P₁:A → Ω} `{P₂:B → Ω} {Q} : (∀ x₁ x₂, Q ⊸ P₁ x₁ ⊞ P₂ x₂) ↔ (Q ⊸ all P₁ ⊞ all P₂).
Proof. sym. trans (apos ( (∐ x₁, (P₁ x₁)ᗮ) ⊠ (∐ x₂, (P₂ x₂)ᗮ) ⊸ Q ᗮ)). {
    refine (aiff_iff_pos (acontra_eq _ _)).
  }
  trans (∀ x₁ x₂, (P₁ x₁)ᗮ ⊠ (P₂ x₂)ᗮ ⊸ Q ᗮ). sym; exact aex_adj2.
  do 2 forall_proper_iff_tac.
  refine (aiff_iff_pos (acontra_eq _ _)).
Qed.

Definition affirmative_alt P : Affirmative P ↔ (aneg P ↔ ¬ apos P) := tautology.
Definition refutative_alt P : Refutative P ↔ (apos P ↔ ¬ aneg P) := tautology.

Coercion decidable_affirmative P : Decidable P → Affirmative P := tautology.
Coercion decidable_refutative  P : Decidable P → Refutative  P := tautology.

Definition not_of_course_refutative P : Refutative (not_of_course P) := tautology.
Global Hint Extern 2 (Refutative (not_of_course _)) => simple notypeclasses refine (not_of_course_refutative _) : typeclass_instances.
Global Hint Extern 2 (Affirmative (of_course_rel _ _ _)) => simple notypeclasses refine (Affirmative_of_course _) : typeclass_instances.
Global Hint Extern 2 (Affirmative (leq _)) => simple notypeclasses refine (Affirmative_of_course _) : typeclass_instances.

Definition atrue_decidable  : Decidable 𝐓 := tautology.
Definition afalse_decidable : Decidable 𝐅 := tautology.
Global Hint Extern 2 (Decidable atrue) => simple notypeclasses refine atrue_decidable : typeclass_instances.
Global Hint Extern 2 (Decidable afalse) => simple notypeclasses refine afalse_decidable : typeclass_instances.
Global Hint Extern 2 (Affirmative atrue) => simple notypeclasses refine atrue_decidable : typeclass_instances.
Global Hint Extern 2 (Affirmative afalse) => simple notypeclasses refine afalse_decidable : typeclass_instances.
Global Hint Extern 2 (Refutative  atrue) => simple notypeclasses refine atrue_decidable : typeclass_instances.
Global Hint Extern 2 (Refutative  afalse) => simple notypeclasses refine afalse_decidable : typeclass_instances.

Definition anot_decidable `{Decidable P} : Decidable P ᗮ := tautology.
Definition anot_refutative `{Affirmative P} : Refutative P ᗮ := tautology.
Definition anot_affirmative `{Refutative P} : Affirmative P ᗮ := tautology.
Global Hint Extern 2 (Decidable (_ ᗮ)) => simple notypeclasses refine anot_decidable : typeclass_instances.
Global Hint Extern 2 (Affirmative (_ ᗮ)) => simple notypeclasses refine anot_affirmative : typeclass_instances.
Global Hint Extern 2 (Refutative (_ ᗮ)) => simple notypeclasses refine anot_refutative : typeclass_instances.

Definition aand_decidable  `{Decidable P} `{Decidable Q} : Decidable (P ∧ Q) := tautology.
Definition aor_decidable   `{Decidable P} `{Decidable Q} : Decidable (P ∨ Q) := tautology.
Definition aprod_decidable `{Decidable P} `{Decidable Q} : Decidable (P ⊠ Q) := tautology.
Definition apar_decidable  `{Decidable P} `{Decidable Q} : Decidable (P ⊞ Q) := tautology.
Global Hint Extern 2 (Decidable (aand _)) => simple notypeclasses refine aand_decidable : typeclass_instances.
Global Hint Extern 2 (Decidable (aor _)) => simple notypeclasses refine aor_decidable : typeclass_instances.
Global Hint Extern 2 (Decidable (_ ⊠ _)) => simple notypeclasses refine aprod_decidable : typeclass_instances.
Global Hint Extern 2 (Decidable (_ ⊞ _)) => simple notypeclasses refine apar_decidable : typeclass_instances.

Definition aimpl_decidable `{Decidable P} `{Decidable Q} : Decidable (P ⊸ Q) := _ : Decidable (P ᗮ ⊞ Q).
Global Hint Extern 2 (Decidable (_ ⊸ _)) => simple notypeclasses refine aimpl_decidable : typeclass_instances.
Definition aiff_decidable `{Decidable P} `{Decidable Q} : Decidable (P ⧟ Q) := _ : Decidable ((P ⊸ Q) ∧ (Q ⊸ P)).
Global Hint Extern 2 (Decidable (_ ⧟ _)) => simple notypeclasses refine aiff_decidable : typeclass_instances.

Definition aand_aprod_dec_l (P Q:Ω) `{!Decidable P} : P ∧ Q ⧟ P ⊠ Q := tautology.
Definition aand_aprod_dec_r (P Q:Ω) `{!Decidable Q} : P ∧ Q ⧟ P ⊠ Q := tautology.
Definition apar_aor_dec_l   (P Q:Ω) `{!Decidable P} : P ⊞ Q ⧟ P ∨ Q := tautology.
Definition apar_aor_dec_r   (P Q:Ω) `{!Decidable Q} : P ⊞ Q ⧟ P ∨ Q := tautology.

Definition aor_affirmative `{Affirmative P} `{Affirmative Q} : Affirmative (P ∨ Q) := tautology.
Definition aand_refutative `{Refutative P} `{Refutative Q} : Refutative (P ∧ Q) := tautology.
Global Hint Extern 2 (Affirmative (aor _)) => simple notypeclasses refine aor_affirmative : typeclass_instances.
Global Hint Extern 2 (Refutative (aand _)) => simple notypeclasses refine aand_refutative : typeclass_instances.

Definition apar_affirmative `{Affirmative P} `{Affirmative Q} : Affirmative (P ⊞ Q) := tautology.
Definition aprod_refutative `{Refutative P} `{Refutative Q} : Refutative (P ⊠ Q) := tautology.
Global Hint Extern 2 (Affirmative (_ ⊞ _)) => simple notypeclasses refine apar_affirmative : typeclass_instances.
Global Hint Extern 2 (Refutative (_ ⊠ _)) => simple notypeclasses refine aprod_refutative : typeclass_instances.

Definition aprod_affirmative `{Affirmative P} `{Affirmative Q} : Affirmative (P ⊠ Q) := tautology.
Definition apar_refutative `{Refutative P} `{Refutative Q} : Refutative (P ⊞ Q) := tautology.
Global Hint Extern 2 (Affirmative (_ ⊠ _)) => simple notypeclasses refine aprod_affirmative : typeclass_instances.
Global Hint Extern 2 (Refutative (_ ⊞ _)) => simple notypeclasses refine apar_refutative : typeclass_instances.

Definition aimpl_affirmative `{Refutative P} `{Affirmative Q} : Affirmative (P ⊸ Q) := tautology.
Definition aimpl_refutative `{Affirmative P} `{Refutative Q} : Refutative (P ⊸ Q) := tautology.
Global Hint Extern 2 (Affirmative (_ ⊸ _)) => simple notypeclasses refine aimpl_affirmative : typeclass_instances.
Global Hint Extern 2 (Refutative (_ ⊸ _)) => simple notypeclasses refine aimpl_refutative : typeclass_instances.

Definition affirmative_aimpl {P Q : Ω} `{!Affirmative P} : (P → Q) → (P ⊸ Q) := tautology.
Definition refutative_aimpl {P Q : Ω} `{!Refutative Q} : (Q ᗮ → P ᗮ) → (P ⊸ Q) := tautology.
Definition refutative_aimpl_dual {P Pd Q Qd : Ω} `{!Refutative Q} `{DeMorganDual P Pd} `{DeMorganDual Q Qd} : (Qd → Pd) → (P ⊸ Q) := tautology.
Definition decidable_aimpl {P Q : Ω} `{!Decidable P} : (P → Q) → (P ⊸ Q) := affirmative_aimpl.

Definition affirmative_aiff `{Affirmative P} `{Affirmative Q} : (P ↔ Q) → (P ⧟ Q) := tautology.
Definition refutative_aiff `{Refutative P} `{Refutative Q} : (P ᗮ ↔ Q ᗮ) → (P ⧟ Q) := tautology.

Definition refutative_apar_l {P Q : Ω} `{!Refutative P} : (P ᗮ → Q) → (P ⊞ Q) := tautology.
Definition refutative_apar_r {P Q : Ω} `{!Refutative P} : (P ᗮ → Q) → (Q ⊞ P) := tautology.

Definition whynot_aimpl_refutative {P Q} `{Refutative Q} : (P ⊸ Q) → (? P ⊸ Q) := tautology.
Definition affirmative_aimpl_of_course {P Q} `{Affirmative P} : (P ⊸ Q) → (P ⊸ !Q) := tautology.

Definition affirmative_aand_aprod {P Q R : Ω} `{!Affirmative P} : (P ⊸ Q ∧ R) → (P ⊸ Q ⊠ R) := tautology.
Definition aor_apar_refutative {P Q R : Ω} {H:Refutative R} : (P ∨ Q ⊸ R) → (P ⊞ Q ⊸ R) := tautology.
Definition affirmative_aprod_aimpl_l {P Q R : Ω} `{!Affirmative P} : (P → (Q ⊸ R)) → (P ⊠ Q ⊸ R) := tautology.
Definition affirmative_aprod_aimpl_r {P Q R : Ω} `{!Affirmative P} : (P → (Q ⊸ R)) → (Q ⊠ P ⊸ R) := tautology.
Definition of_course_aprod_aimpl_l {P Q R : Ω} : (P → (Q ⊸ R)) → (!P ⊠ Q ⊸ R) := tautology.
Definition of_course_aprod_aimpl_r {P Q R : Ω} : (P → (Q ⊸ R)) → (Q ⊠ !P ⊸ R) := tautology.

Lemma affirmative_aex `{P:A → Ω} {H:∀ x, Affirmative (P x)} : Affirmative (aex P).
Proof. apply affirmative_alt. split.
+ intros Q [y Py]. revert Py. change (¬ (P y)). apply affirmative_alt. exact (H y). exact (Q y).
+ intros Q y. apply affirmative_alt. exact (H y). intro. apply Q. now exists y.
Qed.
Global Hint Extern 4 (Affirmative (aex _)) => notypeclasses refine affirmative_aex : typeclass_instances.

Lemma refutative_all `{P:A → Ω} {H:∀ x, Refutative (P x)} : Refutative (all P).
Proof. now change (Refutative (∐ y, (P y)ᗮ)ᗮ). Qed.
Global Hint Extern 4 (Refutative (all _)) => notypeclasses refine refutative_all : typeclass_instances.

