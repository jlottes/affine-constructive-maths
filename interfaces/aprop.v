Require Import interfaces.notation sprop tauto tactics.misc.
Require Export interfaces.aprop_kernel.
Export sprop.notation.

Local Open Scope sprop_scope.

(** The affine propositions.  At its core this is the antithesis/Chu
    construction Chu(SProp, 𝐅) of the paper (§3, Def 3.3): a pair of an
    affirmation [apos] and a refutation [aneg] that cannot both hold.

    The [classicality] field refines the plain Chu construction: its type is
    supplied by the kernel (interfaces/aprop_kernel.v) and constrains which
    pairs are constructible.

    - Default (constructive) kernel: [Classicality P N := 𝐓], and [AProp] is
      exactly the Chu construction.  This model is anticlassical: undecided
      pairs such as (𝐅,𝐅) witness refutations of internal LEM
      (see counterexamples/).
    - Classical kernel (classical/aprop_kernel.v, installed only by
      scripts/classical-build.sh): [Classicality P N := P ∨ N], with an
      SProp-level excluded-middle axiom.  Every constructible pair is then
      decidable, and the model collapses to classical two-valued logic.

    Both proof fields are SProp, hence proof-irrelevant: the kernels differ
    only in what [Build_AProp] demands, never in how a constructed [Ω]
    behaves.  Shared code therefore constructs [Ω] only through the
    connective API below (which fills the field via the kernel's [_cl]
    combinators) and thereby stays valid in both models — in particular,
    compatible with classical mathematics.  Raw [Build_AProp] is reserved
    for counterexamples/: anticlassical, model-specific results, excluded
    from the classical build. *)
Record AProp : Type :=
{ apos :> SProp
; #[canonical=no] aneg : SProp
; #[canonical=no] not_both : NotBoth apos aneg
; #[canonical=no] classicality : Classicality apos aneg
}.
Arguments Build_AProp {_ _} not_both classicality.
Notation "'Ω'" := AProp : type_scope.
Existing Class apos.

Declare Scope aprop_scope.
Delimit Scope aprop_scope with Ω.
Bind Scope aprop_scope with AProp.

Module props_full_notation.
  Notation "P ⁺" := (apos P) (at level 1, no associativity, format "P ⁺") : type_scope.
  Notation "P ⁻" := (aneg P) (at level 1, no associativity, format "P ⁻") : type_scope.
End props_full_notation.
Module props_notation.
  Notation "P ⁺" := (apos P) (at level 1, no associativity, only parsing) : type_scope.
  Notation "P ⁻" := (aneg P) (at level 1, no associativity, format "P ⁻") : type_scope.
End props_notation.
Import props_notation.

Definition apos_not_aneg {P : Ω} : P → P⁻ → False := λ p n, not_both P (conj p n).
Definition aneg_not_apos {P : Ω} : P⁻ → P → False := λ n p, not_both P (conj p n).

Ltac tautological_hook := idtac.
Ltac full_tautological :=
  timeout 5 (repeat (tautological_hook; hnf; intuition; repeat match goal with
  | H : ex _ |- _ => destruct H
  | H : ∀ _ : ?A, _, x : ?A |- _ => learn constr:(H x)
  | H : @ex ?A ?P → _, H2 : ?P ?x |- _ => specialize (H (exists P x H2))
  | H : @ex ?A ?P → _, x : ?A |- _ =>
    let H' := fresh "H" in
    assert (P x) as H' by (try clearbody H; clear H; full_tautological);
    specialize (H (exists P x H'))
  | x : ?A |- @ex ?A ?P =>
    exists x; full_tautological; fail
  | H : apos ?P |- _ => learn constr:(apos_not_aneg H)
  | H : aneg ?P |- _ => learn constr:(aneg_not_apos H)
  end)).
Abbreviation full_tautology := ltac:(normalize_proof full_tautological) (only parsing).
Local Abbreviation nb p n := (full_tautology : NotBoth p n) (only parsing).

Local Abbreviation tautology := full_tautology (only parsing).

Definition atrue_nb  := nb 𝐓 𝐅.
Definition afalse_nb := nb 𝐅 𝐓.
Definition anot_nb  (P : Ω) := nb P⁻ P⁺.
Definition aand_nb  (P Q : Ω) := nb ( P⁺ ∧ Q⁺ ) ( P⁻ ∨ Q⁻ ).
Definition aor_nb   (P Q : Ω) := nb ( P⁺ ∨ Q⁺ ) ( P⁻ ∧ Q⁻ ).
Definition aprod_nb (P Q : Ω) := nb ( P⁺ ∧ Q⁺ ) ( (P⁺ → Q⁻) ∧ (Q⁺ → P⁻) ).
Definition apar_nb  (P Q : Ω) := nb ( (P⁻ → Q⁺) ∧ (Q⁻ → P⁺) ) ( P⁻ ∧ Q⁻ ).
Definition aimpl_nb (P Q : Ω) := nb ( (P⁺ → Q⁺) ∧ (Q⁻ → P⁻) ) ( P⁺ ∧ Q⁻ ).
Definition of_course_nb     (P : SProp) := nb P (¬ P).
Definition not_of_course_nb (P : SProp) := nb (¬ P) P.
Definition why_not_nb       (P : Ω) := not_of_course_nb P⁻.
Definition all_nb `(P:A → Ω) := nb ( ∀ x, (P x)⁺ ) ( ∃ x, (P x)⁻ ).
Definition aex_nb `(P:A → Ω) := nb ( ∃ x, (P x)⁺ ) ( ∀ x, (P x)⁻ ).

Canonical Structure atrue := Build_AProp atrue_nb atrue_cl.
Canonical Structure afalse := Build_AProp afalse_nb afalse_cl.
Definition aand := λ '(P, Q) : Ω ∗ Ω, Build_AProp (aand_nb P Q) (aand_cl (classicality P) (classicality Q)).
Definition aor  := λ '(P, Q) : Ω ∗ Ω, Build_AProp (aor_nb P Q) (aor_cl (classicality P) (classicality Q)).
Definition anot (P : Ω) := Build_AProp (anot_nb P) (anot_cl (classicality P)).
Definition aprod := λ '(P, Q) : Ω ∗ Ω, Build_AProp (aprod_nb P Q) (aprod_cl (not_both P) (not_both Q) (classicality P) (classicality Q)).
Definition apar  := λ '(P, Q) : Ω ∗ Ω, Build_AProp (apar_nb  P Q) (apar_cl (not_both P) (not_both Q) (classicality P) (classicality Q)).
Definition aimpl := λ '(P, Q) : Ω ∗ Ω, Build_AProp (aimpl_nb P Q) (aimpl_cl (not_both P) (not_both Q) (classicality P) (classicality Q)).
Definition of_course (P : SProp) := Build_AProp (of_course_nb P) (of_course_cl P).
Definition not_of_course (P : SProp) := Build_AProp (not_of_course_nb P) (not_of_course_cl P).
Definition why_not (P : Ω) := Build_AProp (why_not_nb P) (not_of_course_cl P⁻).
Definition all `(P:A → Ω) := Build_AProp (all_nb P) (all_cl (λ x, classicality (P x))).
Definition aex `(P:A → Ω) := Build_AProp (aex_nb P) (aex_cl (λ x, classicality (P x))).

(** Switch from [sprop_scope] to [aprop_scope] now that the connectives
    are defined.  The [_nb] bodies above needed [sprop_scope] on top of
    the stack for the SProp-level [∧]/[∨]/[𝐓]/[𝐅] to parse; from here on
    we want the Ω-level versions. *)
Local Open Scope aprop_scope.
Global Open Scope aprop_scope.

(** [∧]/[∨]/[𝐓]/[𝐅] in [aprop_scope]: parse and print as the Ω-level connectives.
    Parsing forms use [@pair Ω Ω _ _] explicitly to pin the sort instance of
    sort-polymorphic [tprod]; printing forms use the compact [(P, Q)] notation. *)
Notation "'𝐓'" := atrue : aprop_scope.
Notation "'𝐅'" := afalse : aprop_scope.
Notation "P ∧ Q" := (aand (P, Q)) : aprop_scope.
Notation "P ∨ Q" := (aor  (P, Q)) : aprop_scope.

(** Unambiguous notation specific to [Ω] *)
Notation "P 'ᗮ'" := (anot P) (at level 1, left associativity) : aprop_scope.
Notation "P ⊠ Q" := (aprod (P, Q)) : aprop_scope.
Notation "P ⊞ Q" := (apar  (P, Q)) : aprop_scope.
Notation "P ⊸ Q" := (aimpl (P, Q)) : aprop_scope.

Definition aiff := λ '(P, Q) : Ω ∗ Ω, (P ⊸ Q) ∧ (Q ⊸ P).
Notation "P ⧟ Q" := (aiff (P, Q)) : aprop_scope.

Notation "∏ x .. y , P" := (all (fun x => .. (all (fun y => P)) ..))
  (at level 10, x binder, y binder, P at level 200) : aprop_scope.

Notation "∐ x .. y , P" := (aex (fun x => .. (aex (fun y => P)) ..))
  (at level 10, x binder, y binder, P at level 200) : aprop_scope.

Module modality_notation.
  Notation "! P" := (of_course P) (at level 75, right associativity, format "! P") : aprop_scope.
  Notation "? P" := (why_not P) (at level 75, right associativity) : aprop_scope.
End modality_notation.
Import modality_notation.


Class Decidable (P:Ω) : SProp := decidability : P ∨ P ᗮ.
Class Affirmative (P:Ω) : SProp := affirmativity : P ⧟ !P.
Class Refutative (P:Ω) : SProp := refutativity : P ⧟ ? P.
Arguments decidability P {_}.
Arguments affirmativity P {_}.
Arguments refutativity P {_}.

Class DeMorganDual (P Q : Ω) : SProp := demorgan_dual : P ᗮ ⧟ Q.
Arguments demorgan_dual P {Q _}.
Global Hint Mode DeMorganDual + - : typeclass_instances.

Section predicates.
  Universes u.
  Context {A:Type@{u}}.

  Definition of_course_rel (R:A → SProp) := λ p, ! (R p).

  Context (R:A → Ω).

  Definition complement x := (R x)ᗮ.
  
  Definition DecidableRelation   := ∀ p, Decidable   (R p).
  Definition AffirmativeRelation := ∀ p, Affirmative (R p).
  Definition RefutativeRelation  := ∀ p, Refutative  (R p).
  Existing Class DecidableRelation.
  Existing Class AffirmativeRelation.
  Existing Class RefutativeRelation.

  Class Subrelation (R': A → Ω) : SProp := subrelation : ∀ p, R p ⊸ R' p.
End predicates.
Global Hint Extern 2 (Decidable   (?R ?x)) => simple notypeclasses refine ((_ : DecidableRelation   R) x) : typeclass_instances.
Global Hint Extern 2 (Affirmative (?R ?x)) => simple notypeclasses refine ((_ : AffirmativeRelation R) x) : typeclass_instances.
Global Hint Extern 2 (Refutative  (?R ?x)) => simple notypeclasses refine ((_ : RefutativeRelation  R) x) : typeclass_instances.

Class Dec `(R: A → Ω) := dec : A → bool.
Arguments dec {A} R {_} _.
Class IsDec `(R: A → Ω) {d:Dec R} : SProp :=
  dec_spec p : if dec R p then R p else (R p)ᗮ.
Arguments dec_spec {A} R {d _} _.

Definition flip@{u} {A B : Type@{u}} (R:A ∗ B → Ω) := λ '(x,y), R (y, x).

Section relations.
  Universes u.
  Context {A:Type@{u}}.

  Definition leq := of_course_rel (@seq A).

  Context (R:A ∗ A → Ω).

  Class Reflexive  : SProp := reflexivity x : R (x, x).
  Class Symmetric  : SProp := symmetry x y : R (x, y) ⊸ R (y, x).
  Class Transitive : SProp := transitivity x y z : R (x, y) ⊠ R (y, z) ⊸ R (x, z).
  Class StronglyTransitive : SProp := strong_transitivity x y z : R (x, y) ∧ R (y, z) ⊸ R (x, z).
  Class PseudoAntisymmetric (eq : A ∗ A → Ω) : SProp := pseudo_antisymmetry x y : R (x, y) ⊠ R (y, x) ⊸ eq (x, y).
  Class Antisymmetric (eq : A ∗ A → Ω) : SProp := antisymmetry x y : R (x, y) ∧ R (y, x) ⊸ eq (x, y).
  Class PseudoTotalRelation : SProp := pseudo_total x y : R (x, y) ⊞ R (y, x).
  Class TotalRelation : SProp := total x y : R (x, y) ∨ R (y, x) : Ω .

  Record Equivalence : SProp :=
  { #[reversible=no] equiv_refl  :> Reflexive
  ; #[reversible=no] equiv_sym   :> Symmetric
  ; #[reversible=no] equiv_trans :> Transitive
  }.
  Existing Class Equivalence.

  Record PartialEquivalence : SProp :=
  { #[reversible=no] partial_equiv_sym   :> Symmetric
  ; #[reversible=no] partial_equiv_trans :> Transitive
  }.
  Existing Class PartialEquivalence.

  Definition Equivalence_to_PartialEquivalence : Equivalence → PartialEquivalence.   Proof. intro. split; exact _. Defined.
  Coercion Equivalence_to_PartialEquivalence : Equivalence >-> PartialEquivalence.
End relations.

