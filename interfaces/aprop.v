Require Import interfaces.notation sprop tauto tactics.misc.
Export sprop.notation.

(* Unset Universe Polymorphism. *)

Definition NotBoth (P Q : SProp) := ¬ (P ∧ Q).
Record AProp :=
{ apos :> SProp
; #[canonical=no] aneg : SProp
; #[canonical=no] not_both : NotBoth apos aneg
}.
Arguments Build_AProp {_ _} not_both.
Notation "'Ω'" := AProp : type_scope.
Existing Class apos.

Declare Scope aprop_scope.
Delimit Scope aprop_scope with Ω.
Bind Scope aprop_scope with AProp.
Global Open Scope aprop_scope.

Module props_full_notation.
  Notation "P ⁺" := (apos P) (at level 7, no associativity, format "P ⁺") : type_scope.
  Notation "P ⁻" := (aneg P) (at level 7, no associativity, format "P ⁻") : type_scope.
End props_full_notation.
Module props_notation.
  Notation "P ⁺" := (apos P) (at level 7, no associativity, only parsing) : type_scope.
  Notation "P ⁻" := (aneg P) (at level 7, no associativity, format "P ⁻") : type_scope.
End props_notation.
Import props_notation.

Definition apos_not_aneg {P : Ω} : P → P⁻ → False := λ p n, not_both P (conj p n).
Definition aneg_not_apos {P : Ω} : P⁻ → P → False := λ n p, not_both P (conj p n).

Ltac tautological_hook := idtac.
Ltac tautological :=
  timeout 5 (repeat (tautological_hook; hnf; intuition; repeat match goal with
  | H : ex _ |- _ => destruct H
  | H : ∀ _ : ?A, _, x : ?A |- _ => learn constr:(H x)
  | H : @ex ?A ?P → _, H2 : ?P ?x |- _ => specialize (H (exists P x H2))
  | H : @ex ?A ?P → _, x : ?A |- _ =>
    let H' := fresh "H" in
    assert (P x) as H' by (try clearbody H; clear H; tautological);
    specialize (H (exists P x H'))
  | x : ?A |- @ex ?A ?P =>
    exists x; tautological; fail
  | H : apos ?P |- _ => learn constr:(apos_not_aneg H)
  | H : aneg ?P |- _ => learn constr:(aneg_not_apos H)
  end)).
Notation tautology := ltac:(normalize_proof tautological) (only parsing).
Local Notation nb p n := (tautology : NotBoth p n) (only parsing).

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
Polymorphic Definition all_nb `(P:A → Ω) := nb ( ∀ x, (P x)⁺ ) ( ∃ x, (P x)⁻ ).
Polymorphic Definition aex_nb `(P:A → Ω) := nb ( ∃ x, (P x)⁺ ) ( ∀ x, (P x)⁻ ).

Canonical Structure atrue := Build_AProp atrue_nb.
Canonical Structure afalse := Build_AProp afalse_nb.
Canonical Structure aand (P Q : Ω) := Build_AProp (aand_nb P Q).
Canonical Structure aor  (P Q : Ω) := Build_AProp (aor_nb P Q).
Definition anot (P : Ω) := Build_AProp (anot_nb P).
Definition aprod (P Q : Ω) := Build_AProp (aprod_nb P Q).
Definition apar  (P Q : Ω) := Build_AProp (apar_nb  P Q).
Definition aimpl (P Q : Ω) := Build_AProp (aimpl_nb P Q).
Definition of_course (P : SProp) := Build_AProp (of_course_nb P).
Definition not_of_course (P : SProp) := Build_AProp (not_of_course_nb P).
Definition why_not (P : Ω) := Build_AProp (why_not_nb P).
Polymorphic Definition all `(P:A → Ω) := Build_AProp (all_nb P).
Polymorphic Definition aex `(P:A → Ω) := Build_AProp (aex_nb P).

(** Shared notation with [SProp].
  Parsed as [SProp], but coerceable to [Ω] via canonical projections. *)
Notation "'𝐓'" := atrue (only printing) : aprop_scope.
Notation "'𝐅'" := afalse (only printing) : aprop_scope.
Infix "∧" := aand (only printing) : aprop_scope.
Infix "∨" := aor (only printing) : aprop_scope.

(** Unambiguous notation specific to [Ω] *)
Notation "P 'ᗮ'" := (anot P) (at level 6, left associativity) : aprop_scope.
Infix "⊠" := aprod : aprop_scope.
Infix "⊞" := apar  : aprop_scope.
Infix "⊸" := aimpl : aprop_scope.

Definition aiff (P Q : Ω) : Ω := (P ⊸ Q) ∧ (Q ⊸ P).
Infix "⧟" := aiff  : aprop_scope.

Notation "∏ x .. y , P" := (all (fun x => .. (all (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : aprop_scope.

Notation "∐ x .. y , P" := (aex (fun x => .. (aex (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : aprop_scope.

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

Section relations.
  Universes i.
  Context {A:Type@{i}}.

  Definition of_course_rel (R:srelation A) := λ x y, ! (R x y).
  Definition leq := of_course_rel (@seq A).

  Context (R:A → A → Ω).

  Definition flip x y := R y x.
  Definition complement x y := (R x y)ᗮ.

  Definition DecidableRelation   := ∀ x y, Decidable   (R x y).
  Definition AffirmativeRelation := ∀ x y, Affirmative (R x y).
  Definition RefutativeRelation  := ∀ x y, Refutative  (R x y).
  Existing Class DecidableRelation.
  Existing Class AffirmativeRelation.
  Existing Class RefutativeRelation.

  Class Reflexive  : SProp := reflexivity x : R x x.
  Class Symmetric  : SProp := symmetry x y : R x y ⊸ R y x.
  Class Transitive : SProp := transitivity x y z : R x y ⊠ R y z ⊸ R x z.
  Class StronglyTransitive : SProp := strong_transitivity x y z : R x y ∧ R y z ⊸ R x z.
  Class PseudoAntisymmetric (eq : A → A → Ω) : SProp := pseudo_antisymmetry x y : R x y ⊠ R y x ⊸ eq x y.
  Class Antisymmetric (eq : A → A → Ω) : SProp := antisymmetry x y : R x y ∧ R y x ⊸ eq x y.
  Class PseudoTotalRelation : SProp := pseudo_total x y : R x y ⊞ R y x.
  Class TotalRelation : SProp := total x y : R x y ∨ R y x : Ω .

  Record Equivalence : SProp :=
  { equiv_refl  :> Reflexive
  ; equiv_sym   :> Symmetric
  ; equiv_trans :> Transitive
  }.
  Existing Class Equivalence.

  Class Subrelation@{} (R':A → A → Ω) : SProp := subrelation : ∀ {x y}, R x y ⊸ R' x y.

  Record PartialEquivalence : SProp :=
  { partial_equiv_sym   :> Symmetric
  ; partial_equiv_trans :> Transitive
  }.
  Existing Class PartialEquivalence.

  Definition Equivalence_to_PartialEquivalence : Equivalence → PartialEquivalence.   Proof. intro. split; exact _. Defined.
  Coercion Equivalence_to_PartialEquivalence : Equivalence >-> PartialEquivalence.
End relations.
Global Hint Extern 2 (Decidable   (?R ?x ?y)) => simple notypeclasses refine ((_ : DecidableRelation   R) x y) : typeclass_instances.
Global Hint Extern 2 (Affirmative (?R ?x ?y)) => simple notypeclasses refine ((_ : AffirmativeRelation R) x y) : typeclass_instances.
Global Hint Extern 2 (Refutative  (?R ?x ?y)) => simple notypeclasses refine ((_ : RefutativeRelation  R) x y) : typeclass_instances.

Class Dec `(R:A → A → Ω) := dec : A → A → bool.
Arguments dec {A} R {_} _ _.
Class IsDec `(R:A → A → Ω) {d:Dec R} : SProp :=
  dec_spec x y : if dec R x y then R x y else (R x y)ᗮ.
Arguments dec_spec {A} R {d _} _ _.
