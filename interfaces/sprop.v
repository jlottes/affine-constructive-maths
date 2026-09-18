Require Import interfaces.notation.

Declare Scope sprop_scope.
Delimit Scope sprop_scope with sprop.
Local Open Scope sprop_scope.

Inductive True : SProp := I : True.
Inductive False: SProp :=.

Definition not (P: SProp) : SProp := P → False.
Register not as core.not.type.

Record and (P Q : SProp) : SProp := conj { andl : P ; andr : Q }.
Inductive or (P Q : SProp) : SProp := or_introl : P → or P Q | or_intror : Q → or P Q.

Arguments conj {P Q} _ _.
Arguments andl {P Q} _.
Arguments andr {P Q} _.
Arguments or_introl {P} Q _.
Arguments or_intror P {Q} _.

Definition impl := λ '(P, Q) : SProp ∗ SProp, P → Q.

Definition iff := λ '(P, Q) : SProp ∗ SProp, and (P → Q) (Q → P).

Inductive ex `(P:A → SProp) : SProp := exists : ∀ x, P x → ex P.

Module notation.
(** Shared with [Ω]: parsed via the open scope. *)
Notation "'𝐓'" := True : sprop_scope.
Notation "'𝐅'" := False : sprop_scope.
Infix "∧" := and : sprop_scope.
Infix "∨" := or  : sprop_scope.

(** Unique to [SProp]: kept in [type_scope] so they're always available. *)
Notation "¬ x" := (not x) : type_scope.
Notation "P ↔ Q" := (iff (@pair SProp SProp P Q)) (only parsing) : type_scope.
Notation "P ↔ Q" := (iff (P, Q)) (only printing) : type_scope.
Notation "∃ x .. y , P" := (ex (fun x => .. (ex (fun y => P)) ..))
  (at level 10, x binder, y binder, P at level 200) : type_scope.
End notation.
Export notation.

Class Inhabited (A:Type) : SProp := inhabited : ∃ (x:A), True.
Arguments inhabited A {_}.

Inductive seqt {A:Type} (x:A) : A → SProp := seq_refl : seqt x x.
Arguments seq_refl {A x} , [A] x.
Definition seq {A:Type} : A ∗ A → SProp := λ '(x,y), seqt x y.

Definition scomplement `(R:A → SProp) := λ x, ¬ R x.
Class sSubrelation {A} (R R' : A → SProp) : SProp := ssubrelation p : R p → R' p.
Definition sflip `(R:A ∗ B → SProp) := λ '(x, y), R (y, x).

Definition srelation (A:Type) := A ∗ A → SProp.

Class sReflexive     `(R : srelation A) : SProp := sreflexivity x : R (x, x).
Class sIrreflexive   `(R : srelation A) : SProp := sirreflexivity x : ¬ R (x, x).
Class sSymmetric     `(R : srelation A) : SProp := ssymmetry x y: R (x, y) → R (y, x).
Class sTransitive    `(R : srelation A) : SProp := stransitivity x y z : R (x, y) → R (y, z) → R (x, z).
Class sAntisymmetric {A} (eq R : srelation A) : SProp := santisymmetry x y : R (x, y) → R (y, x) → eq (x, y).

Record sEquivalence `(R : srelation A) : SProp :=
{ #[reversible=no] sequiv_refl  :> sReflexive R
; #[reversible=no] sequiv_sym   :> sSymmetric R
; #[reversible=no] sequiv_trans :> sTransitive R
}.
Existing Class sEquivalence.

Record sPartialEquivalence `(R : srelation A) : SProp :=
{ #[reversible=no] spartial_equiv_sym   :> sSymmetric R
; #[reversible=no] spartial_equiv_trans :> sTransitive R
}.
Existing Class sPartialEquivalence.

Definition sEquivalence_is_sPartialEquivalence `(@sEquivalence A R) : sPartialEquivalence R
  := Build_sPartialEquivalence _ _ _ _.
Coercion sEquivalence_is_sPartialEquivalence : sEquivalence >-> sPartialEquivalence.


