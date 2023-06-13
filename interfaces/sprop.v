Require Import interfaces.notation.

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

Definition impl (P Q : SProp) : SProp := P → Q.

Definition iff (P Q : SProp) : SProp := and (P → Q) (Q → P).

Inductive ex `(P:A → SProp) : SProp := exists : ∀ x, P x → ex P.

Module notation.
Notation "'𝐓'" := True : type_scope.
Notation "'𝐅'" := False : type_scope.
Notation "¬ x" := (not x) : type_scope.
Infix "∧" := and : type_scope.
Infix "∨" := or  : type_scope.
Infix "↔" := iff : type_scope.
Notation "∃ x .. y , P" := (ex (fun x => .. (ex (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
End notation.
Export notation.

Inductive seq {A:Type} (x:A) : A → SProp := seq_refl : seq x x.
Arguments seq_refl {A x} , [A] x.

Definition srelation (A:Type) := A → A → SProp.
Definition scomplement `(R:srelation A) : srelation A := λ x y, ¬ R x y.
Definition sflip `(R:srelation A) : srelation A := λ x y, R y x.

Class sReflexive     `(R : srelation A) : SProp := sreflexivity x : R x x.
Class sIrreflexive   `(R : srelation A) : SProp := sirreflexivity x : ¬ R x x.
Class sSymmetric     `(R : srelation A) : SProp := ssymmetry x y: R x y → R y x.
Class sTransitive    `(R : srelation A) : SProp := stransitivity x y z : R x y → R y z → R x z.
Class sAntisymmetric {A} (eq R : srelation A) : SProp := santisymmetry x y : R x y → R y x → eq x y.
Class sSubrelation {A} (R R' : srelation A) : SProp := ssubrelation x y : R x y → R' x y.

Record sEquivalence `(R : srelation A) : SProp :=
{ sequiv_refl  :> sReflexive R
; sequiv_sym   :> sSymmetric R
; sequiv_trans :> sTransitive R
}.
Existing Class sEquivalence.

Record sPartialEquivalence `(R : srelation A) : SProp :=
{ spartial_equiv_sym   :> sSymmetric R
; spartial_equiv_trans :> sTransitive R
}.
Existing Class sPartialEquivalence.

Definition sEquivalence_is_sPartialEquivalence `(@sEquivalence A R) : sPartialEquivalence R
  := Build_sPartialEquivalence _ _ _ _.
Coercion sEquivalence_is_sPartialEquivalence : sEquivalence >-> sPartialEquivalence.

(** Proper and respectful *)
Declare Scope ssignature_scope.
Delimit Scope ssignature_scope with ssignature.

Class sProper `(R : srelation A) m : SProp := sproper_prf : R m m.
Arguments sProper {A}%type (R)%ssignature _.

Definition srespectful {A B} (R:srelation A) (R':srelation B) : srelation (A → B)
  := λ f g, ∀ x y, R x y → R' (f x) (g y).
Arguments srespectful {A B}%type (R R')%ssignature _ _.

Definition srespectful_flip {A B} (R:srelation A) (R':srelation B) := srespectful (sflip R) R'.
Arguments srespectful_flip {A B}%type (R R')%ssignature _ _.

Notation " R ++> R' " := (srespectful R R')      (right associativity, at level 55) : ssignature_scope.
Notation " R ==> R' " := (srespectful R R')      (right associativity, at level 55) : ssignature_scope.
Notation " R --> R' " := (srespectful_flip R R') (right associativity, at level 55) : ssignature_scope.
