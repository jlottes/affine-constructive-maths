Declare Scope type_scope.
Delimit Scope type_scope with type.
Bind Scope type_scope with Sortclass.

Declare Scope function_scope.
Delimit Scope function_scope with function.
Bind Scope function_scope with Funclass.

Open Scope function_scope.
Open Scope type_scope.

Declare ML Module "ltac_plugin".
Global Set Default Proof Mode "Classic".

Declare ML Module "number_string_notation_plugin".

Declare ML Module "firstorder_plugin".

Create HintDb core.
Global Hint Variables Opaque : core.
Global Hint Constants Opaque : core.

Global Set Primitive Projections.
Global Set Universe Polymorphism.
Global Set Private Polymorphic Universes.
Global Set Polymorphic Inductive Cumulativity.
Global Set Keyed Unification.
Global Generalizable All Variables.

Definition id `(x:A) := x.

Inductive empty : Set :=.
Definition abort {A} (x:empty) : A := match x with end.
Definition dep_abort {P:forall (_ : empty), Type} (x:empty) : P x := match x with end.

Inductive unit : Set := tt : unit.
Existing Class unit.
Global Hint Extern 0 (unit) => exact tt : typeclass_instances.
Definition to_unit `(x:A) : unit := _.

Inductive bool : Set := true : bool | false : bool.

Record tprod A B := pair { proj1 : A ; proj2 : B }.
Arguments pair {A B} _ _.
Arguments proj1 {_ _} _.
Arguments proj2 {_ _} _.

Inductive tsig@{i j} {A:Type@{i}} (B: forall (_:A), Type@{j}) := dpair : forall a (b : B a), @tsig A B.
Arguments dpair {A B} a b.
Definition tproj1@{i j} {A B} (p: @tsig@{i j} A B) : A := match p with dpair a b => a end.
Definition tproj2@{i j} {A B} (p: @tsig@{i j} A B) : B (tproj1 p) := match p with dpair a b => b end.

Inductive tsum A B := inl : forall (_:A), tsum A B | inr : forall (_:B), tsum A B.
Arguments inl {A B} _.
Arguments inr {A B} _.

Definition tcurry   `(f:forall _ : tprod A B, C) a b := f (pair a b).
Definition tuncurry `(f:forall (_ : A) (_ : B), C) p := f (proj1 p) (proj2 p).

Notation "exact:( x )" := ltac:(let t := constr:(x) in exact t) (only parsing).
Notation eval_red tm := ltac:( let t := eval red in tm in exact t ) (only parsing).
Notation eval_tuncurry tm := (eval_red (tuncurry tm)) (only parsing).
Notation eval_tuncurry3 tm := (eval_tuncurry (eval_tuncurry tm)) (only parsing).
