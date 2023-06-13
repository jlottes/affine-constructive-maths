Require Import interfaces.notation theory.set theory.default_equality.
Require Import logic.srelations logic.aprop.
Require Import easy.

Global Hint Extern 2 (Equiv bool) => exact leq : typeclass_instances.
Canonical Structure bool_set : set := default_set_make bool.
Notation "𝟐" := bool : set_scope.

Declare Scope bool_scope.
Bind Scope bool_scope with bool.
Delimit Scope bool_scope with bool.

Global Hint Extern 2 (DefaultEquality bool_set) => refine default_set_make_prop : typeclass_instances.
Global Hint Extern 2 (AffirmativeEquality bool_set) => refine default_set_make_prop : typeclass_instances.

Definition andb : bool * bool → bool := λ '(p, q), if p then q else false.
Definition orb : bool * bool → bool := λ '(p, q), if p then true else q.
Definition notb (p : bool) := if p then false else true.

Canonical Structure andb_fun : 𝟐 ⊗ 𝟐 ⇾ 𝟐 := default_eq_func (X:=𝟐 ⊗ 𝟐) andb.
Canonical Structure orb_fun  : 𝟐 ⊗ 𝟐 ⇾ 𝟐 := default_eq_func (X:=𝟐 ⊗ 𝟐) orb.
Canonical Structure notb_fun : 𝟐 ⇾ 𝟐 := default_eq_func notb.

Notation "x && y" := (andb (pair x y)) : bool_scope.
Notation "x || y" := (orb  (pair x y)) : bool_scope.

Definition bool_eq_dec : Dec (A:=bool) (=) := λ p q : bool, if p then q else (if q then false else true).
Global Hint Extern 2 (Dec (A:=bool) (=)) => refine bool_eq_dec : typeclass_instances.
Global Hint Extern 2 (Dec (A:=set_T bool_set) (=)) => refine bool_eq_dec : typeclass_instances.

Definition bool_eq_code (p q : bool) : Ω := if dec (=) p q then 𝐓 else 𝐅.
Lemma bool_eq_encode (p q : bool) : p = q → bool_eq_code p q.
Proof. intros []. clear q. destruct p as [|]; now change 𝐓. Defined.

Definition true_ne_false : true ≠ false := bool_eq_encode _ _.
Definition false_ne_true : false ≠ true := bool_eq_encode _ _.

Lemma bool_eq_is_dec : IsDecEq 𝟐.
Proof. hnf; unfold dec; intros [|] [|]; cbn [ bool_eq_dec ]; [ refl | refine (bool_eq_encode _ _).. | refl ]. Qed.
Global Hint Extern 2 (IsDecEq bool_set) => refine bool_eq_is_dec : typeclass_instances.

Global Hint Extern 2 (DecidableEquality bool_set) => refine bool_eq_is_dec : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality bool_set) => refine bool_eq_is_dec : typeclass_instances.
