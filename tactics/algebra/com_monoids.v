Require Import abstract_algebra bundled_algebra.
Require Import nat list.
Require Export interfaces.free.generators interfaces.free.groups.
Require Import implementations.free.com_monoids.
Require Import logic.dec tactics.misc strip_coercions.
Require Import quote.base quote.vars.
Require Export theory.bundled_groups.

Module add_mon.
  Definition F@{u} := free_add_mon@{u} Nat_naturals@{u}.
  Definition eval := @free_additive_monoid.eval F.
  Arguments eval {M} Γ.
End add_mon.

Module com_mon.
  Definition F@{u} := free_com_mon@{u} Nat_naturals@{u}.
  Definition eval := @free_commutative_monoid.eval F.
  Arguments eval {M} Γ.
End com_mon.

Ltac add_mon_tac _ :=
  find_structure_and_quote_equation
    additive_monoid
    ltac:(fun M => refine (make_additive_monoid M))
    ltac:(fun M Γ => constr:(@add_mon.eval M Γ));
  decide_relation.
Tactic Notation "add_mon" := add_mon_tac ltac:(0).

Ltac com_mon_tac _ :=
  find_structure_and_quote_equation
    commutative_monoid
    ltac:(fun M => refine (make_commutative_monoid M))
    ltac:(fun M Γ => constr:(@com_mon.eval M Γ));
  decide_relation.
Tactic Notation "com_mon" := com_mon_tac ltac:(0).

