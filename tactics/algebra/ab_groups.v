Require Import abstract_algebra bundled_algebra.
Require Import nat list.
Require Export interfaces.free.generators interfaces.free.groups.
Require Import implementations.free.ab_groups.
Require Import signed_naturals_integers.
Require Import logic.dec tactics.misc strip_coercions.
Require Import quote.base quote.vars.
Require Export theory.bundled_groups.

Module add_grp.
  Definition F@{u} := free_add_group@{u} SignedNat@{u}.
  Definition eval := @free_additive_group.eval F.
  Arguments eval {G} Γ.
End add_grp.

Ltac add_grp_tac _ :=
  find_structure_and_quote_equation
    additive_group
    ltac:(fun G => refine (make_additive_group G))
    ltac:(fun G Γ => constr:(@add_grp.eval G Γ));
  decide_relation.
Tactic Notation "add_grp" := add_grp_tac ltac:(0).
