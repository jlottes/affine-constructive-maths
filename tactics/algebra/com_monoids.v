Require Import abstract_algebra bundled_algebra.
Require Import nat list.
Require Export interfaces.free.generators interfaces.free.groups.
Require Import implementations.free.com_monoids.
Require Import logic.dec tactics.misc strip_coercions.
Require Import quote.base quote.vars quote.onepass.
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

(** The patterns are elaborated at the goal's own carrier [Y], so that they
    are the operations as they occur in the goal; the lemma heads are at the
    structure [M] built from it. *)
Ltac add_mon_tac _ :=
  let Y := lazymatch goal with |- apos (_ = _ :> set_T ?Y) => Y end in
  let M := strip_coercions_or_self Y in
  let M := constr:(ltac:(solve [ exact M | refine (make_additive_monoid M) ]) : additive_monoid) in
  quote_onepass_2
    constr:(fun Γ : list M => add_mon.eval Γ)
    constr:(fun Γ : list M => let ev := add_mon.eval Γ in @quote_equation _ _ ev)
    constr:(fun Γ : list M => let ev := add_mon.eval Γ in @quote_var _ _ _ ev)
    constr:(@cons M) constr:(@nil M)
    constr:(fun a b : Y => a + b)
    constr:(fun Γ : list M => let ev := add_mon.eval Γ in
      fun x₁ y₁ x₂ y₂ (p : quote ev x₁ y₁) (q : quote ev x₂ y₂) => quote_plus ev p q)
    constr:(0 : Y)
    constr:(fun Γ : list M => let ev := add_mon.eval Γ in quote_zero ev);
  decide_relation.
Tactic Notation "add_mon" := add_mon_tac ltac:(0).

Ltac com_mon_tac _ :=
  let Y := lazymatch goal with |- apos (_ = _ :> set_T ?Y) => Y end in
  let M := strip_coercions_or_self Y in
  let M := constr:(ltac:(solve [ exact M | refine (make_commutative_monoid M) ]) : commutative_monoid) in
  quote_onepass_2
    constr:(fun Γ : list M => com_mon.eval Γ)
    constr:(fun Γ : list M => let ev := com_mon.eval Γ in @quote_equation _ _ ev)
    constr:(fun Γ : list M => let ev := com_mon.eval Γ in @quote_var _ _ _ ev)
    constr:(@cons M) constr:(@nil M)
    constr:(fun a b : Y => func_op sg_op (a, b))
    constr:(fun Γ : list M => let ev := com_mon.eval Γ in
      fun x₁ y₁ x₂ y₂ (p : quote ev x₁ y₁) (q : quote ev x₂ y₂) => quote_sg_op ev p q)
    constr:(mon_unit : Y)
    constr:(fun Γ : list M => let ev := com_mon.eval Γ in quote_mon_unit ev);
  decide_relation.
Tactic Notation "com_mon" := com_mon_tac ltac:(0).
