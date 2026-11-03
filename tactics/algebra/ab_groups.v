Require Import abstract_algebra bundled_algebra.
Require Import nat list.
Require Export interfaces.free.generators interfaces.free.groups.
Require Import implementations.free.ab_groups.
Require Import signed_naturals_integers theory.additive_groups.
Require Import logic.dec tactics.misc strip_coercions.
Require Import quote.base quote.vars quote.onepass.
Require Export theory.bundled_groups.

Module add_grp.
  Definition F@{u} := free_add_group@{u} SignedNat@{u}.
  Definition eval := @free_additive_group.eval F.
  Arguments eval {G} Γ.
End add_grp.

Ltac add_grp_tac _ :=
  let Y := lazymatch goal with |- apos (_ = _ :> set_T ?Y) => Y end in
  let G := strip_coercions_or_self Y in
  let G := constr:(ltac:(solve [ exact G | refine (make_additive_group G) ]) : additive_group) in
  quote_onepass_3
    constr:(fun Γ : list G => add_grp.eval Γ)
    constr:(fun Γ : list G => let ev := add_grp.eval Γ in @quote_equation _ _ ev)
    constr:(fun Γ : list G => let ev := add_grp.eval Γ in @quote_var _ _ _ ev)
    constr:(@cons G) constr:(@nil G)
    constr:(fun a b : Y => a + b)
    constr:(fun Γ : list G => let ev := add_grp.eval Γ in
      fun x₁ y₁ x₂ y₂ (p : quote ev x₁ y₁) (q : quote ev x₂ y₂) => quote_plus ev p q)
    constr:(0 : Y)
    constr:(fun Γ : list G => let ev := add_grp.eval Γ in quote_zero ev)
    constr:(fun a : Y => - a)
    constr:(fun Γ : list G => let ev := add_grp.eval Γ in
      fun x y (p : quote ev x y) => quote_negate_alt ev p);
  decide_relation.
Tactic Notation "add_grp" := add_grp_tac ltac:(0).
