Require Import interfaces.notation interfaces.aprop logic.relations.
Require Import implementations.bool theory.set.
Require Import easy rewrite.

Local Open Scope bool_scope.

Lemma dec_spec_by_iff `{IsDec (R:=R)} {x y} {P}
  : (R x y ⧟ P) → if dec R x y then P else P ᗮ.
Proof. intro Q. generalize (dec_spec R x y); destruct (dec R x y); apply Q. Qed.

Lemma dec_spec_dual `{IsDec (R:=R)} x y `{!DeMorganDual (R x y) P}
  : if dec R x y then R x y else P.
Proof.
  generalize (dec_spec R x y).
  destruct (dec R x y); [ easy | apply (demorgan_dual (R x y)) ].
Qed.
Arguments dec_spec_dual {_} R {d _} x y {_ _}.

Lemma dec_spec_andb `{IsDec (R:=R₁)} `{IsDec (R:=R₂)} x₁ y₁ x₂ y₂
  : if dec R₁ x₁ y₁ && dec R₂ x₂ y₂ then (R₁ x₁ y₁ ∧ R₂ x₂ y₂) else (R₁ x₁ y₁)ᗮ ∨ (R₂ x₂ y₂)ᗮ.
Proof. generalize (dec_spec R₁ x₁ y₁), (dec_spec R₂ x₂ y₂).
  destruct (dec R₁ x₁ y₁), (dec R₂ x₂ y₂). 
+ now split.
+ now right.
+ now left.
+ now left.
Qed.

Lemma dec_spec_true `{IsDec (R:=R)} x y : R x y ⧟ dec R x y = true.
Proof. generalize (dec_spec R x y). destruct (dec R x y).
+ intro P. now rew (aiff_true_l P).
+ intro P. apply by_contrapositive_iff. rew (aiff_true_l P). exact false_ne_true.
Qed.

Ltac decide_relation :=
  let E := lazymatch goal with |- apos ?E => E end in
  lazymatch E with ?R ?x ?y => apply (dec_spec_true (R:=R) x y) end;
  lazy;
  lazymatch goal with
  | |- sprop.seq true true => constructor
  | |- sprop.seq false true => fail "Equation does not hold:" E
  | |- ?G => fail "Decision procedure stuck:" G
  end.
