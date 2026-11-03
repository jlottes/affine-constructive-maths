Require Import interfaces.notation interfaces.aprop logic.relations.
Require Import implementations.bool theory.set.
Require Import easy rewrite.

Local Open Scope bool_scope.

Lemma dec_spec_by_iff `{IsDec (R:=R)} {x} {P}
  : (R x ⧟ P) → if dec R x then P else P ᗮ.
Proof. intro Q. generalize (dec_spec R x); destruct (dec R x); apply Q. Qed.

Lemma dec_spec_dual `{IsDec (R:=R)} x `{!DeMorganDual (R x) P}
  : if dec R x then R x else P.
Proof.
  generalize (dec_spec R x).
  destruct (dec R x); [ easy | apply (demorgan_dual (R x)) ].
Qed.
Arguments dec_spec_dual {_} R {d _} x {_ _}.

Lemma dec_spec_andb `{IsDec (R:=R₁)} `{IsDec (R:=R₂)} x₁ x₂
  : if dec R₁ x₁ && dec R₂ x₂ then (R₁ x₁ ∧ R₂ x₂) else (R₁ x₁)ᗮ ∨ (R₂ x₂)ᗮ.
Proof. generalize (dec_spec R₁ x₁), (dec_spec R₂ x₂).
  destruct (dec R₁ x₁), (dec R₂ x₂). 
+ now split.
+ now right.
+ now left.
+ now left.
Qed.

Lemma dec_spec_true `{IsDec (R:=R)} x : R x ⧟ dec R x = true.
Proof. generalize (dec_spec R x). destruct (dec R x).
+ intro P. now rew (aiff_true_l P).
+ intro P. apply by_contrapositive_iff. rew (aiff_true_l P). exact false_ne_true.
Qed.

Lemma dec_true `{IsDec (R:=R)} x : sprop.seqt (dec R x) true → R x.
Proof. intro e. exact (sprop.andl (sprop.andr (dec_spec_true x)) e). Qed.

(** On success the proof is the single application [dec_true x (seq_refl true)]:
    the kernel checks [dec R x ≡ true] by conversion. The decision is evaluated
    with [lazy] only to report a failure. *)
Ltac decide_relation :=
  let E := lazymatch goal with |- apos ?E => E end in
  lazymatch E with ?R ?x =>
    first
    [ exact (dec_true (R:=R) x (sprop.seq_refl true))
    | let b := eval lazy in (dec R x) in
      lazymatch b with
      | false => fail 1 "Equation does not hold:" E
      | _ => fail 1 "Decision procedure stuck:" b
      end ]
  end.

