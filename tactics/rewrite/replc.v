Require Export rewrite.
Require Import relation_notation.


Tactic Notation "replc" constr(x) "with" uconstr(y) :=
  let E := fresh "E" in assert (x = y) as E; [| rew E; clear E ].

Tactic Notation "replc" constr(x) "with" uconstr(y) "by" tactic3(tac) :=
  let E := fresh "E" in assert (x = y) as E by tac; rew E; clear E.

Tactic Notation "replc" constr(x₁) "with" uconstr(y₁) "by" tactic3(tac₁)
                "and"   constr(x₂) "with" uconstr(y₂) "by" tactic3(tac₂) :=
  let E₁ := fresh "E" in let E₂ := fresh "E" in
  assert (x₁ = y₁ ∧ x₂ = y₂) as [E₁ E₂] by (split; [tac₁ | tac₂]);
  rew [ E₁ | E₂ ]; clear E₁ E₂.

Tactic Notation "replc" constr(x) "with" uconstr(y) "using" uconstr(R) :=
  let E := fresh "E" in assert (R x y) as E; [| rew E; clear E ].
