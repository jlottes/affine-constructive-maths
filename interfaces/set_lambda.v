Require Export interfaces.set interfaces.set_lambda.notation.
Require Import tactics.set_internalize.

Notation "'set:(' expr )" := ltac:(set_internalize_tac expr) (only parsing, expr constr at level 200).

Global Hint Extern 20 (SetLambdaDerivation _) => solve_SetLambda : typeclass_instances.

