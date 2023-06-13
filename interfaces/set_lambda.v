Require Export interfaces.set interfaces.set_lambda.notation.
Require Import tactics.set_internalize.

Notation "'set:(' expr )" := ltac:(set_internalize_tac expr) (only parsing, expr constr at level 200).

Ltac solve_SetLambda := match goal with |- SetLambdaDerivation ?expr =>
  let f := constr:( set:(expr) ) in exact (func_is_fun f) end.

Global Hint Extern 20 (SetLambdaDerivation _) => solve_SetLambda : typeclass_instances.
