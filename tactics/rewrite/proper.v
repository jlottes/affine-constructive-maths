Require Import prelude tactics.misc.

Create HintDb proper discriminated.
Ltac solve_proper := typeclasses eauto with proper nocore.
Ltac proper_solution H := constr_from_tac H ltac:(solve_proper).
