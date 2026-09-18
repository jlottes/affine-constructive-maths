Require Import prelude tactics.misc.

Create HintDb proper discriminated.
#[global] Hint Constants Opaque : proper.
#[global] Hint Variables Opaque : proper.
Ltac solve_proper := typeclasses eauto with proper nocore.
Ltac proper_solution H := constr_from_tac H ltac:(solve_proper).

Create HintDb rewrite_swap_tag discriminated.
Inductive RewriteSwapTag {A} (term : A) := DeclareRewriteSwapTag : forall _ : A, RewriteSwapTag term.
Arguments DeclareRewriteSwapTag {_ _} _.

Ltac swap_rewrite_tag t :=
  let s := constr:( ltac:(
      solve [ typeclasses eauto with rewrite_swap_tag nocore
            | idtac "No instance to swap tag of" t;
              fail 1 "No instance to swap tag of" t ]
    ) : RewriteSwapTag t ) in
  lazymatch s with DeclareRewriteSwapTag ?t' => constr:(t') end.

