Require Import interfaces.notation interfaces.aprop tactics.misc.

Ltac rewrite_quantifiers tm :=
  let inner var body :=
    let body' := rewrite_quantifiers body in exact body'
  in
  lazymatch tm with
  | ∀ binder : ?A, ?body => let res := eval_under_binder inner binder A body in constr:(all res)
  | ∃ binder : ?A, ?body => let res := eval_under_binder inner binder A body in constr:(aex res)
  | apos ?P => constr:(P)
  end.

Ltac change_quantifiers :=
  progress lazymatch goal with |- ?G => let G' := rewrite_quantifiers G in change (apos G') end.
