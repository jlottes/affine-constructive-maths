Require Import interfaces.notation.

Definition StripCoercions `(s:T) := Dummy.

Create HintDb strip_coercions discriminated.
Ltac solve_strip_coercions := typeclasses eauto with strip_coercions nocore.
Tactic Notation "strip_coercions_chain" uconstr(term) := change (StripCoercions term).

Global Hint Extern 100 (StripCoercions ?x) => let t := fresh "t" in pose (t := x); constructor : strip_coercions.

Ltac strip_coercions tm :=
  lazymatch constr:(ltac:(solve_strip_coercions) : StripCoercions tm) with
    (let _ := ?x in _) => x
  end.

Ltac exact_strip_coercions tm :=
  let t := strip_coercions tm in solve [ refine t ].
