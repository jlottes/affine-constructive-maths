Require Export interfaces.set.

Definition SetLambdaDerivation@{u} {X Y : set@{u}} (f : X → Y) := IsFun f.
Existing Class SetLambdaDerivation.

Definition set_lambda@{u} : ∀ {X Y : set@{u}} (f : X → Y) {H:SetLambdaDerivation f}, X ⇾ Y := @func_make.
Notation "'λₛ' x .. y , t" := (set_lambda (fun x => .. (set_lambda (fun y => t)) ..))
  (at level 10, x binder, y binder, t at level 200).

(** Pretty-printing for binary destructuring lambdas at the top level.
    When the pattern lambda is nested inside other lambdas, the recursive
    [λ x .. y, t] form absorbs the pattern binder; the [let '(...)]
    printing notation below recovers the destructuring in the body. *)
Notation "'λₛ' ' '(' a ',' b ')' ',' t" :=
  (set_lambda (fun pat => let p := pat in let a := proj1 p in let b := proj2 p in t))
  (at level 10, t at level 200, only printing,
   format "'λₛ'  ''' '(' a ','  b ')' ','  t").

(** Pretty-printing for doubly-nested binary destructuring lambdas. *)
Notation "'λₛ' ' '(' '(' x1 ',' y1 ')' ',' '(' x2 ',' y2 ')' ')' ',' t" :=
  (set_lambda (fun pat =>
   let z := pat in
   let a := proj1 z in let b := proj2 z in
   let w := a in let x1 := proj1 w in let y1 := proj2 w in
   let v := b in let x2 := proj1 v in let y2 := proj2 v in
   t))
  (at level 10, t at level 200, only printing,
   format "'λₛ'  ''' '(' '(' x1 ','  y1 ')' ','  '(' x2 ','  y2 ')' ')' ','  t").

