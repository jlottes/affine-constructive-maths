Require Export interfaces.set.

Definition SetLambdaDerivation@{i} {X Y : set@{i}} (f : X → Y) := IsFun f.
Existing Class SetLambdaDerivation.

Definition set_lambda@{i} : ∀ {X Y : set@{i} } (f : X → Y) {H:SetLambdaDerivation f}, X ⇾ Y := @make_fun.
Notation "'λₛ' x .. y , t" := (set_lambda (fun x => .. (set_lambda (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).
