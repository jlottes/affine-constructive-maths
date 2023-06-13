Require Import interfaces.aprop theory.set.
Require Import interfaces.set_lambda.notation.

(** Define 𝒫 X ≡ subset X to be convertible to X ⇾ Ω.
    We give subsets a type with a distinct name to enable coercions specific to subsets. *)

Definition subset (X:set) := func X Ω.
Notation 𝒫 := subset.
Identity Coercion subset_func : subset >-> func.
Global Hint Extern 2 (Equiv (subset ?X)) => change (Equiv (func X AProp_set)) : typeclass_instances.

Canonical Structure subset_set (X:set) := {| set_T := subset X; set_eq := ext_eq; set_is_set := func_is_set |}.
Notation "'𝒫'" := subset_set (only printing).

Definition subset_comprehension@{i} {X : set@{i} } : ∀ (f : X → AProp_set) {H:SetLambdaDerivation f}, 𝒫 X := @make_fun X Ω.

Notation "{ x | P }" := (subset_comprehension (fun x => P : Ω )) (only parsing) : set_scope.
Notation "{ x : X | P }" := (subset_comprehension (X:=X) (fun x => P : Ω )) (only parsing) : set_scope.
Notation "{ x : X | P }" := (subset_comprehension (X:=X) (fun x => P )) (only printing) : set_scope.
