Require Import abstract_algebra interfaces.bundled_notation.
Require Import theory.projected_set.
Require Import nat list.
Require Import strip_coercions.

(** A name for the generators *)
Class Var (X:set) := var : Nat → X.
Arguments var {X _} _%nat.

(** [ Var_Morphism Γ f ] means [ f ] sends [ var n ] to the [n]th element of [ Γ ] *)
Class Var_Morphism {X Y} {v:Var X} (Γ:list Y) (f:X ⇾ Y) : SProp
  := preserves_var (n:Nat) {b:ListInBounds Γ n} : f (var n) = list_nth Γ n.
Arguments preserves_var {X Y _} Γ f {_} n%nat {_}.

Set Implicit Arguments.

Record > has_var X := HasVar { op_var : Var X }.
Arguments op_var {X} _.

Global Hint Extern 4 (Var ?X) => let t := strip_coercions X in refine (op_var t) : typeclass_instances.

Record var_set :=
{ var_set_car :> set
; #[canonical=no] var_set_var :> has_var var_set_car
}.
Global Hint Extern 2 (StripCoercions (var_set_car ?X)) => strip_coercions_chain X : strip_coercions.
Definition make_var_set : ∀ (X:set) {v:Var X}, var_set := @Build_var_set.
Arguments make_var_set X {v}.

Record var_morphism_t (X:var_set) {Y:set} (Γ:list Y) :=
{ var_morphism_func :> func X Y
; #[canonical=no] var_morphism_prop :> Var_Morphism Γ var_morphism_func
}.
Global Hint Extern 2 (StripCoercions (var_morphism_func ?f)) => strip_coercions_chain f : strip_coercions.
Global Hint Extern 4 (Var_Morphism _ ?f) => exact_strip_coercions f : typeclass_instances.
Canonical Structure var_morphism (X:var_set) {Y:set} (Γ:list Y)
  := projected_set (@var_morphism_func X Y Γ).
Definition make_var_morphism : ∀ {X:var_set} {Y:set} (Γ:list Y) (f:X ⇾ Y),
  Var_Morphism Γ f → var_morphism X Γ := @Build_var_morphism_t.
Arguments make_var_morphism {X Y} Γ f {_}.
