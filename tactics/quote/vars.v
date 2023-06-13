Require Import abstract_algebra interfaces.bundled_algebra interfaces.free.generators.
Require Import nat list.
Require Export quote.base.
Require Import strip_coercions.

Definition QuoteFindEnv := empty.
Existing Class QuoteFindEnv.

Lemma quote_find_atom `(f:X ⇾ Y) y {e:QuoteFindEnv} : quote f (abort e) y.
Proof match e with end.

Global Hint Extern 101 (quote ?f ?x ?y) => is_evar x; refine (quote_find_atom f _) : quote.

Lemma quote_var_alt `(f:X ⇾ Y) `{Var_Morphism (X:=X) (Y:=Y) (Γ:=Γ) (f:=f)}
  (n:nat) {b:ListInBounds Γ n} : quote f (var n) (list_nth Γ n).
Proof preserves_var Γ f n.

Definition quote_var `(f:var_morphism X (Y:=Y) Γ) (n:nat) {b:ListInBounds Γ n}
  : quote f (var n) (list_nth Γ n)
:= quote_var_alt f n.


Local Ltac test_eq a b := constr:(ltac:(first [ unify a b; exact true | exact false ]) : bool).

(** Inputs are terms (constrs)
     [ x : X ]
     [ Γ : list X ]
   returns [ Γ ] if x is already in [ Γ ], and [ x :: Γ ] otherwise *)
Ltac union_list x Γ :=
  let rec slow Δ :=
    lazymatch Δ with
    | nil => constr:(cons x Γ)
    | cons ?y ?Δ' =>
      let c := test_eq y x in lazymatch c with
      | true => constr:(Γ)
      | false => slow Δ'
      end
    end in
  let rec fast Δ :=
    lazymatch Δ with
    | nil => slow Γ
    | cons ?y ?Δ' =>
      lazymatch y with
      | x => constr:(Γ)
      | _ => fast Δ'
      end
    end in
  fast Γ.

(** Inputs are terms (constrs)
     [ Γ : list X ]
     [ x : X ]
   returns [ n ] such that [ list_nth Γ n ] is [ x ] *)
Ltac list_index Γ x :=
  let rec slow Δ n :=
    lazymatch Δ with
    | nil => fail "term " x " not in list " Γ
    | cons ?y ?Δ' =>
      let c := test_eq y x in lazymatch c with
      | true => n
      | false => slow Δ' (nat_S n)
      end
    end in
  let rec fast Δ n :=
    lazymatch Δ with
    | nil => slow Γ nat_0
    | cons ?y ?Δ' =>
      lazymatch y with
      | x => n
      | _ => fast Δ' (nat_S n)
      end
    end in
  fast Γ nat_0.


Ltac quote_add_env Γ f quote_tac :=
  let build_env _ :=
    let e := fresh "e" in intro e;
    let t := quote_tac f in
    let rec aux t := lazymatch t with
    | context C [ quote_find_atom _ ?z ] =>
         let a := constr:(quote_find_atom f z) in
         let Q := type of a in
         let t' := context C [ @abort Q e ] in
         let Γ' := aux t' in
         union_list z Γ'
    | _ => Γ
    end in
    let Γ' := aux t in
    exact Γ'
  in
  let T := type of Γ in
  let t := constr:(ltac:(build_env ltac:(0)) : ∀ e:QuoteFindEnv, T) in
  lazymatch t with λ _, ?Γ' => constr:(Γ') end.

Ltac quote_build_env f quote_tac :=
  let Y := lazymatch constr:(quote f) with @quote ?X ?Y _ => Y end in
  quote_add_env constr:(@nil Y) f quote_tac.


Ltac quote_unfold_list Γ :=
  lazymatch Γ with nil => Γ | cons _ _ => Γ | _ => let t := eval red in Γ in t end.

Ltac quote_var f y := first
  [ let cf := constr:(f : var_morphism_t _ _) in
    let vf := lazymatch cf with ?g => g end in
    let Γ := lazymatch type of vf with var_morphism_t _ ?Γ => quote_unfold_list Γ end in
    let n := list_index Γ y in
    refine (quote_var vf n)
  | let H' := constr:(_ : Var_Morphism _ f) in
    let H := lazymatch H' with ?H => H end in
    let Γ := lazymatch type of H with Var_Morphism ?Γ _ => quote_unfold_list Γ end in
    let n := list_index Γ y in
    refine (quote_var_alt _ _ (H:=H) n)
  ].

Global Hint Extern 90 (quote _ ?x ?y) => is_evar x; quote_hint_strip (fun f => quote_var f y) : quote.


Ltac quote_equation ev :=
    lazymatch goal with |- apos ?E =>
      let quote_tac f := quote_wrap f uconstr:(apos (_ ⊸ E)) in
      let ev₀ := ev uconstr:(nil) in
      let Γ' := quote_build_env ev₀ quote_tac in
      let Γ := fresh "Γ" in pose (Γ := Γ');
      let evΓ := ev uconstr:(Γ) in
      let f := fresh "ev" in pose (f := evΓ);
      let H := quote_tac f in
      refine (sprop.andl H _); clear Γ f
    end.

Ltac find_structure_and_quote_equation structure make ev :=
  let Y := lazymatch goal with |- apos (_ = _ :> set_T ?Y) => strip_coercions Y end in
  let X := fresh "X" in
  lazymatch constr:(ltac:(solve [ exact Y | make Y ] ) : structure) with ?s => pose (X := s) end;
  quote_equation ltac:(ev X); clear X.


