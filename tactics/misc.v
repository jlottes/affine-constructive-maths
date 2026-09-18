Require Import interfaces.notation prop_eq sprop.

Ltac get_goal := lazymatch goal with |- ?G => uconstr:(G) end.
Ltac unify_goal t := lazymatch goal with |- ?g => unify g t end.

Ltac constr_from_tac T tac :=
  lazymatch constr:(ltac:(tac) : T) with ?x => x end.

Ltac eunify u c :=
  let t := constr_from_tac constr:(c ≡ c) ltac:( refine ( eq_refl u ) ) in
  lazymatch t with (eq_refl ?u') => constr:(u') end.

Ltac echange_tac t := let G := get_goal in let t' := eunify t G in change t'.
Tactic Notation "echange" uconstr(t) := echange_tac t.

Ltac get_instance T := constr_from_tac T ltac:(exact _).


Ltac sapply_1_tac utm :=
  let g := get_goal in
  let t := constr:(ltac:(refine utm; exact _) : _ → g) in
  let p := lazymatch t with ?t' => t' end in
  simple notypeclasses refine (p _).

Ltac sapply_2_tac utm :=
  let g := get_goal in
  let t := constr:(ltac:(refine utm; exact _) : _ → _ → g) in
  let p := lazymatch t with ?t' => t' end in
  simple notypeclasses refine (p _ _).

Ltac sapply_3_tac utm :=
  let g := get_goal in
  let t := constr:(ltac:(refine utm; exact _) : _ → _ → _ → g) in
  let p := lazymatch t with ?t' => t' end in
  simple notypeclasses refine (p _ _ _).

Tactic Notation "sapply_1" uconstr(term_to_apply) := sapply_1_tac term_to_apply.
Tactic Notation "sapply_2" uconstr(term_to_apply) := sapply_2_tac term_to_apply.
Tactic Notation "sapply_3" uconstr(term_to_apply) := sapply_3_tac term_to_apply.

Ltac normalize_proof tac :=
  match goal with |- ?G =>
    let t := constr:(ltac:(tac) : G) in
    let t' := eval lazy in t in exact t'
  end.

Ltac learn tm :=
  let t := type of tm in lazymatch goal with H : t |- _ => fail | _ => pose proof tm end.


(** [real_progress tac] runs [tac] and fails if the goal didn't change
    syntactically (modulo universe instances). Stricter than the built-in
    [progress], which is fooled by fresh universe metavariables — useful
    around [change] or other tactics that re-elaborate the goal and refresh
    its universes without changing its shape. *)
Ltac real_progress tac :=
  let G := lazymatch goal with |- ?G => G end in
  tac tt;
  lazymatch goal with
  | |- ?G' => tryif constr_eq G G' then fail else idtac
  end.


(** Given a constr [body] under the given [binder] with type [T],
   runs [tac var body] in a context where the (possibly renamed) binder
   has been added as the hypothesis [var].

   Returns the constr [ λ binder: T, result ], where [result] is the
   result of [tac] (via [exact]), but with [var] renamed back to [binder].
*)
Ltac eval_under_binder tac binder T body :=
  let var := fresh binder in
  let body_var := fresh "body" in
  let res := constr:(
    λ var : T, let body_var := match var with binder => body end in
    ltac:(
      let b := eval red in body_var in clear body_var;
      tac var b
    )
  ) in
  lazymatch res with
  | λ var : ?T, let _ := ?body in ?result =>
    constr:(λ binder : T, match binder with var => result end)
  end.


Ltac eval_under_let tac binder T defn body :=
  let var := fresh binder in
  let body_var := fresh "body" in
  let res := constr:(
    let var : T := defn in let body_var := match var with binder => body end in
    ltac:(
      let b := eval red in body_var in clear body_var;
      tac var b
    )
  ) in
  lazymatch res with
  | let var : ?T := ?defn in let _ := ?body in ?result =>
    constr:(let binder : T := defn in match binder with var => result end)
  end.


Ltac eval_under_binder2 tac binder1 T1 binder2 T2 body :=
  let var1 := fresh binder1 in
  let var2 := fresh binder2 in
  let body_var := fresh "body" in
  let res := constr:(
    λ (var1 : T1) (var2 : T2),
    let body_var := match var1 with binder1 => match var2 with binder2 => body end end in
    ltac:(
      let b := eval red in body_var in clear body_var;
      tac var1 var2 b
    )
  ) in
  lazymatch res with
  | λ (var1 : ?T1) (var2 : ?T2), let _ := ?body in ?result =>
    constr:(λ (binder1 : T1) (binder2 : T2),
      match binder1 with var1 => match binder2 with var2 => result end end)
  end.


(** Given a constr [body] under the given [binder] with type [T],
   runs [tac var body] in a context where the (possibly renamed) binder
   has been added as the hypothesis [var].

   The tactic [tac] is expected to "return" via [ exact ( res, body' ) ]
   where [var] may appear in [body'] but not [res].

   Returns the constr [ (res, λ var: T, body') ], but with [var] renamed
   back to the original [binder].
*)
Ltac eval_under_binder_pair tac binder T body :=
  let res := eval_under_binder tac binder T body in
  lazymatch res with
  | λ var : ?T, (?res, ?body) =>  constr:( (res, λ var : T, body) )
  end.
