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


Local Ltac ecut_1 g := let T1 := fresh "T" in evar (T1:Type);
                       unify_goal (T1 → g).
Local Ltac ecut_2 g := let T1 := fresh "T" in evar (T1:Type);
                       let T2 := fresh "T" in evar (T2:Type);
                       unify_goal (T1 → T2 → g).
Local Ltac ecut_3 g := let T1 := fresh "T" in evar (T1:Type);
                       let T2 := fresh "T" in evar (T2:Type);
                       let T3 := fresh "T" in evar (T3:Type);
                       unify_goal (T1 → T2 → T3 → g).

Local Ltac strip_let_1 t := lazymatch t with (let _ := _ in ?u) => u end.
Local Ltac strip_let_2 t := lazymatch t with (let _ := _ in
                                              let _ := _ in ?u) => u end.
Local Ltac strip_let_3 t := lazymatch t with (let _ := _ in
                                              let _ := _ in
                                              let _ := _ in ?u) => u end.

Local Ltac rapply_1 t := simple notypeclasses refine (t _).
Local Ltac rapply_2 t := simple notypeclasses refine (t _ _).
Local Ltac rapply_3 t := simple notypeclasses refine (t _ _ _).


Local Ltac sapply_gen ecut strip_let rapply utm :=
  let g := get_goal in
  let t := constr:(ltac:(ecut g; refine utm; exact _)) in
  let p := strip_let t in
  rapply p.

Ltac sapply_1_tac := sapply_gen ecut_1 strip_let_1 rapply_1.
Ltac sapply_2_tac := sapply_gen ecut_2 strip_let_2 rapply_2.
Ltac sapply_3_tac := sapply_gen ecut_3 strip_let_3 rapply_3.

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
