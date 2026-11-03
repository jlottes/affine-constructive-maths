(** Extend typeclass resolution to consider all possible _coercions_ of hypotheses in the current context.
  The standard resolution behavior does consider hypotheses, but not coercions from them.
  This effectively allows coercions to be used to declare "forward mode" typeclass hints.

  The hypothesis loop is written in Ltac2. It reads the context directly
  ([Control.hyps]) instead of reverting and reintroducing it, tries each
  hypothesis once, and is a single step for the Ltac1 debugger. Only the
  elaboration of a hypothesis against the goal goes through Ltac1
  ([simple notypeclasses refine h]), because that is where Rocq inserts
  coercions: Ltac2 cannot pretype a hypothesis chosen at run time against an
  expected type with coercions (an antiquoted constr is taken as already typed).
  On a projection-headed goal ([apos P]) only class-typed hypotheses take that
  path; the others are tried by unification alone, which is much cheaper
  (see [hyp_closes_goal]).
*)

Require Import prelude.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Inductive Dummy : SProp := dummy : Dummy.

Ltac assert_fails' tac :=
  tryif (once tac) then gfail 0 tac "succeeds" else idtac.
Tactic Notation "assert_fails" tactic3(tac) :=
  assert_fails' tac.

(** Set to [true] ([Ltac2 Set use_assumption_verbose := true.]) to print the
    hypothesis that closes a goal, as a complement to [Typeclasses Debug]. *)
Ltac2 mutable use_assumption_verbose := false.

Ltac2 fail_msg (s : string) : unit :=
  Control.zero (Tactic_failure (Some (Message.of_string s))).

(** The goal lives in [Prop] or [SProp], so it does not matter (in principle)
    which instance is chosen. *)
Ltac2 goal_is_prop_or_sprop () : bool :=
  let s := Constr.type (Control.goal ()) in
  Bool.or (Constr.equal s 'SProp) (Constr.equal s 'Prop).

Ltac2 goal_has_evar () : bool := Constr.has_evar (Control.goal ()).

(** Try [tac h] on every hypothesis [h], most recent first, with backtracking
    (like [multimatch]).  Hypotheses whose type contains evars are skipped. *)
Ltac2 try_all_hyps_tac (tac : ident -> unit) : unit :=
  let rec go hs :=
    match hs with
    | [] => fail_msg "try_all_hyps: no hypothesis works"
    | h :: rest =>
      let (id, _, ty) := h in
      if Constr.has_evar ty then go rest
      else Control.plus (fun () => tac id) (fun _ => go rest)
    end
  in go (List.rev (Control.hyps ())).

(** [simple notypeclasses refine h; fail] succeeds exactly when [h], possibly
    through coercions, closes the goal outright. *)
Ltac2 refine_hyp_closes_goal (h : ident) : unit :=
  let tac := ltac1:(h |- simple notypeclasses refine h; fail) in
  tac (Ltac1.of_ident h);
  if use_assumption_verbose
  then Message.print (Message.concat (Message.of_string "use_assumption: ") (Message.of_ident h))
  else ().

(** Whether [c] is headed by a primitive projection, as [apos P] is. *)
Ltac2 rec proj_headed (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => proj_headed f
  | Constr.Unsafe.Proj _ _ _ => true
  | _ => false
  end.

Ltac2 is_sprop_or_prop (ty : constr) : bool :=
  let s := Constr.type ty in
  Bool.or (Constr.equal s 'SProp) (Constr.equal s 'Prop).

(** [h] closes the goal by unification alone, without coercions. *)
Ltac2 unify_hyp_closes_goal (h : ident) : unit :=
  let c := Control.hyp h in
  Unification.unify_with_full_ts (Constr.type c) (Control.goal ());
  Control.refine (fun () => c);
  if use_assumption_verbose
  then Message.print (Message.concat (Message.of_string "use_assumption: ") (Message.of_ident h))
  else ().

(** On a projection-headed goal ([apos P]), only a hypothesis whose type is an
    (S)Prop class can reach the goal through a coercion (a [:>] field of
    [apos] type); it keeps the elaboration path.  Every other hypothesis (an
    [apos] fact, or a Type-sorted structure or element) can close the goal
    only up to conversion, so it is tried by unification alone.  This matters
    because [refine]'s coercion fallback recomputes the goal's head class by
    fully reducing the goal on every failing hypothesis; on membership atoms
    built by [set:(…)] that costs milliseconds per hypothesis, while a failing
    unification is free. *)
Ltac2 hyp_closes_goal (h : ident) : unit :=
  if proj_headed (Control.goal ()) then
    let ty := Constr.type (Control.hyp h) in
    if Bool.and (is_sprop_or_prop ty) (Bool.neg (proj_headed ty))
    then refine_hyp_closes_goal h
    else unify_hyp_closes_goal h
  else refine_hyp_closes_goal h.

Ltac2 use_assumption_tac () : unit := try_all_hyps_tac hyp_closes_goal.

(** Hint bodies, one atomic step each for the Ltac1 debugger.

   Solving a goal containing evars from a hypothesis risks instantiating them
   incorrectly: unification may see through definitional walls (e.g. carrier-identity
   constructions) and pick a hypothesis that determines the evars wrongly.  So on
   goals with evars, demote this greedy fallback below all pattern-keyed hints:
   the correct structured instance wins if one is registered, while coercion-fills
   with no competing hint still resolve as before, just later. *)
Ltac2 use_assumption_no_evars_tac () : unit :=
  if goal_is_prop_or_sprop () then
    if goal_has_evar () then fail_msg "use_assumption: goal has evars"
    else use_assumption_tac ()
  else fail_msg "use_assumption: goal is not a (S)Prop".

Ltac2 use_assumption_has_evar_tac () : unit :=
  if goal_is_prop_or_sprop () then
    if goal_has_evar () then use_assumption_tac ()
    else fail_msg "use_assumption: goal has no evars"
  else fail_msg "use_assumption: goal is not a (S)Prop".

(** Ltac1 entry points.

   An [ltac2:(…)] quotation without bound variables is evaluated eagerly when
   the Ltac1 tactic containing it is passed as an argument (e.g. to
   [assert_fails]); the leading [idtac;] makes the body a sequence, which is
   evaluated only when run. A quotation with bound variables is an Ltac1
   function of those variables and must be applied, hence [let f := … in f tac]. *)
Tactic Notation "try_all_hyps" tactic(tac) :=
  let f := ltac2:(t |- try_all_hyps_tac (fun h => Ltac1.apply t [Ltac1.of_ident h] Ltac1.run)) in f tac.

Ltac use_assumption := idtac; ltac2:(use_assumption_tac ()).
Ltac check_is_prop := idtac; ltac2:(if goal_is_prop_or_sprop () then () else fail_msg "goal is not a (S)Prop").
Ltac check_no_evars := idtac; ltac2:(if goal_has_evar () then fail_msg "goal has evars" else ()).
Ltac check_has_evar := idtac; ltac2:(if goal_has_evar () then () else fail_msg "goal has no evars").

Ltac use_assumption_no_evars := idtac; ltac2:(use_assumption_no_evars_tac ()).
Ltac use_assumption_has_evar := idtac; ltac2:(use_assumption_has_evar_tac ()).

Global Hint Extern 1  => use_assumption_no_evars : typeclass_instances.
Global Hint Extern 99 => use_assumption_has_evar : typeclass_instances.
