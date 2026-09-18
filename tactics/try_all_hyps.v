(** Extend typeclass resolution to consider all possible _coercions_ of hypotheses in the current context.
  The standard resolution behavior does consider hypotheses, but not coercions from them.
  This effectively allows coercions to be used to declare "forward mode" typeclass hints.
*)

Require Import prelude.

Local Ltac debug_msg tac := idtac.
(* Local Ltac debug_msg tac := match goal with |- ?G => tac G end. *)

Inductive Dummy : SProp := dummy : Dummy.

(** Linear iteration over hypotheses. From a Jonathan Leivent post to coq-club:
   https://coq-club.inria.narkive.com/Gog56von/a-trick-for-iterating-over-hypotheses *)
Ltac revert_clearbody_all := repeat lazymatch goal with H:_ |- _ => try clearbody H; revert H end.
Ltac hyp_stack := constr:(ltac:(revert_clearbody_all; intros; exact dummy) : Dummy).

Ltac assert_fails' tac :=
  tryif (once tac) then gfail 0 tac "succeeds" else idtac.
Tactic Notation "assert_fails" tactic3(tac) :=
  assert_fails' tac.

(** Filter the "stack" of hypotheses, keeping only those for which (tac H) would succeed.
   Pass the new "stack" to the continuation cont. *)
Ltac filtered_hyp_stack tac cont :=
  let rec step stack out :=
    lazymatch stack with (?stack' ?H) =>
        first [
          assert_fails (let t := type of H in has_evar t);
          assert_succeeds tac H;
          let out' := constr:((fun _ => out) H) in
          step stack' out' || fail 1
        | let _ := debug_msg ltac:(fun G => idtac "skipping" H) in 
          step stack' out ]
      | _ => cont out
    end
  in let stack := hyp_stack in step stack dummy.

(** Try [ tac H ] for every hypothesis H, with back-tracking.
   Done in two stages; the set of hypotheses is filtered down to those that would
   succeed, limiting the back-tracking. *)
Tactic Notation "try_all_hyps" tactic(tac) :=
  let _ := debug_msg ltac:(fun G => idtac "try_all_hyps on" G) in
  let use H := let _ := debug_msg ltac:(fun G => idtac "using" H "on" G) in tac H
  in let rec step stack :=
    multimatch stack with
    | ((fun _ => ?stack') ?H) => use H
    | ((fun _ => ?stack') ?H) =>
       let _ := debug_msg ltac:(fun _ => idtac "using" H "failed") in step stack'
    end
  in filtered_hyp_stack tac step.


(** Extend typeclass resolution to try [ exact H ] with every hypothesis, but
   only for (S)Props, since it does not matter (in principle) which instance is chosen.
*)

Ltac use_assumption := try_all_hyps (fun H => simple notypeclasses refine H; fail).
Ltac check_is_prop := lazymatch goal with |- ?G => lazymatch type of G with Prop => idtac | SProp => idtac end end.

(** Solving a goal containing evars from a hypothesis risks instantiating them
   incorrectly: unification may see through definitional walls (e.g. carrier-identity
   constructions) and pick a hypothesis that determines the evars wrongly.  So on
   goals with evars, demote this greedy fallback below all pattern-keyed hints:
   the correct structured instance wins if one is registered, while coercion-fills
   with no competing hint still resolve as before, just later. *)
Ltac check_no_evars := lazymatch goal with |- ?G => assert_fails (has_evar G) end.
Ltac check_has_evar := lazymatch goal with |- ?G => has_evar G end.

Global Hint Extern 1  => check_is_prop; check_no_evars; use_assumption : typeclass_instances.
Global Hint Extern 99 => check_is_prop; check_has_evar; use_assumption : typeclass_instances.
