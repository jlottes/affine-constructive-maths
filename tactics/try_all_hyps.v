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
Ltac hyp_stack := constr:(ltac:(revert_clearbody_all;constructor) : Dummy).

Ltac assert_fails' tac :=
  tryif (once tac) then gfail 0 tac "succeeds" else idtac.
Ltac assert_succeeds' tac :=
  tryif (assert_fails' tac) then gfail 0 tac "fails" else idtac.
Tactic Notation "assert_succeeds" tactic3(tac) :=
  assert_succeeds' tac.
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
        | step stack' out ]
      | _ => cont out
    end
  in let stack := hyp_stack in step stack dummy.

(** Try [ tac H ] for every hypothesis H, with back-tracking.
   Done in two stages; the set of hypotheses is filtered down to those that would
   succeed, limiting the back-tracking. *)
Tactic Notation "try_all_hyps" tactic(tac) :=
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

Ltac use_assumption := try_all_hyps (fun H => exact H).
Ltac check_is_prop := lazymatch goal with |- ?G => lazymatch type of G with Prop => idtac | SProp => idtac end end.

Global Hint Extern 1 => check_is_prop; use_assumption : typeclass_instances.
