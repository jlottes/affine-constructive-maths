(** Implementations of [tauto] and [intuition] tactics, copy-pasted from [ Coq.Init.Tauto ],
  with tiny edits to make the tactics work with SProp.
*)

Require Import interfaces.notation sprop.

Declare ML Module "tauto_plugin".

Local Ltac not_dep_intros :=
  repeat match goal with
  | |- (forall (_: ?X1), ?X2) => intro
  | |- (not ?P) => change (P → False); intro
  end.

Local Ltac axioms flags :=
  match reverse goal with
    | |- ?X1 => is_unit_or_eq flags X1; constructor 1
    | _:?X1 |- _ => is_empty flags X1; elimtype X1; assumption
    | _:?X1 |- ?X1 => assumption
  end.

Local Ltac simplif flags :=
  not_dep_intros;
  repeat
     (match reverse goal with
      | id: ?X1 |- _ => is_conj flags X1; elim id; do 2 intro; clear id
      | id: (iff _ _) |- _ => elim id; do 2 intro; clear id
      | id: (not ?P) |- _ => change (P → False) in id
      | id: ?X1 |- _ => is_disj flags X1; elim id; intro; clear id
      | id0: (forall (_: ?X1), ?X2), id1: ?X1|- _ =>
    (* generalize (id0 id1); intro; clear id0 does not work
       (see Marco Maggiesi's BZ#301)
    so we instead use Assert and exact. *)
    assert X2; [exact (id0 id1) | clear id0]
      | id: forall (_ : ?X1), ?X2|- _ =>
        is_unit_or_eq flags X1; cut X2;
    [ intro; clear id
    | (* id : forall (_: ?X1), ?X2 |- ?X2 *)
      cut X1; [exact id| constructor 1; fail]
    ]
      | id: forall (_ : ?X1), ?X2|- _ =>
        flatten_contravariant_conj flags X1 X2 id
  (* moved from "id:(?A/\?B)->?X2|-" to "?A->?B->?X2|-" *)
      | id: forall (_: iff ?X1 ?X2), ?X3|- _ =>
        assert (forall (_: forall _:X1, X2), forall (_: forall _: X2, X1), X3)
    by (do 2 intro; apply id; split; assumption);
          clear id
      | id: forall (_:?X1), ?X2|- _ =>
        flatten_contravariant_disj flags X1 X2 id
  (* moved from "id:(?A\/?B)->?X2|-" to "?A->?X2,?B->?X2|-" *)
      | |- ?X1 => is_conj flags X1; split
      | |- (iff _ _) => split
      | |- (not ?P) => change (P → False)
      end;
      not_dep_intros).

Local Ltac tauto_intuit flags t_reduce t_solver :=
 let rec t_tauto_intuit :=
 (simplif flags; axioms flags
 || match reverse goal with
    | id:forall(_: forall (_: ?X1), ?X2), ?X3|- _ =>
  cut X3;
    [ intro; clear id; t_tauto_intuit
    | cut (forall (_: X1), X2);
        [ exact id
        | generalize (fun y:X2 => id (fun x:X1 => y)); intro; clear id;
          solve [ t_tauto_intuit ]]]
    | id:forall (_:not ?X1), ?X3|- _ =>
  cut X3;
    [ intro; clear id; t_tauto_intuit
    | cut (not X1); [ exact id | clear id; intro; solve [t_tauto_intuit ]]]
    | |- ?X1 =>
        is_disj flags X1; solve [left;t_tauto_intuit | right;t_tauto_intuit]
    end
  ||
  (* NB: [|- _ -> _] matches any product *)
  match goal with | |- forall (_ : _),  _ => intro; t_tauto_intuit
  |  |- _  => t_reduce;t_solver
  end
  ||
  t_solver
 ) in t_tauto_intuit.

Local Ltac intuition_gen flags solver := tauto_intuit flags reduction_not_iff solver.
Local Ltac tauto_intuitionistic flags := intuition_gen flags fail || fail "tauto failed".
(* Local Ltac tauto_classical flags :=
  (apply_nnpp || fail "tauto failed"); (tauto_intuitionistic flags || fail "Classical tauto fail
ed"). *)
Local Ltac tauto_gen flags := tauto_intuitionistic flags (* || tauto_classical flags *).

(*
Ltac tauto := with_uniform_flags ltac:(fun flags => tauto_gen flags).
Ltac dtauto := with_power_flags ltac:(fun flags => tauto_gen flags).

Local Ltac intuition_then tac := with_uniform_flags ltac:(fun flags => intuition_gen flags tac).
Local Ltac dintuition_then tac := with_power_flags ltac:(fun flags => intuition_gen flags tac).

Tactic Notation "intuition" := intuition_then ltac:(trivial).
Tactic Notation "intuition" tactic(t) := intuition_then t.

Tactic Notation "dintuition" := dintuition_then ltac:(trivial).
Tactic Notation "dintuition" tactic(t) := dintuition_then t.
*)

Ltac tauto := with_power_flags ltac:(fun flags => tauto_gen flags).
Local Ltac intuition_then tac := with_power_flags ltac:(fun flags => intuition_gen flags tac).
Tactic Notation "intuition" := intuition_then ltac:(trivial).
Tactic Notation "intuition" tactic(t) := intuition_then t.

