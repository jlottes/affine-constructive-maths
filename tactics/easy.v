Require Import interfaces.notation sprop interfaces.aprop tactics.misc.

Ltac fold_complement :=
  lazymatch goal with
  | |- ¬ (?R ?x ?y) => change ((scomplement R) x y)
  end.

Ltac fold_impl := lazymatch goal with |- forall _ : ?P, ?Q => change (impl P Q) end.

Ltac unfold_sflip := lazymatch goal with |- (sflip ?R) ?a ?b => change (R b a) end.

Ltac refl :=
  lazymatch goal with
  | |- apos _ => refine (reflexivity _ _)
  | |- _ => try fold_complement; apply sreflexivity
  end.

Ltac sym :=
  lazymatch goal with
  | |- apos _ => refine (andl (symmetry _ _ _) _)
  | |- _ => (fold_complement; apply ssymmetry; red) || apply ssymmetry
  end.

Tactic Notation "trans" uconstr(y) :=
  lazymatch goal with
  | |- apos _ => refine (andl (transitivity _ _ y _) (conj _ _))
  | |- _ => ((fold_impl; apply stransitivity with y; red) || apply stransitivity with y)
  end.

Tactic Notation "antisym" :=
  match goal with
  | |- iff ?P ?Q => split
  | _ => apply santisymmetry
  end.
Tactic Notation "antisym" "with" open_constr(R) := apply (santisymmetry (R:=R)).

(** Taken from Coq.Init.Tactics *)
Ltac easy :=
  let rec use_hyp H :=
    match type of H with
    | and _ _ => exact H || destruct_hyp H
    | _ => try solve [inversion H]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H : and _ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H : _ |- _ => solve [inversion H]
    | _ => idtac
    end in
  let do_atom :=
    solve [ trivial | refl | sym; trivial | contradiction | exact _ ] in
  let rec do_ccl :=
    try do_atom;
    repeat (do_intro; try do_atom);
    solve [ split; do_ccl ] in
  solve [ do_atom | use_hyps; do_ccl ] ||
  fail "Cannot solve this goal".

Tactic Notation "now" tactic(t) := t; easy.

(*
Notation "'by_easy' '(' P ')'" := ltac:(
  let P' := constr:(P) in
  match type of P' with Ω => set_goal (apos P') | _ => set_goal P' end;
  easy) (only parsing).
*)