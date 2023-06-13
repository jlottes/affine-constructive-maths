Require Import interfaces.notation prop_eq sprop srelations tactics.misc logic.aprop.
Require Export rewrite.proper rewrite.base srewrite arewrite.

Local Ltac clear_tags P := eval unfold arewrite_tag_l, arewrite_tag_r, srewrite_tag_l, srewrite_tag_r in P.
Ltac hyp_rewrite := hyp_rewrite_gen clear_tags.
Ltac goal_rewrite := goal_rewrite_gen clear_tags.

Local Definition needs_impl_cast {E:Prop} (p:E) := p.

Ltac wrap_tag atag_eq stag_eq E :=
  let inner := (
    let false_dummy_var := fresh "false_dummy_var" in
    let aux t := simple notypeclasses refine (λ false_dummy_var:False, t); elimtype False; assumption in
    solve [ aux uconstr:(atag_eq _ _ _ _ E)
          | aux uconstr:(stag_eq _ _ _ _ E)
          | aux uconstr:(needs_impl_cast (stag_eq _ _ _ _ (E : impl _ _)))
    ]
  ) in
  lazymatch constr:( ltac:(inner) ) with
  | λ _, atag_eq _ _ _ _ _ => uconstr:(atag_eq _ _ _ _ E)
  | λ _, stag_eq _ _ _ _ _ => uconstr:(stag_eq _ _ _ _ E)
  | λ _, needs_impl_cast (stag_eq _ _ _ _ _) => uconstr:(stag_eq _ _ _ _ (E : impl _ _))
  end.

Ltac wrap_tag_l := wrap_tag constr:(@arewrite.arewrite_tag_l_eq) constr:(@srewrite.srewrite_tag_l_eq).
Ltac wrap_tag_r := wrap_tag constr:(@arewrite.arewrite_tag_r_eq) constr:(@srewrite.srewrite_tag_r_eq).

Ltac rewrite_tag_l    avoid_capture_E := let avoid_capture_E' := wrap_tag_l avoid_capture_E in rewrite_in_term    avoid_capture_E'.
Ltac rewrite_tag_l_at avoid_capture_E := let avoid_capture_E' := wrap_tag_l avoid_capture_E in rewrite_in_term_at avoid_capture_E'.
Ltac rewrite_tag_r    avoid_capture_E := let avoid_capture_E' := wrap_tag_r avoid_capture_E in rewrite_in_term    avoid_capture_E'.
Ltac rewrite_tag_r_at avoid_capture_E := let avoid_capture_E' := wrap_tag_r avoid_capture_E in rewrite_in_term_at avoid_capture_E'.

Tactic Notation "tag_rewrite" "in" uconstr(target_term)
  "then" tactic1(continuation_tac)
  "by" "->" uconstr(avoid_capture_E)
  "|" tactic3(next_rewrite_tac)
  := rewrite_tag_l avoid_capture_E next_rewrite_tac target_term continuation_tac.

Tactic Notation "tag_rewrite" "in" uconstr(target_term)
  "then" tactic1(continuation_tac)
  "by" "<-" uconstr(avoid_capture_E)
  "|" tactic3(next_rewrite_tac)
  := rewrite_tag_r avoid_capture_E next_rewrite_tac target_term continuation_tac.

Tactic Notation "tag_rewrite" "in" uconstr(target_term)
  "then" tactic1(continuation_tac)
  "by" "->" uconstr(avoid_capture_E)
  := tag_rewrite in target_term then continuation_tac by -> avoid_capture_E | tag_rewrite_done.

Tactic Notation "tag_rewrite" "in" uconstr(target_term)
  "then" tactic1(continuation_tac)
  "by" "<-" uconstr(avoid_capture_E)
  := tag_rewrite in target_term then continuation_tac by <- avoid_capture_E | tag_rewrite_done.

Tactic Notation "tag_rewrite" "in" uconstr(target_term)
  "then" tactic1(continuation_tac)
  "by" "->" uconstr(avoid_capture_E)
  "where" tactic1(drop_tag_tac)
  "|" tactic3(next_rewrite_tac)
  := rewrite_tag_l_at avoid_capture_E drop_tag_tac next_rewrite_tac target_term continuation_tac.

Tactic Notation "tag_rewrite" "in" uconstr(target_term)
  "then" tactic1(continuation_tac)
  "by" "<-" uconstr(avoid_capture_E)
  "where" tactic1(drop_tag_tac)
  "|" tactic3(next_rewrite_tac)
  := rewrite_tag_r_at avoid_capture_E drop_tag_tac next_rewrite_tac target_term continuation_tac.

Tactic Notation "tag_rewrite" "in" uconstr(target_term)
  "then" tactic1(continuation_tac)
  "by" "->" uconstr(avoid_capture_E)
  "where" tactic1(drop_tag_tac)
  := tag_rewrite in target_term then continuation_tac by -> avoid_capture_E where drop_tag_tac | tag_rewrite_done.

Tactic Notation "tag_rewrite" "in" uconstr(target_term)
  "then" tactic1(continuation_tac)
  "by" "<-" uconstr(avoid_capture_E)
  "where" tactic1(drop_tag_tac)
  := tag_rewrite in target_term then continuation_tac by <- avoid_capture_E where drop_tag_tac | tag_rewrite_done.


Tactic Notation "rew" uconstr(buggy_E1)
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1.
Tactic Notation "rew" "<-" uconstr(buggy_E1)
  := let G := get_goal in tag_rewrite in G then goal_rewrite by <- buggy_E1.
Tactic Notation "rew" uconstr(buggy_E1) "at" ne_int_or_var_list(occ1)
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1 where (fun x y => change x with y at occ1).
Tactic Notation "rew" "<-" uconstr(buggy_E1) "at" ne_int_or_var_list(occ1)
  := let G := get_goal in tag_rewrite in G then goal_rewrite by <- buggy_E1 where (fun x y => change x with y at occ1).

Tactic Notation "rew" uconstr(buggy_E1) "in" hyp(hypothesis_ident)
  := let G := type of hypothesis_ident in tag_rewrite in G then (hyp_rewrite hypothesis_ident) by -> buggy_E1.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "in" hyp(hypothesis_ident)
  := let G := type of hypothesis_ident in tag_rewrite in G then (hyp_rewrite hypothesis_ident) by <- buggy_E1.
Tactic Notation "rew" uconstr(buggy_E1) "in" hyp(hypothesis_ident) "at" ne_int_or_var_list(occ1)
  := let G := type of hypothesis_ident in tag_rewrite in G then (hyp_rewrite hypothesis_ident) by -> buggy_E1 where (fun x y => change x with y at occ1).
Tactic Notation "rew" "<-" uconstr(buggy_E1) "in" hyp(hypothesis_ident) "at" ne_int_or_var_list(occ1)
  := let G := type of hypothesis_ident in tag_rewrite in G then (hyp_rewrite hypothesis_ident) by <- buggy_E1 where (fun x y => change x with y at occ1).

Tactic Notation "rew_debug" uconstr(buggy_E1)
  := let G := get_goal in tag_rewrite in G then goal_debug_rewrite by -> buggy_E1.
Tactic Notation "rew_debug" "<-" uconstr(buggy_E1)
  := let G := get_goal in tag_rewrite in G then goal_debug_rewrite by <- buggy_E1.
Tactic Notation "rew_debug" uconstr(buggy_E1) "at" ne_int_or_var_list(occ1)
  := let G := get_goal in tag_rewrite in G then goal_debug_rewrite by -> buggy_E1 where (fun x y => change x with y at occ1).
Tactic Notation "rew_debug" "<-" uconstr(buggy_E1) "at" ne_int_or_var_list(occ1)
  := let G := get_goal in tag_rewrite in G then goal_debug_rewrite by <- buggy_E1 where (fun x y => change x with y at occ1).

Tactic Notation "rew" "?" uconstr(avoid_capture_E) := repeat (rew avoid_capture_E).
Tactic Notation "rew" "!" uconstr(avoid_capture_E) := rew avoid_capture_E; repeat (rew avoid_capture_E).

Tactic Notation "rew" "?" int_or_var(number_of_times) uconstr(avoid_capture_E) := do number_of_times (try rew avoid_capture_E).
Tactic Notation "rew" "!" int_or_var(number_of_times) uconstr(avoid_capture_E) := do number_of_times (rew avoid_capture_E).

Tactic Notation "rew" "<-" "?" uconstr(avoid_capture_E) := repeat (rew <-avoid_capture_E).
Tactic Notation "rew" "<-" "!" uconstr(avoid_capture_E) := rew <-avoid_capture_E; repeat (rew <-avoid_capture_E).

Tactic Notation "rew" "<-" "?" int_or_var(number_of_times) uconstr(avoid_capture_E) := do number_of_times (try rew <-avoid_capture_E).
Tactic Notation "rew" "<-" "!" int_or_var(number_of_times) uconstr(avoid_capture_E) := do number_of_times (rew <-avoid_capture_E).

Tactic Notation "rew" "["      uconstr(buggy_E1) "|"      uconstr(buggy_E2) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1 | rewrite_tag_l buggy_E2 tag_rewrite_done.
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|"      uconstr(buggy_E2) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by <- buggy_E1 | rewrite_tag_l buggy_E2 tag_rewrite_done.
Tactic Notation "rew" "["      uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1 | rewrite_tag_r buggy_E2 tag_rewrite_done.
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by <- buggy_E1 | rewrite_tag_r buggy_E2 tag_rewrite_done.

Tactic Notation "rew" "["      uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|"      uconstr(buggy_E3) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1 | rewrite_tag_l buggy_E2 ltac:(rewrite_tag_l buggy_E3 tag_rewrite_done).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|"      uconstr(buggy_E3) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by <- buggy_E1 | rewrite_tag_l buggy_E2 ltac:(rewrite_tag_l buggy_E3 tag_rewrite_done).
Tactic Notation "rew" "["      uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|"      uconstr(buggy_E3) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1 | rewrite_tag_r buggy_E2 ltac:(rewrite_tag_l buggy_E3 tag_rewrite_done).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|"      uconstr(buggy_E3) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by <- buggy_E1 | rewrite_tag_r buggy_E2 ltac:(rewrite_tag_l buggy_E3 tag_rewrite_done).
Tactic Notation "rew" "["      uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1 | rewrite_tag_l buggy_E2 ltac:(rewrite_tag_r buggy_E3 tag_rewrite_done).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by <- buggy_E1 | rewrite_tag_l buggy_E2 ltac:(rewrite_tag_r buggy_E3 tag_rewrite_done).
Tactic Notation "rew" "["      uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1 | rewrite_tag_r buggy_E2 ltac:(rewrite_tag_r buggy_E3 tag_rewrite_done).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by <- buggy_E1 | rewrite_tag_r buggy_E2 ltac:(rewrite_tag_r buggy_E3 tag_rewrite_done).

Tactic Notation "rew" "["      uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|"      uconstr(buggy_E3) "|"      uconstr(buggy_E4) "]"
  := let G := get_goal in tag_rewrite in G then goal_rewrite by -> buggy_E1 | rewrite_tag_l buggy_E2 ltac:(rewrite_tag_l buggy_E3 ltac:(rewrite_tag_l buggy_E4 tag_rewrite_done)).


Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) := rew   buggy_E1; rew   buggy_E2.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) := rew   buggy_E1; rew <-buggy_E2.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) := rew <-buggy_E1; rew   buggy_E2.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) := rew <-buggy_E1; rew <-buggy_E2.

Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) := rew   buggy_E1,   buggy_E2; rew   buggy_E3.
Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) := rew   buggy_E1,   buggy_E2; rew <-buggy_E3.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) := rew   buggy_E1, <-buggy_E2; rew   buggy_E3.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) := rew   buggy_E1, <-buggy_E2; rew <-buggy_E3.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) := rew <-buggy_E1,   buggy_E2; rew   buggy_E3.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) := rew <-buggy_E1,   buggy_E2; rew <-buggy_E3.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) := rew <-buggy_E1, <-buggy_E2; rew   buggy_E3.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) := rew <-buggy_E1, <-buggy_E2; rew <-buggy_E3.

Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) ","      uconstr(buggy_E4) := rew   buggy_E1,   buggy_E2,   buggy_E3; rew   buggy_E4.
Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) := rew   buggy_E1,   buggy_E2,   buggy_E3; rew <-buggy_E4.
Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) ","      uconstr(buggy_E4) := rew   buggy_E1,   buggy_E2, <-buggy_E3; rew   buggy_E4.
Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) := rew   buggy_E1,   buggy_E2, <-buggy_E3; rew <-buggy_E4.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) ","      uconstr(buggy_E4) := rew   buggy_E1, <-buggy_E2,   buggy_E3; rew   buggy_E4.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) := rew   buggy_E1, <-buggy_E2,   buggy_E3; rew <-buggy_E4.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) ","      uconstr(buggy_E4) := rew   buggy_E1, <-buggy_E2, <-buggy_E3; rew   buggy_E4.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) := rew   buggy_E1, <-buggy_E2, <-buggy_E3; rew <-buggy_E4.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) ","      uconstr(buggy_E4) := rew <-buggy_E1,   buggy_E2,   buggy_E3; rew   buggy_E4.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) := rew <-buggy_E1,   buggy_E2,   buggy_E3; rew <-buggy_E4.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) ","      uconstr(buggy_E4) := rew <-buggy_E1,   buggy_E2, <-buggy_E3; rew   buggy_E4.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) := rew <-buggy_E1,   buggy_E2, <-buggy_E3; rew <-buggy_E4.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) ","      uconstr(buggy_E4) := rew <-buggy_E1, <-buggy_E2,   buggy_E3; rew   buggy_E4.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) := rew <-buggy_E1, <-buggy_E2,   buggy_E3; rew <-buggy_E4.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) ","      uconstr(buggy_E4) := rew <-buggy_E1, <-buggy_E2, <-buggy_E3; rew   buggy_E4.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) := rew <-buggy_E1, <-buggy_E2, <-buggy_E3; rew <-buggy_E4.

Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) "in" hyp(buggy_H) := rew   buggy_E1 in buggy_H; rew   buggy_E2 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "in" hyp(buggy_H) := rew   buggy_E1 in buggy_H; rew <-buggy_E2 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) "in" hyp(buggy_H) := rew <-buggy_E1 in buggy_H; rew   buggy_E2 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "in" hyp(buggy_H) := rew <-buggy_E1 in buggy_H; rew <-buggy_E2 in buggy_H.

Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) "in" hyp(buggy_H) := rew   buggy_E1,   buggy_E2 in buggy_H; rew   buggy_E3 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "in" hyp(buggy_H) := rew   buggy_E1,   buggy_E2 in buggy_H; rew <-buggy_E3 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) "in" hyp(buggy_H) := rew   buggy_E1, <-buggy_E2 in buggy_H; rew   buggy_E3 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "in" hyp(buggy_H) := rew   buggy_E1, <-buggy_E2 in buggy_H; rew <-buggy_E3 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) "in" hyp(buggy_H) := rew <-buggy_E1,   buggy_E2 in buggy_H; rew   buggy_E3 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "in" hyp(buggy_H) := rew <-buggy_E1,   buggy_E2 in buggy_H; rew <-buggy_E3 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) "in" hyp(buggy_H) := rew <-buggy_E1, <-buggy_E2 in buggy_H; rew   buggy_E3 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "in" hyp(buggy_H) := rew <-buggy_E1, <-buggy_E2 in buggy_H; rew <-buggy_E3 in buggy_H.

Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) ","      uconstr(buggy_E4) "in" hyp(buggy_H) := rew   buggy_E1,   buggy_E2,   buggy_E3 in buggy_H; rew   buggy_E4 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) "in" hyp(buggy_H) := rew   buggy_E1,   buggy_E2,   buggy_E3 in buggy_H; rew <-buggy_E4 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) ","      uconstr(buggy_E4) "in" hyp(buggy_H) := rew   buggy_E1,   buggy_E2, <-buggy_E3 in buggy_H; rew   buggy_E4 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) "in" hyp(buggy_H) := rew   buggy_E1,   buggy_E2, <-buggy_E3 in buggy_H; rew <-buggy_E4 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) ","      uconstr(buggy_E4) "in" hyp(buggy_H) := rew   buggy_E1, <-buggy_E2,   buggy_E3 in buggy_H; rew   buggy_E4 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) "in" hyp(buggy_H) := rew   buggy_E1, <-buggy_E2,   buggy_E3 in buggy_H; rew <-buggy_E4 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) ","      uconstr(buggy_E4) "in" hyp(buggy_H) := rew   buggy_E1, <-buggy_E2, <-buggy_E3 in buggy_H; rew   buggy_E4 in buggy_H.
Tactic Notation "rew"      uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) "in" hyp(buggy_H) := rew   buggy_E1, <-buggy_E2, <-buggy_E3 in buggy_H; rew <-buggy_E4 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) ","      uconstr(buggy_E4) "in" hyp(buggy_H) := rew <-buggy_E1,   buggy_E2,   buggy_E3 in buggy_H; rew   buggy_E4 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) ","      uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) "in" hyp(buggy_H) := rew <-buggy_E1,   buggy_E2,   buggy_E3 in buggy_H; rew <-buggy_E4 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) ","      uconstr(buggy_E4) "in" hyp(buggy_H) := rew <-buggy_E1,   buggy_E2, <-buggy_E3 in buggy_H; rew   buggy_E4 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) ","      uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) "in" hyp(buggy_H) := rew <-buggy_E1,   buggy_E2, <-buggy_E3 in buggy_H; rew <-buggy_E4 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) ","      uconstr(buggy_E4) "in" hyp(buggy_H) := rew <-buggy_E1, <-buggy_E2,   buggy_E3 in buggy_H; rew   buggy_E4 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) ","      uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) "in" hyp(buggy_H) := rew <-buggy_E1, <-buggy_E2,   buggy_E3 in buggy_H; rew <-buggy_E4 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) ","      uconstr(buggy_E4) "in" hyp(buggy_H) := rew <-buggy_E1, <-buggy_E2, <-buggy_E3 in buggy_H; rew   buggy_E4 in buggy_H.
Tactic Notation "rew" "<-" uconstr(buggy_E1) "," "<-" uconstr(buggy_E2) "," "<-" uconstr(buggy_E3) "," "<-" uconstr(buggy_E4) "in" hyp(buggy_H) := rew <-buggy_E1, <-buggy_E2, <-buggy_E3 in buggy_H; rew <-buggy_E4 in buggy_H.

(*
Section test.
  Context (P Q R R2 : SProp) (E:impl P Q).
  Context (E2:impl R R2).
  Context (E3:∀ Z (R:SProp), impl P Z).

  Context (E':impl Q P) (E2':impl R2 R).

  Let G := (R → Q) ∧ (R → Q).
  Goal G. red.
    rew [ <-E | E2 ]. Show Proof.
    Show Proof.
    cut G. intro. red in H.
    rew <-E2' in H at 1 2. Show Proof.
  Abort.
End test.

Section test.
  Context (P Q R R2 : Ω).
  Context (E:aimpl P Q).
  Context (E2:aimpl R R2).

  Let G := (R ⊸ Q) ⊠ (R ⊸ Q).
  Goal G. unfold G.
    rew [ <-E | E2 ].
  Abort.
End test.
*)
