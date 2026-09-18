(** * Custom Rewrite Tactic

    The [rew] tactic rewrites goals and hypotheses using affine (AProp)
    and SProp relations, via a proper-morphism framework analogous to
    Stdlib's [setoid_rewrite] but designed for affine logic.

    ** Architecture

    A rewrite [rew E] where [E : P ⧟ Q] (or [E : P ⊸ Q], etc.) works as follows:

    1. **Tag determination** ([tag_l_tac] / [tag_r_tac]):
       Probes the type of [E] to decide whether to use affine tags
       ([arewrite_tag_l/r]) or SProp tags ([srewrite_tag_l/r]).
       Uses backtracking to avoid leaking existential variables.

    2. **Subterm matching** ([match_tag_on_subterms]):
       Finds all subterms of the goal that match the tag's reduced form
       (i.e., the LHS or RHS of [E]). Each match is abstracted as a binder
       so that subsequent matches don't accidentally match inside a tag.
       Returns a [mark]-stack paired with the tagged term.

    3. **Occurrence selection** ([tag_subterms_at]):
       The [mark]-stack has one [skip_match] entry per occurrence. To select
       specific occurrences, [eval unfold skip_match at N] unfolds the N-th
       entry to [found_match]. [swap_tags] then walks the stack: at [found_match]
       entries it keeps the tag (and produces the swapped tag for the other
       side of the relation); at [skip_match] entries it removes the tag.

    4. **Properness proof** ([goal_rewrite] / [hyp_rewrite]):
       Given tagged terms [P] (original with tags) and [Q] (swapped tags),
       solves [impl Q P] via [proper_solution] (typeclass search in the
       [proper] hint database), then applies the proof to the goal.

    ** Chaining

    [rew [E1 | E2 | E3]] chains multiple rewrites. Each [tag_subterms]
    takes a continuation [k] that is invoked when no more occurrences of
    the current tag are found. The continuation starts matching the next tag.
    This ensures that tags from earlier rewrites (which are abstracted as
    binders) are not matched by later rewrites.

    ** Key types

    - [FoundMatch : SProp] — sentinel type used as a dummy in term encodings.
    - [skip_match : FoundMatch] — marks an unselected occurrence (unfolds to
      [found_match] when selected).
    - [mark : FoundMatch → FoundMatch → FoundMatch] — cons cell in the
      occurrence marker stack. First arg is per-occurrence marker
      ([skip_match] or [found_match]), second is the recursive rest.
    - [(fun _ _ => found_match) P Q] — encodes a pair [(P, Q)] of tagged terms.
*)

Require Import interfaces.notation sprop prop_eq srelations tactics.misc logic.aprop.
Require Export rewrite.proper srewrite arewrite.

Ltac debug_msg tac := idtac.
(*Ltac debug_msg tac := match goal with |- ?G => tac G end.*)

(** Elaborate [utm] with partial typeclass resolution: only resolves goals
    whose type is ground (contains no existential variables). *)
Ltac resolve_ground_typeclasses utm :=
  unshelve (let t := open_constr:(utm) in exact t);
  try lazymatch goal with |- ?G => is_ground G; try exact _ end.

Inductive FoundMatch : SProp := found_match : FoundMatch.
Definition skip_match := found_match.
Definition mark (a b : FoundMatch) := found_match.
Arguments mark: simpl never.



Ltac unify_pattern subterm term :=
  let res := open_constr:( ltac:(
    let F := fresh "F" in intro F;
    let E := open_constr:( eq_refl subterm ) in case E;
    let g':= lazymatch goal with |- ?G => open_constr:( G ) end in
    eexact (match F return g' with end)
  ) : False → term ) in
  lazymatch res with
    (fun _ => match @eq_refl ?T _ in (eq _ binder) return ?body with | eq_refl => _ end) =>
      open_constr:(fun binder : T => body)
  end.


Ltac assert_uses_arg tm :=
  let uses var body :=
    lazymatch body with
    | context [ var ] => exact found_match
    end
  in
  lazymatch tm with (fun binder : ?T => ?body ) =>
    first [ let res := eval_under_binder uses binder T body in idtac
          | fail 1 "lambda body does not contain its binder: " tm ]
  end.


Ltac match_subterm_with_tag try_conv check tm utag :=
  let _ := debug_msg ltac:(fun _ => idtac "match_subterm_with_tag"; idtac "  tm=" tm; idtac "  utag=" utag) in
  once solve [ unshelve (
    let tag := open_constr:( ltac:( resolve_ground_typeclasses utag ) ) in
    let original := eval red in tag in
    let T := type of original in
    let _ := debug_msg ltac:(fun _ => idtac "  tag=" tag; idtac "  original=" original; idtac "  T=" T) in
    let syntax_based _ :=
      multimatch tm with context C [original] =>
        let subbed := context C [ original ] in
        let _ := debug_msg ltac:(fun _ => idtac "  subbed=" tag) in
        unify tm subbed;
        let _ := debug_msg ltac:(fun _ => idtac "  unified subbed=" tag; idtac "  unified original=" original) in
        let v := fresh "v" in
        let tm' := constr:( (fun _ v => ltac:(let r := context C [ v ] in exact r)) found_match tag ) in
        let T' := lazymatch tm' with ((fun _ (v : ?T) => _) _ _) => constr:(T) end in
        unify T' T;  (* don't allow coercions *)
        check original;
        exact tm'
      end in
    let conv_based _ :=
      let _ := debug_msg ltac:(fun _ => idtac "  no syntatic match; trying generalization") in
      let res := unify_pattern original tm in
      let _ := debug_msg ltac:(fun _ => idtac "  res=" res) in
      let _ := debug_msg ltac:(fun _ => idtac "  tag=" tag; idtac "  original=" original; idtac "  T=" T) in
      check original;
      assert_uses_arg res;
      let subbed := lazymatch res with (fun binder => ?body) => open_constr:( match original with binder => body end) end in
      tryif constr_eq subbed tm
      then (* Substitution dissolved back to [tm]: the occurrences are dependently
              linked (e.g. in a binder type and in implicit arguments depending on
              it), so no single occurrence can be tagged alone. Tag all of them at
              once using the abstraction computed by [unify_pattern]. *)
        lazymatch res with (fun binder : ?T' => ?body) =>
          exact ((fun _ (binder : T') => body) found_match tag)
        end
      else exact ((fun _ => skip_match) subbed) in
    syntax_based found_match
    + lazymatch try_conv with true => conv_based found_match end
  ); let _ := debug_msg ltac:(fun g => idtac "  leftover goal=" g) in
    try exact _; exact _
  | let _ := debug_msg ltac:(fun _ => idtac "  failed to match") in
   exact tm ].


(** Try to match a single subterm of [tm] against the reduced form of [utag].
    Returns either:
    - [(fun _ (v : T) => body) found_match tag] if a match is found,
      where [v] abstracts the matched subterm in [body], and [tag] is the
      fully-resolved tag term. Holes in the tag are filled by [unify]-ing the
      reconstructed term against [tm].
    - [tm] unchanged if no match is found.

    [check] is called on the resolved [original] term after [unify]; if it fails
    (e.g., because [original] mentions a binder variable from a prior match),
    [multimatch] backtracks to the next candidate subterm. *)
(*
Ltac match_subterm_with_tag check tm utag :=
  let _ := debug_msg ltac:(fun _ => idtac "match_subterm_with_tag"; idtac "  tm=" tm; idtac "  utag=" utag) in
  once solve [ unshelve (
    let tag := open_constr:( ltac:( resolve_ground_typeclasses utag ) ) in
    let original := eval red in tag in
    let T := type of original in
    let _ := debug_msg ltac:(fun _ => idtac "  tag=" tag; idtac "  original=" original; idtac "  T=" T) in
    multimatch tm with context C [original] =>
      let subbed := context C [ original ] in
      let _ := debug_msg ltac:(fun _ => idtac "  subbed=" tag) in
      unify tm subbed;
      let _ := debug_msg ltac:(fun _ => idtac "  unified subbed=" tag; idtac "  unified original=" original) in
      let v := fresh "v" in
      let tm' := constr:( (fun _ v => ltac:(let r := context C [ v ] in exact r)) found_match tag ) in
      let T' := lazymatch tm' with ((fun _ (v : ?T) => _) _ _) => constr:(T) end in
      unify T' T;  (* don't allow coercions *)
      check original;
      exact tm'
    end
  ); let _ := debug_msg ltac:(fun g => idtac "  leftover goal=" g) in
    try exact _; exact _
  | let _ := debug_msg ltac:(fun _ => idtac "  failed to match") in
   exact tm ].
*)

(** Recursively match all subterms of [term] against [utag].

    Each match is abstracted as a binder, so later matches cannot
    accidentally match inside an already-tagged subterm. The [check]
    tactic accumulates guards against all prior binder variables.

    When no more matches are found, calls continuation [k] on the
    residual term (used for chaining multiple tags).

    Returns [mark m t] where [m] is the occurrence marker stack and [t]
    is the tagged term with [(fun binder => body) tag] at each match site. *)
Ltac match_tag_on_subterms utag k term :=
  let rec match_subterms try_conv check v tm :=
    let check' matched_term := check matched_term; lazymatch matched_term with context [v] => fail | _ => idtac end in
    let matched_tag := constr:( ltac:( match_subterm_with_tag try_conv check' tm utag ) ) in
    lazymatch matched_tag with
    | (fun _ (binder : ?T) => ?body) found_match ?final_tag =>
      let t := eval_under_binder ltac:(match_subterms constr:(false) check') binder T body in
      lazymatch t with (fun binder : ?T => mark ?m ?body) =>
        exact (mark (mark skip_match m) ((fun (binder : T) => body) final_tag))
      end
    | (fun _ => skip_match) ?tm' => match_subterms constr:(false) check v tm'
    | _ => let tm' := k tm in exact (mark found_match tm')
    end
  in constr:( ltac:( match_subterms constr:(true) ltac:(fun _ => idtac) found_match term ) ).


(*
Ltac match_tag_on_subterms utag k term :=
  let rec match_subterms check v tm :=
    let check' matched_term := check matched_term; lazymatch matched_term with context [v] => fail 1 | _ => idtac end in
    let matched_tag := constr:( ltac:( match_subterm_with_tag check' tm utag ) ) in
    lazymatch matched_tag with
    | (fun _ (binder : ?T) => ?body) found_match ?final_tag =>
      let t := eval_under_binder ltac:(match_subterms check') binder T body in
      lazymatch t with (fun binder : ?T => mark ?m ?body) =>
        exact (mark (mark skip_match m) ((fun (binder : T) => body) final_tag))
      end
    | _ => let tm' := k tm in exact (mark found_match tm')
    end
  in constr:( ltac:( match_subterms ltac:(fun _ => idtac) found_match term ) ).
*)


(** Walk the marker stack [m] and tagged term [t] in parallel, producing
    a pair [(P, Q)] encoded as [(fun _ _ => found_match) P Q].

    At each occurrence:
    - [found_match] in [m] (selected): keeps the tag in [P], uses
      [swap_rewrite_tag] to produce the swapped tag in [Q].
    - [skip_match] in [m] (unselected): removes the tag from both [P] and [Q],
      substituting the original (untagged) subterm.

    Raises an error if [m] is [found_match] (no occurrences were matched). *)
Ltac swap_tags utag m t :=
  let _ := lazymatch m with
    | found_match =>
      let tag := open_constr:( ltac:( resolve_ground_typeclasses utag ) ) in
      let original := eval red in tag in
      fail "no occurrences of" original " ≡ " tag
    | _ => idtac
  end in
  let rec do_swap marks tm :=
    lazymatch marks with
    | found_match => exact tm
    | mark ?m ?ms =>
      lazymatch tm with (fun (binder : ?T) => ?body) ?tag =>
        let t := eval_under_binder ltac:(fun _ x => do_swap ms x) binder T body in
        lazymatch t with (fun (binder' : ?T) => (fun _ _ => found_match) ?original_body ?swapped_body) =>
          lazymatch m with
          | skip_match =>
              let untagged := eval red in tag in
              let original := constr:(match untagged with binder' => original_body end) in
              let swapped := constr:(match untagged with binder' => swapped_body end) in
              exact ((fun _ _ => found_match) original swapped)
          | found_match =>
              let swapped_tag := swap_rewrite_tag tag in
              let original := constr:(match tag with binder' => original_body end) in
              let swapped := constr:(match swapped_tag with binder' => swapped_body end) in
              exact ((fun _ _ => found_match) original swapped)
          end
        end
      end
    end
  in constr:( ltac:( do_swap m t ) ).

(** Determine the left-tag form for equation [utm].

    Probes the type of [utm] by trying to elaborate each tag constructor
    via [open_constr]. The first that succeeds determines the classification.
    Nested [match found_match] with increasing [fail] levels ensures that
    evars from probing are discarded (each probe always fails, and the
    corresponding [uconstr] is returned from the catch branch):
    - If [arewrite_tag_l utm] elaborates — affine relation: use [arewrite_tag_l].
    - If [srewrite_tag_l utm] elaborates — SProp relation: use [srewrite_tag_l].
    - If [srewrite_tag_l (R:=impl) utm] elaborates — SProp implication: use [srewrite_tag_l (R:=impl)].
    - Otherwise: fail with an error message. *)
Ltac tag_l_tac utm :=
  match found_match with
  | _ => match found_match with
    | _ => match found_match with
      | _ => match found_match with
        | _ => let _ := open_constr:(arewrite_tag_l utm) in fail 1
        | _ => let _ := open_constr:(srewrite_tag_l utm) in fail 2
        | _ => let _ := open_constr:(srewrite_tag_l (R:=impl) utm) in fail 3
        | _ => fail 4 "unable to find tag type for" utm
        end
      | _ => uconstr:( arewrite_tag_l utm )
      end
    | _ => uconstr:( srewrite_tag_l utm )
    end
  | _ => uconstr:( srewrite_tag_l (R:=impl) utm )
  end.

(** Like [tag_l_tac] but for the right/swapped tag. *)
Ltac tag_r_tac utm :=
  match found_match with
  | _ => match found_match with
    | _ => match found_match with
      | _ => match found_match with
        | _ => let _ := open_constr:(arewrite_tag_r utm) in fail 1
        | _ => let _ := open_constr:(srewrite_tag_r utm) in fail 2
        | _ => let _ := open_constr:(srewrite_tag_r (R:=impl) utm) in fail 3
        | _ => fail 4 "unable to find tag type for" utm
        end
      | _ => uconstr:( arewrite_tag_r utm )
      end
    | _ => uconstr:( srewrite_tag_r utm )
    end
  | _ => uconstr:( srewrite_tag_r (R:=impl) utm )
  end.

(** Terminal continuation for tag chaining: returns [tm] as both the
    original and swapped term (identity rewrite). *)
Ltac tag_done tm := constr:((fun _ _ => found_match) tm tm).

(** Match, select occurrences, and swap tags for a single equation.
    [utag] is the tag uconstr, [occ] selects occurrences from the marker stack,
    [k] is the continuation for chaining, [tm] is the term to rewrite in.
    Returns [(fun _ _ => found_match) P Q] where [P] has original tags and
    [Q] has swapped tags. *)
Ltac tag_subterms_at utag occ k tm :=
  let tagged_tm := match_tag_on_subterms utag k tm in
  lazymatch tagged_tm with mark ?m ?t =>
    let m' := occ m in
    let swapped := swap_tags utag m' t in
    swapped
  end.

(** Like [tag_subterms_at] but selects all occurrences
    (unfolds all [skip_match] to [found_match]). *)
Ltac tag_subterms utag k tm := tag_subterms_at utag ltac:(fun m => eval unfold skip_match in m) k tm.

(** Remove all rewrite tags from [P] by unfolding them.
    Each tag [arewrite_tag_l E] reduces to the relevant component of [E]. *)
Ltac clear_tags P := eval unfold arewrite_tag_l, arewrite_tag_r, srewrite_tag_l, srewrite_tag_r in P.

(** Rewrite in hypothesis [H] using the tagging tactic [tag_tac].
    [tag_tac] takes a term and returns [(fun _ _ => found_match) P Q].
    Solves [impl P Q] via [proper_solution], clears tags, and replaces [H]. *)
Ltac hyp_rewrite H tag_tac :=
  let tm := type of H in
  let PQ := tag_tac tm in
  lazymatch PQ with ((fun _ _ => _) ?P ?Q) =>
  first [
    let pf := proper_solution (impl (P, Q)) in
    let pf' := clear_tags pf in
    let Q' := clear_tags Q in
    let H' := fresh H in pose proof pf' H : Q' as H'; clear H; rename H' into H
  | idtac "Could not solve proper goal.";
    assert (impl (P, Q)) ]
  end.

(** Rewrite the goal using the tagging tactic [tag_tac].
    [tag_tac] takes a term and returns [(fun _ _ => found_match) P Q].
    Solves [impl Q P] via [proper_solution] (note: reversed direction for
    goals vs hypotheses), clears tags, and applies to the goal. *)
Ltac goal_rewrite tag_tac :=
  let g := get_goal in
  let tm := open_constr:( g ) in
  let PQ := tag_tac tm in
  lazymatch PQ with ((fun _ _ => _) ?P ?Q) =>
  first [
    let pf := proper_solution (impl (Q, P)) in
    let pf' := clear_tags pf in
    let Q' := clear_tags Q in
    simple notypeclasses refine (pf' _); change Q'
  | idtac "Could not solve proper goal.";
    assert (impl (Q, P))
  ]
  end.

(** Like [goal_rewrite] but instead of solving the proper goal,
    asserts it as a new goal for manual inspection. *)
Ltac goal_debug_rewrite tag_tac :=
  let g := get_goal in
  let tm := open_constr:( g ) in
  let PQ := tag_tac tm in
  lazymatch PQ with ((fun _ _ => _) ?P ?Q) => assert (impl (Q, P)) end.


Tactic Notation "rew_debug" uconstr(buggy_E1) :=
  let E1 := tag_l_tac buggy_E1 in
  goal_debug_rewrite ltac:(tag_subterms E1 tag_done).  
Tactic Notation "rew_debug" "<-" uconstr(buggy_E1) :=
  let E1 := tag_r_tac buggy_E1 in
  goal_debug_rewrite ltac:(tag_subterms E1 tag_done).  


Tactic Notation "rew" uconstr(buggy_E1) :=
  let E1 := tag_l_tac buggy_E1 in
  goal_rewrite ltac:(tag_subterms E1 tag_done).  
Tactic Notation "rew" "<-" uconstr(buggy_E1) :=
  let E1 := tag_r_tac buggy_E1 in
  goal_rewrite ltac:(tag_subterms E1 tag_done).  
Tactic Notation "rew" uconstr(buggy_E1) "at" ne_int_or_var_list(occ1) :=
  let E1 := tag_l_tac buggy_E1 in let o1 := ltac:(fun m => eval unfold skip_match at occ1 in m) in
  goal_rewrite ltac:(tag_subterms_at E1 o1 tag_done).  
Tactic Notation "rew" "<-" uconstr(buggy_E1) "at" ne_int_or_var_list(occ1) :=
  let E1 := tag_r_tac buggy_E1 in let o1 := ltac:(fun m => eval unfold skip_match at occ1 in m) in
  goal_rewrite ltac:(tag_subterms_at E1 o1 tag_done).  

Tactic Notation "rew" uconstr(buggy_E1) "in" hyp(hypothesis_ident1) :=
  let E1 := tag_l_tac buggy_E1 in
  hyp_rewrite hypothesis_ident1 ltac:(tag_subterms E1 tag_done).  
Tactic Notation "rew" "<-" uconstr(buggy_E1) "in" hyp(hypothesis_ident1) :=
  let E1 := tag_r_tac buggy_E1 in
  hyp_rewrite hypothesis_ident1 ltac:(tag_subterms E1 tag_done).  
Tactic Notation "rew" uconstr(buggy_E1) "at" ne_int_or_var_list(occ1) "in" hyp(hypothesis_ident1) :=
  let E1 := tag_l_tac buggy_E1 in let o1 := ltac:(fun m => eval unfold skip_match at occ1 in m) in
  hyp_rewrite hypothesis_ident1 ltac:(tag_subterms_at E1 o1 tag_done).  
Tactic Notation "rew" "<-" uconstr(buggy_E1) "at" ne_int_or_var_list(occ1) "in" hyp(hypothesis_ident1) :=
  let E1 := tag_r_tac buggy_E1 in let o1 := ltac:(fun m => eval unfold skip_match at occ1 in m) in
  hyp_rewrite hypothesis_ident1 ltac:(tag_subterms_at E1 o1 tag_done).

Tactic Notation "rew" "["      uconstr(buggy_E1) "|"      uconstr(buggy_E2) "]" :=
  let E1 := tag_l_tac buggy_E1 in let E2 := tag_l_tac buggy_E2 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 tag_done)).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|"      uconstr(buggy_E2) "]" :=
  let E1 := tag_r_tac buggy_E1 in let E2 := tag_l_tac buggy_E2 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 tag_done)).
Tactic Notation "rew" "["      uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "]" :=
  let E1 := tag_l_tac buggy_E1 in let E2 := tag_r_tac buggy_E2 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 tag_done)).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "]" :=
  let E1 := tag_r_tac buggy_E1 in let E2 := tag_r_tac buggy_E2 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 tag_done)).

Tactic Notation "rew" "["      uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|"      uconstr(buggy_E3) "]" :=
  let E1 := tag_l_tac buggy_E1 in let E2 := tag_l_tac buggy_E2 in let E3 := tag_l_tac buggy_E3 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 tag_done))).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|"      uconstr(buggy_E3) "]" :=
  let E1 := tag_r_tac buggy_E1 in let E2 := tag_l_tac buggy_E2 in let E3 := tag_l_tac buggy_E3 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 tag_done))).
Tactic Notation "rew" "["      uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|"      uconstr(buggy_E3) "]" :=
  let E1 := tag_l_tac buggy_E1 in let E2 := tag_r_tac buggy_E2 in let E3 := tag_l_tac buggy_E3 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 tag_done))).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|"      uconstr(buggy_E3) "]" :=
  let E1 := tag_r_tac buggy_E1 in let E2 := tag_r_tac buggy_E2 in let E3 := tag_l_tac buggy_E3 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 tag_done))).
Tactic Notation "rew" "["      uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "]" :=
  let E1 := tag_l_tac buggy_E1 in let E2 := tag_l_tac buggy_E2 in let E3 := tag_r_tac buggy_E3 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 tag_done))).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "]" :=
  let E1 := tag_r_tac buggy_E1 in let E2 := tag_l_tac buggy_E2 in let E3 := tag_r_tac buggy_E3 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 tag_done))).
Tactic Notation "rew" "["      uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "]" :=
  let E1 := tag_l_tac buggy_E1 in let E2 := tag_r_tac buggy_E2 in let E3 := tag_r_tac buggy_E3 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 tag_done))).
Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "]" :=
  let E1 := tag_r_tac buggy_E1 in let E2 := tag_r_tac buggy_E2 in let E3 := tag_r_tac buggy_E3 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 tag_done))).

Tactic Notation "rew" "["      uconstr(buggy_E1) "|"      uconstr(buggy_E2) "|"      uconstr(buggy_E3) "|"      uconstr(buggy_E4) "]" :=
  let E1 := tag_l_tac buggy_E1 in let E2 := tag_l_tac buggy_E2 in let E3 := tag_l_tac buggy_E3 in let E4 := tag_l_tac buggy_E4 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 ltac:(tag_subterms E4 tag_done)))).

Tactic Notation "rew" "[" "<-" uconstr(buggy_E1) "|" "<-" uconstr(buggy_E2) "|" "<-" uconstr(buggy_E3) "|" "<-" uconstr(buggy_E4) "]" :=
  let E1 := tag_r_tac buggy_E1 in let E2 := tag_r_tac buggy_E2 in let E3 := tag_r_tac buggy_E3 in let E4 := tag_r_tac buggy_E4 in
  goal_rewrite ltac:(tag_subterms E1 ltac:(tag_subterms E2 ltac:(tag_subterms E3 ltac:(tag_subterms E4 tag_done)))).


Tactic Notation "rew" "?" uconstr(avoid_capture_E) := repeat (rew avoid_capture_E).
Tactic Notation "rew" "!" uconstr(avoid_capture_E) := rew avoid_capture_E; repeat (rew avoid_capture_E).

Tactic Notation "rew" "?" int_or_var(number_of_times) uconstr(avoid_capture_E) := do number_of_times (try rew avoid_capture_E).
Tactic Notation "rew" "!" int_or_var(number_of_times) uconstr(avoid_capture_E) := do number_of_times (rew avoid_capture_E).

Tactic Notation "rew" "<-" "?" uconstr(avoid_capture_E) := repeat (rew <-avoid_capture_E).
Tactic Notation "rew" "<-" "!" uconstr(avoid_capture_E) := rew <-avoid_capture_E; repeat (rew <-avoid_capture_E).

Tactic Notation "rew" "<-" "?" int_or_var(number_of_times) uconstr(avoid_capture_E) := do number_of_times (try rew <-avoid_capture_E).
Tactic Notation "rew" "<-" "!" int_or_var(number_of_times) uconstr(avoid_capture_E) := do number_of_times (rew <-avoid_capture_E).


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
    rew <-E2' at 1 2 in H. Show Proof.
  Abort.
End test.

Section test.
  Context (P Q R R2 : Ω).
  Context (E:aimpl P Q).
  Context (E2:aimpl R R2).

  Let G := (R ⊸ Q) ⊠ (R ⊸ Q).
  Goal G. unfold G.
    rew [ <-E | E2 ].
    Show Proof.
  Abort.
End test.
*)
