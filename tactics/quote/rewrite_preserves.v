Require Import abstract_algebra.
Require Import tactics.misc rewrite.
Require Export quote.base.

Definition quote_tag `(f:X ⇾ Y) x := f x.
Definition unfold_quote {X Y} {f : X ⇾ Y} {x y} (q : quote f x y) : f x = y := q.

(** Recursively walk the marks + tagged term from [match_tag_on_subterms],
    replacing each [quote_tag f x] with [arewrite_tag_l (quote_source f x)]
    when [quote_source] produces a non-trivial equation, or leaving the tag
    as-is (with [skip_match]) for [quote_refl] results.

    Must be called inside [constr:(ltac:(...))] since it returns via [exact]. *)
Ltac quote_replace_tags marks tm :=
  lazymatch marks with
  | found_match =>
      exact (mark found_match tm)
  | mark skip_match ?ms =>
      lazymatch tm with
      | (fun (binder : ?T) => ?body) (@quote_tag ?X ?Y ?ff ?x) =>
          let q := quote_source ff x in
          let inner := eval_under_binder
            ltac:(fun _ b => quote_replace_tags ms b) binder T body in
          lazymatch inner with (fun binder' : ?T => mark ?ms' ?body') =>
            lazymatch q with
            | quote_refl _ _ =>
                exact (mark (mark skip_match ms')
                  ((fun binder' : T => body') (quote_tag ff x)))
            | _ =>
                exact (mark (mark found_match ms')
                  ((fun binder' : T => body') (arewrite_tag_l (unfold_quote q))))
            end
          end
      end
  end.

(** Tag tactic for [goal_rewrite]: finds all [f ?x] subterms via
    [match_tag_on_subterms], expands structure-preserving properties
    via [quote_source], and produces the swapped tag pair. *)
Ltac quote_tag_tac f tm :=
  let tagged := match_tag_on_subterms uconstr:(quote_tag f _) tag_done tm in
  lazymatch tagged with mark ?m ?t =>
    let r := constr:(ltac:(quote_replace_tags m t)) in
    lazymatch r with mark ?m' ?t' =>
      swap_tags uconstr:(quote_tag f _) m' t'
    end
  end.

(** Rewrite occurrences of [f ?x] in the goal or a hypothesis, expanding
    any structure preserving properties of [f] (e.g., [f(a+b) = f a + f b]). *)
Tactic Notation "rewrite_preserves" uconstr(f) :=
  goal_rewrite ltac:(quote_tag_tac f).
Tactic Notation "rewrite_preserves" uconstr(f) "in" hyp(H) :=
  hyp_rewrite H ltac:(quote_tag_tac f).

