Require Import abstract_algebra.
Require Import prop_eq tactics.misc rewrite.
Require Export quote.base.

Definition quote_tag `(f:X ⇾ Y) x := f x.
Definition quote_tag_eq `(f:X ⇾ Y) x : quote_tag f x ≡ f x := eq_refl.

(** Returns the constr [t] with [lrewrite_tag_l] replaced by [lewrite_tag_r] *)
Ltac quote_swap_tags t :=
  lazymatch t with
    | context C [ arewrite_tag_l ?E ] =>
      let t' := context C [ arewrite_tag_r E ] in quote_swap_tags t'
    | _ => t
  end.

(** Finds all "tagged" occurences in [tagged_tm] of [f ?x] ---
   that is, subterms [quote_tag f x] --- quotes them with
   quote_source, introducing equations [E : f x = _] into the context,
   finally running the continuation [k], passing [tagged_tm] with
   each subterm [quote_tag f x] replaced by [lrewrite_tag_l ?E] *)
Ltac quote_tagged_subterms_then f tagged_tm k :=
  lazymatch tagged_tm with
  | context C [ @quote_tag ?X ?Y ?f ?x ] =>
      let q := quote_source f x in
      lazymatch q with
      | quote_refl f _ =>
          let t' := context C [ func_op f x ] in
          quote_tagged_subterms_then f t' k
      | _ =>
        let E := fresh "E" in pose proof q as E;
        unfold quote in E;
        let t' := context C [ arewrite_tag_l E ] in
        quote_tagged_subterms_then f t' k
      end
  | _ => k tagged_tm
  end.

(** Tags occurences of [f ?x] in [tm] and invokes [quote_tagged_subterms] *)
Ltac tag_and_quote_then f tm k :=
  let tagged_tm := run_tactic_on_term tm ltac:(rewrite <-?(quote_tag_eq f _)) in
  quote_tagged_subterms_then f tagged_tm k.

(** Rewrite occurences of [f ?x] in the goal, expanding any structure
   preserving properties *)
Ltac rewrite_preserves f :=
  let g := lazymatch goal with |- ?G => G end in
  notypeclasses refine (_ _); [
    let clear_tags t := eval unfold arewrite_tag_l, arewrite_tag_r in t in
    let with_tagged_term tagged_Q :=
      let tagged_P := quote_swap_tags tagged_Q in
      let pf := proper_solution (sprop.impl tagged_P tagged_Q) in
      let P := clear_tags tagged_P in
      let Q := clear_tags tagged_Q in
      (echange (sprop.impl P Q)); refine pf
    in
    tag_and_quote_then f g with_tagged_term
    | ].
