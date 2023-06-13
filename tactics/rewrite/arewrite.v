Require Import interfaces.notation prop_eq sprop srelations tactics.misc tactics.easy rewrite.base logic.aprop.

Definition arewrite_tag_l `{R:A → A → Ω} `(E:R a b) := a.
Definition arewrite_tag_r `{R:A → A → Ω} `(E:R a b) := b.
Definition arewrite_tag_l_eq `{R:A → A → Ω} `(E:R a b) : arewrite_tag_l E ≡ a := eq_refl.
Definition arewrite_tag_r_eq `{R:A → A → Ω} `(E:R a b) : arewrite_tag_r E ≡ b := eq_refl.

Global Hint Unfold arewrite_tag_l : typeclass_instances.
Global Hint Unfold arewrite_tag_r : typeclass_instances.

Global Hint Extern 0 (RewriteSwapTag (@arewrite_tag_r ?A ?R ?a ?b ?E))
  => simple refine (DeclareRewriteSwapTag (@arewrite_tag_l A R a b E)) : rewrite_swap_tag.
Global Hint Extern 0 (RewriteSwapTag (@arewrite_tag_l ?A ?R ?a ?b ?E))
  => simple refine (DeclareRewriteSwapTag (@arewrite_tag_r A R a b E)) : rewrite_swap_tag.

Local Ltac debug_msg tac := idtac.
(* Local Ltac debug_msg tac ::= match goal with |- ?G => tac G end. *)

(** Proves [ R2 a b → R a b ], by finding a [ Subrelation ] instance *)
Local Ltac handle_subrel R2 R :=
  let _ := debug_msg ltac:(fun G => idtac "handle_subrel" R2 R G) in
  lazymatch R2 with
  | R => solve [ refine (λ E, E) ]
  | _ => solve [ let S := get_instance (Subrelation R2 R) in simple refine (andl (S _ _))
               | let S := get_instance (sSubrelation (of_course_rel R2) (of_course_rel R)) in simple refine (S _ _)
               | let g := get_goal in
                   idtac "No Subrelation instance found to show" g;
                   fail 1 "No Subrelation instance found to show" g ]
  end.

(** Proves [ R2 b a → R a b ], by applying symmetry and invoking [ handle_subrel ] if needed. *)
Local Ltac handle_symmetry R2 R a b :=
  let _ := debug_msg ltac:(fun G => idtac "handle_symmetry" R2 R a b G) in
  let error _ := (let g := get_goal in
                  idtac "No Symmetric instance found to show" g;
                  fail 1 "No Symmetric instance found to show" g) in
  lazymatch R with
  | R2 => solve [ let S := get_instance (Symmetric R2) in simple refine (andl (S _ _))
                | error ltac:(0) ]
  | _  => first [ let S := get_instance (Symmetric R2) in
                  let H := fresh in intro H; cut (apos (R2 a b)); [ clear H | simple refine ( andl (S _ _) H) ]
                | let S := get_instance (Symmetric R) in
                  let H := fresh in intro H; cut (apos (R b a)); [ clear H; simple refine ( andl (S _ _) ) | revert H ]
                | error ltac:(0) ];
          handle_subrel R2 R
  end.

Local Ltac fixup_given_sym _ :=
  lazymatch goal with
  | |- apos (?R2 ?b ?a) → apos (?R ?a ?b) => handle_symmetry R2 R a b
  | |- apos ?P → apos (?R ?a ?b) =>
    echange (apos (_ b a) → apos (R a b));
    lazymatch goal with |- apos (?R2 _ _) → _ => handle_symmetry R2 R a b end
  end.

Local Ltac fixup_given _ :=
  let _ := debug_msg ltac:(fun G => idtac "fixup given" G) in
  lazymatch goal with
  | |- apos (?R2 ?a ?b) → apos (?R ?a ?b) => handle_subrel R2 R
  | |- apos ?P → apos (?R ?a ?b) =>
    echange (apos (_ a b) → apos (R a b));
    lazymatch goal with |- apos (?R2 _ _) → _ => handle_subrel R2 R end
  end.

Local Ltac solve_given_aux fixup E :=
  unfold arewrite_tag_l, arewrite_tag_r;
  simple notypeclasses refine (_ E);
  try lazymatch goal with |- (∀ _ : ?P, ?Q) → ?P2 => change (impl P Q → P2) end;
  fixup ltac:(0).

Local Ltac solve_given := solve_given_aux fixup_given.
Local Ltac solve_given_sym := solve_given_aux fixup_given_sym.

Local Ltac solve_if_given :=
  let _ := debug_msg ltac:(fun G => idtac "solve_if_given" G) in
  let error E txt := (
    let g := get_goal in
    let g' := eval unfold arewrite_tag_l, arewrite_tag_r in g in
    let t := type of E in
    txt ltac:(0);
    idtac "  Goal : " g;
    idtac "     = : " g';
    idtac "  Given: " t;
    fail 1 "solve_if_given failed on" g
  ) in
  lazymatch goal with
  | |- apos (?R (arewrite_tag_l (R:=?R') ?E) (arewrite_tag_r _)) =>
         first [ lazymatch R' with R => exact E end (* "exact" can try really hard to unify, so don't always try it *)
               | solve_given E
               | error E ltac:(fun _ => idtac "Could not solve using given relation")
               ]
  | |- apos (?R (arewrite_tag_r ?E) (arewrite_tag_l _)) =>
         first [ solve_given_sym E
               | error E ltac:(fun _ => idtac "Could not solve using (reverse of) given relation")
               ]
  end.

Local Ltac solve_if_refl :=
  lazymatch goal with
  | |- apos (?R ?a ?a) => solve [ refl |
       idtac "Reflexivity failed for" R "on" a;
       fail 1 "Reflexivity failed for" R "on" a ]
  end.

Global Hint Extern 1 => solve_if_given : proper.
Global Hint Extern 1 => solve_if_refl : proper.

