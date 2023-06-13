Require Import interfaces.notation prop_eq sprop tactics.easy srelations tactics.misc rewrite.base.

Definition srewrite_tag_l `{R:srelation A} `(E:R a b) := a.
Definition srewrite_tag_r `{R:srelation A} `(E:R a b) := b.
Definition srewrite_tag_l_eq `{R:srelation A} `(E:R a b) : srewrite_tag_l E ≡ a := eq_refl.
Definition srewrite_tag_r_eq `{R:srelation A} `(E:R a b) : srewrite_tag_r E ≡ b := eq_refl.

Global Hint Unfold srewrite_tag_l : typeclass_instances.
Global Hint Unfold srewrite_tag_r : typeclass_instances.

Global Hint Extern 0 (RewriteSwapTag (@srewrite_tag_r ?A ?R ?a ?b ?E))
  => simple refine (DeclareRewriteSwapTag (@srewrite_tag_l A R a b E)) : rewrite_swap_tag.
Global Hint Extern 0 (RewriteSwapTag (@srewrite_tag_l ?A ?R ?a ?b ?E))
  => simple refine (DeclareRewriteSwapTag (@srewrite_tag_r A R a b E)) : rewrite_swap_tag.

(** Proves [ R2 a b → R a b ], by finding an [ sSubrelation ] instance *)
Local Ltac handle_subrel R2 R :=
  lazymatch R2 with
  | R => exact (λ E, E)
  | _ => solve [ let S := get_instance (sSubrelation R2 R) in simple refine (S _ _)
               | let g := get_goal in
                   idtac "No sSubrelation instance found to show" g;
                   fail 1 "No sSubrelation instance found to show" g ]
  end.

(** Proves [ R2 b a → R a b ], by applying symmetry and invoking [ handle_subrel ] if needed. *)
Local Ltac handle_symmetry R2 R a b :=
  let error _ := (let g := get_goal in
                  idtac "No sSymmetric instance found to show" g;
                  fail 1 "No sSymmetric instance found to show" g) in
  lazymatch R with
  | R2 => solve [ let S := get_instance (sSymmetric R2) in simple refine (S _ _)
                | error ltac:(0) ]
  | _  => first [ let S := get_instance (sSymmetric R2) in
                  let H := fresh in intro H; cut (R2 a b); [ clear H | simple refine (S _ _ H) ]
                | let S := get_instance (sSymmetric R) in
                  let H := fresh in intro H; cut (R b a); [ clear H; simple refine (S _ _) | revert H ]
                | error ltac:(0) ];
          handle_subrel R2 R
  end.

Local Ltac fixup_given_sym _ :=
  lazymatch goal with
  | |- ?R2 ?b ?a → ?R ?a ?b => handle_symmetry R2 R a b
  | |- ?P → ?R ?a ?b =>
    echange (_ b a → R a b);
    lazymatch goal with |- ?R2 _ _ → _ => handle_symmetry R2 R a b end
  end.

Local Ltac fixup_given _ :=
  lazymatch goal with
  | |- ?R2 ?a ?b → ?R ?a ?b => handle_subrel R2 R
  | |- ?P → ?R ?a ?b =>
    echange (_ a b → R a b);
    lazymatch goal with |- ?R2 _ _ → _ => handle_subrel R2 R end
  end.

Local Ltac solve_given_aux fixup E :=
  unfold srewrite_tag_l, srewrite_tag_r;
  simple notypeclasses refine (_ E);
  try lazymatch goal with |- (∀ _ : ?P, ?Q) → ?P2 => change (impl P Q → P2) end;
  fixup ltac:(0).

Local Ltac solve_given := solve_given_aux fixup_given.
Local Ltac solve_given_sym := solve_given_aux fixup_given_sym.

Local Ltac solve_if_given :=
  let error E txt := (
    let g := get_goal in
    let g' := eval unfold srewrite_tag_l, srewrite_tag_r in g in
    let t := type of E in
    txt ltac:(0);
    idtac "  Goal : " g;
    idtac "     = : " g';
    idtac "  Given: " t;
    fail 1 "solve_if_given failed on" g
  ) in
  lazymatch goal with
  | |- ?R (srewrite_tag_l (R:=?R') ?E) (srewrite_tag_r _) =>
         first [ lazymatch R' with R => exact E end (* "exact" can try really hard to unify, so don't always try it *)
               | solve_given E
               | error E ltac:(fun _ => idtac "Could not solve using given relation")
               ]
  | |- ?R (srewrite_tag_r ?E) (srewrite_tag_l _) =>
         first [ solve_given_sym E
               | error E ltac:(fun _ => idtac "Could not solve using (reverse of) given relation")
               ]
  end.

Local Ltac solve_if_refl :=
  lazymatch goal with
  | |- ?R ?a ?a => solve [ refl |
       idtac "Reflexivity failed for" R "on" a;
       fail 1 "Reflexivity failed for" R "on" a ]
  end.

Global Hint Extern 1 => solve_if_given : proper.
Global Hint Extern 1 => solve_if_refl : proper.
