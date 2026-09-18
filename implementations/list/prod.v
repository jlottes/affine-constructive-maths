Require Import interfaces.set abstract_algebra bundled_algebra interfaces.free_monoid.
Require Import interfaces.sprop relations theory.set theory.groups theory.bundled_groups.
Require Import logic.aprop.
Require Import list.base.
Require Import easy rewrite tactics.misc simplify.
Require Import set_lambda.

Local Open Scope sg_op_scope.

Definition prod_list X := list X.
Global Hint Extern 1 (Equiv (prod_list _)) => refine (list_equiv aand) : typeclass_instances.

Local Instance prod_list_is_set X : IsSet (prod_list X).
Proof. split; hnf; unfold equiv.
+ induction x as [|x₀ x]; now simpl.
+ induction x as [|x₀ x]; intros [|y₀ y]; try now simpl.
  change list with prod_list in *.
  change (x₀ = y₀ ∧ x = y ⊸ y₀ = x₀ ∧ y = x).
  refine (aand_proper_aimpl _ (IHx y)).
  now apply symmetry.
+ induction x as [|x₀ x]; intros [|y₀ y][|z₀ z]; try now simpl.
  change list with prod_list in *.
  change ((x₀ = y₀ ∧ x = y) ⊠ (y₀ = z₀ ∧ y = z) ⊸ (x₀ = z₀ ∧ x = z)).
  rew (aand_aprod_swap _ _ _ _). refine (aand_proper_aimpl _ (IHx y z)).
  now apply transitivity.
Qed.

Canonical Structure ProdList X := set_make (prod_list X).
Local Notation "X *" := (ProdList X) (at level 1, left associativity, format "X *").

Lemma ProdList_is_strong `{!StrongSet X} : StrongSet X*.
Proof. hnf. induction x as [|x₀ x]; intros [|y₀ y][|z₀ z];
    try (simpl; solve [ easy | tautological ]).
  change list with prod_list in *.
  change ((x₀ = y₀ ∧ x = y) ∧ (y₀ = z₀ ∧ y = z) ⊸ (x₀ = z₀ ∧ x = z)).
  rew (aand_assoc _ _ _). rew <-(aand_assoc (x=y) _ _). rew (aand_com (x=y) _).
  rew (aand_assoc _ _ _). rew <-(aand_assoc (x₀=y₀) _ _).
  refine (aand_proper_aimpl _ (IHx y z)).
  now apply strong_transitivity.
Qed.
Global Hint Extern 2 (StrongSet _*) => simple notypeclasses refine ProdList_is_strong : typeclass_instances.

Global Hint Extern 1 (MonUnit _*) => refine nil : typeclass_instances.
Local Abbreviation ε := (mon_unit (M:=_*)).

Lemma ProdList_cons_is_fun X : @IsFun (X × X*) X* (λ '(x, xs), cons x xs).
Proof. now intros [x₀ x][y₀ y]. Qed.
Definition ProdCons {X} : X × X* ⇾ X* := @func_make _ _ _ (ProdList_cons_is_fun X).
Local Notation "x :: y" := (func_op ProdCons (x, y)) (at level 60, right associativity).

Definition ProdList_unit {X} : X ⇾ X* := ap2 (ProdCons ∘ tensor_to_prod _ _) ε.
Local Abbreviation η := ProdList_unit.
Local Notation "[ x ]" := (func_op η x).
Global Hint Extern 1 (Cast ?X (?X *)) => refine ProdList_unit : typeclass_instances.

Definition ProdList_induction {X} (P : X* → Ω) : (∏ x₀ x, P x ⊸ P (x₀ :: x)) → (P ε ⊸ all P) := list_induction P.
Definition ProdList_sinduction {X} (P:X* → SProp) : P ε → (∀ x₀ x, P x → P (x₀ :: x)) → ∀ x, P x := list_sinduction P.

Local Ltac doit P := let x₀ := fresh "x₀" in let x := fresh "x" in let IHx := fresh "IHx" in
  let y₀ := fresh "y₀" in let y := fresh "y" in
  hnf; intros [x y]; revert x y; refine (ProdList_sinduction _ _ _);
  [| intros x₀ x IHx]; intros [|y₀ y];
  [ now change (P 𝐓) | now change (P 𝐅) .. |
    specialize (IHx y); now change (P (x₀ = y₀ ∧ x = y)) ].
Lemma ProdList_DecidableEquality   `{!DecidableEquality   X} : DecidableEquality   X*.  Proof. doit Decidable.   Qed.
Lemma ProdList_RefutativeEquality  `{!RefutativeEquality  X} : RefutativeEquality  X*.  Proof. doit Refutative.  Qed.
Global Hint Extern 2 (DecidableEquality   _*) => simple notypeclasses refine ProdList_DecidableEquality   : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality  _*) => simple notypeclasses refine ProdList_RefutativeEquality  : typeclass_instances.

Import projection_notation.

Local Instance ProdList_match_is_fun@{u} {X Y:set@{u}} : @IsFun (Y × ((X × X* ) ⇾ Y) ⊗ X* ) Y
   (λ p, match π₂ p with
         | nil => π₁ (π₁ p)
         | cons x l => π₂ (π₁ p) (x, l)
         end).
Proof. intros [p [|x l]][q [|y l']].
+ change (p = q ⊠ atrue ⊸ π₁ p = π₁ q). simplify.
  exact (is_fun (prod_proj1 _ _) _ _).
+ change (?P ⊸ ?Q) with (p = q ⊠ afalse ⊸ Q). now simplify.
+ change (?P ⊸ ?Q) with (p = q ⊠ afalse ⊸ Q). now simplify.
+ let f := constr:( set:( (λ '((y, f), q) : (Y × (X × X* ⇾ Y)) ⊗ (X × X* ), f q)) ) in
  exact ( is_fun f (p, (x, l)) (q, (y, l')) ).
Qed.
Definition ProdList_match@{u} {X Y:set@{u}} := curry (@func_make _ _ _ (@ProdList_match_is_fun X Y)).



Definition ProdList_elim_op@{u} {X Y:set@{u}} (f: (X × X*) × Y ⇾ Y) (y:Y) : X* → Y := fix F l :=
match l with
| nil => y
| cons x l => f (x, l, F l)
end.

Local Instance ProdList_elim_is_fun@{u} {X Y:set@{u}} (f: (X × X*) × Y ⇾ Y) : @IsFun (Y × X*) Y
  (tuncurry (ProdList_elim_op f)).
Proof. intros [y l][y' l']. unfold_pair_eq.
  unfold tuncurry, proj1, proj2. revert l l'.
  refine (list_sinduction _ _ _); [| intros x l IH ];
  (refine (list_sdestruct _ _ _); [| intros x' l' ]).
+ now change (y = y' ∧ ε = ε :> X* ⊸ y = y').
+ change (nil = _) with afalse. now simplify.
+ change (_ = nil) with afalse. now simplify.
+ change (ProdList_elim_op f ?y (cons ?x ?l)) with (f (x, l, ProdList_elim_op f y l)).
  rew <-(is_fun f _ _). apply aand_intro; [ exact (aandr _ _) |].
  rew <-(IH l'). change (y = y' ∧ (x = x' ∧ l = l' :> X*) ⊸ y = y' ∧ l = l' :> X*).
  now rew (aandr (x = x') _).
Qed.

Definition ProdList_elim@{u} {X Y:set@{u}} (f: (X × X*) × Y ⇾ Y) : Y × X* ⇾ Y := @func_make _ _ _ (@ProdList_elim_is_fun X Y f).

Definition ProdList_fold_right@{u} {X Y:set@{u}} (f: X × Y ⇾ Y) : X* × Y ⇾ Y
  := ProdList_elim set:(λ '((a, b), c) : (X × X*) × Y, f (a, c)) ∘ prod_swap _ _.

(*
Section fold_right.
  Local Instance fold_right_is_fun {X Y} (f: X × Y ⇾ Y) : @IsFun (X* × Y) Y (λ p, fold_right f (π₁ p) (π₂ p)).
  Proof. intros [x y₀][x' y₀']. unfold proj1, proj2. unfold_pair_eq.
    revert x x'. refine (ProdList_sinduction _ _ _).
  + intros [|x₀ x'].
    * now change (ε = ε :> X* ∧ y₀ = y₀' ⊸ y₀ = y₀').
    * change (ε = cons x₀ x') with afalse. now rew (aand_false_l _).
  + intros x₀ x IH [|x₀' x'].
    * change (x₀ :: x = nil) with afalse. now rew (aand_false_l _).
    * change ( (x₀ = x₀' ∧ x = x') ∧ y₀ = y₀' ⊸ f (x₀, fold_right f x y₀) = f (x₀', fold_right f x' y₀') ).
      rew [(aand_assoc _ _ _) | <- (is_fun f _ _)].
      refine (aand_proper_aimpl _ _); [ refl | exact (IH _) ].
  Qed.

  Definition ProdList_fold_right {X Y} (f: X × Y ⇾ Y) : X* × Y ⇾ Y := @make_fun _ _ _ (fold_right_is_fun f).
End fold_right.
*)

Definition ProdList_concat {X} : X* × X* ⇾ X* := ProdList_fold_right ProdCons.
Global Hint Extern 1 (SgOp _*) => refine (ProdList_concat ∘ tensor_to_prod _ _) : typeclass_instances.

Definition ProdList_induction_alt `(P:X* → Ω) : (∏ x₀ x, P x ⊸ P ([x₀] ∙ x)) → (P ε ⊸ all P)
:= ProdList_induction P.
Definition ProdList_sinduction_alt `(P:X* → SProp) : P ε → (∀ x₀ x, P x → P ([x₀] ∙ x)) → ∀ x, P x
:= ProdList_sinduction P.

Lemma ProdList_sdestruct `(P:X* → SProp) : P ε → (∀ x₀ x, P ([x₀] ∙ x)) → ∀ x, P x.
Proof. intros P0 Ps [|??]; trivial. exact (Ps _ _). Qed.


Local Instance ProdList_concat_assoc X: Associative (X:=X*) (∙).
Proof. refine (ProdList_sinduction_alt _ _ _); [ easy | intros x₀ x IHx ].
  intros y z. change ( [x₀] ∙ (x ∙ (y ∙ z)) = [x₀] ∙ (x ∙ y ∙ z) ).
  now rew (IHx y z).
Qed.

Local Instance ProdList_concat_left_id X: LeftIdentity (X:=X*) (∙) ε.
Proof. now hnf. Qed.

Local Instance ProdList_concat_right_id X: RightIdentity (X:=X*) (∙) ε.
Proof. refine (ProdList_sinduction_alt _ _ _); [ easy | intros x₀ x IHx ].
  change ([x₀] ∙ (x ∙ ε) = [x₀] ∙ x). now rew IHx.
Qed.

Local Instance ProdList_is_str_monoid {X} : StrongOpMonoid X*.
Proof. split; [ now apply alt_Build_Monoid | exact _ ]. Qed.
Global Hint Extern 2 (StrongOpMonoid _*) => simple notypeclasses refine ProdList_is_str_monoid : typeclass_instances.
Global Hint Extern 2 (Monoid _*) => simple notypeclasses refine ProdList_is_str_monoid : typeclass_instances.
Global Hint Extern 2 (SemiGroup _*) => simple notypeclasses refine ProdList_is_str_monoid : typeclass_instances.

Canonical Structure ProdList_mon (X:set) := make_monoid X*.
Canonical Structure ProdList_str_mon (X:set) := make_strong_op_monoid X*.

Global Hint Extern 1 (Cast ?X (strong_op_monoid_car (ProdList_str_mon ?X))) => refine ProdList_unit : typeclass_instances.

Section to_monoid.
  Universes u.
  Context {X:set@{u}} {M:strong_op_monoid@{u}}.
  Abbreviation e := (mon_unit (M:=strong_op_monoid_car M)).

  Definition ProdList_to_monoid_op (f:X ⇾ M) : X* ⇾ M :=
    set:(λ x, ProdList_fold_right (set:(λ '(a, b) : X × M, f a ∙ b)) (x, e)).
  Local Abbreviation ϕ := ProdList_to_monoid_op.

  Local Instance ProdList_to_monoid_is_fun : IsFun ϕ.
  Proof. intros f g. change (f = g ⊸ ∏ x, ϕ f x = ϕ g x). rew <-all_adj.
    refine (ProdList_sinduction_alt _ _ _); [| intros a x IH ].
  + change (f = g ⊸ e = e). now rew (aiff_is_true (_ : e = e)).
  + change (f = g ⊸ f a ∙ ϕ f x = g a ∙ ϕ g x).
    rew <-( (_ : StrongOp (∙)) (f a, ϕ f x) (g a, ϕ g x) ); apply aand_intro; trivial.
    exact (all_lb _ a).
  Qed.

  Definition ProdList_to_monoid : _ ⇾ _ := func_make ϕ.

  Local Notation "X ⟶ Y" := (strong_op_monoid_morphism X Y).

  Section with_f.
    Context (f: X ⇾ M).
    Local Abbreviation g := (ProdList_to_monoid_op f).

    Lemma ProdList_to_monoid_is_mon_mor : Monoid_Morphism g.
    Proof. apply alt_Build_Monoid_Morphism; [| refl].
      refine (ProdList_sinduction_alt _ _ _); [| intros a x IH ]; intros y.
    + change (g y = e ∙ g y). now group_simplify.
    + change (f a ∙ g (x ∙ y) = (f a ∙ g x) ∙ g y).
      rew (IH y). now group_simplify.
    Qed.

    Lemma ProdList_to_monoid_spec : f = g ∘ η.
    Proof. intros a. change (f a = f a ∙ e). now group_simplify. Qed.

    Lemma ProdList_to_monoid_unique (h:X* ⟶ M) : f = h ∘ η → h = g :> (X* ⇾ M).
    Proof. pose proof ProdList_to_monoid_is_mon_mor.
      intros E. refine (ProdList_sinduction_alt _ _ _).
    + now rew (preserves_unit _).
    + intros x₀ x IH. rew (preserves_sg_op _ _ _).
      now rew [ IH | <-(E x₀ : f x₀ = h (η x₀)) | <-(ProdList_to_monoid_spec x₀ : f x₀ = g (η x₀)) ].
    Qed.
  End with_f.

  Definition ProdList_to_monoid_mon_mor@{} : (X ⇾ M) ⇾ (X* ⟶ M).
  Proof. simple refine (func_make (λ f, make_monoid_morphism (ProdList_to_monoid_op f))).
  + exact (ProdList_to_monoid_is_mon_mor f).
  + exact ProdList_to_monoid_is_fun.
  Defined.
End to_monoid.
Canonical ProdList_to_monoid.
Global Hint Extern 1 (FromFreeStrongMonoid (cast ?X (ProdList ?X))) => refine (@ProdList_to_monoid_mon_mor _) : typeclass_instances.
Global Hint Extern 1 (FromFreeStrongMonoid (cast ?X (strong_op_monoid_car (ProdList_str_mon ?X)))) => refine (@ProdList_to_monoid_mon_mor _) : typeclass_instances.
Global Hint Extern 1 (FromFreeStrongMonoid ProdList_unit) => refine (@ProdList_to_monoid_mon_mor _) : typeclass_instances.

Lemma ProdList_FreeStrongMonoid {X} : FreeStrongMonoid (X:=X) η.
Proof. split; intros M f.
+ apply ProdList_to_monoid_spec.
+ apply ProdList_to_monoid_unique.
Qed.

Global Hint Extern 2 (FreeStrongMonoid (cast ?X (ProdList ?X))) => notypeclasses refine ProdList_FreeStrongMonoid : typeclass_instances.
Global Hint Extern 2 (FreeStrongMonoid (cast ?X (strong_op_monoid_car (ProdList_str_mon ?X)))) => notypeclasses refine ProdList_FreeStrongMonoid : typeclass_instances.
Global Hint Extern 2 (FreeStrongMonoid ProdList_unit) => notypeclasses refine ProdList_FreeStrongMonoid : typeclass_instances.

Definition ProdList_map `(f:X ⇾ Y) := ProdList_to_monoid_mon_mor (ProdList_unit ∘ f).
Definition ProdList_map_in_bounds `(f:X ⇾ Y) : ∀ (l:X*) n,  ListInBounds l n → ListInBounds (ProdList_map f l) n := list_map_in_bounds f.
Global Hint Extern 2 (ListInBounds (func_op (monoid_morphism_fun (ProdList_map ?f)) ?l) ?n) => simple notypeclasses refine (ProdList_map_in_bounds f l n _) : typeclass_instances.
