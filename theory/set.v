Require Export interfaces.set.
Require Import sprop relations.
Require Import logic.aprop tauto.
Require Import easy rewrite tactics.misc simplify.base.

Local Open Scope set_scope.

Lemma tprod_inhabited `{Inhabited A} `{Inhabited B} : Inhabited (A ∗ B).
Proof. pose proof inhabited A as [a _]. pose proof inhabited B as [b _]. now exists (a, b). Qed.
#[global] Hint Extern 2 (Inhabited (_ ∗ _)) => simple notypeclasses refine tprod_inhabited : typeclass_instances.
#[global] Hint Extern 2 (Inhabited (set_T (_ ⊗ _))) => simple notypeclasses refine tprod_inhabited : typeclass_instances.
#[global] Hint Extern 2 (Inhabited (set_T (_ × _))) => simple notypeclasses refine tprod_inhabited : typeclass_instances.


Global Hint Extern 2 (apos (aimpl (equiv _, _))) => sapply_2 (Transitive_rel_proper_aimpl (=)) : proper.
Global Hint Extern 2 (apos (aiff  (equiv _, _))) => sapply_2 (PER_rel_proper_aiff (=)) : proper.

Lemma prod_pair_proper@{u} {X Y : set@{u}} {x₁ x₂ : X} {y₁ y₂ : Y} :
  x₁ = x₂ → y₁ = y₂ → (x₁, y₁) = (x₂, y₂) :> X × Y.
Proof. now split. Qed.
Lemma tensor_pair_proper@{u} : ∀ {X Y : set@{u}} {x₁ x₂ : X} {y₁ y₂ : Y},
  x₁ = x₂ → y₁ = y₂ → (x₁, y₁) = (x₂, y₂) :> X ⊗ Y.
Proof. exact @prod_pair_proper. Qed.
Global Hint Extern 2 (apos (pair _ _ = _ :> set_T (_ × _) )) => sapply_2 prod_pair_proper : proper.
Global Hint Extern 2 (apos (pair _ _ = _ :> set_T (_ ⊗ _) )) => sapply_2 tensor_pair_proper : proper.
Global Hint Extern 2 (apos (pair _ _ = _ :> _ ∗ _ ))
  => first [ sapply_2 prod_pair_proper
           | sapply_2 tensor_pair_proper ] : proper.


Global Hint Extern 1 (Subrelation (@equiv _ ?R) (@equiv _ ?R)) =>
  simple notypeclasses refine (Subrelation_refl_applied _) : typeclass_instances.
Global Hint Extern 3 (Subrelation (=) (=)) =>
  simple notypeclasses refine (Subrelation_refl_applied _) : typeclass_instances.
Global Hint Extern 10 (sSubrelation
  (fun p => apos (of_course_rel (fun x => apos (equiv x)) p))
  (fun p => apos (of_course_rel (fun x => apos (equiv x)) p))) =>
  simple notypeclasses refine (srelations.sSubrelation_refl_applied _) : typeclass_instances.



Definition eval_pt@{u} {A:Type@{u}} {Y:set@{u}} (x:A) : (A → Y) ⇾ Y
  := @func_make _ _ (λ f, f x) (λ f g, all_lb _ x).

Lemma func_op_is_fun@{u} {X Y:set@{u}} : @IsFun (X ⇾ Y) (X → Y) func_op.
Proof. now intros f g. Qed.
#[global] Hint Extern 2 (IsFun func_op) => simple notypeclasses refine func_op_is_fun : typeclass_instances.

Canonical func_op_fun@{u} (X Y:set@{u}) : (X ⇾ Y) ⇾ (X → Y) := func_make func_op.


(** There is a comonad "!" where !X forgets the refutative part of equality. *)

Global Hint Extern 4 (@IsSet _ (of_course_rel (λ p, apos (equiv p)))) => lazymatch goal with |- @IsSet _ ?R => change (Equivalence R) end : typeclass_instances.
Definition of_course_set (X:set) : set := set_make X (set_eq := of_course_rel (=)).

Global Hint Extern 10 (apos (?a = ?b :> set_T (of_course_set ?X) )) => change (apos (a = b :> set_T X)) : proper.

Module of_course_set_notation.
  Notation "! X" := (of_course_set X) (at level 7, right associativity, format "! X") : set_scope.
End of_course_set_notation.
Import of_course_set_notation.

Lemma of_course_set_aff_eq {X:set} : AffirmativeEquality !X.
Proof. now change (AffirmativeRelation (of_course_rel (A:=X∗X) (=))). Qed.
Global Hint Extern 2 (AffirmativeEquality !_) => simple notypeclasses refine of_course_set_aff_eq : typeclass_instances.

Definition of_course_counit_is_fun {X:set} : @IsFun !X X id := tautology.
Definition of_course_counit X : !X ⇾ X := @func_make _ _ _ (@of_course_counit_is_fun X).

Lemma of_course_map_is_fun `(f:X ⇾ Y) : @IsFun (!X) (!Y) f.
Proof. intros x₁ x₂. apply affirmative_aimpl. intros E. now apply (is_fun f _ _). Qed.
Definition of_course_map `(f:X ⇾ Y) : !X ⇾ !Y := @func_make _ _ _ (of_course_map_is_fun f).

(** Co-multiplication is definitionally the identity: !X ≡ !!X *)

Ltac flatten_of_course_set tm :=
  lazymatch tm with
  | context f [ !! ?X ] =>
    let tm' := context f [ !X ] in
    flatten_of_course_set tm'
  | _ => tm
  end.

Definition of_course_extend {X Y} (f:!X ⇾ Y) : !X ⇾ !Y := of_course_map f.

Lemma of_course_equiv_subrel {X:set} : @Subrelation (set_T X ∗ set_T X) (@equiv (set_T X) (set_eq (of_course_set X))) (=).
Proof. tautological. Qed.
Global Hint Extern 2 (Subrelation (@equiv _ (set_eq (of_course_set ?X))) (@equiv _ (set_eq ?X))) =>
  simple notypeclasses refine of_course_equiv_subrel : typeclass_instances.

Definition of_course_tensor_set X Y : !(X ⊗ Y) ⇾ (!X ⊗ !Y) := @func_make (set_T !(X ⊗ Y)) (set_T (!X ⊗ !Y)) id tautology.
Definition of_course_tensor_set_inv@{u} (X Y : set@{u}) : (!X ⊗ !Y) ⇾ !(X ⊗ Y) := @func_make (set_T (!X ⊗ !Y)) (set_T !(X ⊗ Y)) id tautology.
Global Hint Extern 1 (Inverse (of_course_tensor_set ?X ?Y)) => refine (of_course_tensor_set_inv X Y) : typeclass_instances.
Global Hint Extern 1 (Inverse (of_course_tensor_set_inv ?X ?Y)) => refine (of_course_tensor_set X Y) : typeclass_instances.

Definition of_course_prod_set X Y : !(X × Y) ⇾ (!X ⊗ !Y) := @func_make (set_T !(X × Y)) (set_T (!X ⊗ !Y)) id tautology.
Definition of_course_prod_set_inv@{u} (X Y : set@{u}) : (!X ⊗ !Y) ⇾ !(X × Y) := @func_make (set_T (!X ⊗ !Y)) (set_T !(X × Y)) id tautology.
Global Hint Extern 1 (Inverse (of_course_prod_set ?X ?Y)) => refine (of_course_prod_set_inv X Y) : typeclass_instances.
Global Hint Extern 1 (Inverse (of_course_prod_set_inv ?X ?Y)) => refine (of_course_prod_set X Y) : typeclass_instances.

Global Hint Extern 2 (apos (?x = ?y :> set_T( !(?X ⊗ ?Y)))) =>  change (x = y :> !X ⊗ !Y) : proper.
Global Hint Extern 2 (apos (?x = ?y :> set_T( !(?X × ?Y)))) =>  change (x = y :> !X ⊗ !Y) : proper.

Definition of_course_op@{u} {X Y Z : set@{u}} (f:X ⊗ Y ⇾ Z) : !X ⊗ !Y ⇾ !Z
 := of_course_map f ∘ of_course_tensor_set_inv _ _.

Definition of_course_extend2@{u} {X Y Z:set@{u}} (f:!X ⊗ !Y ⇾ Z) : !X ⊗ !Y ⇾ !Z := of_course_op f.

Ltac make_fun_alt_tac f H :=
  let H' := constr:(H : IsFun _) in
  lazymatch type of H' with @IsFun ?X ?Y _ =>
    let X' := flatten_of_course_set X in
    let Y' := flatten_of_course_set Y in
    exact (@func_make X' Y' f H : X' ⇾ Y')
  end.

Abbreviation make_fun_alt f H := ltac:(make_fun_alt_tac f H) (only parsing).


Lemma IsWeakFun@{u} {X Y : set@{u}} (f:X → Y) : (∀ x y, x = y → f x = f y) → @IsFun !X !Y f.
Proof. intros H x y. apply affirmative_aimpl. now apply H. Qed.
Definition make_weak_fun {X Y : set} (f:X → Y) (H:∀ x y, x = y → f x = f y) : !X ⇾ !Y
  := make_fun_alt f (IsWeakFun f H).


Lemma simplifies_of_course_set {X:set} {x x' : X} `{!SimplifiesTo x x'} : @SimplifiesTo (of_course_set X) x x'.
Proof. split. exact (simplify x). Qed.
Global Hint Extern 1 (@SimplifiesTo (of_course_set _) _ _) => notypeclasses refine simplifies_of_course_set : typeclass_instances.


#[global] Hint Extern 1 (Coerce (! ?X) ?X) => exact (of_course_counit X) : typeclass_instances.
#[global] Hint Extern 2 (Coerce (! ?X) (! ?Y)) => simple notypeclasses refine (of_course_extend (coerce (!X) Y)) : typeclass_instances.
#[global] Hint Extern 2 (Coerce (! (?X ⊗ ?Y)) ?Z) => simple notypeclasses refine (coerce (!X ⊗ !Y) Z ∘ of_course_tensor_set X Y) : typeclass_instances.
#[global] Hint Extern 2 (Coerce (! (?X × ?Y)) ?Z) => simple notypeclasses refine (coerce (!X ⊗ !Y) Z ∘ of_course_prod_set X Y) : typeclass_instances.
#[global] Hint Extern 99 (Coerce (! ?X) _) => simple notypeclasses refine (of_course_counit X) : typeclass_instances.


Coercion IsDecEq_DecidableEquality `{H:IsDecEq X} : DecidableEquality X := IsDec_Decidable.

Coercion dec_eq_aff_eq {X:set} {H:DecidableEquality X} : AffirmativeEquality X := H.
Coercion dec_eq_ref_eq {X:set} {H:DecidableEquality X} : RefutativeEquality X := H.
Coercion dec_eq_strong {X:set} `{!DecidableEquality X} : StrongSet X := dec_trans_strong (=).

Lemma dec_strong_op_l `(f:X ⊗ Y ⇾ Z) `{!DecidableEquality X} : StrongOp f.
Proof. intros [x₁ y₁][x₂ y₂]. change (x₁ = x₂ ∧ y₁ = y₂ ⊸ f (x₁, y₁) = f (x₂, y₂)).
  rew (aand_aprod_dec_l _ _). exact (is_fun f (x₁, y₁) (x₂, y₂)).
Qed.

Lemma dec_strong_op_r `(f:X ⊗ Y ⇾ Z) `{!DecidableEquality Y} : StrongOp f.
Proof. intros [x₁ y₁][x₂ y₂]. change (x₁ = x₂ ∧ y₁ = y₂ ⊸ f (x₁, y₁) = f (x₂, y₂)).
  rew (aand_aprod_dec_r _ _). exact (is_fun f (x₁, y₁) (x₂, y₂)).
Qed.

Lemma unit_inhabited : Inhabited unit.
Proof. now exists tt. Qed.
#[global] Hint Extern 1 (Inhabited unit) => simple notypeclasses refine unit_inhabited : typeclass_instances.
#[global] Hint Extern 1 (Inhabited set_T 𝟏) => simple notypeclasses refine unit_inhabited : typeclass_instances.

Definition unit_eq_dec : Dec (A:=𝟏∗𝟏) (=) := λ p, true.
Global Hint Extern 1 (Dec (A:=unit ∗ unit) (=)) => refine unit_eq_dec : typeclass_instances.
Global Hint Extern 1 (Dec (A:=set_T 𝟏 ∗ set_T 𝟏) (=)) => refine unit_eq_dec : typeclass_instances.
Lemma unit_is_dec_eq : IsDecEq 𝟏. Proof. tautological. Qed.
Global Hint Extern 1 (IsDecEq 𝟏) => refine unit_is_dec_eq : typeclass_instances.
Global Hint Extern 1 (DecidableEquality 𝟏) => refine unit_is_dec_eq : typeclass_instances.
Global Hint Extern 1 (AffirmativeEquality 𝟏) => refine unit_is_dec_eq : typeclass_instances.
Global Hint Extern 1 (RefutativeEquality 𝟏) => refine unit_is_dec_eq : typeclass_instances.


Definition empty_eq_dec : Dec (A:=𝟎∗𝟎) (=) := λ p, true.
Global Hint Extern 1 (Dec (A:=empty∗empty) (=)) => refine empty_eq_dec : typeclass_instances.
Global Hint Extern 1 (Dec (A:=set_T 𝟎 ∗ set_T 𝟎) (=)) => refine empty_eq_dec : typeclass_instances.
Lemma empty_is_dec_eq : IsDecEq 𝟎. Proof. tautological. Qed.
Global Hint Extern 1 (IsDecEq 𝟎) => refine empty_is_dec_eq : typeclass_instances.
Global Hint Extern 1 (DecidableEquality 𝟎) => refine empty_is_dec_eq : typeclass_instances.
Global Hint Extern 1 (AffirmativeEquality 𝟎) => refine empty_is_dec_eq : typeclass_instances.
Global Hint Extern 1 (RefutativeEquality 𝟎) => refine empty_is_dec_eq : typeclass_instances.


Definition strong_set_make A {Ae: Equiv A}
  `{!Reflexive (A:=A) (=)}
  `{!Symmetric (A:=A) (=)}
  `{!StronglyTransitive (A:=A) (=)}
:= make_strong_set (@set_make A Ae (Build_Equivalence _ _ _ _)).


Lemma operation_proper_equiv@{u} {A:Type@{u}} {Y B:set@{u}} (f g : A → Y) (x : A) {c:Coerce Y B} :
  (f = g) → (coerce Y B (f x) = coerce Y B (g x)).
Proof. intros E. apply (is_fun (coerce Y B)). exact (E x). Qed.

Lemma func_proper_equiv {X Y} (f g : func X Y) (x₁ x₂ : X) `{c:Coerce Y A} :
  (f = g) → (x₁ = x₂) → ((coerce Y A ∘ f) x₁ = (coerce Y A ∘ g) x₂).
Proof. intros Ef Ex. trans ((coerce Y A ∘ g) x₁); [| now apply (is_fun _ _ _)].
  enough (coerce Y A ∘ f = coerce Y A ∘ g) as E by refine (E _).
  apply (is_fun (∘)). now split.
Qed.
Global Hint Extern 2 (apos (func_op ?f ?x = func_op ?g ?y)) => sapply_2 (func_proper_equiv f g x y) : proper.

(* Nonlinear [?f … ?f] patterns silently fail when the two sides differ only
   in universe instances; match linearly and guard with [lazymatch f with g]
   (universe-insensitive), letting the body collapse universes by unification.
   Same idiom in orders/maps.v. *)
Global Hint Extern 10 (apos (?f ?x₁ ?x₂ ?x₃ = ?g ?y₁ ?y₂ ?y₃ :> ?A)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) (eval_tuncurry3 f)) in
  change (f' (x₁, x₂, x₃) = f' (y₁, y₂, y₃) :> A) end : proper.
Global Hint Extern 11 (apos (?f ?x₁ ?x₂ = ?g ?y₁ ?y₂ :> ?A)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) (tuncurry f)) in
  change (f' (x₁, x₂) = f' (y₁, y₂) :> A) end : proper.
(*Global Hint Extern 12 (apos (?f ?x = ?f ?y :> ?A)) =>
  let f' := eval red in (@id (func _ _) f) in
  progress change (f' x = f' y :> A) : proper.*)
Global Hint Extern 12 (apos (?f ?x = ?g ?y :> ?A)) =>
  lazymatch x with
  | y => sapply_1 (operation_proper_equiv f g x)
  | _ => sapply_2 (func_proper_equiv f g x y)
  end  : proper.

Section functions.
  Universes u.
  Lemma func_set_Strong {X Y:set@{u}} `{!StrongSet Y} : StrongSet (X ⇾ Y).
  Proof. intros f g h.
    change ((∏ x, f x = g x) ∧ (∏ x, g x = h x) ⊸ (∏ x, f x = h x)).
    apply all_adj. intros x.
    rew (all_lb _ x).
    now apply strong_transitivity.
  Qed.

  Lemma func_set_refutative {X Y:set@{u}} `{!RefutativeEquality Y} : RefutativeEquality (X ⇾ Y).
  Proof. intros [f g]. now change (Refutative (∏ x, f x = g x)). Qed.
End functions.
Global Hint Extern 2 (StrongSet (_ ⇾ _)) => eapply func_set_Strong : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality (_ ⇾ _)) => eapply func_set_refutative : typeclass_instances.


Global Hint Extern 2 (SimplifiesTo (id ?x) ?out) => change (SimplifiesTo x out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (func_op (id_fun _) ?x) ?out) => change (SimplifiesTo x out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (id_fun _ ∘ ?f) ?out) => change (SimplifiesTo f out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (?f ∘ id_fun _) ?out) => change (SimplifiesTo f out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (func_op (?f ∘ ?g) ?x) ?out) => change (SimplifiesTo (f (g x)) out)  : typeclass_instances.


(** [Ω] forms a set with ⧟ as equality *)

Global Hint Extern 1 (Equiv Ω) => exact aiff : typeclass_instances.
Global Hint Extern 1 (IsSet Ω) => echange (Equivalence aiff) : typeclass_instances.
Canonical Structure AProp_set := set_make Ω.
Notation "'Ω'" := AProp_set (only printing) : set_scope.

(** From here on, affine-proposition atoms reach [abstract_aprop_atoms] typed as
    [set_T AProp_set] (the carrier of [Ω] as a set) rather than the bare [AProp].
    Extend the recognizer to accept that form so atom abstraction is not silently
    a no-op on set-level membership/equality propositions. *)
Ltac is_aprop_type T ::= first [ constr_eq T AProp | constr_eq T (set_T AProp_set) ].

Import projection_notation.

Definition anot_is_fun  : @IsFun Ω Ω anot := tautology.
Definition aand_is_fun  : @IsFun (Ω × Ω) Ω aand  := tautology.
Definition aor_is_fun   : @IsFun (Ω × Ω) Ω aor   := tautology.
Definition aprod_is_fun : @IsFun (Ω ⊗ Ω) Ω aprod := tautology.
Definition apar_is_fun  : @IsFun (Ω ⊗ Ω) Ω apar  := tautology.
Definition aimpl_is_fun : @IsFun (Ω ⊗ Ω) Ω aimpl := tautology.
Definition aiff_is_fun  : @IsFun (Ω ⊗ Ω) Ω aiff  := tautology.
Canonical Structure anot_fun  : _ ⇾ _ := @func_make _ _ _ anot_is_fun.
Canonical Structure aand_fun  : _ ⇾ _ := @func_make _ _ _ aand_is_fun.
Canonical Structure aor_fun   : _ ⇾ _ := @func_make _ _ _ aor_is_fun.
Canonical Structure aprod_fun : _ ⇾ _ := @func_make _ _ _ aprod_is_fun.
Canonical Structure apar_fun  : _ ⇾ _ := @func_make _ _ _ apar_is_fun.
Canonical Structure aimpl_fun : _ ⇾ _ := @func_make _ _ _ aimpl_is_fun.
Canonical Structure aiff_fun  : _ ⇾ _ := @func_make _ _ _ aiff_is_fun.

Lemma all_is_fun {X} : @IsFun (X ⇾ Ω) Ω all.  Proof. hnf; intros; apply all_aiff. Qed.
Lemma aex_is_fun {X} : @IsFun (X ⇾ Ω) Ω aex.  Proof. hnf; intros; apply aex_aiff. Qed.
Canonical Structure all_fun {X} : _ ⇾ _ := @func_make _ _ _ (@all_is_fun X).
Canonical Structure aex_fun {X} : _ ⇾ _ := @func_make _ _ _ (@aex_is_fun X).

Notation "(∧)" := aand_fun : set_scope.
Notation "(∨)" := aor_fun : set_scope.
Notation "(⊠)" := aprod_fun : set_scope.
Notation "(⊞)" := apar_fun : set_scope.
Notation "(ᗮ)" := anot_fun : set_scope.

Lemma eq_is_fun {X} : @IsFun (X ⊗ X) Ω (=).
Proof. intros [x₁ y₁][x₂ y₂].
  change ( (x₁, y₁) = (x₂, y₂) ) with ( x₁ = x₂ ⊠ y₁ = y₂ ).
  apply aand_intro; rew <-(aprod_adj _ _ _).
  + rew (aprod_assoc _ _ _).
    rew (aprod_com _ (x₁ = y₁)), (transitivity (=) _ _ _).
    rew (symmetry_iff (=) x₁ x₂). exact (transitivity (=) _ _ _).
  + rew (symmetry_iff (=) y₁ y₂). rew (aprod_assoc _ _ _).
    rew (aprod_com _ (x₂ = y₂)), (transitivity (=) _ _ _).
    exact (transitivity (=) _ _ _).
Qed.

Canonical Structure eq_fun {X} : X ⊗ X ⇾ Ω := @func_make _ _ _ (@eq_is_fun X).
Notation "x = y" := (func_op eq_fun (x, y)) (only printing) : set_scope.

Lemma eq_fun_strong `{!StrongSet X} : StrongOp (@eq_fun X).
Proof. intros [x₁ y₁][x₂ y₂].
  change (x₁ = x₂ ∧ y₁ = y₂ ⊸ (x₁ = y₁ ⧟ x₂ = y₂)). apply aand_intro; rew <-(aprod_adj _ _ _).
  + rew <-(strong_transitivity (=) x₂ y₁ y₂). apply aand_intro; [| tautological].
    rew (aandl _ _ ), (symmetry_iff (=) x₁ x₂). exact (transitivity (=) _ _ _).
  + rew <-(strong_transitivity (=) x₁ x₂ y₁). apply aand_intro; [tautological|].
    rew (aandr _ _ ), (aprod_com _ _), (symmetry_iff (=) y₁ y₂). exact (transitivity (=) _ _ _).
Qed.
Global Hint Extern 2 (StrongOp eq_fun) => simple notypeclasses refine eq_fun_strong : typeclass_instances.

(* Linear patterns + [lazymatch f with g] guard — see the comment above the
   [=] congruence hints. *)
Global Hint Extern 10 (apos (func_op ?f ?x ⊸ func_op ?g ?y)) =>
  lazymatch f with g =>
  sapply_1 (andl (aimpl_subrel_aiff (func_op f x, func_op f y)));
  change (func_op f x = func_op f y :> AProp_set) end : proper.
Global Hint Extern 2 (apos (func_op ?f ?x ⧟ func_op ?g ?y)) =>
  lazymatch f with g =>
  change (func_op f x = func_op f y :> AProp_set) end : proper.

Global Hint Extern 20 (apos (?f ?x₁ ?x₂ ?x₃ ⊸ ?g ?y₁ ?y₂ ?y₃)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) (eval_tuncurry3 f)) in
  sapply_1 (andl (aimpl_subrel_aiff (f x₁ x₂ x₃, f y₁ y₂ y₃)));
  change (f' (x₁, x₂, x₃) = f' (y₁, y₂, y₃) :> AProp_set) end : proper.
Global Hint Extern 21 (apos (?f ?x₁ ?x₂ ⊸ ?g ?y₁ ?y₂)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) (tuncurry f)) in
  sapply_1 (andl (aimpl_subrel_aiff (f x₁ x₂, f y₁ y₂)));
  change (f' (x₁, x₂) = f' (y₁, y₂) :> AProp_set) end : proper.
Global Hint Extern 22 (apos (?f ?x ⊸ ?g ?y)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) f) in
  sapply_1 (andl (aimpl_subrel_aiff (f x, f y)));
  change (f' x = f' y :> AProp_set) end : proper.

Global Hint Extern 10 (apos (?f ?x₁ ?x₂ ?x₃ ⧟ ?g ?y₁ ?y₂ ?y₃)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) (eval_tuncurry3 f)) in
  change (f' (x₁, x₂, x₃) = f' (y₁, y₂, y₃) :> AProp_set) end : proper.
Global Hint Extern 11 (apos (?f ?x₁ ?x₂ ⧟ ?g ?y₁ ?y₂)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) (tuncurry f)) in
  change (f' (x₁, x₂) = f' (y₁, y₂) :> AProp_set) end : proper.
Global Hint Extern 12 (apos (?f ?x ⧟ ?g ?y)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) f) in
  change (f' x = f' y :> AProp_set) end : proper.


(** [SProp] forms a set with [↔] as equality *)

Global Hint Extern 1 (Equiv SProp) => exact (of_course_rel iff) : typeclass_instances.
Global Hint Extern 1 (IsSet SProp) => echange (Equivalence (of_course_rel iff)) : typeclass_instances.
Canonical Structure SProp_set := set_make SProp.

Definition SProp_set_aff_eq : AffirmativeEquality SProp_set := tautology.
Global Hint Extern 2 (AffirmativeEquality SProp_set) => simple notypeclasses refine SProp_set_aff_eq : typeclass_instances.

Definition not_is_fun : @IsFun SProp SProp not := tautology.
Definition and_is_fun : @IsFun (SProp ⊗ SProp) SProp (λ P, and  (π₁ P) (π₂ P)) := tautology.
Definition or_is_fun : @IsFun (SProp ⊗ SProp) SProp (λ P, or  (π₁ P) (π₂ P)) := tautology.
Canonical Structure not_fun : _ ⇾ _ := @func_make _ _ _ not_is_fun.
Canonical Structure and_fun : _ ⇾ _ := @func_make _ _ _ and_is_fun.
Canonical Structure or_fun  : _ ⇾ _ := @func_make _ _ _ or_is_fun.

(*Lemma ex_is_fun {X} : @IsFun (of_course_set (X ⇾ SProp)) SProp ex.
Proof. intros P Q. apply affirmative_aimpl. tautological. Qed.
Canonical Structure ex_fun {X} := @make_fun _ _ _ (@ex_is_fun X).*)

Definition of_course_is_fun : @IsFun SProp !Ω of_course := tautology.
Canonical Structure of_course_fun : _ ⇾ _ := @func_make _ _ _ of_course_is_fun.

Definition why_not_is_fun : @IsFun !Ω Ω why_not := tautology.
Canonical Structure why_not_fun : _ ⇾ _ := @func_make _ _ _ why_not_is_fun.

Definition apos_is_fun : @IsFun !Ω SProp apos := tautology.
Canonical Structure apos_fun := @func_make _ _ _ apos_is_fun.

#[global] Hint Extern 2 (Inverse (of_course_fun)) => exact apos_fun : typeclass_instances.
#[global] Hint Extern 2 (Inverse (apos_fun)) => exact of_course_fun : typeclass_instances.

Lemma of_course_inj : Injective of_course_fun.  Proof. tautological. Qed.
Lemma apos_surj : Surjective apos_fun.  Proof. tautological. Qed.
#[global] Hint Extern 2 (Injective of_course_fun) => simple notypeclasses refine of_course_inj : typeclass_instances.
#[global] Hint Extern 2 (Surjective apos_fun) => simple notypeclasses refine apos_surj : typeclass_instances.


Global Hint Extern 10 (impl (func_op ?f ?x, func_op ?f ?y)) =>
  sapply_1 (srelations.impl_sSubrelation_iff (func_op f x, func_op f y));
  change (func_op f x = func_op f y :> SProp_set) : proper.
Global Hint Extern 2 (iff (func_op ?f ?x, func_op ?f ?y)) =>
  change (func_op f x = func_op f y :> SProp_set) : proper.

Global Hint Extern 20 (impl (?f ?x₁ ?x₂ ?x₃, ?f ?y₁ ?y₂ ?y₃)) =>
  let f' := eval red in (@id (func _ _) (eval_tuncurry3 f)) in
  sapply_1 (srelations.impl_sSubrelation_iff (f x₁ x₂ x₃, f y₁ y₂ y₃));
  change (f' (x₁, x₂, x₃) = f' (y₁, y₂, y₃) :> SProp_set) : proper.
Global Hint Extern 21 (impl (?f ?x₁ ?x₂, ?f ?y₁ ?y₂)) =>
  let f' := eval red in (@id (func _ _) (tuncurry f)) in
  sapply_1 (srelations.impl_sSubrelation_iff (f x₁ x₂, f y₁ y₂));
  change (f' (x₁, x₂) = f' (y₁, y₂) :> SProp_set) : proper.
Global Hint Extern 22 (impl (?f ?x, ?f ?y)) =>
  let f' := eval red in (@id (func _ _) f) in
  sapply_1 (srelations.impl_sSubrelation_iff (f x, f y));
  change (f' x = f' y :> SProp_set) : proper.

Global Hint Extern 10 (iff (?f ?x₁ ?x₂ ?x₃, ?f ?y₁ ?y₂ ?y₃)) =>
  let f' := eval red in (@id (func _ _) (eval_tuncurry3 f)) in
  change (f' (x₁, x₂, x₃) = f' (y₁, y₂, y₃) :> SProp_set) : proper.
Global Hint Extern 11 (iff (?f ?x₁ ?x₂, ?f ?y₁ ?y₂)) =>
  let f' := eval red in (@id (func _ _) (tuncurry f)) in
  change (f' (x₁, x₂) = f' (y₁, y₂) :> SProp_set) : proper.
Global Hint Extern 12 (iff (?f ?x, ?f ?y)) =>
  let f' := eval red in (@id (func _ _) f) in
  change (f' x = f' y :> SProp_set) : proper.


Definition IsWeakSPred {X : set} (P:X → SProp) : (∀ x y, x = y → P x → P y) → @IsFun !X SProp P.
Proof. intros H. refine (IsWeakFun _ _). intros ?? E; split; now apply H. Qed.
Definition make_weak_spred {X : set} (P:X → SProp) (H:∀ x y, x = y → P x → P y) : !X ⇾ SProp
:= @func_make (of_course_set X) _ P (IsWeakSPred P H).

Definition IsWeakSPred2@{u} {X Y : set@{u}} (P:X → Y → SProp) : (∀ x₁ x₂ y₁ y₂, x₁ = x₂ → y₁ = y₂ → P x₁ y₁ → P x₂ y₂)
  → @IsFun (!X ⊗ !Y) SProp (tuncurry P).
Proof. intros H.
  enough (@IsFun !(X ⊗ Y) SProp (tuncurry P)) by exact (is_fun (@func_make !(X ⊗ Y) SProp (tuncurry P) _ ∘ of_course_tensor_set_inv _ _)).
  refine (IsWeakFun _ _). intros [??][??] [??]; split; now apply H.
Qed.
Definition make_weak_spred2@{u} {X Y : set@{u}} (P:X → Y → SProp) (H:∀ x₁ x₂ y₁ y₂, x₁ = x₂ → y₁ = y₂ → P x₁ y₁ → P x₂ y₂)
  : !X ⊗ !Y ⇾ SProp
:= @func_make (!X ⊗ !Y) _ (λ p, P (π₁ p) (π₂ p)) (IsWeakSPred2 P H).


(** jections *)

Local Open Scope fun_inv_scope.

Lemma Injective_proper_impl {X Y} {f g : X ⇾ Y} : f = g → impl (Injective f, Injective g).
Proof. intro E; unfold Injective; now rew E. Qed.
Canonical Structure Injective_fun {X Y} : !(X ⇾ Y) ⇾ SProp :=  make_weak_spred Injective (@Injective_proper_impl X Y).

Lemma WeaklySurjective_proper_impl@{u} {A:Type@{u}} {Y:set@{u}} {f g : A → Y} : f = g → impl (WeaklySurjective f, WeaklySurjective g).
Proof. intro E; unfold WeaklySurjective; now rew E. Qed.
Canonical Structure WeaklySurjective_fun@{u} {A:Type@{u}} {Y:set@{u}} : !(A → Y) ⇾ SProp :=  make_weak_spred WeaklySurjective (@WeaklySurjective_proper_impl A Y).

Lemma Surjective_proper_impl {X Y} {f g : X ⇾ Y} {fi gi : Y ⇾ X } : f = g → fi = gi → impl (Surjective f (inv:=fi), Surjective g (inv:=gi)).
Proof. intros E1 E2; unfold Surjective, inverse. now rew [ E1 | E2 ]. Qed.
Canonical Structure Surjective_fun {X Y} :=  make_weak_spred2 Surjective (@Surjective_proper_impl X Y).

Lemma Bijective_proper_impl {X Y} {f g : X ⇾ Y} {fi gi : Y ⇾ X } : f = g → fi = gi → impl (Bijective f (inv:=fi), Bijective g (inv:=gi)).
Proof. intros E1 E2 [??]; split.
+ now rew <-E1.
+ now rew [ <-E1 | <-E2 ].
Qed.
Canonical Structure Bijective_fun {X Y} :=  make_weak_spred2 Bijective (@Bijective_proper_impl X Y).

Lemma injective_iff {X Y} (f:X ⇾ Y) `{!Injective f} x y : x = y ⧟ f x = f y.
Proof. split; [ exact (is_fun f _ _) | exact (injective f _ _) ]. Qed.

Lemma injective_iff_simp {X Y} (f:X ⇾ Y) `{!Injective f} (x y : X)
  {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
  : x = y ⧟ fx = fy.
Proof. rew (injective_iff f _ _). now rew [(simplify (f x))|(simplify (f y))]. Qed.


Lemma injective_compose_cancel@{u} {X Y Z:set@{u}} (f : Y ⇾ Z)  (g h : X ⇾ Y)
  `{!Injective f} : f ∘ g = f ∘ h ⊸ g = h.
Proof. change ((∏ x, f (g x) = f (h x)) ⊸ ∏ x, g x = h x).
  apply all_adj. intros x. rew (all_lb _ x). exact (injective f _ _).
Qed.

Definition surjective_applied `{Surjective (f:=f)} y : f (f⁻¹ y) = y := surjective f y.
Arguments surjective_applied {_ _} f {_ _} _.

Coercion Surjective_WeaklySurjective `{@Surjective X Y f fi} : WeaklySurjective f.
Proof. intros y. exists (f⁻¹ y). exact (surjective_applied f y). Qed.

Lemma surjective_compose_cancel@{u} {X Y Z:set@{u}} (f : X ⇾ Y) `{!Inverse f} (g h : Y ⇾ Z)
  `{!Surjective f} : g ∘ f = h ∘ f ⊸ g = h.
Proof.
  change ((∏ x, g (f x) = h (f x)) ⊸ ∏ y, g y = h y).
  apply all_adj. intros y. rew (all_lb _ (f⁻¹ y)).
  now rew (surjective_applied f _).
Qed.

Lemma bijective_applied `{Bijective (f:=f)} x : f⁻¹ (f x) = x.
Proof. apply (injective f _ _). exact (surjective f _). Qed.

Lemma bijective `{Bijective (f:=f)} : f⁻¹ ∘ f = id_fun _.
Proof. exact bijective_applied. Qed.

Arguments bijective_applied {_ _} f {_ _} x.
Arguments bijective {_ _} f {_ _}.

Global Hint Extern 2 (Inverse (id_fun ?X)) => refine (id_fun X) : typeclass_instances.
Lemma id_bijective {X} : Bijective (id_fun X).  Proof. now split. Qed.
Global Hint Extern 2 (Bijective  (id_fun _)) => simple notypeclasses refine id_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (id_fun _)) => simple notypeclasses refine id_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (id_fun _)) => simple notypeclasses refine id_bijective : typeclass_instances.
Global Hint Extern 2 (WeaklySurjective (func_op (id_fun _))) => simple notypeclasses refine id_bijective : typeclass_instances.

Global Hint Extern 8 (SimplifiesTo (?f ∘ (?g)⁻¹) _) => lazymatch f with g => solve_simplify (surjective f) end : typeclass_instances.
Global Hint Extern 8 (SimplifiesTo ((?f)⁻¹ ∘ ?g) _) => lazymatch f with g => solve_simplify (bijective f) end : typeclass_instances.
Global Hint Extern 8 (SimplifiesTo (func_op ?f (func_op (?g)⁻¹ _)) _) => lazymatch f with g => solve_simplify (surjective_applied f _) end : typeclass_instances.
Global Hint Extern 8 (SimplifiesTo (func_op (?f)⁻¹ (func_op ?g _)) _) => lazymatch f with g => solve_simplify (bijective_applied f _) end : typeclass_instances.


Section compositions.
  Universes u.
  Instance compose_injective {X Y Z:set@{u}} {f: X ⇾ Y} {g: Y ⇾ Z} : Injective f → Injective g → Injective (g ∘ f).
  Proof. intros ?? x y. change (func_op (g ∘ f) ?x) with (g (f x)).
    rew (injective g _ _). exact (injective f _ _).
  Qed.

  Instance compose_surjective {X Y Z:set@{u}} {f: X ⇾ Y} {g: Y ⇾ Z} `{!Inverse f, !Inverse g} : Surjective f → Surjective g → Surjective (g ∘ f).
  Proof. intros ?? z. change (g (f (f⁻¹ (g⁻¹ z))) = z).
    rew (surjective_applied f _). exact (surjective g _).
  Qed.

  Instance compose_bijective {X Y Z:set@{u}} {f: X ⇾ Y} {g: Y ⇾ Z} `{!Inverse f, !Inverse g} : Bijective f → Bijective g → Bijective (g ∘ f).
  Proof. intros; now split. Qed.
End compositions.
Global Hint Extern 4 (Injective  (_ ∘ _)) => simple notypeclasses refine (compose_injective  _ _)  : typeclass_instances.
Global Hint Extern 4 (Surjective (_ ∘ _)) => simple notypeclasses refine (compose_surjective _ _)  : typeclass_instances.
Global Hint Extern 4 (Bijective  (_ ∘ _)) => simple notypeclasses refine (compose_bijective  _ _)  : typeclass_instances.

Lemma injective_factor@{u} {X Y Z:set@{u}} (f: X ⇾ Y) (g: Y ⇾ Z)
  : Injective (g ∘ f) → Injective f.
Proof. intros ? x y. rew (is_fun g (f x) (f y)). exact (injective (g ∘ f) x y). Qed.

Lemma surjective_factor@{u} {X Y Z:set@{u}} (f: X ⇾ Y) (g: Y ⇾ Z) (j:Inverse (g ∘ f))
  : Surjective (g ∘ f) → Surjective g (inv := f ∘ (g ∘ f)⁻¹).
Proof. intros Hs. exact (surjective (g ∘ f)). Qed.

Lemma weakly_surjective_factor@{u} {X Y Z:set@{u}} (f: X ⇾ Y) (g: Y ⇾ Z)
  : WeaklySurjective (g ∘ f) → WeaklySurjective g.
Proof. intros H z. destruct (H z) as [x Hx]. now exists (f x). Qed.

Lemma alt_Build_Injective `(f: X ⇾ Y) `{!Inverse f} : f⁻¹ ∘ f = id_fun _ → Injective f.
Proof.
  intros E x y.
  rew <-exact:(E x : f⁻¹ (f x) = x) at 2.
  rew <-exact:(E y : f⁻¹ (f y) = y) at 2.
  exact (is_fun _ _ _).
Qed.

Lemma alt_Build_Bijective `(f: X ⇾ Y) `{!Inverse f} :
  f⁻¹ ∘ f = id_fun _ → f ∘ f⁻¹ = id_fun _ → Bijective f.
Proof. intros. split; trivial. now apply (alt_Build_Injective f). Qed.

Global Hint Extern 4 (Inverse (?f ⁻¹)) => refine f : typeclass_instances.

Lemma flip_bijection `(f: X ⇾ Y) `{!Inverse f, !Bijective f} : Bijective f⁻¹.
Proof. apply alt_Build_Bijective. exact (surjective f). exact (bijective f). Qed.
Global Hint Extern 4 (Bijective _⁻¹) => simple notypeclasses refine (flip_bijection _) : typeclass_instances.
Global Hint Extern 8 (Injective _⁻¹) => simple notypeclasses refine (flip_bijection _) : typeclass_instances.
Global Hint Extern 8 (Surjective _⁻¹) => simple notypeclasses refine (flip_bijection _) : typeclass_instances.
Global Hint Extern 8 (WeaklySurjective (func_op _⁻¹)) => simple notypeclasses refine Surjective_WeaklySurjective : typeclass_instances.

Lemma inverse_involutive `(f : X ⇾ Y) `{!Inverse f} : (f⁻¹)⁻¹ = f.
Proof. refl. Qed.

Lemma flip_bijection_back `(f: X ⇾ Y) `{!Inverse f} : Bijective f⁻¹ → Bijective f.
Proof. intro. now change (Bijective (f⁻¹⁻¹)). Qed.


Lemma of_course_tensor_set_bijective {X Y} : Bijective (of_course_tensor_set X Y).
Proof. now apply alt_Build_Bijective. Qed.
Lemma of_course_tensor_set_inv_bijective {X Y} : Bijective (of_course_tensor_set_inv X Y).
Proof. now apply alt_Build_Bijective. Qed.

Global Hint Extern 2 (Bijective  (of_course_tensor_set ?X ?Y)) => simple notypeclasses refine of_course_tensor_set_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (of_course_tensor_set ?X ?Y)) => simple notypeclasses refine of_course_tensor_set_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (of_course_tensor_set ?X ?Y)) => simple notypeclasses refine of_course_tensor_set_bijective : typeclass_instances.
Global Hint Extern 2 (Bijective  (of_course_tensor_set_inv ?X ?Y)) => simple notypeclasses refine of_course_tensor_set_inv_bijective  : typeclass_instances.
Global Hint Extern 2 (Injective  (of_course_tensor_set_inv ?X ?Y)) => simple notypeclasses refine of_course_tensor_set_inv_bijective  : typeclass_instances.
Global Hint Extern 2 (Surjective (of_course_tensor_set_inv ?X ?Y)) => simple notypeclasses refine of_course_tensor_set_inv_bijective  : typeclass_instances.


Global Hint Extern 2 (SimplifiesTo (proj1 (?x, _)) ?out) => change (SimplifiesTo x out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (proj2 (_, ?x)) ?out) => change (SimplifiesTo x out)  : typeclass_instances.

Section product.
  Universes u.
  Local Instance tensor_to_prod_is_fun {X Y:set@{u}} : @IsFun (X⊗Y) (X×Y) id.
  Proof. intros [x₁ y₁] [x₂ y₂]. refine (aprod_aand _ _). Qed.
  Definition tensor_to_prod (X Y:set@{u}) : X⊗Y ⇾ X×Y := @func_make (X⊗Y) (X×Y) id _.
 
  Local Instance prod_proj1_is_fun {X Y : set@{u}} : @IsFun (X×Y) X π₁.
  Proof. intros [x₁ y₁][x₂ y₂]. exact (aandl _ _). Qed.
  Local Instance prod_proj2_is_fun {X Y : set@{u}} : @IsFun (X×Y) Y π₂.
  Proof. intros [x₁ y₁][x₂ y₂]. exact (aandr _ _). Qed.
  Definition prod_proj1 (X Y :set@{u}) : X × Y ⇾ X := @func_make (X×Y) X π₁ prod_proj1_is_fun.
  Definition prod_proj2 (X Y :set@{u}) : X × Y ⇾ Y := @func_make (X×Y) Y π₂ prod_proj2_is_fun.

  Local Instance tensor_proj1_is_fun {X Y : set@{u}} : @IsFun (X ⊗ Y) X π₁.  Proof. exact (is_fun (prod_proj1 X Y ∘ tensor_to_prod X Y)). Qed.
  Local Instance tensor_proj2_is_fun {X Y : set@{u}} : @IsFun (X ⊗ Y) Y π₂.  Proof. exact (is_fun (prod_proj2 X Y ∘ tensor_to_prod X Y)). Qed.

  Definition tensor_proj1 (X Y : set@{u}) : X ⊗ Y ⇾ X := @func_make (X ⊗ Y) X _ tensor_proj1_is_fun.
  Definition tensor_proj2 (X Y : set@{u}) : X ⊗ Y ⇾ Y := @func_make (X ⊗ Y) Y _ tensor_proj2_is_fun.
End product.
Canonical prod_proj1.
Canonical prod_proj2.
Global Hint Extern 1 (Cast (?X ⊗ ?Y) (?X × ?Y)) => notypeclasses refine (tensor_to_prod X Y) : typeclass_instances.

Global Hint Extern 1 (StrongOp (?f ∘ tensor_to_prod _ _)) => simple notypeclasses refine (is_fun f) : typeclass_instances.

Lemma tensor_to_prod_weak_surj@{u} {X Y:set@{u}} : WeaklySurjective (tensor_to_prod X Y).
Proof. intros p. now exists p. Qed.
#[global] Hint Extern 2 (WeaklySurjective (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_weak_surj : typeclass_instances.

Global Hint Extern 4 (apos (proj1 ?x = proj1 ?y)) =>
  lazymatch type of x with
  | set_T (_ ⊗ _) => change (apos (tensor_proj1 _ _ x = tensor_proj1 _ _ y))
  | set_T (_ × _) => change (apos (prod_proj1 _ _ x = prod_proj1 _ _ y))
  end : proper.

Global Hint Extern 4 (apos (proj2 ?x = proj2 ?y)) =>
  lazymatch type of x with
  | set_T (_ ⊗ _) => change (apos (tensor_proj2 _ _ x = tensor_proj2 _ _ y))
  | set_T (_ × _) => change (apos (prod_proj2 _ _ x = prod_proj2 _ _ y))
  end : proper.


Global Hint Extern 2 (SimplifiesTo (func_op (prod_proj1 _ _) (?x, _)) ?out) => change (SimplifiesTo x out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (func_op (prod_proj2 _ _) (_, ?x)) ?out) => change (SimplifiesTo x out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (func_op (tensor_proj1 _ _) (?x, _)) ?out) => change (SimplifiesTo x out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (func_op (tensor_proj2 _ _) (_, ?x)) ?out) => change (SimplifiesTo x out)  : typeclass_instances.


Ltac unfold_pair_eq :=
  try change ( (?a, ?b) = (?c, ?d) :> set_T (_ × _) ) with (a = c ∧ b = d);
  try change ( (?a, ?b) = (?c, ?d) :> set_T (_ ⊗ _) ) with (a = c ⊠ b = d).

Lemma tensor_dec_eq@{u} {X Y:set@{u}} `{DecidableEquality X} `{DecidableEquality Y}
  : DecidableEquality (X ⊗ Y).
Proof. intros [[x₁ y₁][x₂ y₂]]. now unfold_pair_eq. Qed.
Global Hint Extern 2 (DecidableEquality (_ ⊗ _)) => simple notypeclasses refine tensor_dec_eq : typeclass_instances. 

Lemma tensor_affirmative_eq@{u} {X Y:set@{u}} `{AffirmativeEquality X} `{AffirmativeEquality Y}
  : AffirmativeEquality (X ⊗ Y).
Proof. intros [[x₁ y₁][x₂ y₂]]. now unfold_pair_eq. Qed.
Global Hint Extern 2 (AffirmativeEquality (_ ⊗ _)) => simple notypeclasses refine tensor_affirmative_eq : typeclass_instances. 

Lemma tensor_refutative_eq@{u} {X Y:set@{u}} `{RefutativeEquality X} `{RefutativeEquality Y}
  : RefutativeEquality (X ⊗ Y).
Proof. intros [[x₁ y₁][x₂ y₂]]. now unfold_pair_eq. Qed.
Global Hint Extern 2 (RefutativeEquality (_ ⊗ _)) => simple notypeclasses refine tensor_refutative_eq : typeclass_instances. 

Lemma prod_dec_eq@{u} {X Y:set@{u}} `{DecidableEquality X} `{DecidableEquality Y}
  : DecidableEquality (X × Y).
Proof. intros [[x₁ y₁][x₂ y₂]]. now unfold_pair_eq. Qed.
Global Hint Extern 2 (DecidableEquality (_ × _)) => simple notypeclasses refine prod_dec_eq : typeclass_instances. 

Lemma prod_refutative_eq@{u} {X Y:set@{u}} `{RefutativeEquality X} `{RefutativeEquality Y}
  : RefutativeEquality (X × Y).
Proof. intros [[x₁ y₁][x₂ y₂]]. now unfold_pair_eq. Qed.
Global Hint Extern 2 (RefutativeEquality (_ × _)) => simple notypeclasses refine prod_refutative_eq : typeclass_instances. 

Lemma prod_strong_set@{u} {X Y:set@{u}} `{StrongSet X} `{StrongSet Y}
  : StrongSet (X × Y).
Proof. intros [x₁ y₁][x₂ y₂][x₃ y₃]. unfold_pair_eq. apply aand_intro.
  + rew [ (aandl (x₁ = x₂) _) | (aandl (x₂ = x₃) _) ]. now apply strong_transitivity.
  + rew [ (aandr (x₁ = x₂) _) | (aandr (x₂ = x₃) _) ]. now apply strong_transitivity.
Qed.
Global Hint Extern 2 (StrongSet (_ × _)) => simple notypeclasses refine prod_strong_set : typeclass_instances. 


Section to_prod.
  Universes u.
  Local Abbreviation π₁ := (prod_proj1 _ _).
  Local Abbreviation π₂ := (prod_proj2 _ _).

  Local Instance to_prod_is_fun1 {X Y Z:set@{u}} (f:Z ⇾ X) (g:Z ⇾ Y) : @IsFun Z (X × Y) (λ z, (f z, g z)).
  Proof. intros z₁ z₂. change (z₁ = z₂ ⊸ f z₁ = f z₂ ∧ g z₁ = g z₂).
    rew [<-(is_fun f _ _) | <-(is_fun g _ _)]. now apply aand_intro.
  Qed.
  Local Abbreviation pr X Y Z f g := (@func_make Z (X × Y) (λ z : set_T Z, (f z, g z)) _).

  Local Instance to_prod_is_fun2 {X Y Z : set@{u}} : @IsFun ((Z ⇾ X) × (Z ⇾ Y)) (Z ⇾ X × Y)
    (λ '(a, b), pr X Y Z a b).
  Proof. intros [f₁ g₁][f₂ g₂].
    change ((∏ z, f₁ z = f₂ z) ∧ (∏ z, g₁ z = g₂ z) ⊸ ∏ z, f₁ z = f₂ z ∧ g₁ z = g₂ z).
    rew <-all_adj; intro z; refine (aand_proper_aimpl _ _); exact (all_lb _ _).
  Qed.
  Definition to_prod {X Y Z : set@{u}} : _ ⇾ _ := @func_make ((Z ⇾ X) × (Z ⇾ Y)) (Z ⇾ X × Y) _ to_prod_is_fun2.
End to_prod.
Definition prod_diag X := to_prod (id_fun X, id_fun X).

Lemma tensor_diag_is_fun `{!AffirmativeEquality X} : @IsFun X (X ⊗ X) (λ x, (x, x)).
Proof. intros x y. apply affirmative_aimpl. intro E. now rew E. Qed.
Definition tensor_diag X `{!AffirmativeEquality X} : X ⇾ X ⊗ X := @func_make _ _ _ tensor_diag_is_fun.

Lemma coordinatewise_is_fun@{u} {X Y Z : set@{u}} `(f:(X ⊗ Y)%set → Z) :
    (∀ x₁ x₂ y, x₁ = x₂ ⊸ f(x₁, y) = f(x₂, y))
  → (∀ x y₁ y₂, y₁ = y₂ ⊸ f(x, y₁) = f(x, y₂))
  → IsFun f.
Proof. intros Px Py [x₁ y₁][x₂ y₂]; unfold_pair_eq.
  rew <-(transitivity (=) _ (f(x₂,y₁)) _).
  refine (aprod_proper_aimpl _ _); [ apply Px | apply Py ].
Qed.

Lemma commutative_is_fun@{u} {X Z : set@{u}} `(f:(X ⊗ X)%set → Z) :
    (∀ x y, f(x, y) = f(y, x))
  → (∀ x₁ x₂ y, x₁ = x₂ ⊸ f(x₁, y) = f(x₂, y))
  → IsFun f.
Proof. intros P H. apply coordinatewise_is_fun; trivial.
  intros x y₁ y₂. rew [ (P x y₁) | (P x y₂) ].
  now apply H.
Qed.

Section unit_empty.
  Definition from_Empty X : 𝟎 ⇾ X.
  Proof. refine (func_make abort). intros x []. Defined.
  Definition to_Unit X : X ⇾ 𝟏.
  Proof. refine (func_make to_unit). intros x y. exact (aimpl_true _). Defined.
End unit_empty.
Canonical from_Empty.
Canonical to_Unit.
Global Hint Extern 2 (The (set_T 𝟏)) => exact tt : typeclass_instances.
Global Hint Extern 2 (The (set_T (𝟎 ⇾ ?X))) => eapply from_Empty : typeclass_instances.
Global Hint Extern 2 (The (set_T (?X ⇾ 𝟏))) => eapply to_Unit : typeclass_instances.

Lemma empty_initial `(f:𝟎 ⇾ X) : f = the.  Proof. intros []. Qed.
Lemma unit_terminal `(f:X ⇾ 𝟏) : f = the.  Proof. easy. Qed.

Section swap.
  Universes u.
  Local Abbreviation swap := (λ '(a,b), (b, a)).
  Local Instance tensor_swap_is_fun (X Y:set@{u}) : @IsFun (X ⊗ Y) (Y ⊗ X) swap.
  Proof. intros [x₁ y₁][x₂ y₂].
    change (x₁ = x₂ ⊠ y₁ = y₂ ⊸ y₁ = y₂ ⊠ x₁ = x₂). now rew (aprod_com _ _) at 1.
  Qed.
  Local Instance prod_swap_is_fun (X Y:set@{u}) : @IsFun (X × Y) (Y × X) swap.
  Proof. intros [x₁ y₁][x₂ y₂].
    change (x₁ = x₂ ∧ y₁ = y₂ ⊸ y₁ = y₂ ∧ x₁ = x₂). now rew (aand_com _ _) at 1.
  Qed.
  Definition tensor_swap (X Y:set@{u}) : _ ⇾ _ := @func_make _ _ _ (tensor_swap_is_fun X Y).
  Definition prod_swap (X Y:set@{u}) : _ ⇾ _ := @func_make _ _ _ (prod_swap_is_fun X Y).
End swap.

Global Hint Extern 2 (Inverse (tensor_swap ?X ?Y)) => eexact (tensor_swap Y X) : typeclass_instances.
Global Hint Extern 2 (Inverse (prod_swap ?X ?Y)) => eexact (prod_swap Y X) : typeclass_instances.


Lemma tensor_swap_bijective@{u} {X Y:set@{u}} : Bijective (tensor_swap X Y).
Proof. apply alt_Build_Bijective; now intros [x y]. Qed.
Lemma prod_swap_bijective@{u} {X Y:set@{u}} : Bijective (prod_swap X Y).
Proof. apply alt_Build_Bijective; now intros [x y]. Qed.

Global Hint Extern 2 (Bijective  (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_bijective : typeclass_instances.
Global Hint Extern 2 (Bijective  (prod_swap _ _)) => simple notypeclasses refine prod_swap_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (prod_swap _ _)) => simple notypeclasses refine prod_swap_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (prod_swap _ _)) => simple notypeclasses refine prod_swap_bijective : typeclass_instances.


Global Hint Extern 2 (SimplifiesTo (func_op (prod_swap _ _) (?x, ?y)) ?out) => change (SimplifiesTo (y, x) out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (func_op (tensor_swap _ _) (?x, ?y)) ?out) => change (SimplifiesTo (y, x) out)  : typeclass_instances.


Section map.
  Universes u.
  Local Instance tensor_map_is_fun1 {X₁ X₂ Y₁ Y₂:set@{u}} (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂) : @IsFun (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (λ p, (f₁ (π₁ p), f₂ (π₂ p))).
  Proof. intros [x₁ x₂][y₁ y₂].
    change (x₁ = y₁ ⊠ x₂ = y₂ ⊸ f₁ x₁ = f₁ y₁ ⊠ f₂ x₂ = f₂ y₂).
    refine (aprod_proper_aimpl _ _); exact (is_fun _ _ _).
  Qed.
  Definition tensor_map_op {X₁ X₂ Y₁ Y₂:set@{u}} : (X₁ ⇾ Y₁) ∗ (X₂ ⇾ Y₂) → (X₁ ⊗ X₂ ⇾ Y₁ ⊗ Y₂) := λ '(f₁, f₂), func_make (λ p, (f₁ (π₁ p), f₂ (π₂ p))).

  Local Instance tensor_map_is_fun2 {X₁ X₂ Y₁ Y₂:set@{u}} : IsFun (@tensor_map_op X₁ X₂ Y₁ Y₂).
  Proof. intros [f₁ f₂][g₁ g₂].
    change ( (∏ x, f₁ x = g₁ x) ⊠ (∏ y, f₂ y = g₂ y) ⊸ ∏ p, f₁ (π₁ p) = g₁ (π₁ p) ⊠ f₂ (π₂ p) = g₂ (π₂ p)).
    rew <-all_adj; intros [x₁ x₂]. refine (aprod_proper_aimpl _ _); exact (all_lb _ _).
  Qed.

  Definition tensor_map_fun {X₁ X₂ Y₁ Y₂:set@{u}} : _ ⇾ _ := @func_make _ _ _ (@tensor_map_is_fun2 X₁ X₂ Y₁ Y₂).
End map.
Canonical tensor_map_fun.
Abbreviation tensor_map f g := (tensor_map_op (@pair (set_T (_ ⇾ _)) (set_T (_ ⇾ _)) f g)).
Module tensor_map_notation.
  Notation "⟨ a , b , .. , c ⟩" := (tensor_map .. (tensor_map a b) .. c ) (at level 0) : set_scope.
End tensor_map_notation.
Import tensor_map_notation.


Lemma tensor_map_injective@{u} {X₁ X₂ Y₁ Y₂:set@{u}} (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂)
  `{!Injective f₁, !Injective f₂} : Injective ⟨f₁, f₂⟩.
Proof. intros [x₁ x₂][y₁ y₂].
  change (f₁ x₁ = f₁ y₁ ⊠ f₂ x₂ = f₂ y₂ ⊸ x₁ = y₁ ⊠ x₂ = y₂).
  refine (aprod_proper_aimpl _ _); exact (injective _ _ _).
Qed.
Global Hint Extern 2 (Injective ⟨ _, _⟩) => simple notypeclasses refine (tensor_map_injective _ _) : typeclass_instances.
Global Hint Extern 2 (Injective (func_op tensor_map_fun _)) => simple notypeclasses refine (tensor_map_injective _ _) : typeclass_instances.


Global Hint Extern 2 (Inverse ⟨?f, ?g⟩) => eexact (⟨f⁻¹, g⁻¹⟩) : typeclass_instances.
Global Hint Extern 2 (Inverse (func_op tensor_map_fun (?f, ?g))) => eexact (⟨f⁻¹, g⁻¹⟩) : typeclass_instances.


Lemma tensor_map_surjective@{u} {X₁ X₂ Y₁ Y₂:set@{u}} (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂) `{!Inverse f₁, !Inverse f₂}
  `{!Surjective f₁, !Surjective f₂} : Surjective ⟨f₁, f₂⟩.
Proof.
  enough (⟨f₁ ∘ f₁⁻¹, f₂ ∘ f₂⁻¹⟩ = ⟨id, id⟩) as E by (intros [x y]; refine (E _)).
  apply (is_fun _ _ _); split; exact (surjective _).
Qed.
Global Hint Extern 2 (Surjective ⟨ _, _⟩) => simple notypeclasses refine (tensor_map_surjective _ _) : typeclass_instances.
Global Hint Extern 2 (Surjective (func_op tensor_map_fun _)) => simple notypeclasses refine (tensor_map_surjective _ _) : typeclass_instances.

Lemma tensor_map_bijective@{u} {X₁ X₂ Y₁ Y₂:set@{u}} (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂) `{!Inverse f₁, !Inverse f₂}
  `{!Bijective f₁, !Bijective f₂} : Bijective ⟨f₁, f₂⟩.
Proof. now split. Qed.
Global Hint Extern 2 (Bijective ⟨ _, _⟩) => simple notypeclasses refine (tensor_map_bijective _ _) : typeclass_instances.
Global Hint Extern 2 (Bijective (func_op tensor_map_fun _)) => simple notypeclasses refine (tensor_map_bijective _ _) : typeclass_instances.


Section assoc.
  Universes u.
  Local Abbreviation aₗ := (λ p, (π₁ (π₁ p), (π₂ (π₁ p), π₂ p))).
  Local Abbreviation aᵣ := (λ p, ((π₁ p, π₁ (π₂ p)), π₂ (π₂ p))).

  Local Instance tnsr_al_is_fun (X Y Z :set@{u}) : @IsFun (X⊗Y⊗Z) (X⊗(Y⊗Z)) aₗ.
  Proof. intros [[x₁ y₁] z₁] [[x₂ y₂] z₂]. apply aprod_assoc. Qed.
  Local Instance tnsr_ar_is_fun (X Y Z :set@{u}) : @IsFun (X⊗(Y⊗Z)) (X⊗Y⊗Z) aᵣ.
  Proof. intros [x₁ [y₁ z₁]] [x₂ [y₂ z₂]]. apply aprod_assoc. Qed.

  Local Instance prod_al_is_fun (X Y Z :set@{u}) : @IsFun (X×Y×Z) (X×(Y×Z)) aₗ.
  Proof. intros [[x₁ y₁] z₁] [[x₂ y₂] z₂]. apply aand_assoc. Qed.
  Local Instance prod_ar_is_fun (X Y Z :set@{u}) : @IsFun (X×(Y×Z)) (X×Y×Z) aᵣ.
  Proof. intros [x₁ [y₁ z₁]] [x₂ [y₂ z₂]]. apply aand_assoc. Qed.

  Definition tensor_assoc_l X Y Z : _ ⇾ _ := @func_make _ _ _ (tnsr_al_is_fun X Y Z).
  Definition tensor_assoc_r X Y Z : _ ⇾ _ := @func_make _ _ _ (tnsr_ar_is_fun X Y Z).
  Definition prod_assoc_l X Y Z : _ ⇾ _ := @func_make _ _ _ (prod_al_is_fun X Y Z).
  Definition prod_assoc_r X Y Z : _ ⇾ _ := @func_make _ _ _ (prod_ar_is_fun X Y Z).
End assoc.

Global Hint Extern 2 (Inverse (tensor_assoc_l ?X ?Y ?Z)) => eexact (tensor_assoc_r X Y Z) : typeclass_instances.
Global Hint Extern 2 (Inverse (tensor_assoc_r ?X ?Y ?Z)) => eexact (tensor_assoc_l X Y Z) : typeclass_instances.
Global Hint Extern 2 (Inverse (prod_assoc_l ?X ?Y ?Z)) => eexact (prod_assoc_r X Y Z) : typeclass_instances.
Global Hint Extern 2 (Inverse (prod_assoc_r ?X ?Y ?Z)) => eexact (prod_assoc_l X Y Z) : typeclass_instances.


Lemma tensor_assoc_l_bijective@{u} {X Y Z:set@{u}} : Bijective (tensor_assoc_l X Y Z).
Proof. apply alt_Build_Bijective; [ now intros [[??]?] | now intros [?[??]]]. Qed.
Lemma tensor_assoc_r_bijective@{u} {X Y Z:set@{u}} : Bijective (tensor_assoc_r X Y Z).
Proof. apply alt_Build_Bijective; [ now intros [?[??]] | now intros [[??]?]]. Qed.
Lemma prod_assoc_l_bijective@{u} {X Y Z:set@{u}} : Bijective (prod_assoc_l X Y Z).
Proof. apply alt_Build_Bijective; [ now intros [[??]?] | now intros [?[??]]]. Qed.
Lemma prod_assoc_r_bijective@{u} {X Y Z:set@{u}} : Bijective (prod_assoc_r X Y Z).
Proof. apply alt_Build_Bijective; [ now intros [?[??]] | now intros [[??]?]]. Qed.

Global Hint Extern 2 (Bijective  (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_bijective : typeclass_instances.
Global Hint Extern 2 (Bijective  (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_bijective : typeclass_instances.
Global Hint Extern 2 (Bijective  (prod_assoc_l _ _ _)) => simple notypeclasses refine prod_assoc_l_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (prod_assoc_l _ _ _)) => simple notypeclasses refine prod_assoc_l_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (prod_assoc_l _ _ _)) => simple notypeclasses refine prod_assoc_l_bijective : typeclass_instances.
Global Hint Extern 2 (Bijective  (prod_assoc_r _ _ _)) => simple notypeclasses refine prod_assoc_r_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (prod_assoc_r _ _ _)) => simple notypeclasses refine prod_assoc_r_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (prod_assoc_r _ _ _)) => simple notypeclasses refine prod_assoc_r_bijective : typeclass_instances.



Section unitors.
  Local Instance tensor_unit_l_is_fun X : @IsFun (𝟏 ⊗ X) X proj2.
  Proof. intros [u₁ x₁][u₂ x₂]. apply aprod_unit_l. Qed.
  Local Instance tensor_unit_r_is_fun X : @IsFun (X ⊗ 𝟏) X proj1.
  Proof. intros [x₁ u₁][x₂ u₂]. apply aprod_unit_r. Qed.
  Definition tensor_unit_l X : _ ⇾ _ := @func_make _ _ _ (tensor_unit_l_is_fun X).
  Definition tensor_unit_r X : _ ⇾ _ := @func_make _ _ _ (tensor_unit_r_is_fun X).

  Local Instance tensor_unit_l_inv_is_fun X : @IsFun X (𝟏 ⊗ X) (λ x, (tt, x)).
  Proof. intros x₁ x₂. change (x₁ = x₂ ⊸ 𝐓 ⊠ x₁ = x₂). now rew (aprod_unit_l _). Qed.
  Local Instance tensor_unit_r_inv_is_fun X : @IsFun X (X ⊗ 𝟏) (λ x, (x, tt)).
  Proof. intros x₁ x₂. change (x₁ = x₂ ⊸ x₁ = x₂ ⊠ 𝐓). now rew (aprod_unit_r _). Qed.
  Local Instance tensor_unit_l_inv X : Inverse (tensor_unit_l X) := @func_make _ _ _ (tensor_unit_l_inv_is_fun X).
  Local Instance tensor_unit_r_inv X : Inverse (tensor_unit_r X) := @func_make _ _ _ (tensor_unit_r_inv_is_fun X).

  Lemma tensor_unit_l_bijective X : Bijective (tensor_unit_l X).
  Proof. apply alt_Build_Bijective; [ now intros [??] | easy ]. Qed.
  Lemma tensor_unit_r_bijective X : Bijective (tensor_unit_r X).
  Proof. apply alt_Build_Bijective; [ now intros [??] | easy ]. Qed.
End unitors.
Global Hint Extern 2 (Inverse  (tensor_unit_l ?X)) => eexact (tensor_unit_l_inv X) : typeclass_instances.
Global Hint Extern 2 (Inverse  (tensor_unit_r ?X)) => eexact (tensor_unit_r_inv X) : typeclass_instances.
Global Hint Extern 2 (Bijective  (tensor_unit_l ?X)) => simple notypeclasses refine (tensor_unit_l_bijective X) : typeclass_instances.
Global Hint Extern 2 (Injective  (tensor_unit_l ?X)) => simple notypeclasses refine (tensor_unit_l_bijective X) : typeclass_instances.
Global Hint Extern 2 (Surjective (tensor_unit_l ?X)) => simple notypeclasses refine (tensor_unit_l_bijective X) : typeclass_instances.
Global Hint Extern 2 (Bijective  (tensor_unit_r ?X)) => simple notypeclasses refine (tensor_unit_r_bijective X) : typeclass_instances.
Global Hint Extern 2 (Injective  (tensor_unit_r ?X)) => simple notypeclasses refine (tensor_unit_r_bijective X) : typeclass_instances.
Global Hint Extern 2 (Surjective (tensor_unit_r ?X)) => simple notypeclasses refine (tensor_unit_r_bijective X) : typeclass_instances.

Definition tensor_swap_tail@{u} (X Y Z : set@{u}) : X ⊗ Y ⊗ Z ⇾ X ⊗ Z ⊗ Y
  := @func_make _ _ (λ '(x,y,z), (x,z,y)) (is_fun (tensor_assoc_r _ _ _ ∘ ⟨ id, tensor_swap _ _ ⟩ ∘ tensor_assoc_l _ _ _)).
Global Hint Extern 2 (Inverse (tensor_swap_tail ?X ?Y ?Z)) => eexact (tensor_swap_tail X Z Y) : typeclass_instances.
Lemma tensor_swap_tail_bijective@{u} {X Y Z:set@{u}} : Bijective (tensor_swap_tail X Y Z).
Proof. apply alt_Build_Bijective; now intros [[??]?]. Qed.
Global Hint Extern 2 (Bijective  (tensor_swap_tail _ _ _)) => simple notypeclasses refine tensor_swap_tail_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (tensor_swap_tail _ _ _)) => simple notypeclasses refine tensor_swap_tail_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (tensor_swap_tail _ _ _)) => simple notypeclasses refine tensor_swap_tail_bijective : typeclass_instances.

Definition tensor_medial@{u} (X Y Z W:set@{u}) : (X ⊗ Y) ⊗ (Z ⊗ W) ⇾ (X ⊗ Z) ⊗ (Y ⊗ W)
  := @func_make _ _ (λ '((x,y),(z,w)), ((x,z),(y,w)))
       (is_fun (tensor_assoc_l _ _ _ ∘ ⟨ tensor_swap_tail _ _ _, id ⟩ ∘ tensor_assoc_r _ _ _)).
Global Hint Extern 2 (Inverse (tensor_medial ?X ?Y ?Z ?W)) => eexact (tensor_medial X Z Y W) : typeclass_instances.
Lemma tensor_medial_bijective@{u} {X Y Z W:set@{u}} : Bijective (tensor_medial X Y Z W).
Proof. apply alt_Build_Bijective; now intros [[??][??]]. Qed.
Global Hint Extern 2 (Bijective  (tensor_medial _ _ _ _)) => simple notypeclasses refine tensor_medial_bijective : typeclass_instances.
Global Hint Extern 2 (Injective  (tensor_medial _ _ _ _)) => simple notypeclasses refine tensor_medial_bijective : typeclass_instances.
Global Hint Extern 2 (Surjective (tensor_medial _ _ _ _)) => simple notypeclasses refine tensor_medial_bijective : typeclass_instances.

Section curry.
  Universes u.
  Local Instance curry_is_fun1 {X Y Z:set@{u}} (f:X ⊗ Y ⇾ Z) (x:X) : @IsFun Y Z (λ y, f (x, y)).
  Proof. intros y₁ y₂. rew <-(is_fun f _ _). change (y₁ = y₂ ⊸ x = x ⊠ y₁ = y₂).
    now rew (aprod_true_l (_ : x = x)).
  Qed.
  Local Abbreviation ap Y Z f x := (@func_make Y Z (λ y, f (x, y)) (curry_is_fun1 f x) : _ ⇾ _).

  Local Instance curry_is_fun2 {X Y Z:set@{u}} (f:X ⊗ Y ⇾ Z) : @IsFun X (Y ⇾ Z) (λ x, ap Y Z f x).
  Proof. intros x₁ x₂. change (x₁ = x₂ ⊸ ∏ y, f(x₁,y) = f(x₂,y)). rew <-all_adj; intros y.
    rew <-(is_fun f _ _). change (x₁ = x₂ ⊸ x₁ = x₂ ⊠ y = y). now rew (aprod_true_r (_ : y=y)).
  Qed.
  Local Abbreviation ap' X Y Z f := (@func_make X (Y ⇾ Z) (λ x, ap Y Z f x) (curry_is_fun2 f) : X ⇾ (Y ⇾ Z)).

  Local Instance curry_is_fun3 {X Y Z:set@{u}} : @IsFun (X ⊗ Y ⇾ Z) (X ⇾ Y ⇾ Z) (λ f, ap' X Y Z f).
  Proof. intros f₁ f₂. change ( (∏ p, f₁ p = f₂ p) ⊸ (∏ x y, f₁ (x,y) = f₂ (x,y)) ).
    rew <-all_adj; intros x. rew <-all_adj; intros y. exact (all_lb _ (x, y)).
  Qed.
  Definition curry {X Y Z:set@{u}} : _ ⇾ _ := @func_make (X ⊗ Y ⇾ Z) (X ⇾ Y ⇾ Z) _ curry_is_fun3.

  Local Instance uncurry_is_fun1 {X Y Z:set@{u}} (f:X ⇾ Y ⇾ Z) : @IsFun (X ⊗ Y) Z (λ p, f (π₁ p) (π₂ p)).
  Proof. intros [x₁ y₁][x₂ y₂].
    change (x₁ = x₂ ⊠ y₁ = y₂ ⊸ f x₁ y₁ = f x₂ y₂).
    rew <-(transitivity (=) (f x₁ y₁) (f x₂ y₁) (f x₂ y₂)).
    refine (aprod_proper_aimpl _ _).
    + enough (f x₁ = f x₂ ⊸ f x₁ y₁ = f x₂ y₁) as E by (rew <-E; exact (is_fun f _ _)).
      exact (all_lb _ _).
    + exact (is_fun _ _ _).
  Qed.
  Local Abbreviation uc X Y Z f := (@func_make (X ⊗ Y) Z (λ p, f (π₁ p) (π₂ p)) (uncurry_is_fun1 f) : X ⊗ Y ⇾ Z).

  Local Instance uncurry_is_fun2 {X Y Z:set@{u}} : @IsFun (X ⇾ Y ⇾ Z) (X ⊗ Y ⇾ Z) (λ f, uc X Y Z f).
  Proof. intros f₁ f₂.
    change ((∏ x y, f₁ x y = f₂ x y) ⊸ ∏ p, f₁ (π₁ p) (π₂ p) = f₂ (π₁ p) (π₂ p)).
    rew <-all_adj. intros [x y]. rew (all_lb _ x). exact (all_lb _ _).
  Qed.
  Definition uncurry {X Y Z:set@{u}} : _ ⇾ _ := @func_make _ _ _ (@uncurry_is_fun2 X Y Z).
End curry.

Section partial_application.
  Universes u.
  Definition ap1 {X Y Z:set@{u}} : (X ⊗ Y ⇾ Z) ⇾ X ⇾ Y ⇾ Z := curry.
  Definition ap2 {X Y Z:set@{u}} : (X ⊗ Y ⇾ Z) ⇾ Y ⇾ X ⇾ Z :=
    curry ∘ curry ((∘) ∘ tensor_swap _ _) (tensor_swap _ _).
End partial_application.
Notation "( f ∘)" := (func_op2 ap1 scompose_fun f) : set_scope.
Notation "(∘ f )" := (func_op2 ap2 scompose_fun f) : set_scope.

Global Hint Extern 2 (SimplifiesTo (func_op (func_op2 ap1 ?f ?x) ?y) ?out) => change (SimplifiesTo (f (x, y)) out)  : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (func_op (func_op2 ap2 ?f ?x) ?y) ?out) => change (SimplifiesTo (f (y, x)) out)  : typeclass_instances.

Lemma to_strong_set_strong@{u} {X Y Z:set@{u}} {f:X ⊗ Y ⇾ Z} `{!StrongSet Z} : StrongOp f.
Proof. intros [x₁ y₁][x₂ y₂]. unfold_pair_eq.
  rew <-(strong_transitivity (=) _ (f (x₂, y₁)) _).
  apply aand_intro.
+ rew (aandl _ _). exact (is_fun (ap2 f y₁) _ _).
+ rew (aandr _ _). exact (is_fun (ap1 f x₂) _ _).
Qed.
Global Hint Extern 4 (StrongOp _) => simple notypeclasses refine to_strong_set_strong : typeclass_instances.

Section misc.
  Universes u.
  (** Evaluation *)
  Definition eval {X Y:set@{u}} : (X ⇾ Y) ⊗ X ⇾ Y := uncurry id.

  (** Constant functions *)
  Definition const {X Y:set@{u}} : Y ⇾ X ⇾ Y := curry (tensor_unit_r _ ∘ ⟨ id, the ⟩).

  (** Cartesian product functor action on functions *)
  Local Abbreviation π₁ := (prod_proj1 _ _).
  Local Abbreviation π₂ := (prod_proj2 _ _).
  Definition prod_map {X₁ X₂ Y₁ Y₂:set@{u}} : (X₁ ⇾ Y₁) × (X₂ ⇾ Y₂) ⇾ X₁ × X₂ ⇾ Y₁ × Y₂
     := to_prod ∘ to_prod ((∘ π₁) ∘ π₁, (∘ π₂) ∘ π₂).

  (** [pair] is a function *)
  Definition tensor_pair {X Y:set@{u}} : X ⇾ Y ⇾ X ⊗ Y := ap1 id.
  Definition tensor_pair_swap {X Y:set@{u}} : Y ⇾ X ⇾ X ⊗ Y := ap2 id.
  Definition prod_pair {X Y:set@{u}} : X ⇾ Y ⇾ X × Y := ap1 (cast _ _).
  Definition prod_pair_swap {X Y:set@{u}} : Y ⇾ X ⇾ X × Y := ap2 (cast _ _).


  Definition tensor_map2 {X₁ X₂ Y₁ Y₂ Z₁ Z₂:set@{u}}
    : (X₁ ⊗ Y₁ ⇾ Z₁) ⊗ (X₂ ⊗ Y₂ ⇾ Z₂) ⇾ (X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ⇾ Z₁ ⊗ Z₂.
  Proof. refine ((∘ _) ∘ tensor_map_fun).
    refine (tensor_assoc_l _ _ _ ∘ _ ∘ tensor_assoc_r _ _ _).
    refine (tensor_map (tensor_swap_tail _ _ _) id).
  Defined.

  Definition prod_map2 {X₁ X₂ Y₁ Y₂ Z₁ Z₂:set@{u}}
    : (X₁ ⊗ Y₁ ⇾ Z₁) × (X₂ ⊗ Y₂ ⇾ Z₂) ⇾ (X₁ × X₂) ⊗ (Y₁ × Y₂) ⇾ Z₁ × Z₂
  := (∘ to_prod (tensor_map π₁ π₁, tensor_map π₂ π₂)) ∘ prod_map.

  Lemma prod_map2_strong `{StrongOp@{u} (f:=f)} `{StrongOp@{u} (f:=g)}
    : StrongOp (prod_map2 (f, g)).
  Proof. intros [[a b][c d]][[x y][z w]].
    change ((a = x ∧ b = y) ∧ (c = z ∧ d = w) ⊸ f (a, c) = f (x, z) ∧ g (b, d) = g (y, w)).
    rew <-(is_fun (strong_op f) (_, _) (_, _) : a = x ∧ c = z ⊸ f (a, c) = f (x, z)).
    rew <-(is_fun (strong_op g) (_, _) (_, _) : b = y ∧ d = w ⊸ g (b, d) = g (y, w)).
    tautological.
  Qed.
End misc.
Global Hint Extern 2 (StrongOp (prod_map2 _)) => simple notypeclasses refine prod_map2_strong : typeclass_instances.


Lemma tensor_map_id@{u} {X Y:set@{u}} : ⟨@id X, @id Y⟩ = id_fun _.
Proof. now intros [??]. Qed.

Lemma prod_map_id@{u} {X Y:set@{u}} : prod_map (id_fun X, id_fun Y) = id_fun _.
Proof. now intros [??]. Qed.


Lemma prod_map_injective@{u} {X₁ X₂ Y₁ Y₂:set@{u}} (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂)
  `{!Injective f₁, !Injective f₂} : Injective (prod_map (f₁, f₂)).
Proof. intros [x₁ x₂][y₁ y₂].
  change (f₁ x₁ = f₁ y₁ ∧ f₂ x₂ = f₂ y₂ ⊸ x₁ = y₁ ∧ x₂ = y₂).
  now rew (injective _ _ _).
Qed.
#[global] Hint Extern 2 (Injective (func_op prod_map _)) => simple notypeclasses refine (prod_map_injective _ _) : typeclass_instances.


#[global] Hint Extern 2 (Inverse (func_op prod_map (?f, ?g))) => eexact (prod_map (f⁻¹, g⁻¹)) : typeclass_instances.

Lemma prod_map_surjective@{u} {X₁ X₂ Y₁ Y₂:set@{u}} (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂) `{!Inverse f₁, !Inverse f₂}
  `{!Surjective f₁, !Surjective f₂} : Surjective (prod_map (f₁, f₂)).
Proof.
  enough (prod_map (f₁ ∘ f₁⁻¹, f₂ ∘ f₂⁻¹) = prod_map (id_fun _, id_fun _)) as E by (intros [x y]; refine (E _)).
  apply (is_fun _ _ _); split; exact (surjective _).
Qed.
#[global] Hint Extern 2 (Surjective (func_op prod_map _)) => simple notypeclasses refine (prod_map_surjective _ _) : typeclass_instances.

Lemma prod_map_bijective@{u} {X₁ X₂ Y₁ Y₂:set@{u}} (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂) `{!Inverse f₁, !Inverse f₂}
  `{!Bijective f₁, !Bijective f₂} : Bijective (prod_map (f₁, f₂)).
Proof. now split. Qed.
#[global] Hint Extern 2 (Bijective (func_op prod_map _)) => simple notypeclasses refine (prod_map_bijective _ _) : typeclass_instances.


Definition of_course_op3@{u} {X Y Z W:set@{u}} (f:X ⊗ Y ⊗ Z ⇾ W) : !X ⊗ !Y ⊗ !Z ⇾ !W
:= of_course_map f ∘ of_course_tensor_set_inv _ _  ∘ ⟨of_course_tensor_set_inv _ _, id⟩.

#[global] Hint Extern 2 (Coerce (?X ⊗ ?Y) (?Z ⊗ ?W)) => notypeclasses refine (⟨coerce X Z, coerce Y W⟩) : typeclass_instances.
#[global] Hint Extern 2 (Coerce (?X ⊗ ?Y) (?Z × ?W)) => notypeclasses refine (tensor_to_prod _ _ ∘ ⟨coerce X Z, coerce Y W⟩) : typeclass_instances.
#[global] Hint Extern 2 (Coerce (?X × ?Y) (?Z × ?W)) => notypeclasses refine (prod_map (coerce X Z, coerce Y W)) : typeclass_instances.

Section sum.
  Universes u.
  Import tsum_notation.

  Lemma inl_is_fun {X Y : set@{u}} : @IsFun X (X+Y) inl.  Proof. now intros x₁ x₂. Qed.
  Lemma inr_is_fun {X Y : set@{u}} : @IsFun Y (X+Y) inr.  Proof. now intros y₁ y₂. Qed.

  Canonical Structure inl_fun {X} Y : _ ⇾ _ := @func_make _ _ _ (@inl_is_fun X Y).
  Canonical Structure inr_fun X {Y} : _ ⇾ _ := @func_make _ _ _ (@inr_is_fun X Y).

  Definition inl_ne_inr {X Y : set@{u}} {x:X} {y:Y} : inl x ≠ inr y := I.
  Definition inr_ne_inl {X Y : set@{u}} {x:X} {y:Y} : inr y ≠ inl x := I.

  Definition from_sum_op1 {X Y Z : set@{u}} (f:X ⇾ Z) (g:Y ⇾ Z) : X+Y → Z
    := λ s, match s with inl x => f x | inr y => g y end.
  Lemma from_sum_is_fun1 {X Y Z:set@{u}} {f g} : IsFun (@from_sum_op1 X Y Z f g).
  Proof. intros [x₁|y₁][x₂|y₂].
  + exact (is_fun f _ _).
  + apply false_aimpl.
  + apply false_aimpl.
  + exact (is_fun g _ _).
  Qed.
  Canonical Structure from_sum_op2 {X Y Z:set@{u}} f g : _ ⇾ _ := @func_make _ _ _ (@from_sum_is_fun1 X Y Z f g).

  Lemma from_sum_is_fun2 {X Y Z : set@{u}} : @IsFun ((X ⇾ Z) × (Y ⇾ Z)) (X + Y ⇾ Z) (tuncurry from_sum_op2).
  Proof. intros [f₁ g₁][f₂ g₂]. unfold_pair_eq. apply all_adj; intros [x|y];
    unfold tuncurry, from_sum_op2, func_op, from_sum_op1, proj1, proj2.
  + rew (aandl _ _). change ((∏ z, f₁ z = f₂ z) ⊸ f₁ x = f₂ x). now rew (all_lb _ x).
  + rew (aandr _ _). change ((∏ z, g₁ z = g₂ z) ⊸ g₁ y = g₂ y). now rew (all_lb _ y).
  Qed.
  Canonical Structure from_sum (X Y Z:set@{u}) : _ ⇾ _ := @func_make _ _ _ (@from_sum_is_fun2 X Y Z).
End sum.

