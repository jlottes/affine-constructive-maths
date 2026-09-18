Require Export relation_notation.
Require Import interfaces.sprop logic.aprop logic.relations easy rewrite strip_coercions.

Definition IsSet A {e:Equiv A} := Equivalence (A:=A) (=).
Existing Class IsSet.
Identity Coercion IsSet_to_Equivalence : IsSet >-> Equivalence.

Global Hint Extern 2 (Equivalence (@equiv ?A ?e)) => change (@IsSet A e) : typeclass_instances.
Global Hint Extern 2 (Reflexive   (@equiv ?A ?e)) => simple notypeclasses refine (_ : @IsSet A e) : typeclass_instances.
Global Hint Extern 2 (Symmetric   (@equiv ?A ?e)) => simple notypeclasses refine (_ : @IsSet A e) : typeclass_instances.
Global Hint Extern 2 (Transitive  (@equiv ?A ?e)) => simple notypeclasses refine (_ : @IsSet A e) : typeclass_instances.
Global Hint Extern 2 (PartialEquivalence (@equiv ?A ?e)) => simple notypeclasses refine (_ : @IsSet A e) : typeclass_instances.

Record set@{u} := set_make
{ set_T :> Type@{u}
; #[canonical=no] set_eq : set_T ∗ set_T → Ω
; #[canonical=no] set_is_set : IsSet set_T (e:=set_eq)
}.
Arguments set_make _ {_ _}.
Global Hint Extern 5 (Equiv _) => simple notypeclasses refine (set_eq _) : typeclass_instances.
Global Hint Extern 2 (IsSet _) => simple notypeclasses refine (set_is_set _) : typeclass_instances.

Declare Scope set_scope.
Delimit Scope set_scope with set.
Bind Scope set_scope with set.
Global Open Scope set_scope.

SubClass StrongSet (X:set) := @StronglyTransitive X (=).
SubClass DecidableEquality (X:set) := @DecidableRelation (X ∗ X) (=).
SubClass AffirmativeEquality (X:set) := @AffirmativeRelation (X ∗ X) (=).
SubClass RefutativeEquality (X:set) := @RefutativeRelation (X ∗ X) (=).
Existing Class StrongSet.
Existing Class DecidableEquality.
Existing Class AffirmativeEquality.
Existing Class RefutativeEquality.
Global Hint Extern 2 (StronglyTransitive (A:=set_T ?X) (=)) => change (StrongSet X) : typeclass_instances.
Global Hint Extern 2 (DecidableRelation (A:=set_T ?X ∗ _) (=)) => change (DecidableEquality X) : typeclass_instances.
Global Hint Extern 2 (AffirmativeRelation (A:=set_T ?X ∗ _) (=)) => change (AffirmativeEquality X) : typeclass_instances.
Global Hint Extern 2 (RefutativeRelation (A:=set_T ?X ∗ _) (=)) => change (RefutativeEquality X) : typeclass_instances.

SubClass IsDecEq (X:set) {d:@Dec (X∗X) (=)} := @IsDec (X∗X) (=) d.
Existing Class IsDecEq.
Global Hint Extern 2 (@IsDec (set_T ?X ∗ _) (=) ?d) => change (@IsDecEq X d) : typeclass_instances.


(*
(** subcarrier : a set with its carrier restricted to some SProp predicate *)
Record subcarrier {X:set} (P:X → SProp) :=
{ subcarrier_pt :> X
; subcarrier_prop : P subcarrier_pt
}.
Arguments subcarrier_pt {_ _} _.
Arguments subcarrier_prop {_ _} _.
Definition subcarrier_eq {X P} : Equiv (@subcarrier X P) := λ '(x, y), subcarrier_pt x = subcarrier_pt y.
#[global] Hint Extern 2 (Equiv (@subcarrier ?X ?P)) => simple notypeclasses refine (@subcarrier_eq X P) : typeclass_instances.

Lemma subcarrier_is_set {X P} : IsSet (@subcarrier X P).
Proof. split; hnf; intros; change (?a = ?b) with (subcarrier_pt a = subcarrier_pt b).
+ now apply reflexivity.
+ now apply symmetry.
+ now apply transitivity.
Qed.
#[global] Hint Extern 2 (IsSet (@subcarrier ?X ?P)) => simple notypeclasses refine (@subcarrier_is_set X P) : typeclass_instances.

Canonical Structure subcarrier_set {X:set} (P:X → SProp) := set_make (subcarrier P).
*)


Record strong_set := make_strong_set
  { strong_set_car :> set
  ; #[canonical=no, reversible=no] strong_set_prop :> StrongSet strong_set_car
  }.
Global Hint Extern 2 (StripCoercions (strong_set_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (StrongSet ?X) => exact_strip_coercions X : typeclass_instances.
Arguments make_strong_set _ {_}.


Canonical Structure empty_set : set := @set_make empty _ (trivial_Equivalence _).
Canonical Structure unit_set  : set := @set_make unit  _ (trivial_Equivalence _).
Notation "𝟎" := empty_set : set_scope.
Notation "𝟏" := unit_set : set_scope.
Global Hint Extern 1 (BoldZero set) => refine empty_set : typeclass_instances.
Global Hint Extern 1 (BoldOne  set) => refine unit_set : typeclass_instances.

Section operations.
  Universes u.
  Context {A:Type@{u}} {Y:set@{u}}.

  Local Instance ext_eq : Equiv (A → Y) := λ '(f, g), ∏ x, f x = g x.
  Local Instance opn_is_set : IsSet (A → Y).
  Proof. split; unfold equiv, ext_eq.
  + now intros f x.
  + intros f g. rew <-all_adj. intros x.
    now rew [ <-(symmetry (=) (f x) _) | (all_lb _ x) ].
  + intros f g h. rew <-all_adj. intros x.
    now rew [ <-(transitivity (=) _ (g x) _)
            | (all_lb (λ x, f x = g x) x)
            | (all_lb (λ x, g x = h x) x) ].
  Qed.
  Definition operation := set_make (A → Y).
End operations.
Arguments operation A Y : clear implicits.
Canonical operation.
Notation "A → Y" := (operation A Y) (only printing) : set_scope.
#[global] Hint Extern 2 (Equiv (_ → _)) => notypeclasses refine ext_eq : typeclass_instances.

(** Functions *)
(*
Class IsFun@{u} {X Y:set@{u}} (f:X → Y) : SProp := is_fun x₁ x₂ : x₁ = x₂ ⊸ f x₁ = f x₂ .
Arguments is_fun {X Y} f {_} _ _.

Definition func@{u} (X Y : set@{u}) := ssig (@IsFun X Y).
Strategy opaque [func].
Opaque func.
Definition func_make@{u} {X Y : set@{u}} (f:X → Y) {H:IsFun f} := {| pt := f; pt_prop := H |}.
Definition func_op@{u} `(f:func@{u} X Y) : X → Y := pt f.
#[reversible=yes] Coercion func_op : func >-> Funclass.
Coercion func_is_fun `(f:func X Y) : IsFun (func_op f) := pt_prop f.
Global Hint Extern 2 (IsFun _) => simple notypeclasses refine (func_is_fun _) : typeclass_instances.

Definition func_ext_eq@{u} {X Y:set@{u}} : Equiv (func X Y) := λ '(f, g), ∏ x, f x = g x.
#[global] Hint Extern 2 (Equiv (func _ _)) => notypeclasses refine func_ext_eq : typeclass_instances.

Lemma func_is_set@{u} {X Y:set@{u}} : IsSet (func X Y).
Proof. split; hnf; intros; change (?f = ?g) with (func_op f = func_op g).
+ refl.
+ now apply symmetry.
+ now apply transitivity.
Qed.
#[global] Hint Extern 2 (IsSet (func _ _)) => simple notypeclasses refine func_is_set : typeclass_instances.

Definition func_set@{u} (X Y:set@{u}) := set_make (func X Y).
Canonical func_set.
Infix "⇾" := func_set : set_scope.
Abbreviation func_op2 f x y := (func_op (func_op f x) y) (only parsing).
*)

Section functions.
  Universes u.
  Context {X Y:set@{u}}.
  Class IsFun (f:X → Y) : SProp := is_fun x₁ x₂ : x₁ = x₂ ⊸ f x₁ = f x₂ .
  Global Arguments is_fun f {_} _ _.


  Record func := func_make
  { func_op :> X → Y
  ; #[canonical=no, reversible=no] func_is_fun :> IsFun func_op
  }.
  Global Arguments func_make _ {_}.

  Local Instance func_ext_eq : Equiv func := λ '(f, g), ∏ x, f x = g x.
  Local Instance func_is_set : IsSet func.
  Proof. split; hnf; intros; change (?f = ?g) with (func_op f = func_op g).
  + refl.
  + now apply symmetry.
  + now apply transitivity.
  Qed.

  Definition func_set := set_make func.
End functions.
Arguments func X Y : clear implicits.
Arguments func_set X Y : clear implicits.
Canonical func_set.
Global Hint Extern 2 (IsFun _) => simple notypeclasses refine (func_is_fun _) : typeclass_instances.
Global Hint Extern 0 (Equiv (func _ _)) => simple notypeclasses refine func_ext_eq : typeclass_instances.
Infix "⇾" := func_set : set_scope.
Abbreviation func_op2 f x y := (func_op (func_op f x) y) (only parsing).


Definition strong_set_morphism (X Y : strong_set) := X ⇾ Y.

Canonical Structure id_fun (X:set) : X ⇾ X := @func_make X X id (λ x₁ x₂, aimpl_refl _).
(*Global Hint Extern 1 (Id set) => refine id_fun : typeclass_instances.*)

Import projection_notation.

Section product.
  Universes u.
  Definition prod_set_eq (X Y : set@{u}) : Equiv (X ∗ Y)
    := λ '((x₁, y₁), (x₂, y₂)), x₁ = x₂ ∧ y₁ = y₂.
  Definition tensor_set_eq (X Y : set@{u}) : Equiv (X ∗ Y)
    := λ '((x₁, y₁), (x₂, y₂)), x₁ = x₂ ⊠ y₁ = y₂.

  Local Instance prod_set_is_set (X Y : set@{u}) : IsSet (X∗Y) (e:=prod_set_eq X Y).
  Proof. split; unfold equiv, prod_set_eq.
  + intros [x y]. now split.
  + intros [x₁ y₁] [x₂ y₂]. apply aand_proper_aimpl; now apply symmetry.
  + intros [x₁ y₁] [x₂ y₂] [x₃ y₃]. refine (aand_intro _ _).
    * rew [ (aandl (x₁ = x₂) _) | (aandl (x₂ = x₃) _) ]. now apply transitivity.
    * rew [ (aandr _ (y₁ = y₂)) | (aandr _ (y₂ = y₃)) ]. now apply transitivity.
  Qed.

  Local Instance tensor_set_is_set (X Y : set@{u}) : IsSet (X∗Y) (e:=tensor_set_eq X Y).
  Proof. split; unfold equiv, tensor_set_eq.
  + now refine (λ '(x, y), conj _ _).
  + refine (λ '(x₁, y₁), λ '(x₂, y₂), aprod_proper_aimpl _ _); now apply symmetry.
  + refine (λ '(x₁, y₁), λ '(x₂, y₂), λ '(x₃, y₃), _).
    rew <-(aprod_assoc _ _ _), (aprod_assoc (x₁ = x₂) _ _).
    rew (aprod_com (y₁ = y₂) _).
    rew <-(aprod_assoc _ _ _), (aprod_assoc _ _ (y₂ = y₃)).
    refine (aprod_proper_aimpl _ _); now apply transitivity.
  Qed.

  Definition prod_set (X Y : set@{u}) : set := @set_make (X∗Y) (prod_set_eq X Y) _ .
  Definition tensor_set (X Y : set@{u}) : set := @set_make (X∗Y) (tensor_set_eq X Y) _ .
End product.
Infix "×" := prod_set : set_scope.
Infix "⊗" := tensor_set : set_scope.
Canonical tensor_set.
Global Hint Extern 1 (Product set) => refine prod_set   : typeclass_instances.
Global Hint Extern 1 (Tensor  set) => refine tensor_set : typeclass_instances.

Definition StrongOp@{u} {X Y Z:set@{u}} (f:X ⊗ Y ⇾ Z) := @IsFun (X × Y) Z f.
Existing Class StrongOp.
Definition strong_op@{u} {X Y Z:set@{u}} (f:X ⊗ Y ⇾ Z) {H:StrongOp f} : X × Y ⇾ Z := @func_make _ _ _ H.

Section composition.
  Universes u.
  Local Instance scompose_op_is_fun {X Y Z : set@{u}} (g : Y ⇾ Z) (f : X ⇾ Y) : IsFun (λ x, g (f x)).
  Proof. intros x₁ x₂. rew <-(is_fun g _ _). exact (is_fun f _ _). Qed.

  Definition scompose {X Y Z : set@{u}} : (Y ⇾ Z) ∗ (X ⇾ Y) → (X ⇾ Z) := λ '(g, f), func_make (λ x, g (f x)).

  Local Instance scompose_is_fun {X Y Z : set@{u}} : IsFun (@scompose X Y Z).
  Proof. intros [g₁ f₁] [g₂ f₂].
    change ( (∏ y, g₁ y = g₂ y) ⊠ (∏ x, f₁ x = f₂ x) ⊸ (∏ x, g₁ (f₁ x) = g₂ (f₂ x)) ).
    rew <-all_adj. intros x. rew [(all_lb _ x) | <-(transitivity (=) _ (g₂ (f₁ x)) _)].
    exact (aprod_proper_aimpl (all_lb _ _) (is_fun g₂ _ _)).
  Qed.
  Definition scompose_fun {X Y Z : set@{u}} : (Y ⇾ Z) ⊗ (X ⇾ Y) ⇾ (X ⇾ Z) := func_make scompose.
End composition.
Global Hint Extern 2 (IsFun scompose) => simple notypeclasses refine scompose_is_fun : typeclass_instances.
Canonical scompose_fun.
Notation "(∘)" := scompose : set_scope.
Notation "g ∘ f" := ((∘) (@pair (set_T (_ ⇾ _)) (set_T (_ ⇾ _)) g f)) : set_scope.

(** The "obvious" function from X to Y *)
Class Cast X Y := cast : X ⇾ Y.
Arguments cast X Y {_}.

(** Coercions: set morphisms whose underyling function is the identity *)
Class Coerce@{u} (X Y : set@{u}) := coerce : X ⇾ Y.
Arguments coerce X Y {_}.
#[global] Hint Extern 1 (Coerce ?X ?X) => exact (id_fun X) : typeclass_instances.
#[global] Hint Extern 100 (Coerce _ _) => simple notypeclasses refine (id_fun _) : typeclass_instances.


Class Inverse `(f:X ⇾ Y) := inverse : Y ⇾ X.
Arguments inverse {_ _} f {_}.
Global Typeclasses Transparent Inverse.
Declare Scope fun_inv_scope.
Local Open Scope fun_inv_scope.
Notation "f ⁻¹" := (inverse f) (at level 1, left associativity, format "f ⁻¹") : fun_inv_scope.

Global Hint Extern 2 (Inverse (id_fun ?X)) => refine (id_fun X) : typeclass_instances.
Global Hint Extern 2 (Inverse (?g ∘ ?f)) => notypeclasses refine (inverse f ∘ inverse g) : typeclass_instances.


Section jections.
  Class Injective `(f:X ⇾ Y) : SProp := injective x y : f x = f y ⊸ x = y.

  Class WeaklySurjective@{u} {A:Type@{u}} {Y:set@{u}} (f:A → Y) : SProp := weakly_surjective : ∏ y, ∐ x, f x = y.

  Class Surjective `(f:X ⇾ Y) {inv:Inverse f} : SProp := surjective : f ∘ f⁻¹ = id_fun Y.

  Record Bijective `(f:X ⇾ Y) {inv:Inverse f} : SProp :=
  { #[reversible=no] bijective_injective :> Injective f
  ; #[reversible=no] bijective_surjective :> Surjective f
  }.
  Existing Class Bijective.
End jections.

Arguments injective {_ _} f {_} x y.
Arguments weakly_surjective {_ _} f {_}.
Arguments surjective {_ _} f {_ _}.


Section sum.
  Universes u.
  Import tsum_notation.
  Local Instance sum_set_eq (X Y : set@{u}) : Equiv (X + Y)
    := λ '(a, b), match a with
       | inl x₁ => match b with
         | inl x₂ => x₁ = x₂
         | _ => 𝐅
         end
       | inr y₁ => match b with
         | inl _ => 𝐅
         | inr y₂ => y₁ = y₂
         end
       end.

  Local Instance sum_set_is_set (X Y : set@{u}) : IsSet (X+Y).
  Proof. split; unfold equiv, sum_set_eq.
  + now intros [x|y].
  + intros [x₁|y₁] [x₂|y₂]; try exact _; now apply symmetry.
  + intros [x₁|y₁] [x₂|y₂] [x₃|y₃]. 1, 8: now apply transitivity. all: tautological.
  Qed.

  Definition sum_set (X Y : set@{u}) : set := set_make (X+Y).
End sum.
Canonical sum_set.
Infix "+" := sum_set (only printing) : set_scope.

