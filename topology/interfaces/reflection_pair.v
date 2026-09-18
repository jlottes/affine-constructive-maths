Require Import sprop srelations.
Require Export interfaces.set algebra_notation.
Require Import logic.aprop relations.
Require Import set_lambda.
Require Export interfaces.orders interfaces.subset.
Require Import orders.orders.
Require Import easy.

Import of_course_set_notation.

Definition Cat := Set.

Class Fiber@{u} (C:Cat) := Fib (X:set@{u}) : Type@{u}.
Arguments Fib C {_} X.
Existing Class Fib.

Class ObjClass@{u} C {F:Fiber@{u} C} := Obj (X:set@{u}) {FX:Fib C X} : SProp.
Arguments Obj C {_ _} X {_}.
Existing Class Obj.

Class HomClass@{u} C {F:Fiber@{u} C} := Hom_fun (X Y:set@{u}) {FX:Fib C X} {FY:Fib C Y} : !(X ⇾ Y) ⇾ SProp.
Arguments Hom_fun C {F _ X Y FX FY}.
Definition Hom@{u} C {F H} {X:set@{u}} {Y:set@{u}} {FX FY} (f:X ⇾ Y) : SProp := func_op (@Hom_fun@{u} C F H X Y FX FY) f.
Existing Class Hom.

#[global] Hint Extern 2 (impl (@Hom ?C ?F ?H ?X ?Y ?FX ?FY ?f, _ ?g)) => change (impl (func_op (@Hom_fun C F H X Y FX FY) f, func_op (@Hom_fun C F H X Y FX FY) ?g)) : proper.
#[global] Hint Extern 2 (iff  (@Hom ?C ?F ?H ?X ?Y ?FX ?FY ?f, _ ?g)) => change (iff  (func_op (@Hom_fun C F H X Y FX FY) f, func_op (@Hom_fun C F H X Y FX FY) ?g)) : proper.
  
Class Construct@{u} C `{O:@ObjClass@{u} C F} {H:HomClass C} : SProp :=
{ construct_id {X:set@{u}} {FX:Fib C X} `{!Obj C X} : Hom C (id_fun X)
; construct_hom_X {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {f:X ⇾ Y} : Hom C f → Obj C X
; construct_hom_Y {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {f:X ⇾ Y} : Hom C f → Obj C Y
; construct_compose {X:set@{u}} {Y:set@{u}} {Z:set@{u}} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z}
    {f:X ⇾ Y} {g:Y ⇾ Z} `{!Hom C f} `{!Hom C g} : Hom C (g ∘ f)
}.
#[global] Hint Extern 2 (Hom _ (id_fun _)) => simple notypeclasses refine construct_id : typeclass_instances.
#[global] Hint Extern 2 (Hom _ (_ ∘ _)) => simple notypeclasses refine construct_compose : typeclass_instances.

(** Induced poset on fibers *)
Record fib@{u} C `{HC:@Construct@{u} C F O H} (X:set@{u}) :=
{ fib_Fib :> Fib C X
; fib_Obj :> Obj C X
}.
Arguments fib_Fib {C _ _ _ _ _} _.
Arguments fib_Obj {C _ _ _ _ _} _.
#[global] Hint Extern 2 (Obj _ _ (FX:=fib_Fib ?f)) => exact (fib_Obj f) : typeclass_instances.

Section fib.
  Universes u.
  Context C `{HC:@Construct@{u} C F O H} (X:set@{u}).
  
  Definition fib_sle : srelation (fib C X)
    := (λ '(Φ, Ψ), Hom C (FX:=fib_Fib Φ) (FY:=fib_Fib Ψ) (id_fun X)).
  
  Local Instance fib_sle_refl : sReflexive fib_sle.
  Proof. intros Φ. now unfold fib_sle. Qed.
  
  Local Instance fib_sle_trans : sTransitive fib_sle.
  Proof. intros Φ Ψ Ξ. exact (@construct_compose C F O H HC _ _ _ Φ Ψ Ξ (id_fun _) (id_fun _)). Qed.
  
  #[local] Hint Extern 0 (Le (fib C X)) => exact (of_course_rel fib_sle) : typeclass_instances.
    
  Local Instance fib_preorder : PreOrder (fib C X).
  Proof. split; now unfold le. Qed.
  
  Local Instance fib_eq : Equiv (fib C X) :=  λ '(Φ, Ψ), Φ ≤ Ψ ∧ Ψ ≤ Φ.

  Lemma fib_eq_correct : ∀ Φ Ψ : fib C X, Φ = Ψ ⧟ Φ ≤ Ψ ∧ Ψ ≤ Φ.  Proof. now intros. Qed.

  Definition fib_set := Eval red in induced_poset fib_eq_correct.
  #[local] Hint Extern 0 (Le (set_T fib_set)) => exact (of_course_rel fib_sle) : typeclass_instances.
  Local Instance fib_poset : Poset fib_set := induced_poset_poset fib_eq_correct.
  Lemma fib_aff_order : AffirmativeOrder fib_set.
  Proof. split; try exact _. red. now unfold le. Qed.
End fib.
Canonical fib_set.
#[global] Hint Extern 0 (Le    (@fib ?C ?F ?O ?H ?HC ?X)) => exact (of_course_rel (@fib_sle C F O H HC X)) : typeclass_instances.
#[global] Hint Extern 0 (Le    (set_T (@fib_set ?C ?F ?O ?H ?HC ?X))) => exact (of_course_rel (@fib_sle C F O H HC X)) : typeclass_instances.
#[global] Hint Extern 0 (Equiv (@fib ?C ?F ?O ?H ?HC ?X)) => exact (@fib_eq C F O H HC X) : typeclass_instances.
#[global] Hint Extern 2 (Poset (@fib_set ?C ?F ?O ?H ?HC ?X)) => exact (@fib_poset C F O H HC X) : typeclass_instances.
#[global] Hint Extern 2 (WeakPoset (@fib_set ?C ?F ?O ?H ?HC ?X)) => exact (@fib_poset C F O H HC X) : typeclass_instances.
#[global] Hint Extern 2 (PreOrder (set_T (@fib_set ?C ?F ?O ?H ?HC ?X))) => exact (@fib_preorder C F O H HC X) : typeclass_instances.
#[global] Hint Extern 2 (PreOrder (@fib ?C ?F ?O ?H ?HC ?X)) => exact (@fib_preorder C F O H HC X) : typeclass_instances.
#[global] Hint Extern 2 (AffirmativeOrder (@fib_set ?C ?F ?O ?H ?HC ?X)) => exact (@fib_aff_order C F O H HC X) : typeclass_instances.
#[global] Hint Extern 2 (AffirmativeLe (@fib ?C ?F ?O ?H ?HC ?X)) => exact (@fib_aff_order C F O H HC X) : typeclass_instances.
#[global] Hint Extern 2 (AffirmativeLe (set_T (@fib_set ?C ?F ?O ?H ?HC ?X))) => exact (@fib_aff_order C F O H HC X) : typeclass_instances.

#[global] Hint Extern 10 (Fib ?C ?X) => match goal with
| H:fib C X |- _ => exact H
| H:set_T (fib_set C X) |- _ => exact H
end : typeclass_instances.


Definition RflClass := HomClass.
Definition IniClass := HomClass.
Definition EmbClass := HomClass.
Arguments RflClass C {F}.
Arguments IniClass C {F}.
Arguments EmbClass C {F}.
Existing Class RflClass.
Existing Class IniClass.
Existing Class EmbClass.

Definition Rfl@{u} C `{R:@RflClass@{u} C F} {X:set@{u}} {Y:set@{u}} {FX FY} (f:X ⇾ Y) : SProp := func_op (@Hom_fun@{u} C F R X Y FX FY) f.
Existing Class Rfl.
#[global] Hint Extern 2 (impl (@Rfl ?C ?F ?H ?X ?Y ?FX ?FY ?f, _ ?g)) => change (impl (func_op (@Hom_fun C F H X Y FX FY) f, func_op (@Hom_fun C F H X Y FX FY) ?g)) : proper.
#[global] Hint Extern 2 (iff  (@Rfl ?C ?F ?H ?X ?Y ?FX ?FY ?f, _ ?g)) => change (iff  (func_op (@Hom_fun C F H X Y FX FY) f, func_op (@Hom_fun C F H X Y FX FY) ?g)) : proper.

Require Import easy rewrite.

Local Open Scope sprop_scope.

Class IniClassSpec C `{H:@HomClass C F} {R:@RflClass C F} {I:@IniClass C F} :=
  ini_class_spec X Y {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y)
    : Hom (H:=I) C f ↔ Hom C f ∧ Rfl C f.

Definition Ini@{u} C `{HI:@IniClassSpec@{u} C F H R J} {X:set@{u}} {Y:set@{u}} {FX FY} (f:X ⇾ Y) : SProp := func_op (@Hom_fun@{u} C F J X Y FX FY) f.
Existing Class Ini.

Lemma initial_split_iff@{u} `{HI:@IniClassSpec@{u} C F H R J} {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y) : Ini C f ↔ Hom C f ∧ Rfl C f .
Proof. apply HI. Qed.

Coercion initial_hom `{Hf:@Ini C F H R J HI X Y FX FY f} : Hom C f.
Proof. revert Hf. now rew (initial_split_iff f). Qed.

Coercion initial_rfl `{Hf:@Ini C F H R J HI X Y FX FY f} : Rfl C f.
Proof. revert Hf. now rew (initial_split_iff f). Qed.

#[global] Hint Extern 2 (impl (@Ini ?C ?F _ _ ?J _ ?X ?Y ?FX ?FY ?f, _ ?g)) => change (impl (func_op (@Hom_fun C F J X Y FX FY) f, func_op (@Hom_fun C F J X Y FX FY) ?g)) : proper.
#[global] Hint Extern 2 (iff  (@Ini ?C ?F _ _ ?J _ ?X ?Y ?FX ?FY ?f, _ ?g)) => change (iff  (func_op (@Hom_fun C F J X Y FX FY) f, func_op (@Hom_fun C F J X Y FX FY) ?g)) : proper.


Class EmbClassSpec@{u} C `{HI:@IniClassSpec@{u} C F H R J} {E:@EmbClass C F} :=
  emb_class_spec X Y {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y)
    : Hom (H:=E) C f ↔ Ini C f ∧ Injective f.

Definition Emb@{u} C `{HE:@EmbClassSpec@{u} C F H R J HI E} {X:set@{u}} {Y:set@{u}} {FX FY} (f:X ⇾ Y) : SProp := func_op (@Hom_fun@{u} C F E X Y FX FY) f.
Existing Class Emb.

Lemma embed_split_iff@{u} `{HE:@EmbClassSpec@{u} C F H R J HI E} {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y) : Emb C f ↔ Ini C f ∧ Injective f .
Proof. apply HE. Qed.

Coercion emb_ini `{Hf:@Emb C F H R J HI E HE X Y FX FY f} : Ini C f.
Proof. revert Hf. now rew (embed_split_iff f). Qed.

Coercion emb_inj `{Hf:@Emb C F H R J HI E HE X Y FX FY f} : Injective f.
Proof. revert Hf. now rew (embed_split_iff f). Qed.

#[global] Hint Extern 2 (impl (@Emb ?C ?F _ _ _ _ ?E _ ?X ?Y ?FX ?FY ?f, _ ?g)) => change (impl (func_op (@Hom_fun C F E X Y FX FY) f, func_op (@Hom_fun C F E X Y FX FY) ?g)) : proper.
#[global] Hint Extern 2 (iff  (@Emb ?C ?F _ _ _ _ ?E _ ?X ?Y ?FX ?FY ?f, _ ?g)) => change (iff  (func_op (@Hom_fun C F E X Y FX FY) f, func_op (@Hom_fun C F E X Y FX FY) ?g)) : proper.


Definition RflConstruct C {F O} {R:@RflClass C F} := @Construct C F O R.
Existing Class RflConstruct.

Definition rfl_construct_id `{HC:@RflConstruct C F O R} {X FX HX} : Rfl C (id_fun X) := @construct_id C F O R HC X FX HX.
Definition rfl_construct_compose `{HC:@RflConstruct C F O R} {X Y Z FX FY FZ f g} {Hf:Rfl C f} {Hg:Rfl C g} : Rfl C (g ∘ f) := @construct_compose C F O R HC X Y Z FX FY FZ f g Hf Hg.
#[global] Hint Extern 2 (Rfl _ (id_fun _)) => simple notypeclasses refine rfl_construct_id : typeclass_instances.
#[global] Hint Extern 2 (Rfl _ (_ ∘ _)) => simple notypeclasses refine rfl_construct_compose : typeclass_instances.
Definition rfl_construct_hom_X `{HC:@RflConstruct C F O R} {X Y FX FY f} : Rfl C f → Obj C X := @construct_hom_X C F O R HC X Y FX FY f.
Definition rfl_construct_hom_Y `{HC:@RflConstruct C F O R} {X Y FX FY f} : Rfl C f → Obj C Y := @construct_hom_Y C F O R HC X Y FX FY f.

Definition IniConstruct@{u} C {F O} `{HI:@IniClassSpec@{u} C F H R J} := @Construct C F O J.
Existing Class IniConstruct.

Section ini_construct.
  Universes u.
  Context `{HC:@IniConstruct C F O H R J HI}.

  Lemma ini_construct_id {X:set@{u}} {FX:Fib C X} {HX:Obj C X} : Ini C (id_fun X).  Proof. now apply HC. Qed.
  Lemma ini_construct_hom_X {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {f:X ⇾ Y} : Ini C f → Obj C X.  Proof. now apply HC. Qed.
  Lemma ini_construct_hom_Y {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {f:X ⇾ Y} : Ini C f → Obj C Y.  Proof. now apply HC. Qed.
  Lemma ini_construct_compose {X:set@{u}} {Y:set@{u}} {Z:set@{u}} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z}
    {f:X ⇾ Y} {g:Y ⇾ Z} {Hf:Ini C f} {Hg:Ini C g} : Ini C (g ∘ f).
  Proof. revert Hf Hg. apply HC. Qed.
End ini_construct.
#[global] Hint Extern 2 (Ini _ (id_fun _)) => simple notypeclasses refine ini_construct_id : typeclass_instances.
#[global] Hint Extern 2 (Ini _ (_ ∘ _)) => simple notypeclasses refine ini_construct_compose : typeclass_instances.


Definition EmbConstruct@{u} C {F O} `{HE:@EmbClassSpec@{u} C F H R J HI E} := @Construct C F O E.
Existing Class EmbConstruct.

Section emb_construct.
  Universes u.
  Context `{HC:@EmbConstruct C F O H R J HI E HE}.

  Lemma emb_construct_id {X:set@{u}} {FX:Fib C X} {HX:Obj C X} : Emb C (id_fun X).  Proof. now apply HC. Qed.
  Lemma emb_construct_hom_X {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {f:X ⇾ Y} : Emb C f → Obj C X.  Proof. now apply HC. Qed.
  Lemma emb_construct_hom_Y {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {f:X ⇾ Y} : Emb C f → Obj C Y.  Proof. now apply HC. Qed.
  Lemma emb_construct_compose {X:set@{u}} {Y:set@{u}} {Z:set@{u}} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z}
    {f:X ⇾ Y} {g:Y ⇾ Z} {Hf:Emb C f} {Hg:Emb C g} : Emb C (g ∘ f).
  Proof. revert Hf Hg. apply HC. Qed.
End emb_construct.
#[global] Hint Extern 2 (Emb _ (id_fun _)) => simple notypeclasses refine emb_construct_id : typeclass_instances.
#[global] Hint Extern 2 (Emb _ (_ ∘ _)) => simple notypeclasses refine emb_construct_compose : typeclass_instances.

#[global] Hint Extern 10 (Obj ?C ?X) =>
  match goal with
  | H : Hom C (X:=X) _ |- _ => simple notypeclasses refine (construct_hom_X H)
  | H : Hom C (Y:=X) _ |- _ => simple notypeclasses refine (construct_hom_Y H)
  | H : Rfl C (X:=X) _ |- _ => simple notypeclasses refine (rfl_construct_hom_X H)
  | H : Rfl C (Y:=X) _ |- _ => simple notypeclasses refine (rfl_construct_hom_Y H)
  | H : Ini C (X:=X) _ |- _ => simple notypeclasses refine (ini_construct_hom_X H)
  | H : Ini C (Y:=X) _ |- _ => simple notypeclasses refine (ini_construct_hom_Y H)
  | H : Emb C (X:=X) _ |- _ => simple notypeclasses refine (emb_construct_hom_X H)
  | H : Emb C (Y:=X) _ |- _ => simple notypeclasses refine (emb_construct_hom_Y H)
  end : typeclass_instances.


Record ReflectionPairClasses@{u} (C:Cat) :=
{ rfl_pair_fiber :> Fiber@{u} C
; rfl_pair_obj :> ObjClass@{u} C
; rfl_pair_hom :> HomClass@{u} C
; rfl_pair_rfl :> RflClass@{u} C
; rfl_pair_ini :> IniClass@{u} C
; rfl_pair_emb :> EmbClass@{u} C
}.
Arguments rfl_pair_fiber C {_}.
Arguments rfl_pair_obj C {_}.
Arguments rfl_pair_hom C {_}.
Arguments rfl_pair_rfl C {_}.
Arguments rfl_pair_ini C {_}.
Arguments rfl_pair_emb C {_}.
Existing Class ReflectionPairClasses.
#[global] Hint Extern 4 (Fiber    ?C) => simple notypeclasses refine (rfl_pair_fiber C) : typeclass_instances. 
#[global] Hint Extern 4 (ObjClass ?C) => simple notypeclasses refine (rfl_pair_obj C) : typeclass_instances. 
#[global] Hint Extern 4 (HomClass ?C) => simple notypeclasses refine (rfl_pair_hom C) : typeclass_instances. 
#[global] Hint Extern 4 (RflClass ?C) => simple notypeclasses refine (rfl_pair_rfl C) : typeclass_instances. 
#[global] Hint Extern 4 (IniClass ?C) => simple notypeclasses refine (rfl_pair_ini C) : typeclass_instances. 
#[global] Hint Extern 4 (EmbClass ?C) => simple notypeclasses refine (rfl_pair_emb C) : typeclass_instances. 

Record ReflectionPair@{u} C {CD:ReflectionPairClasses@{u} C} : SProp :=
{ #[canonical=no, reversible=no] rp_fwd_constr :> Construct    C
; #[canonical=no, reversible=no] rp_rfl_constr :> RflConstruct C
; #[canonical=no, reversible=no] rp_ini_spec :> IniClassSpec C
; #[canonical=no, reversible=no] rp_emb_spec :> EmbClassSpec C
; rp_cancel_fwd {X} {Y} {Z} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z}
    {f:X ⇾ Y} {g:Y ⇾ Z} `{!Rfl C g} : Hom C (g ∘ f) → Hom C f
; rp_cancel_rfl {X} {Y} {Z} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z}
    {f:X ⇾ Y} {g:Y ⇾ Z} `{!Hom C g} : Rfl C (g ∘ f) → Rfl C f
}.
Existing Class ReflectionPair.
Arguments rp_cancel_fwd {C _ _ X Y Z _ _ _ f} g {_} _.
Arguments rp_cancel_rfl {C _ _ _ _ _ _ _ _ f} g {_} _.


(** A saturated pair: each class is the largest one satisfying the cancellation
    law against the other.  Reflecting maps are exactly the maps that detect
    forward maps under precomposition, and forward maps exactly those that
    detect reflecting maps; the cancellation laws are the "only if" halves,
    these fields the "if" halves.  Almost all of the theory proceeds without
    saturation; products ([reflection_pair/products.v]) are its first use.
    Every cloven pair is saturated ([cloven_saturated]). *)
Record SaturatedPair@{u} C {CD:ReflectionPairClasses@{u} C} : SProp :=
{ #[canonical=no, reversible=no] saturated_pair :> ReflectionPair C
; rp_rfl_detect {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} `{!Obj C X, !Obj C Y} (m:X ⇾ Y)
    : (∀ (S:set@{u}) (FS:Fib C S) (g:S ⇾ X), Hom C (m ∘ g) → Hom C g) → Rfl C m
; rp_hom_detect {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} `{!Obj C X, !Obj C Y} (m:X ⇾ Y)
    : (∀ (S:set@{u}) (FS:Fib C S) (g:S ⇾ X), Rfl C (m ∘ g) → Rfl C g) → Hom C m
}.
Existing Class SaturatedPair.
Arguments rp_rfl_detect {C _ _ X Y _ _ _ _} m _.
Arguments rp_hom_detect {C _ _ X Y _ _ _ _} m _.


Class Cleavage@{u} C {F:Fiber@{u} C} := pull (S Z:set@{u}) {FZ:Fib C Z} (f:S ⇾ Z) : Fib C S.
Arguments pull C {F _ S Z FZ} f.

Record ClovenPair@{u} C {CD:ReflectionPairClasses@{u} C} {CC:Cleavage@{u} C} : SProp :=
{ #[canonical=no, reversible=no] cloven_pair :> ReflectionPair C
; cloven_cert {S:set@{u}} {Z:set@{u}} (u:S ⇾ Z) {FZ:Fib C Z} `{!Obj C Z} : Ini C (FX:=pull C u) u
}.
Existing Class ClovenPair.

Arguments cloven_cert C {CD CC _ S Z} u {_ _}.
#[global] Hint Extern 2 (Ini ?C (FX:=pull ?C ?f) ?g) => match f with g => simple notypeclasses refine (cloven_cert C f) end : typeclass_instances.
#[global] Hint Extern 2 (Hom ?C (FX:=pull ?C ?f) ?g) => match f with g => simple notypeclasses refine (initial_hom (Hf:=cloven_cert C f)) end : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (FX:=pull ?C ?f) ?g) => match f with g => simple notypeclasses refine (initial_rfl (Hf:=cloven_cert C f)) end : typeclass_instances.

(** Pair morphisms (doc §2.2): the identity on carriers and on underlying maps —
    the data is a fiber map alone, and the laws are preservation of the two
    classes.  Obj-preservation, 𝓜/Emb-preservation, and the cloven-fibred-functor
    comparison are all derivable, not fields. *)

Class FiberMap@{u} (C D:Cat) {FC:Fiber@{u} C} {FD:Fiber@{u} D} := fmap (X:set@{u}) : Fib C X → Fib D X.
Arguments fmap C D {_ _ _ X} _.

Class HomMap@{u} C D {FC FD}
    {HC:@HomClass@{u} C FC} {HD:@HomClass@{u} D FD} {U:@FiberMap@{u} C D FC FD} : SProp :=
  hom_map (X Y:set@{u}) {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y)
    : Hom C f → Hom D (FX:=fmap C D FX) (FY:=fmap C D FY) f.
Arguments hom_map C D {_ _ _ _ _ _ _ _ _ _} f {_}.

Definition RflMap C D {FC FD} {RC:@RflClass C FC} {RD:@RflClass D FD} {U:@FiberMap C D FC FD}
  := @HomMap C D FC FD RC RD U.
Existing Class RflMap.
Definition rfl_map@{u} C D `{RM:@RflMap@{u} C D FC FD RC RD U}
  {X:set@{u}} {Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y)
  {Hf:Rfl C f} : Rfl D (FX:=fmap C D FX) (FY:=fmap C D FY) f
  := @hom_map C D FC FD RC RD U RM X Y FX FY f Hf.

Record PairMorphism@{u} C D {CD:ReflectionPairClasses@{u} C} {DD:ReflectionPairClasses@{u} D} {U:FiberMap@{u} C D} : SProp :=
{ #[canonical=no, reversible=no] pair_mor_C :> ReflectionPair C
; #[canonical=no] pair_mor_D : ReflectionPair D
; #[canonical=no, reversible=no] pair_mor_hom :> HomMap C D
; #[canonical=no, reversible=no] pair_mor_rfl :> RflMap C D
}.
Existing Class PairMorphism.

#[global] Hint Extern 10 (ReflectionPair ?D) =>
  match goal with
  | H : PairMorphism _ ?D |- _ => simple notypeclasses refine (pair_mor_D _ _ H)
  end : typeclass_instances.
#[global] Hint Extern 10 (Construct ?D) =>
  match goal with
  | H : PairMorphism _ ?D |- _ => simple notypeclasses refine (rp_fwd_constr _ (pair_mor_D _ _ H))
  end : typeclass_instances.
#[global] Hint Extern 10 (RflConstruct ?D) =>
  match goal with
  | H : PairMorphism _ ?D |- _ => simple notypeclasses refine (rp_rfl_constr _ (pair_mor_D _ _ H))
  end : typeclass_instances.
#[global] Hint Extern 10 (IniClassSpec ?D) =>
  match goal with
  | H : PairMorphism _ ?D |- _ => simple notypeclasses refine (rp_ini_spec _ (pair_mor_D _ _ H))
  end : typeclass_instances.
#[global] Hint Extern 10 (EmbClassSpec ?D) =>
  match goal with
  | H : PairMorphism _ ?D |- _ => simple notypeclasses refine (rp_emb_spec _ (pair_mor_D _ _ H))
  end : typeclass_instances.


Definition fiber_op (C:Cat) := C.
#[global] Typeclasses Opaque fiber_op.
Local Notation "C 'ᵒ'" := (fiber_op C) (at level 1, format "C 'ᵒ'").

#[global] Hint Extern 1 (Fiber     ?C ᵒ   ) => change (Fiber     C  ) : typeclass_instances.
#[global] Hint Extern 1 (@ObjClass ?C ᵒ ?F) => change (@ObjClass C F) : typeclass_instances.
#[global] Hint Extern 1 (@HomClass ?C ᵒ ?F) => change (@RflClass C F) : typeclass_instances.
#[global] Hint Extern 1 (@RflClass ?C ᵒ ?F) => change (@HomClass C F) : typeclass_instances.
#[global] Hint Extern 1 (@IniClass ?C ᵒ ?F) => change (@IniClass C F) : typeclass_instances.
#[global] Hint Extern 1 (@EmbClass ?C ᵒ ?F) => change (@EmbClass C F) : typeclass_instances.
#[global] Hint Extern 1 (@Cleavage ?C ᵒ ?F) => change (@Cleavage C F) : typeclass_instances.
#[global] Hint Extern 1 (@Construct ?C ᵒ ?F ?O ?H) => change (@RflConstruct C F O H) : typeclass_instances.
#[global] Hint Extern 1 (@RflConstruct ?C ᵒ ?F ?O ?R) => change (@Construct C F O R) : typeclass_instances.

#[global] Hint Extern 1 (@Fib ?C ᵒ ?F ?X) => change (@Fib C F X) : typeclass_instances.
#[global] Hint Extern 10 (Fib ?C ?X) => match goal with FX : Fib C ᵒ X |- _ => exact FX end : typeclass_instances.

#[global] Hint Extern 1 (@FiberMap ?C ᵒ ?D ᵒ ?FC ?FD) => change (@FiberMap C D FC FD) : typeclass_instances.
#[global] Hint Extern 1 (@HomMap ?C ᵒ ?D ᵒ ?FC ?FD ?HC ?HD ?U) => change (@RflMap C D FC FD HC HD U) : typeclass_instances.
#[global] Hint Extern 1 (@RflMap ?C ᵒ ?D ᵒ ?FC ?FD ?RC ?RD ?U) => change (@HomMap C D FC FD RC RD U) : typeclass_instances.

Section pair_product.
  Universes u.
  Context C {CD:ReflectionPairClasses@{u} C}.

  Record PairProduct (X Y:set@{u}) {FX:Fib C X} {FY:Fib C Y} (FP:Fib C (X × Y)) : SProp :=
  { pair_product_refl :> ReflectionPair C
  ; pair_product_proj1 : Hom C (prod_proj1 X Y)
  ; pair_product_proj2 : Hom C (prod_proj2 X Y)
  ; pair_product_pairing {Z:set@{u}} {FZ:Fib C Z} (f:Z ⇾ X) (g:Z ⇾ Y) `{!Hom C f, !Hom C g}
      : Hom C (to_prod (f, g))
  }.
  Existing Class PairProduct.
End pair_product.
Arguments PairProduct C {_} X Y {_ _} FP.
Arguments pair_product_proj1 {C _ X Y _ _ FP _}.
Arguments pair_product_proj2 {C _ X Y _ _ FP _}.
Arguments pair_product_pairing {C _ X Y _ _ FP _ Z FZ} f g {_ _}.
#[global] Hint Extern 2 (Hom _ (prod_proj1 _ _)) => simple notypeclasses refine pair_product_proj1 : typeclass_instances.
#[global] Hint Extern 2 (Hom _ (prod_proj2 _ _)) => simple notypeclasses refine pair_product_proj2 : typeclass_instances.
#[global] Hint Extern 2 (Hom _ (func_op to_prod (_, _))) => simple notypeclasses refine (pair_product_pairing _ _) : typeclass_instances.


