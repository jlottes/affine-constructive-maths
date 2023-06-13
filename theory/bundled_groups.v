Require Export interfaces.bundled_algebra.
Require Import abstract_algebra interfaces.cat theory.projected_set theory.groups.
Require Import theory.additive_groups theory.multiplicative_groups.
Require Import rewrite easy.
Require Import quote.base strip_coercions.

Local Open Scope cat_scope.

(** Semigroups *)

Global Hint Extern 1 (IsProjectedSet (set_T (semigroup_morphism _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom semigroup_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure semigroup_id (X : semigroup) := make_semigroup_morphism (id_fun X).
Global Hint Extern 2 (Id semigroup_cat_t) => refine semigroup_id : typeclass_instances.

Local Notation make_compose_fun c := (@make_fun _ _ _ (projected_is_fun (tuncurry c) (∘) (λ _, reflexivity (=) _))).

Canonical Structure semigroup_morphism_compose_op {X Y Z : semigroup}
  (g : semigroup_morphism Y Z) (f:semigroup_morphism X Y) : semigroup_morphism X Z
:= make_semigroup_morphism (g ∘ f).
Definition semigroup_morphism_compose {X Y Z : semigroup} := make_compose_fun (@semigroup_morphism_compose_op X Y Z).
Global Hint Extern 2 (Compose semigroup_cat_t) => refine @semigroup_morphism_compose : typeclass_instances.

Local Instance semigroup_is_cat : IsCat semigroup_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐒𝐞𝐦𝐢𝐆𝐫𝐩 := Build_cat semigroup_cat_t.


(** Multiplicative Semigroups *)

Global Hint Extern 1 (IsProjectedSet (set_T (multiplicative_semigroup_morphism _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom multiplicative_semigroup_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure multiplicative_semigroup_id (X : multiplicative_semigroup) := make_multiplicative_semigroup_morphism (id_fun X).
Global Hint Extern 2 (Id multiplicative_semigroup_cat_t) => refine multiplicative_semigroup_id : typeclass_instances.

Canonical Structure multiplicative_semigroup_morphism_compose_op {X Y Z : multiplicative_semigroup}
  (g: multiplicative_semigroup_morphism Y Z) (f: multiplicative_semigroup_morphism X Y) : multiplicative_semigroup_morphism X Z
:= make_multiplicative_semigroup_morphism (g ∘ f).
Definition multiplicative_semigroup_morphism_compose {X Y Z : multiplicative_semigroup} := make_compose_fun (@multiplicative_semigroup_morphism_compose_op X Y Z).
Global Hint Extern 2 (Compose multiplicative_semigroup_cat_t) => refine @multiplicative_semigroup_morphism_compose : typeclass_instances.

Local Instance multiplicative_semigroup_is_cat : IsCat multiplicative_semigroup_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐌𝐮𝐥𝐒𝐞𝐦𝐢𝐆𝐫𝐩 := Build_cat multiplicative_semigroup_cat_t.

(** 𝐌𝐮𝐥𝐒𝐞𝐦𝐢𝐆𝐫𝐩 and 𝐒𝐞𝐦𝐢𝐆𝐫𝐩 are just relabellings of each other *)

Canonical Structure multiplicative_semigroup_as_semigroup (X:multiplicative_semigroup) := @make_semigroup X (_ : Mult X) (_ : MultiplicativeSemiGroup X).
(*Coercion multiplicative_semigroup_as_semigroup : multiplicative_semigroup >-> semigroup.*)

Canonical Structure multiplicative_semigroup_morphism_as_sg_mor `(f:multiplicative_semigroup_morphism_t X Y)
  : semigroup_morphism_t (multiplicative_semigroup_as_semigroup X) (multiplicative_semigroup_as_semigroup Y).
Proof. unshelve refine (make_semigroup_morphism _). exact f. now change (MultiplicativeSemiGroup_Morphism f). Defined.
(*Coercion multiplicative_semigroup_morphism_as_sg_mor : multiplicative_semigroup_morphism_t >-> semigroup_morphism_t.*)

Canonical Structure semigroup_as_mul_sg (X:semigroup) : multiplicative_semigroup
  := {| multiplicative_semigroup_car  := semigroup_car X
      ; multiplicative_semigroup_op   := {| op_mult := op_sg_op X |}
      ; multiplicative_semigroup_prop := semigroup_prop X
     |}.
(*Coercion semigroup_as_mul_sg : semigroup >-> multiplicative_semigroup.*)
Canonical Structure semigroup_mor_as_mul_sg_mor `(f:semigroup_morphism_t X Y) : multiplicative_semigroup_morphism_t (semigroup_as_mul_sg X) (semigroup_as_mul_sg Y).
Proof. unshelve esplit. exact f. exact (semigroup_morphism_prop f). Defined.


(** Commutative semigroups *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom commutative_semigroup_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id commutative_semigroup_cat_t) => refine semigroup_id : typeclass_instances.
Global Hint Extern 2 (Compose commutative_semigroup_cat_t) => refine @semigroup_morphism_compose : typeclass_instances.
Local Instance commutative_semigroup_is_cat : IsCat commutative_semigroup_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐂𝐒𝐞𝐦𝐢𝐆𝐫𝐩 := Build_cat commutative_semigroup_cat_t.

(** Monoids *)

Global Hint Extern 1 (IsProjectedSet (set_T (monoid_morphism _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom monoid_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure monoid_id (X : monoid) := make_monoid_morphism (id_fun X).
Global Hint Extern 2 (Id monoid_cat_t) => refine monoid_id : typeclass_instances.

Canonical Structure monoid_morphism_compose_op {X Y Z : monoid}
  (g:monoid_morphism Y Z) (f:monoid_morphism X Y) : monoid_morphism X Z
:= make_monoid_morphism (g ∘ f).
Definition monoid_morphism_compose {X Y Z : monoid} := make_compose_fun (@monoid_morphism_compose_op X Y Z).
Global Hint Extern 2 (Compose monoid_cat_t) => refine @monoid_morphism_compose : typeclass_instances.

Local Instance monoid_is_cat : IsCat monoid_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐌𝐨𝐧 := Build_cat monoid_cat_t.

Canonical Structure monoid_as_semigroup (M:monoid) := make_semigroup M.
Coercion monoid_as_semigroup : monoid >-> semigroup.
Global Hint Extern 2 (StripCoercions (monoid_as_semigroup ?X)) => strip_coercions_chain X : strip_coercions.

Canonical Structure monoid_mor_as_sg_mor `(f:monoid_morphism_t X Y) : semigroup_morphism_t X Y := make_semigroup_morphism f.
Coercion monoid_mor_as_sg_mor : monoid_morphism_t >-> semigroup_morphism_t.
Global Hint Extern 2 (StripCoercions (monoid_mor_as_sg_mor ?f)) => strip_coercions_chain f : strip_coercions.

(** Additive non-commutative monoids *)

Global Hint Extern 1 (IsProjectedSet (set_T (additive_non_com_monoid_morphism _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom additive_non_com_monoid_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure additive_non_com_monoid_id (X : additive_non_com_monoid) := make_additive_non_com_monoid_morphism (id_fun X).
Global Hint Extern 2 (Id additive_non_com_monoid_cat_t) => refine additive_non_com_monoid_id : typeclass_instances.

Canonical Structure additive_non_com_monoid_morphism_compose_op {X Y Z : additive_non_com_monoid}
  (g:additive_non_com_monoid_morphism Y Z) (f:additive_non_com_monoid_morphism X Y) : additive_non_com_monoid_morphism X Z
:= make_additive_non_com_monoid_morphism (g ∘ f).
Definition additive_non_com_monoid_morphism_compose {X Y Z : additive_non_com_monoid} := make_compose_fun (@additive_non_com_monoid_morphism_compose_op X Y Z).
Global Hint Extern 2 (Compose additive_non_com_monoid_cat_t) => refine @additive_non_com_monoid_morphism_compose : typeclass_instances.

Local Instance additive_non_com_monoid_is_cat : IsCat additive_non_com_monoid_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐀𝐝𝐝𝐍𝐜𝐌𝐨𝐧 := Build_cat additive_non_com_monoid_cat_t.

(** Multiplicative Monoids *)

Global Hint Extern 1 (IsProjectedSet (set_T (multiplicative_monoid_morphism _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom multiplicative_monoid_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure multiplicative_monoid_id (X : multiplicative_monoid) := make_multiplicative_monoid_morphism (id_fun X).
Global Hint Extern 2 (Id multiplicative_monoid_cat_t) => refine multiplicative_monoid_id : typeclass_instances.

Canonical Structure multiplicative_monoid_morphism_compose_op {X Y Z : multiplicative_monoid}
  (g:multiplicative_monoid_morphism Y Z) (f:multiplicative_monoid_morphism X Y) : multiplicative_monoid_morphism X Z
:= make_multiplicative_monoid_morphism (g ∘ f).
Definition multiplicative_monoid_morphism_compose {X Y Z : multiplicative_monoid} := make_compose_fun (@multiplicative_monoid_morphism_compose_op X Y Z).
Global Hint Extern 2 (Compose multiplicative_monoid_cat_t) => refine @multiplicative_monoid_morphism_compose : typeclass_instances.

Local Instance multiplicative_monoid_is_cat : IsCat multiplicative_monoid_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐌𝐮𝐥𝐌𝐨𝐧 := Build_cat multiplicative_monoid_cat_t.

Canonical Structure multiplicative_monoid_as_mul_sg (X:multiplicative_monoid) := make_multiplicative_semigroup X.
Coercion multiplicative_monoid_as_mul_sg : multiplicative_monoid >-> multiplicative_semigroup.
Global Hint Extern 2 (StripCoercions (multiplicative_monoid_as_mul_sg ?X)) => strip_coercions_chain X : strip_coercions.

Canonical Structure mul_monoid_mor_as_mul_sg_mor `(f:multiplicative_monoid_morphism_t X Y) : multiplicative_semigroup_morphism_t X Y := make_multiplicative_semigroup_morphism f.
Coercion mul_monoid_mor_as_mul_sg_mor : multiplicative_monoid_morphism_t >-> multiplicative_semigroup_morphism_t.
Global Hint Extern 2 (StripCoercions (mul_monoid_mor_as_mul_sg_mor ?f)) => strip_coercions_chain f : strip_coercions.

(** 𝐀𝐝𝐝𝐍𝐜𝐌𝐨𝐧, 𝐌𝐮𝐥𝐌𝐨𝐧, and 𝐌𝐨𝐧 are just relabellings of each other *)

Canonical Structure additive_non_com_monoid_as_monoid (M:additive_non_com_monoid) := make_monoid M (o:=_ : Plus M) (u:=_ : Zero M) (H := _ : AdditiveNonComMonoid M).
Canonical Structure multiplicative_monoid_as_monoid (M:multiplicative_monoid) := make_monoid M (o:=_ : Mult M) (u:=_ : One M) (H := _ : MultiplicativeMonoid M).
(*Coercion multiplicative_monoid_as_monoid : multiplicative_monoid >-> monoid.*)

Canonical Structure additive_non_com_monoid_morphism_as_mon_mor `(f:additive_non_com_monoid_morphism_t X Y) : monoid_morphism_t (additive_non_com_monoid_as_monoid X) (additive_non_com_monoid_as_monoid Y).
Proof. simple refine (make_monoid_morphism _). exact f. now change (AdditiveMonoid_Morphism f). Defined.
Canonical Structure multiplicative_monoid_morphism_as_mon_mor `(f:multiplicative_monoid_morphism_t X Y) : monoid_morphism_t (multiplicative_monoid_as_monoid X) (multiplicative_monoid_as_monoid Y).
Proof. simple refine (make_monoid_morphism _). exact f. now change (MultiplicativeMonoid_Morphism f). Defined.
(*Coercion multiplicative_monoid_morphism_as_mon_mor : multiplicative_monoid_morphism_t >-> monoid_morphism_t.*)


Canonical Structure monoid_as_additive_non_com_monoid (M:monoid) : additive_non_com_monoid
  := {| additive_non_com_monoid_car  := monoid_car  M
      ; additive_non_com_monoid_op   := {| op_plus := op_sg_op    M |}
      ; additive_non_com_monoid_u    := {| op_zero := op_mon_unit M |}
      ; additive_non_com_monoid_prop := monoid_prop M
     |}.
(*Coercion monoid_as_multiplicative_monoid : monoid >-> multiplicative_monoid.*)
Canonical Structure monoid_mor_as_add_nc_monoid_mor `(f:monoid_morphism_t X Y) : additive_non_com_monoid_morphism_t (monoid_as_additive_non_com_monoid X) (monoid_as_additive_non_com_monoid Y).
Proof. unshelve esplit. exact f. exact (monoid_morphism_prop f). Defined.
(*Coercion monoid_mor_as_mul_monoid_mor : monoid_morphism_t >-> multiplicative_monoid_morphism_t.*)


Canonical Structure monoid_as_multiplicative_monoid (M:monoid) : multiplicative_monoid
  := {| multiplicative_monoid_car  := monoid_car  M
      ; multiplicative_monoid_op   := {| op_mult := op_sg_op    M |}
      ; multiplicative_monoid_u    := {| op_one  := op_mon_unit M |}
      ; multiplicative_monoid_prop := monoid_prop M
     |}.
(*Coercion monoid_as_multiplicative_monoid : monoid >-> multiplicative_monoid.*)
Canonical Structure monoid_mor_as_mul_monoid_mor `(f:monoid_morphism_t X Y) : multiplicative_monoid_morphism_t (monoid_as_multiplicative_monoid X) (monoid_as_multiplicative_monoid Y).
Proof. unshelve esplit. exact f. exact (monoid_morphism_prop f). Defined.
(*Coercion monoid_mor_as_mul_monoid_mor : monoid_morphism_t >-> multiplicative_monoid_morphism_t.*)


(** Commutative monoids *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom commutative_monoid_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id commutative_monoid_cat_t) => refine monoid_id : typeclass_instances.
Global Hint Extern 2 (Compose commutative_monoid_cat_t) => refine @monoid_morphism_compose : typeclass_instances.
Local Instance commutative_monoid_is_cat : IsCat commutative_monoid_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐂𝐌𝐨𝐧 := Build_cat commutative_monoid_cat_t.


(** Additive Monoids *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom additive_monoid_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id additive_monoid_cat_t) => refine additive_non_com_monoid_id : typeclass_instances.
Global Hint Extern 2 (Compose additive_monoid_cat_t) => refine @additive_non_com_monoid_morphism_compose : typeclass_instances.
Local Instance additive_monoid_is_cat : IsCat additive_monoid_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐀𝐝𝐝𝐌𝐨𝐧 := Build_cat additive_monoid_cat_t.

(** 𝐀𝐝𝐝𝐌𝐨𝐧 and 𝐂𝐌𝐨𝐧 are just relabellings of each other *)

Canonical Structure additive_monoid_as_com_monoid (M:additive_monoid) := make_commutative_monoid M (o:=_:Plus M) (u:=_:Zero M) (H:=_:AdditiveMonoid M).
(* Coercion additive_monoid_as_com_monoid : additive_monoid >-> commutative_monoid. *)

(*
Canonical Structure additive_monoid_morphism_as_mon_mor `(f:additive_monoid_morphism_t X Y) : monoid_morphism_t (additive_monoid_as_com_monoid X) (additive_monoid_as_com_monoid Y).
Proof. unshelve refine (make_monoid_morphism _). exact f. now change (AdditiveMonoid_Morphism f). Defined.
*)
(* Coercion additive_monoid_morphism_as_mon_mor : additive_monoid_morphism_t >-> monoid_morphism_t. *)

Canonical Structure com_monoid_as_additive_monoid (M:commutative_monoid) : additive_monoid
  := {| additive_monoid_car  := commutative_monoid_car  M
      ; additive_monoid_op   := {| op_plus := op_sg_op    M |}
      ; additive_monoid_u    := {| op_zero := op_mon_unit M |}
      ; additive_monoid_prop := commutative_monoid_prop M
     |}.
(* Coercion com_monoid_as_additive_monoid : commutative_monoid >-> additive_monoid. *)
(*
Canonical Structure com_monoid_mor_as_additive_monoid_mor `(f:commutative_monoid_morphism X Y) : additive_monoid_morphism (com_monoid_as_additive_monoid X) (com_monoid_as_additive_monoid Y).
Proof. unshelve esplit. exact f. exact (monoid_morphism_prop f). Defined.
*)

(** Groups *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom group_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id group_cat_t) => refine monoid_id : typeclass_instances.
Global Hint Extern 2 (Compose group_cat_t) => refine @monoid_morphism_compose : typeclass_instances.
Local Instance group_is_cat : IsCat group_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐆𝐫𝐩 := Build_cat group_cat_t.

(** Abelian Groups *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom ab_group_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id ab_group_cat_t) => refine monoid_id : typeclass_instances.
Global Hint Extern 2 (Compose ab_group_cat_t) => refine @monoid_morphism_compose : typeclass_instances.
Local Instance ab_group_is_cat : IsCat ab_group_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐀𝐛𝐆𝐫𝐩 := Build_cat ab_group_cat_t.

(** Additive Groups *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom additive_non_com_group_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id additive_non_com_group_cat_t) => refine additive_non_com_monoid_id : typeclass_instances.
Global Hint Extern 2 (Compose additive_non_com_group_cat_t) => refine @additive_non_com_monoid_morphism_compose : typeclass_instances.
Local Instance additive_non_com_group_is_cat : IsCat additive_non_com_group_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐀𝐝𝐝𝐍𝐜𝐆𝐫𝐩 := Build_cat additive_non_com_group_cat_t.

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom additive_group_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id additive_group_cat_t) => refine additive_non_com_monoid_id : typeclass_instances.
Global Hint Extern 2 (Compose additive_group_cat_t) => refine @additive_non_com_monoid_morphism_compose : typeclass_instances.
Local Instance additive_group_is_cat : IsCat additive_group_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐀𝐝𝐝𝐆𝐫𝐩 := Build_cat additive_group_cat_t.

(** 𝐀𝐝𝐝𝐍𝐜𝐆𝐫𝐩 and 𝐆𝐫𝐩 are just relabellings of each other *)

Canonical Structure additive_non_com_group_as_group (G:additive_non_com_group) := make_group G (o:=_:Plus G) (u:=_:Zero G) (i:=_:Negate G) (H:=_:AdditiveNonComGroup G).
Coercion additive_non_com_group_as_group : additive_non_com_group >-> group.

Canonical Structure group_as_additive_non_com_group (G:group) : additive_non_com_group
  := {| additive_non_com_group_car  := group_car  G
      ; additive_non_com_group_op   := {| op_plus   := op_sg_op    G |}
      ; additive_non_com_group_u    := {| op_zero   := op_mon_unit G |}
      ; additive_non_com_group_i    := {| op_negate := op_inv      G |}
      ; additive_non_com_group_prop := group_prop G
     |}.
Coercion group_as_additive_non_com_group : group >-> additive_non_com_group.

(** 𝐀𝐝𝐝𝐆𝐫𝐩 and 𝐀𝐛𝐆𝐫𝐩 are just relabellings of each other *)

Canonical Structure additive_group_as_ab_group (G:additive_group) := make_ab_group G (o:=_:Plus G) (u:=_:Zero G) (i:=_:Negate G) (H:=_:AdditiveGroup G).
Coercion additive_group_as_ab_group : additive_group >-> ab_group.

Canonical Structure ab_group_as_additive_group (G:ab_group) : additive_group
  := {| additive_group_car  := ab_group_car  G
      ; additive_group_op   := {| op_plus   := op_sg_op    G |}
      ; additive_group_u    := {| op_zero   := op_mon_unit G |}
      ; additive_group_i    := {| op_negate := op_inv      G |}
      ; additive_group_prop := ab_group_prop G
     |}.
Coercion ab_group_as_additive_group : ab_group >-> additive_group.


(** Quote for bundled morphisms *)

Local Open Scope grp_scope.
Definition quote_sg_op `(f:semigroup_morphism X Y) {x₁ y₁ x₂ y₂} :
  quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ ∙ x₂) (y₁ ∙ y₂) := quote_sg_op_alt f.

Definition quote_mon_unit `(f:monoid_morphism X Y) : quote f mon_unit mon_unit := quote_mon_unit_alt f.

Definition quote_inverse `(f:group_morphism X Y) {x y} : quote f x y → quote f (inv x) (inv y) := quote_inverse_alt f.

Global Hint Extern 2 (quote _ (_ ∙ _) _) => quote_hint_strip (fun f => refine (quote_sg_op f _ _)) : quote.
Global Hint Extern 2 (quote _ _ (_ ∙ _)) => quote_hint_strip (fun f => refine (quote_sg_op f _ _)) : quote.

Global Hint Extern 2 (quote _ mon_unit _) => quote_hint_strip (fun f => refine (quote_mon_unit f)) : quote.
Global Hint Extern 2 (quote _ _ mon_unit) => quote_hint_strip (fun f => refine (quote_mon_unit f)) : quote.

Global Hint Extern 2 (quote _ (inv _) _) => quote_hint_strip (fun f => refine (quote_inverse f _)) : quote.
Global Hint Extern 2 (quote _ _ (inv _)) => quote_hint_strip (fun f => refine (quote_inverse f _)) : quote.
Local Close Scope grp_scope.

Local Open Scope mult_scope.
Definition quote_mult `(f:multiplicative_semigroup_morphism X Y) {x₁ y₁ x₂ y₂} :
  quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ · x₂) (y₁ · y₂) := quote_mult_alt f.

Definition quote_one `(f:multiplicative_monoid_morphism X Y) : quote f 1 1 := quote_one_alt f.

Global Hint Extern 2 (quote _ (_ · _) _) => quote_hint_strip (fun f => refine (quote_mult f _ _)) : quote.
Global Hint Extern 2 (quote _ _ (_ · _)) => quote_hint_strip (fun f => refine (quote_mult f _ _)) : quote.

Global Hint Extern 2 (quote _ 1 _) => quote_hint_strip (fun f => refine (quote_one f)) : quote.
Global Hint Extern 2 (quote _ _ 1) => quote_hint_strip (fun f => refine (quote_one f)) : quote.
Local Close Scope mult_scope.

Definition quote_plus `(f:additive_non_com_monoid_morphism X Y) {x₁ y₁ x₂ y₂} :
  quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ + x₂) (y₁ + y₂) := quote_plus_alt f.
Definition quote_zero `(f:additive_non_com_monoid_morphism X Y) : quote f 0 0 := quote_zero_alt f.
Definition quote_negate `(f:additive_group_morphism X Y) {x y} :
    quote f x y → quote f (-x) (-y) := quote_negate_alt f.

Global Hint Extern 2 (quote _ (_ + _) _) => quote_hint_strip (fun f => refine (quote_plus f _ _)) : quote.
Global Hint Extern 2 (quote _ _ (_ + _)) => quote_hint_strip (fun f => refine (quote_plus f _ _)) : quote.

Global Hint Extern 2 (quote _ 0 _) => quote_hint_strip (fun f => refine (quote_zero f)) : quote.
Global Hint Extern 2 (quote _ _ 0) => quote_hint_strip (fun f => refine (quote_zero f)) : quote.

Global Hint Extern 2 (quote _ (-_) _) => quote_hint_strip (fun f => refine (quote_negate f _)) : quote.
Global Hint Extern 2 (quote _ _ (-_)) => quote_hint_strip (fun f => refine (quote_negate f _)) : quote.


