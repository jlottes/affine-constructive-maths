Require Export abstract_algebra bundled_notation interfaces.cat.
Require Import theory.projected_set theory.rings.
Require Import strip_coercions.

Import bundled_notation.definition_hints.

Set Implicit Arguments.

Global Hint Extern 4 (AffirmativeEquality ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (RefutativeEquality ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (DecidableEquality ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (AdditiveCancellation ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (IsDecEq ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (StrongSet ?X) => exact_strip_coercions X : typeclass_instances.

Global Hint Extern 20 (AffirmativeEquality ?X) => let t := strip_coercions X in progress change (AffirmativeEquality t) : typeclass_instances.
Global Hint Extern 20 (RefutativeEquality ?X) => let t := strip_coercions X in progress change (RefutativeEquality t) : typeclass_instances.
Global Hint Extern 20 (DecidableEquality ?X) => let t := strip_coercions X in progress change (DecidableEquality t) : typeclass_instances.
Global Hint Extern 20 (AdditiveCancellation ?X) => let t := strip_coercions X in progress change (AdditiveCancellation t) : typeclass_instances.
Global Hint Extern 20 (IsDecEq ?X) => let t := strip_coercions X in progress change (IsDecEq t) : typeclass_instances.
Global Hint Extern 20 (StrongSet ?X) => let t := strip_coercions X in progress change (StrongSet t) : typeclass_instances.


Global Hint Extern 4 (MonUnit_Pointed_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Global Hint Extern 4 (Zero_Pointed_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Global Hint Extern 4 (One_Pointed_Morphism ?f) => exact_strip_coercions f : typeclass_instances.


Canonical Structure strong_set_cat_t := Build_cat_t strong_set strong_set_morphism.
Global Hint Extern 1 (Id strong_set_cat_t) => refine id_fun : typeclass_instances.
Global Hint Extern 1 (Compose strong_set_cat_t) => refine @scompose : typeclass_instances.
Lemma strong_set_is_cat : IsCat strong_set_cat_t.  Proof. split; intros; exact (reflexivity (=) _). Qed.
Global Hint Extern 1 (IsCat strong_set_cat_t) => refine strong_set_is_cat : typeclass_instances.
Canonical Structure 𝐒𝐭𝐫𝐒𝐞𝐭 := Build_cat strong_set_cat_t.

(** SemiGroups *)

Record semigroup :=
  { semigroup_car :> set
  ; #[canonical=no] semigroup_op :> has_sg_op semigroup_car
  ; #[canonical=no] semigroup_prop :> SemiGroup semigroup_car
  }.
Global Hint Extern 2 (StripCoercions (semigroup_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (SemiGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_semigroup : ∀ (G:set) {o:SgOp G} {H:SemiGroup G}, semigroup := @Build_semigroup.
Arguments make_semigroup G {_ _}.

Record semigroup_morphism_t@{i} (X Y : semigroup@{i}) :=
{ semigroup_morphism_fun  :> func X Y
; #[canonical=no] semigroup_morphism_prop :> SemiGroup_Morphism semigroup_morphism_fun
}.
Global Hint Extern 2 (StripCoercions (semigroup_morphism_fun ?f)) => strip_coercions_chain f : strip_coercions.
Global Hint Extern 4 (SemiGroup_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Canonical Structure semigroup_morphism@{i} (X Y : semigroup@{i}) := projected_set (@semigroup_morphism_fun X Y).
Definition make_semigroup_morphism : ∀ {X Y : semigroup} (f:X ⇾ Y) `{!SemiGroup_Morphism f}, semigroup_morphism X Y := @Build_semigroup_morphism_t.
Arguments make_semigroup_morphism {X Y} f {_}.

Canonical Structure semigroup_cat_t := Build_cat_t semigroup semigroup_morphism.

(** Multiplicative Semigroup *)

Record multiplicative_semigroup :=
  { multiplicative_semigroup_car :> set
  ; #[canonical=no] multiplicative_semigroup_op :> has_mult multiplicative_semigroup_car
  ; #[canonical=no] multiplicative_semigroup_prop :> MultiplicativeSemiGroup multiplicative_semigroup_car
  }.
Global Hint Extern 2 (StripCoercions (multiplicative_semigroup_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (MultiplicativeSemiGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_multiplicative_semigroup : ∀ (G:set) {o:Mult G} {H:MultiplicativeSemiGroup G}, multiplicative_semigroup := @Build_multiplicative_semigroup.
Arguments make_multiplicative_semigroup G {_ _}.

Record multiplicative_semigroup_morphism_t@{i} (X Y : multiplicative_semigroup@{i}) :=
{ multiplicative_semigroup_morphism_fun :> func X Y
; #[canonical=no] multiplicative_semigroup_morphism_prop :> MultiplicativeSemiGroup_Morphism multiplicative_semigroup_morphism_fun
}.
Global Hint Extern 2 (StripCoercions (multiplicative_semigroup_morphism_fun ?f)) => strip_coercions_chain f : strip_coercions.
Canonical Structure multiplicative_semigroup_morphism@{i} (X Y : multiplicative_semigroup@{i}) := projected_set (@multiplicative_semigroup_morphism_fun X Y).
Global Hint Extern 4 (MultiplicativeSemiGroup_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Definition make_multiplicative_semigroup_morphism : ∀ {X Y : multiplicative_semigroup} (f:X ⇾ Y) `{!MultiplicativeSemiGroup_Morphism f}, multiplicative_semigroup_morphism X Y := @Build_multiplicative_semigroup_morphism_t.
Arguments make_multiplicative_semigroup_morphism {X Y} f {_}.

Canonical Structure multiplicative_semigroup_cat_t := Build_cat_t multiplicative_semigroup multiplicative_semigroup_morphism.


(** Commutative SemiGroups *)

Record commutative_semigroup :=
  { commutative_semigroup_car :> set
  ; #[canonical=no] commutative_semigroup_op :> has_sg_op commutative_semigroup_car
  ; #[canonical=no] commutative_semigroup_prop :> CommutativeSemiGroup commutative_semigroup_car
  }.
Global Hint Extern 2 (StripCoercions (commutative_semigroup_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (CommutativeSemiGroup ?X) => exact_strip_coercions X : typeclass_instances.

Canonical Structure commutative_semigroup_as_sg (G:commutative_semigroup) := make_semigroup G.
Coercion commutative_semigroup_as_sg : commutative_semigroup >-> semigroup.
Global Hint Extern 2 (StripCoercions (commutative_semigroup_as_sg ?X)) => strip_coercions_chain X : strip_coercions.

Definition commutative_semigroup_morphism@{i} (X Y : commutative_semigroup@{i}) := semigroup_morphism X Y.

Canonical Structure commutative_semigroup_cat_t := Build_cat_t commutative_semigroup commutative_semigroup_morphism.


(** Monoids *)

Record monoid :=
  { monoid_car :> set
  ; #[canonical=no] monoid_op :> has_sg_op monoid_car
  ; #[canonical=no] monoid_u  :> has_mon_unit monoid_car
  ; #[canonical=no] monoid_prop :> Monoid monoid_car
  }.
Global Hint Extern 2 (StripCoercions (monoid_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (Monoid ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_monoid : ∀ (M:set) {o:SgOp M} {u:MonUnit M} {H:Monoid M}, monoid := @Build_monoid.
Arguments make_monoid M {_ _ _}.

Record monoid_morphism_t@{i} (X Y : monoid@{i}) :=
{ monoid_morphism_fun  :> func X Y
; #[canonical=no] monoid_morphism_prop :> Monoid_Morphism monoid_morphism_fun
}.
Global Hint Extern 2 (StripCoercions (monoid_morphism_fun ?f)) => strip_coercions_chain f : strip_coercions.
Canonical Structure monoid_morphism@{i} (X Y : monoid@{i}) := projected_set (@monoid_morphism_fun X Y).
Global Hint Extern 4 (Monoid_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Definition make_monoid_morphism : ∀ {X Y : monoid} (f:X ⇾ Y) `{!Monoid_Morphism f}, monoid_morphism X Y := @Build_monoid_morphism_t.
Arguments make_monoid_morphism {X Y} f {_}.

Canonical Structure monoid_cat_t := Build_cat_t monoid monoid_morphism.


(** Multiplicative Monoids *)

Record multiplicative_monoid :=
  { multiplicative_monoid_car :> set
  ; #[canonical=no] multiplicative_monoid_op :> has_mult multiplicative_monoid_car
  ; #[canonical=no] multiplicative_monoid_u  :> has_one multiplicative_monoid_car
  ; #[canonical=no] multiplicative_monoid_prop :> MultiplicativeMonoid multiplicative_monoid_car
  }.
Global Hint Extern 2 (StripCoercions (multiplicative_monoid_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (MultiplicativeMonoid ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_multiplicative_monoid : ∀ (M:set) {o:Mult M} {u:One M} {H:MultiplicativeMonoid M}, multiplicative_monoid := @Build_multiplicative_monoid.
Arguments make_multiplicative_monoid M {_ _ _}.

Record multiplicative_monoid_morphism_t@{i} (X Y : multiplicative_monoid@{i}) :=
{ multiplicative_monoid_morphism_fun  :> func X Y
; #[canonical=no] multiplicative_monoid_morphism_prop :> MultiplicativeMonoid_Morphism multiplicative_monoid_morphism_fun
}.
Global Hint Extern 2 (StripCoercions (multiplicative_monoid_morphism_fun ?f)) => strip_coercions_chain f : strip_coercions.
Canonical Structure multiplicative_monoid_morphism@{i} (X Y : multiplicative_monoid@{i}) := projected_set (@multiplicative_monoid_morphism_fun X Y).
Global Hint Extern 4 (MultiplicativeMonoid_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Definition make_multiplicative_monoid_morphism : ∀ {X Y : multiplicative_monoid} (f:X ⇾ Y) `{!MultiplicativeMonoid_Morphism f}, multiplicative_monoid_morphism X Y := @Build_multiplicative_monoid_morphism_t.
Arguments make_multiplicative_monoid_morphism {X Y} f {_}.

Canonical Structure multiplicative_monoid_cat_t := Build_cat_t multiplicative_monoid multiplicative_monoid_morphism.


(** Strong Operation Monoids *)

Record strong_op_monoid :=
  { strong_op_monoid_car :> set
  ; #[canonical=no] strong_op_monoid_op :> has_sg_op strong_op_monoid_car
  ; #[canonical=no] strong_op_monoid_u  :> has_mon_unit strong_op_monoid_car
  ; #[canonical=no] strong_op_monoid_prop :> StrongOpMonoid strong_op_monoid_car
  }.
Global Hint Extern 2 (StripCoercions (strong_op_monoid_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (StrongOpMonoid ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (StrongOpSemiGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_strong_op_monoid : ∀ (M:set) {o:SgOp M} {u:MonUnit M} {H:StrongOpMonoid M}, strong_op_monoid := @Build_strong_op_monoid.
Arguments make_strong_op_monoid M {_ _ _}.

Canonical Structure strong_op_monoid_as_monoid (M:strong_op_monoid) := make_monoid M.
Coercion strong_op_monoid_as_monoid : strong_op_monoid >-> monoid.
Global Hint Extern 2 (StripCoercions (strong_op_monoid_as_monoid ?X)) => strip_coercions_chain X : strip_coercions.

Definition strong_op_monoid_morphism@{i} (X Y : strong_op_monoid@{i}) := monoid_morphism X Y.

Canonical Structure strong_op_monoid_cat_t := Build_cat_t strong_op_monoid strong_op_monoid_morphism.


(** Commutative Monoids *)

Record commutative_monoid :=
  { commutative_monoid_car :> set
  ; #[canonical=no] commutative_monoid_op :> has_sg_op commutative_monoid_car
  ; #[canonical=no] commutative_monoid_u  :> has_mon_unit commutative_monoid_car
  ; #[canonical=no] commutative_monoid_prop :> CommutativeMonoid commutative_monoid_car
  }.
Global Hint Extern 2 (StripCoercions (commutative_monoid_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (CommutativeMonoid ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_commutative_monoid : ∀ (M:set) {o:SgOp M} {u:MonUnit M} {H:CommutativeMonoid M}, commutative_monoid := @Build_commutative_monoid.
Arguments make_commutative_monoid M {_ _ _}.

Canonical Structure commutative_monoid_as_monoid (M:commutative_monoid) := make_monoid M.
Coercion commutative_monoid_as_monoid : commutative_monoid >-> monoid.
Global Hint Extern 2 (StripCoercions (commutative_monoid_as_monoid ?X)) => strip_coercions_chain X : strip_coercions.

Definition commutative_monoid_morphism@{i} (X Y : commutative_monoid@{i}) := monoid_morphism X Y.

Canonical Structure commutative_monoid_cat_t := Build_cat_t commutative_monoid commutative_monoid_morphism.


(** Additive Monoids *)

Record additive_non_com_monoid :=
  { additive_non_com_monoid_car :> set
  ; #[canonical=no] additive_non_com_monoid_op :> has_plus additive_non_com_monoid_car
  ; #[canonical=no] additive_non_com_monoid_u  :> has_zero additive_non_com_monoid_car
  ; #[canonical=no] additive_non_com_monoid_prop :> AdditiveNonComMonoid additive_non_com_monoid_car
  }.
Global Hint Extern 2 (StripCoercions (additive_non_com_monoid_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (AdditiveNonComMonoid ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (AdditiveNonComSemiGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_additive_non_com_monoid : ∀ (M:set) {o:Plus M} {u:Zero M} {H:AdditiveNonComMonoid M}, additive_non_com_monoid := @Build_additive_non_com_monoid.
Arguments make_additive_non_com_monoid M {_ _ _}.

Record additive_non_com_monoid_morphism_t@{i} (X Y : additive_non_com_monoid@{i}) :=
{ additive_non_com_monoid_morphism_fun  :> func X Y
; #[canonical=no] additive_non_com_monoid_morphism_prop :> AdditiveMonoid_Morphism additive_non_com_monoid_morphism_fun
}.
Global Hint Extern 2 (StripCoercions (additive_non_com_monoid_morphism_fun ?f)) => strip_coercions_chain f : strip_coercions.
Canonical Structure additive_non_com_monoid_morphism@{i} (X Y : additive_non_com_monoid@{i}) := projected_set (@additive_non_com_monoid_morphism_fun X Y).
Global Hint Extern 4 (AdditiveSemiGroup_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Global Hint Extern 4 (AdditiveMonoid_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Definition make_additive_non_com_monoid_morphism : ∀ {X Y : additive_non_com_monoid} (f:X ⇾ Y) `{!AdditiveMonoid_Morphism f}, additive_non_com_monoid_morphism X Y := @Build_additive_non_com_monoid_morphism_t.
Arguments make_additive_non_com_monoid_morphism {X Y} f {_}.

Canonical Structure additive_non_com_monoid_cat_t := Build_cat_t additive_non_com_monoid additive_non_com_monoid_morphism.


Record additive_monoid :=
  { additive_monoid_car :> set
  ; #[canonical=no] additive_monoid_op :> has_plus additive_monoid_car
  ; #[canonical=no] additive_monoid_u  :> has_zero additive_monoid_car
  ; #[canonical=no] additive_monoid_prop :> AdditiveMonoid additive_monoid_car
  }.
Global Hint Extern 2 (StripCoercions (additive_monoid_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (AdditiveMonoid ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (AdditiveSemiGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_additive_monoid : ∀ (M:set) {o:Plus M} {u:Zero M} {H:AdditiveMonoid M}, additive_monoid := @Build_additive_monoid.
Arguments make_additive_monoid M {_ _ _}.

Canonical Structure additive_monoid_as_add_nc_monoid (M:additive_monoid) : additive_non_com_monoid := make_additive_non_com_monoid M.
Coercion additive_monoid_as_add_nc_monoid : additive_monoid >-> additive_non_com_monoid.
Global Hint Extern 2 (StripCoercions (additive_monoid_as_add_nc_monoid ?X)) => strip_coercions_chain X : strip_coercions.

Definition additive_monoid_morphism@{i} (X Y : additive_monoid@{i}) := additive_non_com_monoid_morphism X Y.
Definition make_additive_monoid_morphism : ∀ {X Y : additive_monoid} (f:X ⇾ Y) `{!AdditiveMonoid_Morphism f}, additive_monoid_morphism X Y := @Build_additive_non_com_monoid_morphism_t.

Canonical Structure additive_monoid_cat_t := Build_cat_t additive_monoid additive_monoid_morphism.


(** Groups *)

Record group :=
  { group_car :> set
  ; #[canonical=no] group_op :> has_sg_op group_car
  ; #[canonical=no] group_u  :> has_mon_unit group_car
  ; #[canonical=no] group_i  :> has_inv group_car
  ; #[canonical=no] group_prop :> Group group_car
  }.
Global Hint Extern 2 (StripCoercions (group_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (Group ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_group : ∀ (G:set) {o:SgOp G} {u:MonUnit G} {i:Inv G} {H:Group G}, group := @Build_group.
Arguments make_group G {_ _ _ _}.

Canonical Structure group_as_monoid (G:group) := make_monoid G.
Coercion group_as_monoid : group >-> monoid.
Global Hint Extern 2 (StripCoercions (group_as_monoid ?X)) => strip_coercions_chain X : strip_coercions.

Definition group_morphism@{i} (X Y : group@{i}) := monoid_morphism X Y.

Canonical Structure group_cat_t := Build_cat_t group group_morphism.

(** Abelian Groups *)

Record ab_group :=
  { ab_group_car :> set
  ; #[canonical=no] ab_group_op :> has_sg_op ab_group_car
  ; #[canonical=no] ab_group_u  :> has_mon_unit ab_group_car
  ; #[canonical=no] ab_group_i  :> has_inv ab_group_car
  ; #[canonical=no] ab_group_prop :> AbGroup ab_group_car
  }.
Global Hint Extern 2 (StripCoercions (ab_group_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (AbGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_ab_group : ∀ (G:set) {o:SgOp G} {u:MonUnit G} {i:Inv G} {H:AbGroup G}, ab_group := @Build_ab_group.
Arguments make_ab_group G {_ _ _ _}.

Canonical Structure ab_group_as_monoid (G:ab_group) := make_monoid G.
Canonical Structure ab_group_as_group  (G:ab_group) := make_group G.
Coercion ab_group_as_monoid : ab_group >-> monoid.
Coercion ab_group_as_group : ab_group >-> group.
Global Hint Extern 2 (StripCoercions (ab_group_as_monoid ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 2 (StripCoercions (ab_group_as_group ?X)) => strip_coercions_chain X : strip_coercions.

Definition ab_group_morphism@{i} (X Y : ab_group@{i}) := monoid_morphism X Y.

Canonical Structure ab_group_cat_t := Build_cat_t ab_group ab_group_morphism.

(** Additive Groups *)

Record additive_non_com_group :=
  { additive_non_com_group_car :> set
  ; #[canonical=no] additive_non_com_group_op :> has_plus additive_non_com_group_car
  ; #[canonical=no] additive_non_com_group_u  :> has_zero additive_non_com_group_car
  ; #[canonical=no] additive_non_com_group_i  :> has_negate additive_non_com_group_car
  ; #[canonical=no] additive_non_com_group_prop :> AdditiveNonComGroup additive_non_com_group_car
  }.
Global Hint Extern 2 (StripCoercions (additive_non_com_group_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (AdditiveNonComGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_additive_non_com_group : ∀ (G:set) {o:Plus G} {u:Zero G} {i:Negate G} {H:AdditiveNonComGroup G}, additive_non_com_group := @Build_additive_non_com_group.
Arguments make_additive_non_com_group G {_ _ _ _}.

Canonical Structure additive_non_com_group_as_add_nc_mon (G:additive_non_com_group) : additive_non_com_monoid := make_additive_non_com_monoid G.
Coercion additive_non_com_group_as_add_nc_mon : additive_non_com_group >-> additive_non_com_monoid.
Global Hint Extern 2 (StripCoercions (additive_non_com_group_as_add_nc_mon ?X)) => strip_coercions_chain X : strip_coercions.

Definition additive_non_com_group_morphism@{i} (X Y : additive_non_com_group@{i}) := additive_non_com_monoid_morphism X Y.

Canonical Structure additive_non_com_group_cat_t := Build_cat_t additive_non_com_group additive_non_com_group_morphism.


Record additive_group :=
  { additive_group_car :> set
  ; #[canonical=no] additive_group_op :> has_plus additive_group_car
  ; #[canonical=no] additive_group_u  :> has_zero additive_group_car
  ; #[canonical=no] additive_group_i  :> has_negate additive_group_car
  ; #[canonical=no] additive_group_prop :> AdditiveGroup additive_group_car
  }.
Global Hint Extern 2 (StripCoercions (additive_group_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (AdditiveGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_additive_group : ∀ (G:set) {o:Plus G} {u:Zero G} {i:Negate G} {H:AdditiveGroup G}, additive_group := @Build_additive_group.
Arguments make_additive_group G {_ _ _ _}.

Canonical Structure additive_group_as_add_monoid (G:additive_group) : additive_monoid := make_additive_monoid G.
Coercion additive_group_as_add_monoid : additive_group >-> additive_monoid.
Global Hint Extern 2 (StripCoercions (additive_group_as_add_monoid ?X)) => strip_coercions_chain X : strip_coercions.

Canonical Structure additive_group_as_add_nc_group (G:additive_group) : additive_non_com_group := make_additive_non_com_group G.
Coercion additive_group_as_add_nc_group : additive_group >-> additive_non_com_group.
Global Hint Extern 2 (StripCoercions (additive_group_as_add_nc_group ?X)) => strip_coercions_chain X : strip_coercions.

Definition additive_group_morphism@{i} (X Y : additive_group@{i}) := additive_non_com_monoid_morphism X Y.

Canonical Structure additive_group_cat_t := Build_cat_t additive_group additive_group_morphism.


(** Near-rigs *)

Record near_rig :=
  { near_rig_car :> set
  ; #[canonical=no] near_rig_p :> has_plus near_rig_car
  ; #[canonical=no] near_rig_z :> has_zero near_rig_car
  ; #[canonical=no] near_rig_m :> has_mult near_rig_car
  ; #[canonical=no] near_rig_o :> has_one  near_rig_car
  ; #[canonical=no] near_rig_prop :> NearRig near_rig_car
  }.
Global Hint Extern 2 (StripCoercions (near_rig_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (NearRig ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (NearRg ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (MultiplicativeMonoid ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (MultiplicativeSemiGroup ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_near_rig : ∀ (R:set) {p:Plus R} {z:Zero R} {m:Mult R} {o:One R} {H:NearRig R}, near_rig := @Build_near_rig.
Arguments make_near_rig R {_ _ _ _ _}.

Record near_rig_morphism_t@{i} (X Y : near_rig@{i}) :=
{ near_rig_morphism_fun  :> func X Y
; #[canonical=no] near_rig_morphism_prop :> Rig_Morphism near_rig_morphism_fun
}.
Global Hint Extern 2 (StripCoercions (near_rig_morphism_fun ?f)) => strip_coercions_chain f : strip_coercions.
Definition near_rig_morphism@{i} (X Y : near_rig@{i}) := projected_set (@near_rig_morphism_fun X Y).
Global Hint Extern 4 (Rig_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Global Hint Extern 4 (Rg_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Global Hint Extern 4 (MultiplicativeMonoid_Morphism ?f) => exact_strip_coercions f : typeclass_instances.
Global Hint Extern 4 (MultiplicativeSemiGroup_Morphism ?f) => exact_strip_coercions f : typeclass_instances.

Definition make_near_rig_morphism : ∀ {X Y : near_rig} (f:X ⇾ Y) `{!Rig_Morphism f}, near_rig_morphism X Y := @Build_near_rig_morphism_t.
Arguments make_near_rig_morphism {X Y} f {_}.

Canonical Structure near_rig_cat_t := Build_cat_t near_rig near_rig_morphism.



(** Rigs *)

Record rig :=
  { rig_car :> set
  ; #[canonical=no] rig_p :> has_plus rig_car
  ; #[canonical=no] rig_z :> has_zero rig_car
  ; #[canonical=no] rig_m :> has_mult rig_car
  ; #[canonical=no] rig_o :> has_one  rig_car
  ; #[canonical=no] rig_prop :> Rig rig_car
  }.
Global Hint Extern 2 (StripCoercions (rig_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (Rig ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (Rg ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (LeftNearRig ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (LeftNearRg ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_rig : ∀ (R:set) {p:Plus R} {z:Zero R} {m:Mult R} {o:One R} {H:Rig R}, rig := @Build_rig.
Arguments make_rig R {_ _ _ _ _}.

Canonical Structure rig_as_near_rig (R:rig) := make_near_rig R.
Coercion rig_as_near_rig : rig >-> near_rig.
Global Hint Extern 2 (StripCoercions (rig_as_near_rig ?X)) => strip_coercions_chain X : strip_coercions.

Definition rig_morphism@{i} (X Y : rig@{i}) := near_rig_morphism X Y.

Canonical Structure rig_cat_t := Build_cat_t rig rig_morphism.


(** Strong Rigs *)

Record strong_rig :=
  { strong_rig_rig :> rig
  ; #[canonical=no] strong_rig_prop :> StrongSet strong_rig_rig
  }.
Global Hint Extern 2 (StripCoercions (strong_rig_rig ?X)) => strip_coercions_chain X : strip_coercions.

Definition make_strong_rig (R:set) {p:Plus R} {z:Zero R} {m:Mult R} {o:One R} {H:Rig R} {H2:StrongSet R} : strong_rig.
Proof. unshelve esplit. exact (make_rig R). exact H2. Defined.
Arguments make_strong_rig R {_ _ _ _ _ _}.

Definition strong_rig_morphism@{i} (X Y : strong_rig@{i}) := near_rig_morphism X Y.

Canonical Structure strong_rig_cat_t := Build_cat_t strong_rig strong_rig_morphism.


(** Commutative Rigs *)

Record commutative_rig :=
  { commutative_rig_car :> set
  ; #[canonical=no] commutative_rig_p :> has_plus commutative_rig_car
  ; #[canonical=no] commutative_rig_z :> has_zero commutative_rig_car
  ; #[canonical=no] commutative_rig_m :> has_mult commutative_rig_car
  ; #[canonical=no] commutative_rig_o :> has_one  commutative_rig_car
  ; #[canonical=no] commutative_rig_prop :> CommutativeRig commutative_rig_car
  }.
Global Hint Extern 2 (StripCoercions (commutative_rig_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (CommutativeRig ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (MultiplicativeComMonoid ?X) => exact_strip_coercions X : typeclass_instances.

Definition make_commutative_rig : ∀ (R:set) {p:Plus R} {z:Zero R} {m:Mult R} {o:One R} {H:CommutativeRig R}, commutative_rig := @Build_commutative_rig.
Arguments make_commutative_rig R {_ _ _ _ _}.

Canonical Structure commutative_rig_as_rig (R:commutative_rig) := make_rig R.
Coercion commutative_rig_as_rig : commutative_rig >-> rig.
Global Hint Extern 2 (StripCoercions (commutative_rig_as_rig ?X)) => strip_coercions_chain X : strip_coercions.

Definition commutative_rig_morphism@{i} (X Y : commutative_rig@{i}) := near_rig_morphism X Y.

Canonical Structure commutative_rig_cat_t := Build_cat_t commutative_rig commutative_rig_morphism.


(** Near-rings *)

Record near_ring :=
  { near_ring_car :> set
  ; #[canonical=no] near_ring_p :> has_plus   near_ring_car
  ; #[canonical=no] near_ring_z :> has_zero   near_ring_car
  ; #[canonical=no] near_ring_m :> has_mult   near_ring_car
  ; #[canonical=no] near_ring_o :> has_one    near_ring_car
  ; #[canonical=no] near_ring_n :> has_negate near_ring_car
  ; #[canonical=no] near_ring_prop :> NearRing near_ring_car
  }.
Global Hint Extern 2 (StripCoercions (near_ring_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (NearRing ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (NearRng ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_near_ring : ∀ (R:set) {p:Plus R} {z:Zero R} {m:Mult R} {o:One R} {n:Negate R} {H:NearRing R}, near_ring := @Build_near_ring.
Arguments make_near_ring R {_ _ _ _ _ _}.

Canonical Structure near_ring_as_near_rig (R:near_ring) := make_near_rig R.
Coercion near_ring_as_near_rig : near_ring >-> near_rig.
Global Hint Extern 2 (StripCoercions (near_ring_as_near_rig ?X)) => strip_coercions_chain X : strip_coercions.

Definition near_ring_morphism@{i} (X Y : near_ring@{i}) := near_rig_morphism X Y.

Canonical Structure near_ring_cat_t := Build_cat_t near_ring near_ring_morphism.


(** Rings *)

Record ring :=
  { ring_car :> set
  ; #[canonical=no] ring_p :> has_plus   ring_car
  ; #[canonical=no] ring_z :> has_zero   ring_car
  ; #[canonical=no] ring_m :> has_mult   ring_car
  ; #[canonical=no] ring_o :> has_one    ring_car
  ; #[canonical=no] ring_n :> has_negate ring_car
  ; #[canonical=no] ring_prop :> Ring ring_car
  }.
Global Hint Extern 2 (StripCoercions (ring_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (Ring ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (Rng ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_ring : ∀ (R:set) {p:Plus R} {z:Zero R} {m:Mult R} {o:One R} {n:Negate R} {H:Ring R}, ring := @Build_ring.
Arguments make_ring R {_ _ _ _ _ _}.

Canonical Structure ring_as_rig (R:ring) := make_rig R.
Coercion ring_as_rig : ring >-> rig.
Global Hint Extern 2 (StripCoercions (ring_as_rig ?X)) => strip_coercions_chain X : strip_coercions.

Canonical Structure ring_as_near_ring (R:ring) := make_near_ring R.
Coercion ring_as_near_ring : ring >-> near_ring.
Global Hint Extern 2 (StripCoercions (ring_as_near_ring ?X)) => strip_coercions_chain X : strip_coercions.

Definition ring_morphism@{i} (X Y : ring@{i}) := near_rig_morphism X Y.

Canonical Structure ring_cat_t := Build_cat_t ring ring_morphism.


(** Commutative Rings *)

Record commutative_ring :=
  { commutative_ring_car :> set
  ; #[canonical=no] commutative_ring_p :> has_plus   commutative_ring_car
  ; #[canonical=no] commutative_ring_z :> has_zero   commutative_ring_car
  ; #[canonical=no] commutative_ring_m :> has_mult   commutative_ring_car
  ; #[canonical=no] commutative_ring_o :> has_one    commutative_ring_car
  ; #[canonical=no] commutative_ring_n :> has_negate commutative_ring_car
  ; #[canonical=no] commutative_ring_prop :> CommutativeRing commutative_ring_car
  }.
Global Hint Extern 2 (StripCoercions (commutative_ring_car ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (CommutativeRing ?X) => exact_strip_coercions X : typeclass_instances.
Definition make_commutative_ring : ∀ (R:set) {p:Plus R} {z:Zero R} {m:Mult R} {o:One R} {n:Negate R} {H:CommutativeRing R}, commutative_ring := @Build_commutative_ring.
Arguments make_commutative_ring R {_ _ _ _ _ _}.

Canonical Structure commutative_ring_as_ring (R:commutative_ring) := make_ring R.
Coercion commutative_ring_as_ring : commutative_ring >-> ring.
Global Hint Extern 2 (StripCoercions (commutative_ring_as_ring ?X)) => strip_coercions_chain X : strip_coercions.

Canonical Structure commutative_ring_as_commutative_rig (R:commutative_ring) := make_commutative_rig R.
Coercion commutative_ring_as_commutative_rig : commutative_ring >-> commutative_rig.
Global Hint Extern 2 (StripCoercions (commutative_ring_as_commutative_rig ?X)) => strip_coercions_chain X : strip_coercions.

Definition commutative_ring_morphism@{i} (X Y : commutative_ring@{i}) := near_rig_morphism X Y.

Canonical Structure commutative_ring_cat_t := Build_cat_t commutative_ring commutative_ring_morphism.

