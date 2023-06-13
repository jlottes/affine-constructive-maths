Require Export interfaces.bundled_algebra theory.bundled_groups.
Require Import abstract_algebra interfaces.cat theory.projected_set theory.groups.
Require Export theory.rings.
Require Import theory.additive_groups.
Require Import rewrite easy.
Require Import strip_coercions.

Local Open Scope cat_scope.

(** Near rigs *)

Global Hint Extern 1 (IsProjectedSet (set_T (near_rig_morphism _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom near_rig_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure near_rig_id (X : near_rig) := make_near_rig_morphism (id_fun X).
Global Hint Extern 2 (Id near_rig_cat_t) => refine near_rig_id : typeclass_instances.

Local Notation make_compose_fun c := (@make_fun _ _ _ (projected_is_fun (tuncurry c) (∘) (λ _, reflexivity (=) _))).

Canonical Structure near_rig_morphism_compose_op {X Y Z : near_rig}
  (g : near_rig_morphism Y Z) (f: near_rig_morphism X Y) : (near_rig_morphism X Z)
:= make_near_rig_morphism (g ∘ f).
Definition near_rig_morphism_compose {X Y Z : near_rig} := make_compose_fun (@near_rig_morphism_compose_op X Y Z).
Global Hint Extern 2 (Compose near_rig_cat_t) => refine @near_rig_morphism_compose : typeclass_instances.

Local Instance near_rig_is_cat : IsCat near_rig_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐍𝐞𝐚𝐫𝐑𝐢𝐠 := Build_cat near_rig_cat_t.

Canonical Structure near_rig_as_add_nc_mon (R:near_rig) : additive_non_com_monoid := make_additive_non_com_monoid R.
Coercion near_rig_as_add_nc_mon : near_rig >-> additive_non_com_monoid.
Global Hint Extern 2 (StripCoercions (near_rig_as_add_nc_mon ?X)) => strip_coercions_chain X : strip_coercions.

Canonical Structure near_rig_as_mul_mon (R:near_rig) : multiplicative_monoid := make_multiplicative_monoid R.
Coercion near_rig_as_mul_mon : near_rig >-> multiplicative_monoid.
Global Hint Extern 2 (StripCoercions (near_rig_as_mul_mon ?X)) => strip_coercions_chain X : strip_coercions.

Canonical Structure near_rig_morphism_as_addmon_mor `(f:near_rig_morphism_t X Y)
  : additive_non_com_monoid_morphism_t X Y := make_additive_non_com_monoid_morphism f.
Coercion near_rig_morphism_as_addmon_mor : near_rig_morphism_t >-> additive_non_com_monoid_morphism_t.
Global Hint Extern 2 (StripCoercions (near_rig_morphism_as_addmon_mor ?f)) => strip_coercions_chain f : strip_coercions.

Canonical Structure near_rig_morphism_as_mulmon_mor `(f:near_rig_morphism_t X Y)
  : multiplicative_monoid_morphism_t X Y := make_multiplicative_monoid_morphism f.
Coercion near_rig_morphism_as_mulmon_mor : near_rig_morphism_t >-> multiplicative_monoid_morphism_t.
Global Hint Extern 2 (StripCoercions (near_rig_morphism_as_mulmon_mor ?f)) => strip_coercions_chain f : strip_coercions.


(** Rigs *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom rig_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id rig_cat_t) => refine near_rig_id : typeclass_instances.
Global Hint Extern 2 (Compose rig_cat_t) => refine @near_rig_morphism_compose : typeclass_instances.

Local Instance rig_is_cat : IsCat rig_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐑𝐢𝐠 := Build_cat rig_cat_t.

Canonical Structure rig_as_add_mon (R:rig) : additive_monoid := make_additive_monoid R.
Coercion rig_as_add_mon : rig >-> additive_monoid.
Global Hint Extern 2 (StripCoercions (rig_as_add_mon ?X)) => strip_coercions_chain X : strip_coercions.

(** Commutative rigs *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom commutative_rig_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id commutative_rig_cat_t) => refine near_rig_id : typeclass_instances.
Global Hint Extern 2 (Compose commutative_rig_cat_t) => refine @near_rig_morphism_compose : typeclass_instances.
Local Instance commutative_rig_is_cat : IsCat commutative_rig_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐂𝐑𝐢𝐠 := Build_cat commutative_rig_cat_t.

(** Near-ring *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom near_ring_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id near_ring_cat_t) => refine near_rig_id : typeclass_instances.
Global Hint Extern 2 (Compose near_ring_cat_t) => refine @near_rig_morphism_compose : typeclass_instances.
Local Instance near_ring_is_cat : IsCat near_ring_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐍𝐞𝐚𝐫𝐑𝐢𝐧𝐠 := Build_cat near_ring_cat_t.

Canonical Structure near_ring_as_add_nc_grp (R:near_ring) : additive_non_com_group := make_additive_non_com_group R.
Coercion near_ring_as_add_nc_grp : near_ring >-> additive_non_com_group.
Global Hint Extern 2 (StripCoercions (near_ring_as_add_nc_grp ?X)) => strip_coercions_chain X : strip_coercions.

(** Ring *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom ring_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id ring_cat_t) => refine near_rig_id : typeclass_instances.
Global Hint Extern 2 (Compose ring_cat_t) => refine @near_rig_morphism_compose : typeclass_instances.
Local Instance ring_is_cat : IsCat ring_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐑𝐢𝐧𝐠 := Build_cat ring_cat_t.

Canonical Structure ring_as_add_group (R:ring) : additive_group := make_additive_group R.
Coercion ring_as_add_group : ring >-> additive_group.
Global Hint Extern 2 (StripCoercions (ring_as_add_group ?X)) => strip_coercions_chain X : strip_coercions.


(** Commutative Ring *)

Global Hint Extern 1 (IsProjectedSet (set_T (@cat_hom commutative_ring_cat_t _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 2 (Id commutative_ring_cat_t) => refine near_rig_id : typeclass_instances.
Global Hint Extern 2 (Compose commutative_ring_cat_t) => refine @near_rig_morphism_compose : typeclass_instances.
Local Instance commutative_ring_is_cat : IsCat commutative_ring_cat_t.  Proof. now split. Qed.
Canonical Structure 𝐂𝐑𝐢𝐧𝐠 := Build_cat commutative_ring_cat_t.
