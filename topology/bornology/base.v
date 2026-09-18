Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.bornology interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import reflection_pair.base.
Require Import easy rewrite replc simplify tactics.misc.

Local Abbreviation id := (id_fun _).

Coercion bornology_sub_lattice `{@BornologicalSpace X 𝒜} : SubLattice 𝒜.
Proof. exact ideal_sub_lattice. Qed.

Coercion bornology_join_sub_bsl `{@BornologicalSpace X 𝒜} : JoinSubBoundedSemiLattice 𝒜.
Proof. exact ideal_bounded_join_sub_sl. Qed.

#[global] Hint Extern 4 (SubLattice ?𝒜) => match type of 𝒜 with Bornology _ => simple notypeclasses refine (@bornology_sub_lattice _ 𝒜 _) end : typeclass_instances.
#[global] Hint Extern 4 (JoinSubSemiLattice ?𝒜) => match type of 𝒜 with Bornology _ => simple notypeclasses refine (@bornology_sub_lattice _ 𝒜 _) end : typeclass_instances.
#[global] Hint Extern 4 (MeetSubSemiLattice ?𝒜) => match type of 𝒜 with Bornology _ => simple notypeclasses refine (@bornology_sub_lattice _ 𝒜 _) end : typeclass_instances.

#[global] Hint Extern 4 (JoinSubBoundedSemiLattice ?𝒜) => match type of 𝒜 with Bornology _ => simple notypeclasses refine (@bornology_join_sub_bsl _ 𝒜 _) end : typeclass_instances.

(** Morphism classes respect function equality. *)

Import of_course_set_notation.
Import image_notation.

Lemma Bornological_proper_impl@{u} {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (Bornological f, Bornological g).
Proof. intros E [SX SY B]; split; try exact _.
  intros U. rew <-E. exact (B U).
Qed.
Canonical Structure Bornological_fun {X Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@Bornological X Y 𝒜 ℬ) Bornological_proper_impl.

Lemma BornologyReflecting_proper_impl@{u} {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (BornologyReflecting f, BornologyReflecting g).
Proof. intros E [SX SY R]; split; try exact _.
  intros U. rew <-E. exact (R U).
Qed.
Canonical Structure BornologyReflecting_fun {X Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@BornologyReflecting X Y 𝒜 ℬ) BornologyReflecting_proper_impl.

Lemma BornologyInitial_proper_impl@{u} {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (BornologyInitial f, BornologyInitial g).
Proof. intros E [BB BR]; split; now rew <-E. Qed.
Canonical Structure BornologyInitial_fun {X Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@BornologyInitial X Y 𝒜 ℬ) BornologyInitial_proper_impl.

Lemma BornologyEmbedding_proper_impl@{u} {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (BornologyEmbedding f, BornologyEmbedding g).
Proof. intros E ?; split; now rew <-E. Qed.
Canonical Structure BornologyEmbedding_fun {X Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@BornologyEmbedding X Y 𝒜 ℬ) BornologyEmbedding_proper_impl.

(** Category structure: identity and composition. *)

Lemma id_bornology_initial `{@BornologicalSpace X 𝒜} : BornologyInitial (𝒜:=𝒜) (ℬ:=𝒜) (id_fun X).
Proof. do 2 (split; try exact _).
+ intros B. now rew (image_id_alt _).
+ intros B. now rew (preimage_id_alt _).
Qed.
#[global] Hint Extern 2 (BornologyInitial (id_fun _)) => simple notypeclasses refine id_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (Bornological (id_fun _)) => simple notypeclasses refine id_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (id_fun _)) => simple notypeclasses refine id_bornology_initial : typeclass_instances.

Local Instance born_image_mapsto@{u} `{@Bornological@{u} X Y 𝒜 ℬ f} : WeakMapsTo f⁎ 𝒜 ℬ.
Proof. intros A ?. exact (bornological f (to_subset A)). Qed.

Local Instance born_preimage_mapsto@{u} `{@BornologyReflecting@{u} X Y 𝒜 ℬ f} : WeakMapsTo f* ℬ 𝒜.
Proof. intros B ?. exact (bornology_reflecting f (to_subset B)). Qed.

Lemma bornological_alt@{u} `{@Bornological@{u} X Y 𝒜 ℬ f} (A:𝒫 X) `{A ∊ 𝒜} : f⁎ A ∊ ℬ.
Proof. now apply born_image_mapsto. Qed.
Arguments bornological_alt {_ _ _ _} f {_} A {_}.

Lemma bornological_reflecting_alt@{u} `{@BornologyReflecting@{u} X Y 𝒜 ℬ f} (B:𝒫 Y) `{B ∊ ℬ} : f* B ∊ 𝒜.
Proof. now apply born_preimage_mapsto. Qed.
Arguments bornological_reflecting_alt {_ _ _ _} f {_} B {_}.

Definition born_image@{u}    `{@Bornological@{u}        X Y 𝒜 ℬ f} := restrict f⁎ 𝒜 ℬ.
Definition born_preimage@{u} `{@BornologyReflecting@{u} X Y 𝒜 ℬ f} := restrict f* ℬ 𝒜.
Arguments born_image    {_ _ _ _} f {_}.
Arguments born_preimage {_ _ _ _} f {_}.

Lemma compose_bornological@{u} `{@Bornological@{u} X Y 𝒜 ℬ f} `{@Bornological@{u} Y Z ℬ 𝒞 g}
  : Bornological (g ∘ f).
Proof. split; try exact _.
  intros A. rew (image_compose_alt _ _ _).
  apply (born_image g (born_image f A)).
Qed.
#[global] Hint Extern 2 (Bornological (_ ∘ _)) => simple notypeclasses refine compose_bornological : typeclass_instances.

Lemma compose_bornology_reflecting@{u} `{@BornologyReflecting@{u} X Y 𝒜 ℬ f} `{@BornologyReflecting@{u} Y Z ℬ 𝒞 g}
  : BornologyReflecting (g ∘ f).
Proof. split; try exact _. intros C. apply (born_preimage f (born_preimage g C)). Qed.
#[global] Hint Extern 2 (BornologyReflecting (_ ∘ _)) => simple notypeclasses refine compose_bornology_reflecting : typeclass_instances.

Lemma born_refl_factor@{u} {X Y Z:set@{u}}
  {𝒜:Bornology X} {ℬ:Bornology Y} {𝒞:Bornology Z} (f: X ⇾ Y) (g: Y ⇾ Z) `{!Bornological g}
  : BornologyReflecting (g ∘ f) → BornologyReflecting f.
Proof. intros Hgf. split; try exact _. intros B.
  rew (preimage_image_unit g B). change ( (g ∘ f)* (g⁎ B) ∊ 𝒜).
  pose proof bornological g B.
  exact (bornological_reflecting_alt (g ∘ f) _).
Qed.

Lemma bornological_factor@{u} {X Y Z:set@{u}}
  {𝒜:Bornology X} {ℬ:Bornology Y} {𝒞:Bornology Z} (f: X ⇾ Y) (g: Y ⇾ Z) `{!BornologyReflecting g}
  : Bornological (g ∘ f) → Bornological f.
Proof. intros Hgf. split; try exact _. intros A.
  rew (preimage_image_unit g (f⁎ A)), <-(image_compose_alt f g A).
  pose proof bornological (g ∘ f) A.
  exact (bornological_reflecting_alt g _).
Qed.

Lemma compose_bornology_initial@{u} `{@BornologyInitial@{u} X Y 𝒜 ℬ f} `{@BornologyInitial@{u} Y Z ℬ 𝒞 g}
  : BornologyInitial (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (BornologyInitial (_ ∘ _)) => simple notypeclasses refine compose_bornology_initial : typeclass_instances.

Lemma compose_bornology_emb@{u} `{@BornologyEmbedding@{u} X Y 𝒜 ℬ f} `{@BornologyEmbedding@{u} Y Z ℬ 𝒞 g}
  : BornologyEmbedding (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (BornologyEmbedding (_ ∘ _)) => simple notypeclasses refine compose_bornology_emb : typeclass_instances.

(** Abstract reflection pair instance *)

Inductive 𝐁𝐨𝐫𝐧 :=.
#[global] Hint Extern 0 (Fiber 𝐁𝐨𝐫𝐧) => exact Bornology : typeclass_instances.
#[global] Hint Extern 0 (ObjClass 𝐁𝐨𝐫𝐧) => exact @BornologicalSpace : typeclass_instances.
#[global] Hint Extern 0 (HomClass 𝐁𝐨𝐫𝐧) => exact @Bornological_fun : typeclass_instances.
#[global] Hint Extern 0 (RflClass 𝐁𝐨𝐫𝐧) => exact @BornologyReflecting_fun : typeclass_instances.
#[global] Hint Extern 0 (IniClass 𝐁𝐨𝐫𝐧) => exact @BornologyInitial_fun : typeclass_instances.
#[global] Hint Extern 0 (EmbClass 𝐁𝐨𝐫𝐧) => exact @BornologyEmbedding_fun : typeclass_instances.
#[global] Hint Extern 2 (Fib 𝐁𝐨𝐫𝐧 ?X) => change (Bornology X) : typeclass_instances.

Definition born_classes@{u} : ReflectionPairClasses@{u} 𝐁𝐨𝐫𝐧.  Proof. now esplit. Defined.
#[global] Hint Extern 2 (ReflectionPairClasses 𝐁𝐨𝐫𝐧) => exact born_classes : typeclass_instances.

Lemma born_construct: Construct 𝐁𝐨𝐫𝐧.
Proof. split.
+ now change (∀ `{@BornologicalSpace X 𝒜}, Bornological (id_fun X)).
+ now change (∀ `{@Bornological X Y 𝒜 ℬ f}, BornologicalSpace X).
+ now change (∀ `{@Bornological X Y 𝒜 ℬ f}, BornologicalSpace Y).
+ now change (∀ X Y Z 𝒜 ℬ 𝒞 f g, @Bornological X Y 𝒜 ℬ f → @Bornological Y Z ℬ 𝒞 g
                                → Bornological (g ∘ f)).
Qed.
#[global] Hint Extern 0 (Construct 𝐁𝐨𝐫𝐧) => exact born_construct : typeclass_instances.

Lemma born_rfl_construct: RflConstruct 𝐁𝐨𝐫𝐧.
Proof. split.
+ now change (∀ `{@BornologicalSpace X 𝒜}, BornologyReflecting (id_fun X)).
+ now change (∀ `{@BornologyReflecting X Y 𝒜 ℬ f}, BornologicalSpace X).
+ now change (∀ `{@BornologyReflecting X Y 𝒜 ℬ f}, BornologicalSpace Y).
+ now change (∀ X Y Z 𝒜 ℬ 𝒞 f g, @BornologyReflecting X Y 𝒜 ℬ f → @BornologyReflecting Y Z ℬ 𝒞 g
                                → BornologyReflecting (g ∘ f)).
Qed.
#[global] Hint Extern 0 (RflConstruct 𝐁𝐨𝐫𝐧) => exact born_rfl_construct : typeclass_instances.

Lemma born_ini_spec : IniClassSpec 𝐁𝐨𝐫𝐧.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (IniClassSpec 𝐁𝐨𝐫𝐧) => exact born_ini_spec : typeclass_instances.

Lemma born_emb_spec : EmbClassSpec 𝐁𝐨𝐫𝐧.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (EmbClassSpec 𝐁𝐨𝐫𝐧) => exact born_emb_spec : typeclass_instances.

Lemma born_rfl_pair : ReflectionPair 𝐁𝐨𝐫𝐧.
Proof. esplit; try exact _.
+ change (∀ X Y Z 𝒜 ℬ 𝒞 f g, @BornologyReflecting Y Z ℬ 𝒞 g → @Bornological X Z 𝒜 𝒞 (g ∘ f)
                            → @Bornological X Y 𝒜 ℬ f).
  intros. now apply (bornological_factor f g).
+ change (∀ X Y Z 𝒜 ℬ 𝒞 f g, @Bornological Y Z ℬ 𝒞 g → @BornologyReflecting X Z 𝒜 𝒞 (g ∘ f)
                            → @BornologyReflecting X Y 𝒜 ℬ f).
  intros. now apply (born_refl_factor f g).
Qed.
#[global] Hint Extern 0 (ReflectionPair 𝐁𝐨𝐫𝐧) => exact born_rfl_pair : typeclass_instances.


(** Inverses flip classes *)

Local Open Scope fun_inv_scope.
Lemma invert_bornological@{u} `{@Bornological@{u} X Y 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : BornologyReflecting f⁻¹.
Proof. exact (invert_hom (C:=𝐁𝐨𝐫𝐧) (f:=f)). Qed.
#[global] Hint Extern 4 (BornologyReflecting _⁻¹) => simple notypeclasses refine invert_bornological : typeclass_instances.

Lemma invert_bornology_reflecting@{u} `{@BornologyReflecting@{u} X Y 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : Bornological f⁻¹.
Proof. exact (invert_rfl (C:=𝐁𝐨𝐫𝐧) (f:=f)). Qed.
#[global] Hint Extern 4 (Bornological _⁻¹) => simple notypeclasses refine invert_bornology_reflecting : typeclass_instances.

Lemma invert_bornology_initial@{u} `{@BornologyInitial@{u} X Y 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : BornologyEmbedding f⁻¹.
Proof. exact (invert_ini (C:=𝐁𝐨𝐫𝐧) (f:=f)). Qed.
#[global] Hint Extern 4 (BornologyInitial _⁻¹) => simple notypeclasses refine invert_bornology_initial : typeclass_instances.
#[global] Hint Extern 4 (BornologyEmbedding _⁻¹) => simple notypeclasses refine invert_bornology_initial : typeclass_instances.
Local Close Scope fun_inv_scope.

(** Miscellaneous *)
Definition born_singleton_alt `{@BornologicalSpace X 𝒜} (x:X) : 𝒜
  := @to_subset _ 𝒜 (singleton x) (bornology_singleton x).
Arguments born_singleton_alt {X} 𝒜 {_} x.

Definition born_pt `{@BornologicalSpace X 𝒜} : X ⇾ 𝒜
  := @func_make _ _ (born_singleton_alt 𝒜) (is_fun singleton).


(** Regularity: the pointwise form of the decision, cf. [uniform_regularity_alt]. *)
Lemma bornology_regularity_alt `{@BornologyRegularity X 𝒜} (K:𝒜)
  : ∐ (K':𝒜), K ⊆ K' ⊠ ∏ (x:X), x ∊ K' ∨ x ∊̸ K.
Proof.
  pose proof bornology_regularity K as [K' [EK HK]]. exists K'. split; trivial.
  intros x. generalize (I:x ∊ ⊤). now rew <-HK.
Qed.
