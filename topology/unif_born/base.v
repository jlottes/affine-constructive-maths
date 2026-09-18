Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import topology.topology uniform.base uniform.basis bornology.base bornology.basis.
Require Import reflection_pair.base.
Require Import easy rewrite simplify tactics.misc.

Local Open Scope topology_scope.

Import of_course_set_notation.

Coercion UnifBornInitial_UniformlyInitial `{@UnifBornInitial X Y Φ Ψ 𝒜 ℬ f} : UniformlyInitial f.
Proof. now split. Qed.

Coercion UnifBornInitial_BornologyInitial `{@UnifBornInitial X Y Φ Ψ 𝒜 ℬ f} : BornologyInitial f.
Proof. now split. Qed.

Coercion UnifBornEmbedding_UniformlyEmbedding `{@UnifBornEmbedding X Y Φ Ψ 𝒜 ℬ f} : UniformlyEmbedding f.
Proof. now split. Qed.

Coercion UnifBornEmbedding_BornologyEmbedding `{@UnifBornEmbedding X Y Φ Ψ 𝒜 ℬ f} : BornologyEmbedding f.
Proof. now split. Qed.

(** Morphism classes respect function equality. *)

Lemma UnifBornMorphism_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (UnifBornMorphism f, UnifBornMorphism g).
Proof. intros E [HC HB]; split; now rew <-E. Qed.
Canonical Structure UnifBornMorphism_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@UnifBornMorphism X Y Φ Ψ 𝒜 ℬ) UnifBornMorphism_proper_impl.

Lemma UnifBornReflecting_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (UnifBornReflecting f, UnifBornReflecting g).
Proof. intros E [HU HB]; split; now rew <-E. Qed.
Canonical Structure UnifBornReflecting_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@UnifBornReflecting X Y Φ Ψ 𝒜 ℬ) UnifBornReflecting_proper_impl.

Lemma UnifBornInitial_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (UnifBornInitial f, UnifBornInitial g).
Proof. intros E [HM HR]; split; now rew <-E. Qed.
Canonical Structure UnifBornInitial_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@UnifBornInitial X Y Φ Ψ 𝒜 ℬ) UnifBornInitial_proper_impl.

Lemma UnifBornEmbedding_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (UnifBornEmbedding f, UnifBornEmbedding g).
Proof. intros E [HI HJ]; split; now rew <-E. Qed.
Canonical Structure UnifBornEmbedding_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@UnifBornEmbedding X Y Φ Ψ 𝒜 ℬ) UnifBornEmbedding_proper_impl.

(** Category structure: identity and composition, for each morphism flavor. *)

Lemma id_unif_born_emb `{@UnifBornSpace X Φ 𝒜} : UnifBornEmbedding (id_fun X).
Proof. do 3 (split; try exact _). Qed.
#[global] Hint Extern 2 (UnifBornEmbedding (id_fun _)) => simple notypeclasses refine id_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial (id_fun _)) => simple notypeclasses refine id_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism (id_fun _)) => simple notypeclasses refine id_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting (id_fun _)) => simple notypeclasses refine id_unif_born_emb : typeclass_instances.

Lemma compose_unif_born_mor@{u} `{@UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f} `{@UnifBornMorphism@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : UnifBornMorphism (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (_ ∘ _)) => simple notypeclasses refine compose_unif_born_mor : typeclass_instances.

Lemma compose_unif_born_reflecting@{u} `{@UnifBornReflecting@{u} X Y Φ Ψ 𝒜 ℬ f} `{@UnifBornReflecting@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : UnifBornReflecting (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornReflecting (_ ∘ _)) => simple notypeclasses refine compose_unif_born_reflecting : typeclass_instances.

Lemma compose_unif_born_initial@{u} `{@UnifBornInitial@{u} X Y Φ Ψ 𝒜 ℬ f} `{@UnifBornInitial@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : UnifBornInitial (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornInitial (_ ∘ _)) => simple notypeclasses refine compose_unif_born_initial : typeclass_instances.

Lemma unif_born_initial_factor@{u} `{@UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f, @UnifBornMorphism@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : UnifBornInitial (g ∘ f) → UnifBornInitial f.
Proof. intros Hgf. split; try exact _. split.
  + exact (ufm_refl_factor f g _).
  + exact (born_refl_factor f g _).
Qed.

Lemma unif_born_mor_factor@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} {ℬ:Bornology Y} {𝒞:Bornology Z} (f: X ⇾ Y) (g: Y ⇾ Z) `{!UnifBornReflecting g}
  : UnifBornMorphism (g ∘ f) → UnifBornMorphism f.
Proof. intros Hgf. split.
  + exact (ufm_cont_factor f g _).
  + exact (bornological_factor f g _).
Qed.

Lemma unif_born_refl_factor@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} {ℬ:Bornology Y} {𝒞:Bornology Z} (f: X ⇾ Y) (g: Y ⇾ Z) `{!UnifBornMorphism g}
  : UnifBornReflecting (g ∘ f) → UnifBornReflecting f.
Proof. intros Hgf. split.
  + exact (ufm_refl_factor f g _).
  + exact (born_refl_factor f g _).
Qed.

Lemma compose_unif_born_emb@{u} `{@UnifBornEmbedding@{u} X Y Φ Ψ 𝒜 ℬ f} `{@UnifBornEmbedding@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : UnifBornEmbedding (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornEmbedding (_ ∘ _)) => simple notypeclasses refine compose_unif_born_emb : typeclass_instances.

(** Abstract reflection pair instance *)

Inductive 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 :=.
#[global] Hint Extern 0 (Fiber 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact (λ X, Uniformity X ∗ Bornology X) : typeclass_instances.
#[global] Hint Extern 0 (ObjClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact (λ X '(Φ,𝒜), @UnifBornSpace X Φ 𝒜) : typeclass_instances.
#[global] Hint Extern 0 (HomClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @UnifBornMorphism_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (RflClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @UnifBornReflecting_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (IniClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @UnifBornInitial_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (EmbClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @UnifBornEmbedding_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 2 (Fib 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 ?X) => split : typeclass_instances.

Definition unif_born_classes@{u} : ReflectionPairClasses@{u} 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧.  Proof. now esplit. Defined.
#[global] Hint Extern 2 (ReflectionPairClasses 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact unif_born_classes : typeclass_instances.

Lemma unif_born_construct : Construct 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧.
Proof. split.
+ intros X [Φ 𝒜] HX. now change (@UnifBornMorphism X X Φ Φ 𝒜 𝒜 (id_fun X)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (@UnifBornMorphism X Y Φ Ψ 𝒜 ℬ f) in Hf.
  now change (@UnifBornSpace X Φ 𝒜).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (@UnifBornMorphism X Y Φ Ψ 𝒜 ℬ f) in Hf.
  now change (@UnifBornSpace Y Ψ ℬ).
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g Hf Hg. now change (@UnifBornMorphism X Z Φ Ξ 𝒜 𝒞 (g ∘ f)).
Qed.
#[global] Hint Extern 0 (Construct 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact unif_born_construct : typeclass_instances.

Lemma unif_born_rfl_construct : RflConstruct 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧.
Proof. split.
+ intros X [Φ 𝒜] HX. now change (@UnifBornReflecting X X Φ Φ 𝒜 𝒜 (id_fun X)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (@UnifBornReflecting X Y Φ Ψ 𝒜 ℬ f) in Hf.
  now change (@UnifBornSpace X Φ 𝒜).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (@UnifBornReflecting X Y Φ Ψ 𝒜 ℬ f) in Hf.
  now change (@UnifBornSpace Y Ψ ℬ).
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g Hf Hg. now change (@UnifBornReflecting X Z Φ Ξ 𝒜 𝒞 (g ∘ f)).
Qed.
#[global] Hint Extern 0 (RflConstruct 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact unif_born_rfl_construct : typeclass_instances.

Lemma unif_born_ini_spec : IniClassSpec 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (IniClassSpec 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact unif_born_ini_spec : typeclass_instances.

Lemma unif_born_emb_spec : EmbClassSpec 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (EmbClassSpec 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact unif_born_emb_spec : typeclass_instances.

Lemma unif_born_rfl_pair : ReflectionPair 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧.
Proof. esplit; try exact _.
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g Hg Hgf. now apply (unif_born_mor_factor f g).
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g Hg Hgf. now apply (unif_born_refl_factor f g).
Qed.
#[global] Hint Extern 0 (ReflectionPair 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact unif_born_rfl_pair : typeclass_instances.

#[global] Hint Extern 0 (FiberMap 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐔𝐧𝐢𝐟) => exact (λ X '(Φ, 𝒜), Φ) : typeclass_instances.
#[global] Hint Extern 0 (FiberMap 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐁𝐨𝐫𝐧) => exact (λ X '(Φ, 𝒜), 𝒜) : typeclass_instances.
#[global] Hint Extern 0 (FiberMap 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐀𝐓𝐨𝐩) => exact (λ X '(Φ, 𝒜), @UniformNeighborhood X Φ) : typeclass_instances.

Lemma unifborn_unif_pair_map : PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐔𝐧𝐢𝐟.
Proof. split; try exact _.
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (UnifBornMorphism f → UniformlyContinuous f). 
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (UnifBornReflecting f → UniformlyReflecting f). 
Qed.
#[global] Hint Extern 0 (PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐔𝐧𝐢𝐟) => exact unifborn_unif_pair_map : typeclass_instances.

Lemma unifborn_born_pair_map : PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐁𝐨𝐫𝐧.
Proof. split; try exact _.
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (UnifBornMorphism f → Bornological f). 
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (UnifBornReflecting f → BornologyReflecting f). 
Qed.
#[global] Hint Extern 0 (PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐁𝐨𝐫𝐧) => exact unifborn_born_pair_map : typeclass_instances.

Lemma unifborn_atop_pair_map : PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐀𝐓𝐨𝐩.
Proof. exact (PairMorphism_compose 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐔𝐧𝐢𝐟 𝐀𝐓𝐨𝐩). Qed.
#[global] Hint Extern 0 (PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐀𝐓𝐨𝐩) => exact unifborn_atop_pair_map : typeclass_instances.


(** Inverses flip classes *)
Local Open Scope fun_inv_scope.

Lemma invert_unif_born_mor@{u} `{@UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : UnifBornReflecting f⁻¹.
Proof. exact (invert_hom (C:=𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) (f:=f)). Qed.
#[global] Hint Extern 4 (UnifBornReflecting _⁻¹) => simple notypeclasses refine invert_unif_born_mor : typeclass_instances.

Lemma invert_unif_born_reflecting@{u} `{@UnifBornReflecting@{u} X Y Φ Ψ 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : UnifBornMorphism f⁻¹.
Proof. exact (invert_rfl (C:=𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) (f:=f)). Qed.
#[global] Hint Extern 4 (UnifBornMorphism _⁻¹) => simple notypeclasses refine invert_unif_born_reflecting : typeclass_instances.

Lemma invert_unif_born_initial@{u} `{@UnifBornInitial@{u} X Y Φ Ψ 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : UnifBornEmbedding f⁻¹.
Proof. exact (invert_ini (C:=𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) (f:=f)). Qed.
#[global] Hint Extern 4 (UnifBornEmbedding _⁻¹) => simple notypeclasses refine invert_unif_born_initial : typeclass_instances.
#[global] Hint Extern 4 (UnifBornInitial _⁻¹) => simple notypeclasses refine invert_unif_born_initial : typeclass_instances.

Local Close Scope fun_inv_scope.

Lemma unif_born_split_iff@{u} {X Y Φ Ψ 𝒜 ℬ f} : @UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f ↔ (UniformlyContinuous f ∧ Bornological f)%sprop.
Proof. now split. Qed.

(** Initial and terminal objects, and global points.
    The default structures on 𝟎 and 𝟏 are the discrete uniformity and trivial
    bornology (hints in uniform/basis.v and bornology/basis.v); the lemmas
    below hold for arbitrary structures satisfying the stated hypotheses. *)

Lemma from_empty_unif_born_mor@{u} `{@UnifBornSpace 𝟎 NE 𝒜} `{@UniformSpace@{u} X Φ} `{@BornologicalSpace@{u} X ℬ}
  : UnifBornMorphism (from_Empty X).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (from_Empty _)) => simple notypeclasses refine from_empty_unif_born_mor : typeclass_instances.

Lemma to_unit_unif_born_mor@{u} `{@UnifBornSpace@{u} X Φ 𝒜} `{@UnifBornSpace 𝟏 Ψ ℬ}
  : UnifBornMorphism (to_Unit X).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (to_Unit _)) => simple notypeclasses refine to_unit_unif_born_mor : typeclass_instances.

Lemma const_unif_born_mor@{u} `{@UnifBornSpace@{u} X Φ 𝒜} `{@UnifBornSpace@{u} Y Ψ ℬ} {y:Y}
  : UnifBornMorphism (const (X:=X) y).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (func_op const _)) => simple notypeclasses refine const_unif_born_mor : typeclass_instances.

(** * Transport of the WCUnif axiom

    A space sitting over a WCUnif space via a globally uniformly continuous,
    bornological, bornology-reflecting map is itself WCUnif: thicken the
    image of a bounded set, pull the entourage back.  Each resource is spent
    once — [f]'s global uniform continuity makes the pulled-back entourage an
    entourage, and bornology reflection returns the thickening's preimage to
    the domain bornology.  Subsumes the literal-pullback case
    ([unif_born/subspace.v : pullback_wc_unif_space]) and transport along
    the localization counit ([unif_born/localization.v : localized_wcunif]). *)

Import image_notation.
Import thicken_notation.

Lemma wcunif_transport@{u} {X Y:set@{u}} (f:X ⇾ Y)
  `{@UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f, !BornologyReflecting f}
  `{!WCUnifSpace Y} : WCUnifSpace X.
Proof. split; [ now split |]. intros A.
  pose proof (wcunif_thicken Y (born_image f A)) as [W HW]; change (apos (W.[f⁎ A] ∊ ℬ)) in HW.
  exists (ufm_preimage f W).
  enough ( (ufm_preimage f W).[powerset_pt A] ⊆ f* W.[f⁎ A] ) as E.
  * rew E. exact (subset_pt_is_el (born_preimage f (@to_subset _ _ _ HW))).
  * intros x'. change ( (∐ x:X, x ∊ A ⊠ (f x, f x') ∊ W)
                      ⊸ (∐ y:Y, y ∊ f⁎ A ⊠ (y, f x') ∊ W) ).
  now rew (aex_image f A set:(λ y, (y, f x') ∊ W)).
Qed.

