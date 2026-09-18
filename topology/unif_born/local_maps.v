(** Basic theory of the locally-uniform morphism classes of
    [interfaces/unif_born.v] — the intrinsic (localization-free) layer of the
    WCUnif morphism theory (doc/extension_theorem.md §2): properness
    boilerplate, the global ⟹ local inclusions, category structure
    (identities and composition), and the coercions to the topological
    classes ([Continuous] / [ContinuouslyReflecting]).

    The composition asymmetry is structural: the forward composite consumes
    [Bornological] of the *first* map (the codomain-lift mechanism,
    doc/localization_monads.md §1), while the reflecting composite consumes
    [BornologyReflecting] of the *second* (ibid. §2).  Post-composing a
    globally uniformly continuous map (resp. pre-composing a globally
    uniformly reflecting one) is free. *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.interior uniform.base uniform.basis bornology.base bornology.basis.
Require Import unif_born.base.
Require Import uniform.cylinder uniform.product.
Require Import reflection_pair.base.
Require Import easy rewrite simplify tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Import of_course_set_notation.
Import image_notation.
Import tensor_map_notation.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Notation "f ♭" := ((func_op ⟨f,f⟩)⁎) (at level 1, left associativity, format "f ♭").
Local Abbreviation π₁ := (tensor_proj1 _ _).

#[local] Hint Extern 0 (Neighborhood _) => exact UniformNeighborhood : typeclass_instances.

(** * Morphism classes respect function equality *)

Lemma LocallyUniformlyContinuous_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} (f g : X ⇾ Y)
  : f = g → impl (LocallyUniformlyContinuous f, LocallyUniformlyContinuous g).
Proof. intros E [HX HY P]; split; try exact _. red. now rew <-E. Qed.
Canonical Structure LocallyUniformlyContinuous_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@LocallyUniformlyContinuous X Y Φ Ψ 𝒜) LocallyUniformlyContinuous_proper_impl.

Lemma LocallyUniformlyReflecting_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (LocallyUniformlyReflecting f, LocallyUniformlyReflecting g).
Proof. intros E [HX HY P]; split; try exact _. red. now rew <-E. Qed.
Canonical Structure LocallyUniformlyReflecting_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@LocallyUniformlyReflecting X Y Φ Ψ ℬ) LocallyUniformlyReflecting_proper_impl.

Lemma LocallyUnifBorn_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (LocallyUnifBorn f, LocallyUnifBorn g).
Proof. intros E [HC HB]; split; now rew <-E. Qed.
Canonical Structure LocallyUnifBorn_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@LocallyUnifBorn X Y Φ Ψ 𝒜 ℬ) LocallyUnifBorn_proper_impl.

Lemma LocallyUnifBornReflecting_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (LocallyUnifBornReflecting f, LocallyUnifBornReflecting g).
Proof. intros E [HR HB]; split; now rew <-E. Qed.
Canonical Structure LocallyUnifBornReflecting_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@LocallyUnifBornReflecting X Y Φ Ψ 𝒜 ℬ) LocallyUnifBornReflecting_proper_impl.

Lemma LocallyUnifBornInitial_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (LocallyUnifBornInitial f, LocallyUnifBornInitial g).
Proof. intros E [HM HR]; split; now rew <-E. Qed.
Canonical Structure LocallyUnifBornInitial_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@LocallyUnifBornInitial X Y Φ Ψ 𝒜 ℬ) LocallyUnifBornInitial_proper_impl.

Lemma LocallyUnifBornEmbedding_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (LocallyUnifBornEmbedding f, LocallyUnifBornEmbedding g).
Proof. intros E [HI HJ]; split; now rew <-E. Qed.
Canonical Structure LocallyUnifBornEmbedding_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@LocallyUnifBornEmbedding X Y Φ Ψ 𝒜 ℬ) LocallyUnifBornEmbedding_proper_impl.

Lemma WCUnifMorphism_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (WCUnifMorphism f, WCUnifMorphism g).
Proof. intros E [HX HY P]; split; try exact _. now rew <-E. Qed.
Canonical Structure WCUnifMorphism_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@WCUnifMorphism X Y Φ Ψ 𝒜 ℬ) WCUnifMorphism_proper_impl.

Lemma WCUnifReflecting_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (WCUnifReflecting f, WCUnifReflecting g).
Proof. intros E [HX HY P]; split; try exact _. now rew <-E. Qed.
Canonical Structure WCUnifReflecting_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@WCUnifReflecting X Y Φ Ψ 𝒜 ℬ) WCUnifReflecting_proper_impl.

Lemma WCUnifInitial_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (WCUnifInitial f, WCUnifInitial g).
Proof. intros E [HM HR]; split; now rew <-E. Qed.
Canonical Structure WCUnifInitial_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@WCUnifInitial X Y Φ Ψ 𝒜 ℬ) WCUnifInitial_proper_impl.

Lemma WCUnifEmbedding_proper_impl@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f g : X ⇾ Y)
  : f = g → impl (WCUnifEmbedding f, WCUnifEmbedding g).
Proof. intros E [HI HJ]; split; now rew <-E. Qed.
Canonical Structure WCUnifEmbedding_fun {X Y} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@WCUnifEmbedding X Y Φ Ψ 𝒜 ℬ) WCUnifEmbedding_proper_impl.

(** * Global implies local *)

Lemma uc_local_uc@{u} `{@UniformlyContinuous@{u} X Y Φ Ψ f} {𝒜:Bornology X} : LocalUniformContinuity f.
Proof. intros K W. destruct (ufm_continuity f W) as [U HU]. exists U.
  intros [x y]. change (x ∊ K ∧ near U x y ⊸ near W (f x) (f y)).
  rew (aandr _ _). exact (HU x y).
Qed.

Lemma ur_local_ur@{u} `{@UniformlyReflecting@{u} X Y Φ Ψ f} {ℬ:Bornology Y} : LocalUniformReflection f.
Proof. intros L U. destruct (ufm_reflection f U) as [W HW]. exists W.
  intros [x y]. change (f x ∊ L ∧ near W (f x) (f y) ⊸ near U x y).
  rew (aandr _ _). exact (HW x y).
Qed.

Lemma uc_locally_uc@{u} `{@UniformlyContinuous@{u} X Y Φ Ψ f, @BornologicalSpace X 𝒜}
  : LocallyUniformlyContinuous f.
Proof. split; try exact _; [ now split | exact uc_local_uc ]. Qed.

Lemma ur_locally_ur@{u} `{@UniformlyReflecting@{u} X Y Φ Ψ f, @BornologicalSpace Y ℬ}
  : LocallyUniformlyReflecting f.
Proof. split; try exact _; [ now split | exact ur_local_ur ]. Qed.

Coercion unif_born_mor_local@{u} `{@UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f} : LocallyUnifBorn f.
Proof. split; try exact _. exact uc_locally_uc. Qed.

Coercion unif_born_refl_local@{u} `{@UnifBornReflecting@{u} X Y Φ Ψ 𝒜 ℬ f} : LocallyUnifBornReflecting f.
Proof. split; try exact _. exact ur_locally_ur. Qed.

Coercion unif_born_initial_local@{u} `{@UnifBornInitial@{u} X Y Φ Ψ 𝒜 ℬ f} : LocallyUnifBornInitial f.
Proof. now split. Qed.

Coercion unif_born_emb_local@{u} `{@UnifBornEmbedding@{u} X Y Φ Ψ 𝒜 ℬ f} : LocallyUnifBornEmbedding f.
Proof. now split. Qed.

(** * Identity *)

Lemma id_locally_unif_born_emb `{@UnifBornSpace X Φ 𝒜} : LocallyUnifBornEmbedding (id_fun X).
Proof. exact unif_born_emb_local. Qed.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding (id_fun _)) => simple notypeclasses refine id_locally_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial (id_fun _)) => simple notypeclasses refine id_locally_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn (id_fun _)) => simple notypeclasses refine id_locally_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting (id_fun _)) => simple notypeclasses refine id_locally_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (id_fun _)) => simple notypeclasses refine id_locally_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (id_fun _)) => simple notypeclasses refine id_locally_unif_born_emb : typeclass_instances.

Lemma id_wcunif_emb `{@WCUnifSpace X Φ 𝒜} : WCUnifEmbedding (id_fun X).
Proof. repeat (split; try exact _). Qed.
#[global] Hint Extern 2 (WCUnifEmbedding (id_fun _)) => simple notypeclasses refine id_wcunif_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifInitial (id_fun _)) => simple notypeclasses refine id_wcunif_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifMorphism (id_fun _)) => simple notypeclasses refine id_wcunif_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting (id_fun _)) => simple notypeclasses refine id_wcunif_emb : typeclass_instances.

(** * Composition *)

Lemma local_uc_compose@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) (g:Y ⇾ Z) `{!Bornological f}
  : LocalUniformContinuity f → LocalUniformContinuity g → LocalUniformContinuity (g ∘ f).
Proof. intros Pf Pg K W.
  pose proof (Pg (born_image f K) W) as [V HV]; change (apos (π₁* (f⁎ K) ⊓ powerset_pt V ⊆ g♯ W)) in HV.
  pose proof (Pf K V) as [U HU]. exists U.
  assert (π₁* K ⊓ powerset_pt U ⊆ π₁* K ⊓ f♯ V) as Hstep1 by
    (apply meet_glb; split; trivial; exact (meet_lb_l _ _)); rew Hstep1; clear Hstep1.
  intros [x y]. change (x ∊ K ∧ near V (f x) (f y) ⊸ (f x, f y) ∊ g♯ W).
  rew <-HV. change (x ∊ K ∧ near V (f x) (f y) ⊸ f x ∊ f⁎ K ∧ near V (f x) (f y)).
  now rew <-(image_el f x K).
Qed.

Lemma local_uc_compose_uc@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} (f:X ⇾ Y) (g:Y ⇾ Z) `{!UniformlyContinuous g}
  : LocalUniformContinuity f → LocalUniformContinuity (g ∘ f).
Proof. intros Pf K W. pose proof Pf K (ufm_preimage g W) as [U HU]. exists U. now rew HU. Qed.


Lemma local_ur_compose@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {ℬ:Bornology Y} {𝒞:Bornology Z} (f:X ⇾ Y) (g:Y ⇾ Z) `{!BornologyReflecting g}
  : LocalUniformReflection f → LocalUniformReflection g → LocalUniformReflection (g ∘ f).
Proof. intros Pf Pg M U.
  pose proof Pf (born_preimage g M) U as [W HW].
  pose proof Pg M W as [V HV].
  exists V.
  enough ((g ∘ f)♯ (π₁* M ⊓ powerset_pt V) ⊆ f♯ (π₁* (born_preimage g M) ⊓ powerset_pt W)) as E by now rew E.
  intros [x y]. change ( (g (f x) ∊ M ∧ (g (f x), g (f y)) ∊ V) ⊸ (g (f x) ∊ M ∧ (f x, f y) ∊ W) ).
  apply aand_intro; [ easy |].
  exact (HV (f x, f y)).
Qed.


Lemma local_ur_compose_ur@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒞:Bornology Z} (f:X ⇾ Y) (g:Y ⇾ Z) `{!UniformlyReflecting f}
  : LocalUniformReflection g → LocalUniformReflection (g ∘ f).
Proof. intros Pg M U.
  destruct (ufm_reflection_alt f U) as [W HW].
  destruct (Pg M W) as [V HV]. exists V.
  change (f♯ (g♯ (π₁* M ⊓ powerset_pt V)) ⊆ U).
  now rew HV.
Qed.

(** * Factoring (right cancellation): [g] inherits the local classes from
    [h ∘ g] by factoring through the outer map — reflecting [h] for the
    continuity side, continuous bornological [h] for the reflection side,
    mirroring the duality of the free composition lemmas above.  Deliberately
    not hints: factor lemmas grow the goal and would loop with the
    composition hints. *)

Lemma local_uc_factor@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} (g:X ⇾ Y) (h:Y ⇾ Z) `{!UniformlyReflecting h}
  : LocalUniformContinuity (h ∘ g) → LocalUniformContinuity g.
Proof. intros P K W.
  destruct (ufm_reflection_alt h W) as [V HV].
  destruct (P K V) as [U HU]. exists U.
  rew HU.
  change (g♯ (h♯ V) ⊆ g♯ W).
  now rew HV.
Qed.

Lemma local_ur_factor@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {ℬ:Bornology Y} {𝒞:Bornology Z} (g:X ⇾ Y) (h:Y ⇾ Z) `{!UniformlyContinuous h, !Bornological h}
  : LocalUniformReflection (h ∘ g) → LocalUniformReflection g.
Proof. intros P L U.
  destruct (P (born_image h L) U) as [V HV].
  exists (ufm_preimage h V).
  enough (g♯ (π₁* L ⊓ powerset_pt (ufm_preimage h V))
          ⊆ (h ∘ g)♯ (π₁* (h⁎ L) ⊓ powerset_pt V)) as E by now rew E.
  intros [x y].
  change ((g x ∊ L ∧ (h (g x), h (g y)) ∊ V) ⊸ (h (g x) ∊ h⁎ L ∧ (h (g x), h (g y)) ∊ V)).
  apply aand_intro; [| easy ].
  rew (aandl _ _). exact (image_el h (g x) L).
Qed.

Lemma local_uc_factor_local@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} {𝒞:Bornology Z} (g:X ⇾ Y) (h:Y ⇾ Z) `{!Bornological (h ∘ g)}
  : LocalUniformReflection h → LocalUniformContinuity (h ∘ g) → LocalUniformContinuity g.
Proof. intros Ph P K W.
  destruct (Ph (born_image (h ∘ g) K) W) as [V HV].
  destruct (P K V) as [U HU]. exists U.
  enough (π₁* K ⊓ powerset_pt U ⊆ g♯ (h♯ (π₁* ((h ∘ g)⁎ K) ⊓ powerset_pt V))) as E
    by (rew E; now rew HV).
  intros [x y].
  change ((x ∊ K ∧ (x, y) ∊ U) ⊸ (h (g x) ∊ (h ∘ g)⁎ K ∧ (h (g x), h (g y)) ∊ V)).
  apply aand_intro.
  + rew (aandl _ _). exact (image_el (h ∘ g) x K).
  + exact (HU (x, y)).
Qed.

Lemma local_ur_factor_local@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {ℬ:Bornology Y} {𝒞:Bornology Z} (g:X ⇾ Y) (h:Y ⇾ Z) `{!Bornological h}
  : LocalUniformContinuity h → LocalUniformReflection (h ∘ g) → LocalUniformReflection g.
Proof. intros Ph P L U.
  destruct (P (born_image h L) U) as [V HV].
  destruct (Ph L V) as [W HW]. exists W.
  enough (g♯ (π₁* L ⊓ powerset_pt W) ⊆ (h ∘ g)♯ (π₁* (h⁎ L) ⊓ powerset_pt V)) as E
    by now rew E.
  intros [x y].
  change ((g x ∊ L ∧ (g x, g y) ∊ W) ⊸ (h (g x) ∊ h⁎ L ∧ (h (g x), h (g y)) ∊ V)).
  apply aand_intro.
  + rew (aandl _ _). exact (image_el h (g x) L).
  + exact (HW (g x, g y)).
Qed.

Lemma locally_unif_born_rfl_factor@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} {ℬ:Bornology Y} {𝒞:Bornology Z} (g:X ⇾ Y) (h:Y ⇾ Z)
  `{!LocallyUnifBorn h} : LocallyUnifBornReflecting (h ∘ g) → LocallyUnifBornReflecting g.
Proof. intro; split.
+ split; try exact _. exact (local_ur_factor_local g h _ _).
+ exact (born_refl_factor g h _).
Qed.

Lemma locally_unif_born_factor@{u} {X Y Z:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} {ℬ:Bornology Y} {𝒞:Bornology Z} (g:X ⇾ Y) (h:Y ⇾ Z)
  `{!LocallyUnifBornReflecting h} : LocallyUnifBorn (h ∘ g) → LocallyUnifBorn g.
Proof. intro; split.
+ split; try exact _. exact (local_uc_factor_local g h _ _).
+ exact (bornological_factor g h _).
Qed.

Lemma compose_locally_unif_born_locally_uc@{u} `{@LocallyUnifBorn@{u} X Y Φ Ψ 𝒜 ℬ f, @LocallyUniformlyContinuous@{u} Y Z Ψ Ξ ℬ g}
  : LocallyUniformlyContinuous (g ∘ f).
Proof. split; try exact _. now apply local_uc_compose. Qed.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (_ ∘ _)) => simple notypeclasses refine compose_locally_unif_born_locally_uc : typeclass_instances.

Lemma compose_locally_unif_born_refl_locally_ur@{u} `{@LocallyUniformlyReflecting@{u} X Y Φ Ψ ℬ f, @LocallyUnifBornReflecting@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : LocallyUniformlyReflecting (g ∘ f).
Proof. split; try exact _. now apply local_ur_compose. Qed.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (_ ∘ _)) => simple notypeclasses refine compose_locally_unif_born_refl_locally_ur : typeclass_instances.

(** Mixed compositions with a plain uniform map on the bornology-free side:
    the bundled shells of [local_uc_compose_uc] and [local_ur_compose_ur] —
    no bornology is needed on the plain map's carriers.  Not hints: the
    composition hints above stay the canonical [(_ ∘ _)] instances. *)

Lemma compose_locally_uc_uc@{u} `{@LocallyUniformlyContinuous@{u} X Y Φ Ψ 𝒜 f} `{@UniformlyContinuous@{u} Y Z Ψ Ξ g}
  : LocallyUniformlyContinuous (g ∘ f).
Proof. split; try exact _. now apply local_uc_compose_uc. Qed.

Lemma compose_ur_locally_ur@{u} `{@UniformlyReflecting@{u} X Y Φ Ψ f} `{@LocallyUniformlyReflecting@{u} Y Z Ψ Ξ 𝒞 g}
  : LocallyUniformlyReflecting (g ∘ f).
Proof. split; try exact _. now apply local_ur_compose_ur. Qed.

Lemma compose_locally_unif_born@{u} `{@LocallyUnifBorn@{u} X Y Φ Ψ 𝒜 ℬ f} `{@LocallyUnifBorn@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : LocallyUnifBorn (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (LocallyUnifBorn (_ ∘ _)) => simple notypeclasses refine compose_locally_unif_born : typeclass_instances.

Lemma compose_locally_unif_born_reflecting@{u} `{@LocallyUnifBornReflecting@{u} X Y Φ Ψ 𝒜 ℬ f} `{@LocallyUnifBornReflecting@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : LocallyUnifBornReflecting (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (LocallyUnifBornReflecting (_ ∘ _)) => simple notypeclasses refine compose_locally_unif_born_reflecting : typeclass_instances.

Lemma compose_locally_unif_born_initial@{u} `{@LocallyUnifBornInitial@{u} X Y Φ Ψ 𝒜 ℬ f} `{@LocallyUnifBornInitial@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : LocallyUnifBornInitial (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (LocallyUnifBornInitial (_ ∘ _)) => simple notypeclasses refine compose_locally_unif_born_initial : typeclass_instances.

Lemma compose_locally_unif_born_embedding@{u} `{@LocallyUnifBornEmbedding@{u} X Y Φ Ψ 𝒜 ℬ f} `{@LocallyUnifBornEmbedding@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : LocallyUnifBornEmbedding (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding (_ ∘ _)) => simple notypeclasses refine compose_locally_unif_born_embedding : typeclass_instances.

Lemma compose_wcunif_morphism@{u} `{@WCUnifMorphism@{u} X Y Φ Ψ 𝒜 ℬ f} `{@WCUnifMorphism@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : WCUnifMorphism (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (WCUnifMorphism (_ ∘ _)) => simple notypeclasses refine compose_wcunif_morphism : typeclass_instances.

Lemma compose_wcunif_reflecting@{u} `{@WCUnifReflecting@{u} X Y Φ Ψ 𝒜 ℬ f} `{@WCUnifReflecting@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : WCUnifReflecting (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (WCUnifReflecting (_ ∘ _)) => simple notypeclasses refine compose_wcunif_reflecting : typeclass_instances.

Lemma compose_wcunif_initial@{u} `{@WCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ f} `{@WCUnifInitial@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : WCUnifInitial (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (WCUnifInitial (_ ∘ _)) => simple notypeclasses refine compose_wcunif_initial : typeclass_instances.

Lemma compose_wcunif_embedding@{u} `{@WCUnifEmbedding@{u} X Y Φ Ψ 𝒜 ℬ f} `{@WCUnifEmbedding@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  : WCUnifEmbedding (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (WCUnifEmbedding (_ ∘ _)) => simple notypeclasses refine compose_wcunif_embedding : typeclass_instances.

(** * Inversion

    The classes swap polarity under inversion: the [𝒜]-cylinder of a
    locally-u.c. [f] sits on the codomain of [f⁻¹], so it is exactly the
    data of local uniform reflection there, and dually. *)

Local Open Scope fun_inv_scope.

Lemma invert_locally_uc@{u} `{@LocallyUniformlyContinuous@{u} X Y Φ Ψ 𝒜 f} `{!Inverse f, !Bijective f}
  : LocallyUniformlyReflecting f⁻¹.
Proof. split; try exact _. intros L V.
  pose proof local_uniform_continuity f L V as [U HU]. exists U.
  rew HU.
  intros [y₁ y₂]. change ((f (f⁻¹ y₁), f (f⁻¹ y₂)) ∊ V ⊸ (y₁, y₂) ∊ V).
  now rew (surjective_applied f _).
Qed.
#[global] Hint Extern 4 (LocallyUniformlyReflecting _⁻¹) => simple notypeclasses refine invert_locally_uc : typeclass_instances.

Lemma invert_locally_ur@{u} `{@LocallyUniformlyReflecting@{u} X Y Φ Ψ ℬ f} `{!Inverse f, !Bijective f}
  : LocallyUniformlyContinuous f⁻¹.
Proof. split; try exact _. intros L U.
  pose proof local_uniform_reflection f L U as [W HW]. exists W.
  rew <-HW.
  intros [y₁ y₂].
  change ((y₁, y₂) ∊ π₁* L ⊓ powerset_pt W ⊸ (f (f⁻¹ y₁), f (f⁻¹ y₂)) ∊ π₁* L ⊓ powerset_pt W).
  now rew (surjective_applied f _).
Qed.
#[global] Hint Extern 4 (LocallyUniformlyContinuous _⁻¹) => simple notypeclasses refine invert_locally_ur : typeclass_instances.

Lemma invert_locally_unif_born@{u} `{@LocallyUnifBorn@{u} X Y Φ Ψ 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : LocallyUnifBornReflecting f⁻¹.
Proof. now split. Qed.
#[global] Hint Extern 4 (LocallyUnifBornReflecting _⁻¹) => simple notypeclasses refine invert_locally_unif_born : typeclass_instances.

Lemma invert_locally_unif_born_reflecting@{u} `{@LocallyUnifBornReflecting@{u} X Y Φ Ψ 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : LocallyUnifBorn f⁻¹.
Proof. now split. Qed.
#[global] Hint Extern 4 (LocallyUnifBorn _⁻¹) => simple notypeclasses refine invert_locally_unif_born_reflecting : typeclass_instances.

Lemma invert_locally_unif_born_initial@{u} `{@LocallyUnifBornInitial@{u} X Y Φ Ψ 𝒜 ℬ f} `{!Inverse f, !Bijective f}
  : LocallyUnifBornEmbedding f⁻¹.
Proof. now split. Qed.
#[global] Hint Extern 4 (LocallyUnifBornEmbedding _⁻¹) => simple notypeclasses refine invert_locally_unif_born_initial : typeclass_instances.
#[global] Hint Extern 4 (LocallyUnifBornInitial _⁻¹) => simple notypeclasses refine invert_locally_unif_born_initial : typeclass_instances.

Local Close Scope fun_inv_scope.

(** * Topological consequences *)

Coercion locally_uc_cont `{@LocallyUniformlyContinuous X Y Φ Ψ 𝒜 f} : Continuous f.
Proof. split; try exact _. intros x N.
  change ( (∐ W : Ψ, near W (f x) ⊆ N) ⊸ ∐ U : Φ, near U x ⊆ f* N ).
  rew <-aex_adj; intros W.
  pose proof local_uniform_continuity f (born_pt x) W as [U HU].
  rew <-(aex_ub _ U).
  change ((∏ y, near W (f x) y ⊸ y ∊ N) ⊸ ∏ x', near U x x' ⊸ x' ∊ f* N ).
  rew <-all_adj; intros x'; rew (all_lb _ (f x')).
  change (x' ∊ f* N) with (f x' ∊ N).
  apply aimpl_proper_aimpl; [| easy ].
  change ( near U x x' ⊸ (x, x') ∊ f♯ W ). rew <-HU.
  change ( near U x x' ⊸ x = x ∧ (x, x') ∊ U ).
  now rew (aand_true_l (ltac:(refl):x = x)).
Qed.

Coercion locally_ur_cont_refl `{@LocallyUniformlyReflecting X Y Φ Ψ ℬ f} : ContinuouslyReflecting f.
Proof. split; try exact _. intros x N.
  change ( (∐ U : Φ, near U x ⊆ N) ⊸ ∐ M : 𝒫 Y, (∐ V : Ψ, near V (f x) ⊆ M) ⊠ f* M ⊆ N ).
  rew <-aex_adj; intros U.
  pose proof local_uniform_reflection f (born_pt (f x)) U as [W HW].
  rew <-(aex_ub _ (near W (f x))), <-(aex_ub _ W).
  rew (aprod_true_l (ltac:(refl):near W (f x) ⊆ near W (f x)) ).
  enough (f* (near W (f x)) ⊆ near U x) as E by now rew E.
  intros x'. change (near W (f x) (f x') ⊸ (x, x') ∊ U). rew <-HW.
  change (near W (f x) (f x') ⊸ f x = f x ∧ near W (f x) (f x')).
  now rew (aand_true_l (ltac:(refl):f x = f x)).
Qed.

Coercion locally_ub_initial_cont_initial `{@LocallyUnifBornInitial X Y Φ Ψ 𝒜 ℬ f} : ContinuouslyInitial f.
Proof. now split. Qed.

Coercion locally_ub_emb_cont_emb `{@LocallyUnifBornEmbedding X Y Φ Ψ 𝒜 ℬ f} : ContinuouslyEmbedding f.
Proof. now split. Qed.

(** * Embedding from initiality (mirror of [uniform_reflection_injective] /
    [uniform_initial_embedding]): the anchor for injectivity is the
    singleton at [f x], whose membership is refl-true. *)

Lemma local_reflection_injective `{@SeparatedUniformSpace X Φ} `{@UnifBornSpace Y Ψ ℬ}
  {f:X ⇾ Y} `{!LocalUniformReflection f} : Injective f.
Proof. intros x y. rew (uniform_separated_iff x _), <-all_adj; intros U.
  pose proof local_uniform_reflection f (born_pt (f x)) U as [W HW].
  change ( f x = f y ⊸ (x, y) ∊ U ). rew <-HW.
  change ( f x = f y ⊸ f x = f x ∧ near W (f x) (f y) ).
  rew (aand_true_l (ltac:(refl):f x = f x)).
  apply near_refl_alt.
Qed.

Lemma locally_initial_embedding `{@LocallyUnifBornInitial X Y Φ Ψ 𝒜 ℬ f, !SeparatedUniformSpace X}
  : LocallyUnifBornEmbedding f.
Proof. pose proof local_reflection_injective : Injective f. now split. Qed.

Lemma wcunif_initial_embedding `{@WCUnifInitial X Y Φ Ψ 𝒜 ℬ f, !SeparatedUniformSpace X}
  : WCUnifEmbedding f.
Proof. pose proof local_reflection_injective : Injective f. now split. Qed.

(** * Dense lifting of local uniform reflection (mirror of [ufm_dense_initial])

    If [f : X ⇾ Y] is dense and uniformly continuous, [g : Y ⇾ Z] is uniformly
    continuous into a WCUnif space, and [g ∘ f] locally uniformly reflects,
    then [g] locally uniformly reflects.  Entirely entourage-level: the
    exhibited entourage is a symmetric split, no witness pre-uniformity is
    constructed.  Global uniform continuity of [g] is what makes the two
    Y→Z crossings free (apos-level, via the density approximations); the
    cylinder resource [g y ∊ L ∧ near _ (g y) (g y')] is spent once per
    additive branch of the [g ∘ f]-reflection cylinder. *)

Import thicken_notation.
Local Open Scope grp_scope.
Local Open Scope sg_op_scope.

Lemma ufm_dense_local_reflection@{u} {X Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
  `{@UniformlyContinuous X Y Φ Ψ f, !Dense f, @UniformSpace Z Ξ, !Continuous g}
  {ℬ:Bornology Z} `{!WCUnifSpace Z}
  `{!LocalUniformReflection (g ∘ f)}
  : LocalUniformReflection g.
Proof. intros L U. pose proof ufm_split_closure U as [U' [_ PU']].
  pose proof (wcunif_thicken Z L) as [W₀ HW₀].
  pose proof local_uniform_reflection (g ∘ f) (@to_subset _ _ _ HW₀) (ufm_preimage f U') as [W₁ PW₁];
    change (apos (f♯ (g♯ (π₁* W₀.[powerset_pt L] ⊓ powerset_pt W₁)) ⊆ f♯ U')) in PW₁.
  pose proof (cylinder_sub_interior (powerset_pt L) W₀ W₁) as [V P]; exists V; rew P; clear P.
  rew (continuous_preimage_interior ⟨g,g⟩ _).
  rew (dense_interior_closure_unit ⟨f,f⟩ _).
  rew PW₁.
  now rew (image_preimage_counit _ _).
Qed.

Abbreviation cl := closure.
Abbreviation int := interior.

Lemma ufm_dense_bornology_reflecting@{u} {X Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
  `{@UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f, !Dense f}
  `{@UniformlyContinuous@{u} Y Z Ψ Ξ g}
   {𝒞:Bornology Z}
  `{!WCUnifSpace Y} `{!WCUnifSpace Z}
  `{!BornologyReflecting (g ∘ f)}
  : BornologyReflecting g.
Proof. split; try exact _. intros C.
  pose proof (wcunif_thicken Z C) as [W HW].
  pose (C' := @to_subset _ _ _ HW).
  pose proof (wcunif_thicken Y (born_image f (born_preimage (g ∘ f) C'))) as [V HV];
    change (apos (V.[f⁎ ( f* (g* W.[powerset_pt C]) )] ∊ ℬ)) in HV.
  enough (g* C ⊆ V.[f⁎ ( f* (g* W.[powerset_pt C]) )]) as E by now rew E.
  rew <-(closure_sub_thicken V _). 
  rew <-(preimage_thicken_uc_le g W C).
  exact (dense_image_preimage_unit f _ _).
Qed.

(** The bundle: the [ufm_dense_initial] analog for the locally-uniform
    classes.  [f] dense + uniformly continuous + bornological, [g] uniformly
    continuous + bornological, and [g ∘ f] locally unif-born reflecting make
    [g] locally unif-born initial. *)
Lemma ufm_dense_locally_initial@{u} {X Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
  `{@UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f, !Dense f}
  `{@UnifBornMorphism@{u} Y Z Ψ Ξ ℬ 𝒞 g}
  `{!WCUnifSpace Y} `{!WCUnifSpace Z}
  `{!LocallyUnifBornReflecting (g ∘ f)}
  : LocallyUnifBornInitial g.
Proof. split.
+ split.
  * exact uc_locally_uc.
  * exact _.
+ split.
  * split; try exact _. exact (ufm_dense_local_reflection f g).
  * exact (ufm_dense_bornology_reflecting f g).
Qed.

(** Abstract reflection pair instance: the locally pair (doc §2.5) — the same
    fiber and object class as 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧, with the locally hom-classes.  The
    pair laws are verified directly from the local factor lemmas; the one-sided
    component statements (bornology on only one endpoint) remain concrete. *)

Inductive 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc :=.

#[global] Hint Extern 0 (Fiber 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact (λ X, Uniformity X ∗ Bornology X) : typeclass_instances.
#[global] Hint Extern 0 (ObjClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact (λ X '(Φ,𝒜), @UnifBornSpace X Φ 𝒜) : typeclass_instances.
#[global] Hint Extern 0 (HomClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @LocallyUnifBorn_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (RflClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @LocallyUnifBornReflecting_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (IniClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @LocallyUnifBornInitial_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (EmbClass 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @LocallyUnifBornEmbedding_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 2 (Fib 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc ?X) => split : typeclass_instances.

Definition unif_born_loc_classes@{u} : ReflectionPairClasses@{u} 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc.  Proof. now esplit. Defined.
#[global] Hint Extern 2 (ReflectionPairClasses 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact unif_born_loc_classes : typeclass_instances.

Lemma unif_born_loc_construct : Construct 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc.
Proof. split.
+ intros X [Φ 𝒜] HX. now change (@LocallyUnifBorn X X Φ Φ 𝒜 𝒜 (id_fun X)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (LocallyUnifBorn f) in Hf.
  now change (UnifBornSpace X).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (LocallyUnifBorn f) in Hf.
  now change (UnifBornSpace Y).
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g Hf Hg. now change (LocallyUnifBorn (g ∘ f)).
Qed.
#[global] Hint Extern 0 (Construct 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact unif_born_loc_construct : typeclass_instances.

Lemma unif_born_loc_rfl_construct : RflConstruct 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc.
Proof. split.
+ intros X [Φ 𝒜] HX. now change (@LocallyUnifBornReflecting X X Φ Φ 𝒜 𝒜 (id_fun X)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (LocallyUnifBornReflecting f) in Hf.
  now change (UnifBornSpace X).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (LocallyUnifBornReflecting f) in Hf.
  now change (UnifBornSpace Y).
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g Hf Hg. now change (LocallyUnifBornReflecting (g ∘ f)).
Qed.
#[global] Hint Extern 0 (RflConstruct 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact unif_born_loc_rfl_construct : typeclass_instances.

Lemma unif_born_loc_ini_spec : IniClassSpec 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (IniClassSpec 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact unif_born_loc_ini_spec : typeclass_instances.

Lemma unif_born_loc_emb_spec : EmbClassSpec 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (EmbClassSpec 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact unif_born_loc_emb_spec : typeclass_instances.

Lemma unif_born_loc_rfl_pair : ReflectionPair 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc.
Proof. esplit; try exact _.
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g.
  change (LocallyUnifBornReflecting g → LocallyUnifBorn (g ∘ f) → LocallyUnifBorn f).
  apply locally_unif_born_factor.
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g.
  change (LocallyUnifBorn g → LocallyUnifBornReflecting (g ∘ f) → LocallyUnifBornReflecting f).
  apply locally_unif_born_rfl_factor.
Qed.
#[global] Hint Extern 0 (ReflectionPair 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact unif_born_loc_rfl_pair : typeclass_instances.

(** The global-to-local vertical of the §2.2 diagram: identity on fibers,
    inclusion on both classes. *)
#[global] Hint Extern 0 (FiberMap 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact (λ X FX, FX) : typeclass_instances.

Lemma unifborn_loc_pair_map : PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc.
Proof. split; try exact _.
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (UnifBornMorphism f → LocallyUnifBorn f).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (UnifBornReflecting f → LocallyUnifBornReflecting f).
Qed.
#[global] Hint Extern 0 (PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact unifborn_loc_pair_map : typeclass_instances.

(** The 𝐀𝐓𝐨𝐩-leg of the locally pair (§2.2): the underlying topology, with the
    classes descending via [locally_uc_cont] / [locally_ur_cont_refl]. *)
#[global] Hint Extern 0 (FiberMap 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc 𝐀𝐓𝐨𝐩) => exact (λ X '(Φ, 𝒜), @UniformNeighborhood X Φ) : typeclass_instances.

Lemma unifborn_loc_atop_pair_map : PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc 𝐀𝐓𝐨𝐩.
Proof. split; try exact _.
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (LocallyUnifBorn f → Continuous f).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (LocallyUnifBornReflecting f → ContinuouslyReflecting f).
Qed.
#[global] Hint Extern 0 (PairMorphism 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc 𝐀𝐓𝐨𝐩) => exact unifborn_loc_atop_pair_map : typeclass_instances.

(** Abstract reflection pair instance: the restriction WCUnif of UnifBorn_loc. *)

Inductive 𝐖𝐂𝐔𝐧𝐢𝐟 :=.

#[global] Hint Extern 0 (Fiber 𝐖𝐂𝐔𝐧𝐢𝐟) => exact (λ X, Uniformity X ∗ Bornology X) : typeclass_instances.
#[global] Hint Extern 0 (ObjClass 𝐖𝐂𝐔𝐧𝐢𝐟) => exact (λ X '(Φ,𝒜), @WCUnifSpace X Φ 𝒜) : typeclass_instances.
#[global] Hint Extern 0 (HomClass 𝐖𝐂𝐔𝐧𝐢𝐟) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @WCUnifMorphism_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (RflClass 𝐖𝐂𝐔𝐧𝐢𝐟) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @WCUnifReflecting_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (IniClass 𝐖𝐂𝐔𝐧𝐢𝐟) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @WCUnifInitial_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 0 (EmbClass 𝐖𝐂𝐔𝐧𝐢𝐟) => exact (λ X Y '(Φ,𝒜) '(Ψ,ℬ), @WCUnifEmbedding_fun X Y Φ Ψ 𝒜 ℬ) : typeclass_instances.
#[global] Hint Extern 2 (Fib 𝐖𝐂𝐔𝐧𝐢𝐟 ?X) => split : typeclass_instances.

Definition wcunif_classes@{u} : ReflectionPairClasses@{u} 𝐖𝐂𝐔𝐧𝐢𝐟.  Proof. now esplit. Defined.
#[global] Hint Extern 2 (ReflectionPairClasses 𝐖𝐂𝐔𝐧𝐢𝐟) => exact wcunif_classes : typeclass_instances.

Lemma wcunif_construct : Construct 𝐖𝐂𝐔𝐧𝐢𝐟.
Proof. split.
+ intros X [Φ 𝒜] HX. now change (@WCUnifMorphism X X Φ Φ 𝒜 𝒜 (id_fun X)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (WCUnifMorphism f) in Hf.
  now change (WCUnifSpace X).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (WCUnifMorphism f) in Hf.
  now change (WCUnifSpace Y).
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g Hf Hg. now change (WCUnifMorphism (g ∘ f)).
Qed.
#[global] Hint Extern 0 (Construct 𝐖𝐂𝐔𝐧𝐢𝐟) => exact wcunif_construct : typeclass_instances.

Lemma wcunif_rfl_construct : RflConstruct 𝐖𝐂𝐔𝐧𝐢𝐟.
Proof. split.
+ intros X [Φ 𝒜] HX. now change (@WCUnifReflecting X X Φ Φ 𝒜 𝒜 (id_fun X)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (WCUnifReflecting f) in Hf.
  now change (WCUnifSpace X).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f Hf. change (WCUnifReflecting f) in Hf.
  now change (WCUnifSpace Y).
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g Hf Hg. now change (WCUnifReflecting (g ∘ f)).
Qed.
#[global] Hint Extern 0 (RflConstruct 𝐖𝐂𝐔𝐧𝐢𝐟) => exact wcunif_rfl_construct : typeclass_instances.

Lemma wcunif_ini_spec : IniClassSpec 𝐖𝐂𝐔𝐧𝐢𝐟.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (IniClassSpec 𝐖𝐂𝐔𝐧𝐢𝐟) => exact wcunif_ini_spec : typeclass_instances.

Lemma wcunif_emb_spec : EmbClassSpec 𝐖𝐂𝐔𝐧𝐢𝐟.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (EmbClassSpec 𝐖𝐂𝐔𝐧𝐢𝐟) => exact wcunif_emb_spec : typeclass_instances.

Lemma wcunif_rfl_pair : ReflectionPair 𝐖𝐂𝐔𝐧𝐢𝐟.
Proof. esplit; try exact _.
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g.
  change (WCUnifReflecting g → WCUnifMorphism (g ∘ f) → WCUnifMorphism f).
  intros ??. enough (LocallyUnifBorn f) by now split.
  now apply (locally_unif_born_factor f g).
+ intros X Y Z [Φ 𝒜] [Ψ ℬ] [Ξ 𝒞] f g.
  change (WCUnifMorphism g → WCUnifReflecting (g ∘ f) → WCUnifReflecting f).
  intros ??. enough (LocallyUnifBornReflecting f) by now split.
  now apply (locally_unif_born_rfl_factor f g).
Qed.
#[global] Hint Extern 0 (ReflectionPair 𝐖𝐂𝐔𝐧𝐢𝐟) => exact wcunif_rfl_pair : typeclass_instances.

#[global] Hint Extern 0 (FiberMap 𝐖𝐂𝐔𝐧𝐢𝐟 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact (λ X FX, FX) : typeclass_instances.

Lemma wcunif_unifborn_loc_pair_map : PairMorphism 𝐖𝐂𝐔𝐧𝐢𝐟 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc.
Proof. split; try exact _.
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (WCUnifMorphism f → LocallyUnifBorn f).
+ intros X Y [Φ 𝒜] [Ψ ℬ] f. now change (WCUnifReflecting f → LocallyUnifBornReflecting f).
Qed.
#[global] Hint Extern 0 (PairMorphism 𝐖𝐂𝐔𝐧𝐢𝐟 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc) => exact wcunif_unifborn_loc_pair_map : typeclass_instances.

(** The 𝐀𝐓𝐨𝐩-leg of the locally pair (§2.2): the underlying topology, with the
    classes descending via [locally_uc_cont] / [locally_ur_cont_refl]. *)
#[global] Hint Extern 0 (FiberMap 𝐖𝐂𝐔𝐧𝐢𝐟 𝐀𝐓𝐨𝐩) => exact (λ X '(Φ, 𝒜), @UniformNeighborhood X Φ) : typeclass_instances.

Lemma wcunif_atop_pair_map : PairMorphism 𝐖𝐂𝐔𝐧𝐢𝐟 𝐀𝐓𝐨𝐩.
Proof. exact (PairMorphism_compose 𝐖𝐂𝐔𝐧𝐢𝐟 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧_loc 𝐀𝐓𝐨𝐩). Qed.
#[global] Hint Extern 0 (PairMorphism 𝐖𝐂𝐔𝐧𝐢𝐟 𝐀𝐓𝐨𝐩) => exact wcunif_atop_pair_map : typeclass_instances.

