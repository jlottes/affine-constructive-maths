Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology uniform.base uniform.basis bornology.base bornology.basis.
Require Import uniform.final uniform.subspace.
Require Import topology.topology topology.interior topology.uniform.base uniform.basis uniform.product.
Require Import unif_born.base unif_born.local_maps.
Require Import uniform.cylinder.
Require Import easy rewrite replc simplify strip_coercions tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope grp_scope.
Local Open Scope sg_op_scope.
Import projection_notation.
Import image_notation.
Import tensor_map_notation.
Import thicken_notation.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Notation "f ♭" := ((func_op ⟨f,f⟩)⁎) (at level 1, left associativity, format "f ♭").

Local Abbreviation π₁ := (tensor_proj1 _ _).

Lemma cylinder_meet_tensor_subset@{u} {X Y:set@{u}} (K A:𝒫 X) (B:𝒫 Y) : (K ⊓ A) ⊗ B ⊆ π₁* K ⊓ (A ⊗ B) .
Proof. intros [a b]. change ((a ∊ K ∧ a ∊ A) ⊠ b ∊ B ⊸ a ∊ K ∧ (a ∊ A ⊠ b ∊ B)). tautological. Qed.

(** Localized uniformity *)
Definition localization_filter X {Φ:Uniformity X} {𝒜:Bornology X}
  := { V : 𝒫 (X ⊗ X) | ∏ K:𝒜, ∐ U:Φ, π₁* K ⊓ powerset_pt U ⊆ V }.

Definition localized_uniformity X {Φ:Uniformity X} {𝒜:Bornology X} : Uniformity X
  := uniformity_of_filter (localization_filter X).

Definition localization (X:set) {Φ:Uniformity X} {𝒜:Bornology X} : set := X.
Global Typeclasses Opaque localization.
Local Abbreviation ℒ := localization.
#[global] Hint Extern 0 (Bornology (@localization _ _ ?𝒜)) => exact 𝒜 : typeclass_instances.
#[global] Hint Extern 0 (Uniformity (@localization ?X ?Φ ?𝒜)) => exact (@localized_uniformity X Φ 𝒜) : typeclass_instances.


Definition from_localization (X:set) {Φ:Uniformity X} {𝒜:Bornology X} : ℒ X ⇾ X := id_fun X.
Definition to_localization (X:set) {Φ:Uniformity X} {𝒜:Bornology X} : X ⇾ ℒ X := id_fun X.
Local Abbreviation ε := from_localization.
Local Abbreviation η := to_localization.

#[global] Hint Extern 2 (Inverse (@from_localization ?X ?Φ ?𝒜)) => exact (@to_localization   X Φ 𝒜) : typeclass_instances.
#[global] Hint Extern 2 (Inverse (@to_localization   ?X ?Φ ?𝒜)) => exact (@from_localization X Φ 𝒜) : typeclass_instances.

#[global] Hint Extern 2 (Bijective  (from_localization ?X)) => change (Bijective  (id_fun X)) : typeclass_instances.
#[global] Hint Extern 2 (Injective  (from_localization ?X)) => change (Injective  (id_fun X)) : typeclass_instances.
#[global] Hint Extern 2 (Surjective (from_localization ?X)) => change (Surjective (id_fun X)) : typeclass_instances.
#[global] Hint Extern 2 (WeaklySurjective (func_op (from_localization ?X))) => change (WeaklySurjective (func_op (id_fun X))) : typeclass_instances.

#[global] Hint Extern 2 (Bijective  (to_localization ?X)) => change (Bijective  (id_fun X)) : typeclass_instances.
#[global] Hint Extern 2 (Injective  (to_localization ?X)) => change (Injective  (id_fun X)) : typeclass_instances.
#[global] Hint Extern 2 (Surjective (to_localization ?X)) => change (Surjective (id_fun X)) : typeclass_instances.
#[global] Hint Extern 2 (WeaklySurjective (func_op (to_localization ?X))) => change (WeaklySurjective (func_op (id_fun X))) : typeclass_instances.


Section filter.
  Context `{Φ:Uniformity X} {𝒜:Bornology X}.
  
  Local Abbreviation S := (@localization_filter X Φ 𝒜).
  
  Local Ltac unfold_S := change (?W ∊ S) with (∏ K:𝒜, ∐ U:Φ, π₁* K ⊓ powerset_pt U ⊆ W).

  Context `{!UniformSpace X}.
  
  Local Instance localization_filter_filter : Filter S.
  Proof. split.
  + apply Build_UpSet. intros W₁ W₂; unfold_S.
    rew <-(aprod_adj _ _ _), <-all_adj; intros K; rew (all_lb _ K), aex_frob_l, <-aex_adj; intros U.
    rew <-(aex_ub _ U). rew (aprod_com _ _). now apply transitivity.
  + apply Build_DownDirectedSubset.
   * exists ⊤. intros K. now exists ⊤.
   * intros W₁ W₂. rew <-(aex_ub _ (W₁ ⊓ W₂)).
     rew (aprod_true_r (meet_lb_r _ _)), (aprod_true_r (meet_lb_l _ _)).
     unfold_S. rew <-all_adj; intros K. rew (all_lb _ K).
     rew <-aex_adj2; intros U V. rew <-(aex_ub _ (U ⊓ V)).
     rew ( order_preserving (⊓) (π₁* K ⊓ powerset_pt U, π₁* K ⊓ powerset_pt V) (W₁, W₂) : _ ⊠ _ ⊸ _).
     rew (associativity (⊓) _ _ _). rew <-(associativity (⊓) _ (powerset_pt U) _).
     rew (commutativity (⊓) (powerset_pt U) (π₁* K)), (associativity (⊓) _ _ _).
     now rew (binary_idempotency (⊓) _), <-(associativity (⊓) _ _ _).
  Qed.
  
  Lemma localization_space : UniformSpace (ℒ X).
  Proof. exact (uniformity_of_filter_space S). Qed.

  Lemma localized_uniformity_sub_semi : localized_uniformity X ⊆ S.
  Proof. exact (uniformity_of_filter_sub S). Qed.
  
  Lemma local_entourage (V:localized_uniformity X) (K:𝒜) : ∐ U:Φ, π₁* K ⊓ powerset_pt U ⊆ V.
  Proof. assert (powerset_pt V ∊ S) as P by now rew <-localized_uniformity_sub_semi. exact (P K). Qed.
End filter.
#[global] Hint Extern 2 (Filter (localization_filter _)) => simple notypeclasses refine localization_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (UpSet (localization_filter _)) => simple notypeclasses refine localization_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (DownDirectedSubset (localization_filter _)) => simple notypeclasses refine localization_filter_filter : typeclass_instances.

(** Two keys for the same instance.  [localization]'s [Φ]/[𝒜] arguments are
    phantoms ([ℒ X ≡ X] definitionally), so unification is free to fill them
    with junk when [ℒ X] occurs inside a term being elaborated — the first
    pattern then fails to match (and also fails while they are unresolved
    evars).  The [Uniformity] slot of the [UniformSpace] goal carries the
    honest data, so the second key matches in those cases; the phantom
    mismatch in the carrier is discharged by conversion. *)
#[global] Hint Extern 2 (UniformSpace (@localization ?X ?Φ ?𝒜)) => simple notypeclasses refine (@localization_space X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (@UniformSpace _ (@localized_uniformity ?X ?Φ ?𝒜)) => simple notypeclasses refine (@localization_space X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (Topology (@localization ?X ?Φ ?𝒜)) => simple notypeclasses refine (@localization_space X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (@Topology _ (@UniformNeighborhood _ (@localized_uniformity ?X ?Φ ?𝒜))) =>
  simple notypeclasses refine (@localization_space X Φ 𝒜 _) : typeclass_instances.


Section universal.
  Universes u.
  Context `{@UniformSpace@{u} X Φ, 𝒜:Bornology X, @UniformSpace@{u} Y Ψ}.
  Local Abbreviation S := (@localization_filter X Φ 𝒜).

  Lemma localized_uc (f:X ⇾ Y) : LocalUniformContinuity f → UniformlyContinuous (f ∘ ε X).
  Proof. intros Hf. apply uniformly_continuous_alt. intros W.
    pose (Ξ := pullback_uniformity f).
    assert (@UniformSpace X Ξ) as HΞ by now unfold Ξ.
    unshelve eexists; [ now exists Ξ |]; unfold subset_pt. split.
    - intros U.
      change (U ∊ Ξ) with (∐ W':Ψ, f♯ W' ⊆ U).
      rew <-aex_adj; intros W'. apply (up_closed_alt S).
      intros K. apply Hf.
    - exists (f♯ W). split; [| easy ]. now exists W.
  Qed.

  Lemma localized_uc_conv (f:X ⇾ Y) : UniformlyContinuous (f ∘ ε X) → LocalUniformContinuity f.
  Proof. intros Hf.
    enough (∀ W:Ψ, f♯ W ∊ S) as P by (intros K W; apply (P W K)).
    intros W. rew <-localized_uniformity_sub_semi.
    exact (subset_pt_is_el (ufm_preimage (f:ℒ X ⇾ Y) W)).
  Qed.

  Lemma localized_uc_conv_alt `{!BornologicalSpace X} (f:X ⇾ Y) : UniformlyContinuous (f ∘ ε X) → LocallyUniformlyContinuous f.
  Proof. intro. split; try exact _; [ now split |]. now apply localized_uc_conv. Qed.
  
  Lemma uc_localized_uc (f:X ⇾ Y) `{!UniformlyContinuous f} : UniformlyContinuous (f ∘ ε X).
  Proof. apply localized_uc. exact uc_local_uc. Qed.
End universal.


Lemma localization_unif_born `{@UnifBornSpace X Φ 𝒜} : UnifBornSpace (ℒ X).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornSpace (ℒ _)) => simple notypeclasses refine localization_unif_born : typeclass_instances.



Lemma from_localization_ufm_cont `{@UniformSpace X Φ} {𝒜:Bornology X} : UniformlyContinuous (ε X).
Proof. exact (uc_localized_uc (id_fun X)). Qed.
#[global] Hint Extern 2 (UniformlyContinuous (ε _)) => simple notypeclasses refine from_localization_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous          (ε _)) => simple notypeclasses refine from_localization_ufm_cont : typeclass_instances.

Lemma from_localization_dense `{@UniformSpace X Φ} {𝒜:Bornology X} : Dense (ε X).
Proof. exact (weakly_surjective_dense _). Qed.
#[global] Hint Extern 2 (Dense (func_op (ε _))) => simple notypeclasses refine from_localization_dense : typeclass_instances.

Lemma from_localization_born_initial `{Φ:Uniformity X} `{@BornologicalSpace X 𝒜} : BornologyInitial (ε X).
Proof. now change (BornologyInitial (id_fun X)). Qed.
#[global] Hint Extern 2 (BornologyInitial    (ε _)) => simple notypeclasses refine from_localization_born_initial : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (ε _)) => simple notypeclasses refine from_localization_born_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (ε _)) => simple notypeclasses refine from_localization_born_initial : typeclass_instances.

Lemma from_localization_mor `{@UnifBornSpace X Φ 𝒜} : UnifBornMorphism (ε X).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (ε _)) => simple notypeclasses refine from_localization_mor : typeclass_instances.


Lemma to_localization_ufm_refl `{@UniformSpace X Φ} {𝒜:Bornology X} : UniformlyReflecting (η X).
Proof. now change (UniformlyReflecting (inverse (ε X))). Qed.
#[global] Hint Extern 2 (UniformlyReflecting    (η _)) => simple notypeclasses refine to_localization_ufm_refl : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (η _)) => simple notypeclasses refine to_localization_ufm_refl : typeclass_instances.

Lemma to_localization_born_initial `{Φ:Uniformity X} `{@BornologicalSpace X 𝒜} : BornologyInitial (η X).
Proof. now change (BornologyInitial (id_fun X)). Qed.
#[global] Hint Extern 2 (BornologyInitial    (η _)) => simple notypeclasses refine to_localization_born_initial : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (η _)) => simple notypeclasses refine to_localization_born_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (η _)) => simple notypeclasses refine to_localization_born_initial : typeclass_instances.

Lemma to_localization_refl `{@UnifBornSpace X Φ 𝒜} : UnifBornReflecting (η X).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornReflecting (η _)) => simple notypeclasses refine to_localization_refl : typeclass_instances.


Lemma to_localization_locally_uc `{@UnifBornSpace X Φ 𝒜} : LocallyUniformlyContinuous (η X).
Proof. split; try exact _. refine (localized_uc_conv (η X) _). now change (η X ∘ ε X) with (id_fun (ℒ X)). Qed.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (η _)) => simple notypeclasses refine to_localization_locally_uc : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformContinuity (η _)) => simple notypeclasses refine to_localization_locally_uc : typeclass_instances.
#[global] Hint Extern 2 (Continuous (η _)) => simple notypeclasses refine to_localization_locally_uc : typeclass_instances.

Lemma to_localization_dense `{@UniformSpace X Φ} {𝒜:Bornology X} : Dense (η X).
Proof. exact (weakly_surjective_dense _). Qed.
#[global] Hint Extern 2 (Dense (func_op (η _))) => simple notypeclasses refine to_localization_dense : typeclass_instances.

Lemma to_localization_locally_emb `{@UnifBornSpace X Φ 𝒜} : LocallyUnifBornEmbedding (η X).
Proof. split; [| exact _ ]. split.
+ now split.
+ exact to_localization_refl.
Qed.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding   (η _)) => simple notypeclasses refine to_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (η _)) => simple notypeclasses refine to_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (η _)) => simple notypeclasses refine to_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (η _)) => simple notypeclasses refine to_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (η _)) => simple notypeclasses refine to_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformReflection     (η _)) => simple notypeclasses refine to_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding      (η _)) => simple notypeclasses refine to_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (η _)) => simple notypeclasses refine to_localization_locally_emb : typeclass_instances.


Lemma from_localization_locally_emb `{@UnifBornSpace X Φ 𝒜} : LocallyUnifBornEmbedding (ε X).
Proof. now change (LocallyUnifBornEmbedding (inverse (η X))). Qed.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding   (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformContinuity     (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformReflection     (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding      (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting     (ε _)) => simple notypeclasses refine from_localization_locally_emb : typeclass_instances.

(** Over a trivial bornology the localization collapses: [η] (always
    uniformly reflecting) becomes uniformly continuous, and dually [ε]
    (always uniformly continuous) becomes uniformly reflecting, so
    [ℒ X ≅ X] as uniform spaces. *)
Lemma to_localization_trivial_uc `{@UniformSpace X Φ} {𝒜:Bornology X} `{!TrivialBornology 𝒜}
  : UniformlyContinuous (η X).
Proof. split; try exact _. intros V.
  pose proof (local_entourage V (to_subset ⊤ (el:=trivial_bornology_bounded ⊤))) as [U HU].
  exists U. intros x y.
  change (near U x y ⊸ (x, y) ∊ powerset_pt V). rew <-HU.
  change (near U x y ⊸ 𝐓 ∧ near U x y). tautological.
Qed.


Lemma from_localization_trivial_ur `{@UniformSpace X Φ} {𝒜:Bornology X} `{!TrivialBornology 𝒜}
  : UniformlyReflecting (ε X).
Proof. pose proof (to_localization_trivial_uc (𝒜:=𝒜)).
  now change (UniformlyReflecting (inverse (η X))).
Qed.
(** Keyed on the literal [trivial_bornology] instance — never spawn a
    [TrivialBornology] search on an arbitrary bornology (it self-loops through
    the SubClass identity instance). *)
#[global] Hint Extern 2 (UniformlyContinuous (@to_localization ?X ?Φ (trivial_bornology ?K))) => simple notypeclasses refine (@to_localization_trivial_uc X Φ _ (trivial_bornology K) _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (@from_localization ?X ?Φ (trivial_bornology ?K))) => simple notypeclasses refine (@from_localization_trivial_ur X Φ _ (trivial_bornology K) _) : typeclass_instances.

(** Under a trivial bornology the ⊤-cylinder is a box, so the local classes
    collapse to the global ones — and the Dense-walled recast direction of
    [localized_ur] is free. *)

Lemma local_uc_trivial `{@UniformSpace X Φ} {𝒜:Bornology X} `{!TrivialBornology 𝒜}
  `{@UniformSpace Y Ψ} (f:X ⇾ Y) : LocalUniformContinuity f → UniformlyContinuous f.
Proof. intros P.
  pose proof (localized_uc f P). pose proof (to_localization_trivial_uc (𝒜:=𝒜)).
  now change (UniformlyContinuous ((f ∘ ε X) ∘ η X)).
Qed.

Lemma local_ur_trivial `{@UniformSpace X Φ} `{@UniformSpace Y Ψ} {ℬ:Bornology Y}
  `{!TrivialBornology ℬ} (f:X ⇾ Y) : LocalUniformReflection f → UniformlyReflecting f.
Proof. intros P. split; try exact _. intros U.
  destruct (P (to_subset ⊤ (el:=trivial_bornology_bounded ⊤)) U) as [W HW].
  exists W. intros x y.
  change (near W (f x) (f y) ⊸ (x, y) ∊ powerset_pt U). rew <-HW.
  change (near W (f x) (f y) ⊸ 𝐓 ∧ near W (f x) (f y)). tautological.
Qed.

Lemma localized_ur_trivial `{@UniformSpace X Φ} `{@UniformSpace Y Ψ} {ℬ:Bornology Y}
  `{!TrivialBornology ℬ} (f:X ⇾ Y) : LocalUniformReflection f → UniformlyReflecting (η Y ∘ f).
Proof. intros P.
  pose proof (local_ur_trivial f P). pose proof (to_localization_ufm_refl (X:=Y)).
  exact _.
Qed.


Lemma localized_separation `{@SeparatedUniformSpace X Φ} {𝒜:Bornology X}
  : SeparatedUniformSpace (ℒ X).
Proof. exact (uniform_reflects_hausdorff (ε X)). Qed.
#[global] Hint Extern 2 (@SeparatedUniformSpace _ (@localized_uniformity ?X ?Φ ?𝒜))
  => simple notypeclasses refine (@localized_separation X Φ _ 𝒜) : typeclass_instances.

(** ℒ preserves well-containment: transport the WCUnif axiom along the
    counit ε ([unif_born/base.v : wcunif_transport] — ε is uniformly
    continuous and carrier-identical on the bornology). *)
Lemma localized_wcunif `{@WCUnifSpace X Φ 𝒜} : WCUnifSpace (ℒ X).
Proof. pose proof (_ : BornologyInitial (id_fun X)). exact (wcunif_transport (ε X)). Qed.
#[global] Hint Extern 2 (@WCUnifSpace _ (@localized_uniformity ?X ?Φ ?𝒜) _)
  => simple notypeclasses refine (@localized_wcunif X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifSpace (ℒ _)) => simple notypeclasses refine localized_wcunif : typeclass_instances.


Lemma localized_ur_conv@{u} `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ} {ℬ:Bornology Y} (f:X ⇾ Y)
  : UniformlyReflecting (η Y ∘ f) → LocalUniformReflection f.
Proof. intros Hf L U.
  pose proof ufm_reflection_alt (η Y ∘ f) U as [E HE].
  pose proof local_entourage E L as [W HW]. exists W. now rew HW.
Qed.

Lemma localized_ur_conv_alt@{u} `{@UniformSpace@{u} X Φ, @UnifBornSpace@{u} Y Ψ ℬ} (f:X ⇾ Y)
  : UniformlyReflecting (η Y ∘ f) → LocallyUniformlyReflecting f.
Proof. intro. split; try exact _. now apply localized_ur_conv. Qed.

Section unif_born_conv.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ} (f:X ⇾ Y).

  Lemma localized_unif_born_conv : UnifBornMorphism (f ∘ ε X) → LocallyUnifBorn f.
  Proof. intros Hf. split.
  + now apply localized_uc_conv_alt.
  + now change f with (f ∘ ε X).
  Qed. 

  Lemma localized_unif_born_refl_conv : UnifBornReflecting (η Y ∘ f) → LocallyUnifBornReflecting f.
  Proof. intros Hf. split.
  + now apply localized_ur_conv_alt.
  + now change f with (η Y ∘ f).
  Qed. 

  Lemma localized_unif_born_initial_conv : UnifBornMorphism (f ∘ ε X) → UnifBornReflecting (η Y ∘ f) → LocallyUnifBornInitial f.
  Proof. intros ??; split.
  + now apply localized_unif_born_conv.
  + now apply localized_unif_born_refl_conv.
  Qed.
End unif_born_conv.


#[local] Hint Extern 0 (Neighborhood _) => exact UniformNeighborhood : typeclass_instances.

Local Abbreviation int := interior.
Local Abbreviation cl := closure.

Section localized_ur.
  Universes u.
  Context `{@LocallyUniformlyReflecting X Y Φ Ψ ℬ f, !WCUnifSpace Y, !Dense f}.

  Lemma band_fill (R:Φ) : id_rel Y ⊆ int (cl (f♭ (int R))).
  Proof.
    intros [x y].
    pose proof (wcunif_thicken Y (born_pt y)) as [W₀ HW₀].
    pose proof (local_uniform_reflection f (@to_subset _ ℬ _ HW₀) (@to_subset _ Φ _ (interior_entourage R))) as [W PW];
      change (apos (f♯ (π₁* W₀.[powerset_pt (born_pt y)] ⊓ powerset_pt W) ⊆ int R)) in PW.
    pose proof (cylinder_sub_interior (powerset_pt (born_pt y)) W₀ W) as [V P].
    rew <-PW, <-(dense_interior_closure_unit ⟨f,f⟩ _), (idempotent_alt int _), <-P.
    change ( x = y ⊸ y = x ∧ near V x y ); apply aand_intro.
    + now apply symmetry.
    + exact (near_refl_alt x y V).
  Qed.    

  (** Transitivity of the band filter, ∐-packaged like [band_fill]'s
      reflexivity: fill the junction with the band ([band_fill] feeding
      [closure_compose_thicken]), pull the middle through the image,
      counit it away ([reflection_preimage_closure]), then interior
      arithmetic on the sym5 split. *)
  Lemma band_compose (R:Φ) : ∐ S:Φ, cl (f♭ (int S)) ⋄ cl (f♭ (int S)) ⊆ cl (f♭ (int R)).
  Proof. pose proof (uniform_split_sym5 R) as [S [ES PS]]. exists S.
    rew (closure_compose_thicken_alt (f♭ (int S)) (cl (f♭ (int S))) (f♭ (int S)) (band_fill S)).
    rew (image_compose_middle _ _ _ _ _ _ _).
    rew (reflection_preimage_closure ⟨f,f⟩ (int S)).
    enough (int S ⋄ cl (int S) ⋄ int S ⊆ int R) as HM by now rew HM.
    rew (int_compose_both _ _ _).
    apply (order_preserving int).
    rew (closure_subset_thicken (int S) S).
    rew [ES | (interior_subset S)].
    change (S ∙ (S ∙ S ∙ S) ∙ S ≤ R).
    now rew !(associativity (∙) _ _ _).
  Qed.
    

  Definition localized_ur_witness := {V:𝒫 (Y ⊗ Y) | ∐ R:Φ, cl (f♭ (int R)) ⊆ V}.
  Local Abbreviation Ξ := localized_ur_witness.
  
  Local Instance localized_ur_witness_pre_uniform : @PreUniformSpace Y Ξ.
  Proof. split; try exact _.
  + intros V. change ((∐ R:Φ, cl (f♭ (int R)) ⊆ V) ⊸ id_rel Y ⊆ V). rew <-aex_adj; intros R.
    enough (id_rel Y ⊆ cl (f♭ (int R))) as Hr by now rew Hr.
    now rew (band_fill R).
  + intros V. change ((∐ R:Φ, cl (f♭ (int R)) ⊆ V) ⊸ (∐ R:Φ, cl (f♭ (int R)) ⊆ V⁻¹)).
    rew <-aex_adj; intros R. rew <-(aex_ub _ (R⁻¹)).
    rew (interior_inv_alt R), <-(flip_image_tensor_map_alt f f (int R)), (closure_inv_alt (f♭ (int R))).
    exact (order_preserving inv _ _).
    + intros [U [R HR]]. pose proof (band_compose R) as [S HB]. unshelve eexists.
    * unshelve esplit; [ exact (cl (f♭ (int S))) | ].
      change (∐ S':Φ, cl (f♭ (int S')) ⊆ cl (f♭ (int S))). now rew <-(aex_ub _ S).
    * change (cl (f♭ (int S)) ⋄ cl (f♭ (int S)) ⊆ U). now rew HB.
  Qed.

  Local Instance pushforward_entourage_aux (R:Φ) : cl (f♭ (int R)) ∊ localization_filter Y.
  Proof. intros K.
    pose proof (wcunif_thicken Y K) as [W₀ HW₀].
    pose proof local_uniform_reflection f (@to_subset _ _ _ HW₀) (@to_subset _ Φ _ (interior_entourage R)) as [W PW];
      change (apos (f♯ (π₁* W₀.[powerset_pt K] ⊓ powerset_pt W) ⊆ int R)) in PW.
    pose proof (cylinder_sub_interior (powerset_pt K) W₀ W) as [V P]; exists V; rew P; clear P.
    rew (dense_interior_closure_unit ⟨f,f⟩ _).
    now rew PW.
  Qed.

  Local Instance pushforward_entourage_prop (R:Φ) : cl (f♭ (int R)) ∊ localized_uniformity Y.
  Proof. unshelve eexists.
  + unshelve esplit; [ exact Ξ | exact  localized_ur_witness_pre_uniform ].
  + unfold subset_pt. split.
    * clear R. intros V. change ((∐ R:Φ, cl (f♭ (int R)) ⊆ V) ⊸ V ∊ localization_filter Y). rew <-aex_adj; intros R.
      now apply up_closed_alt.
    * rew <-(aex_ub _ (cl (f♭ (int R)))). split; [ now exists R | easy ].
  Qed.
  
  Definition pushforward_entourage (R:Φ) : localized_uniformity Y := to_subset (cl (f♭ (int R))).
  
  Lemma localized_ur : UniformlyReflecting (η Y ∘ f).
  Proof. change (η Y ∘ f) with f. split; try exact _. apply uniform_reflection_alt.
    intros U. pose proof (uniform_split_sym3 U) as [R [ER PR]].
    exists (pushforward_entourage R); change (f♯ (cl (f♭ (int R))) ⊆ U).
    rew (reflection_preimage_closure ⟨f,f⟩ (int R)).
    now rew (closure_subset_thicken _ R), (interior_subset _), ER.
  Qed.
End localized_ur.


(** Localizing the codomain of the intrinsic condition costs [Bornological]:
    the codomain lift of the comonad. *)
Lemma local_uc_localize_codomain@{u} {X Y:set@{u}} {Φ:Uniformity X} {𝒜:Bornology X} `{@UnifBornSpace@{u} Y Ψ ℬ}
  (f:X ⇾ Y) `{!Bornological f}
  : LocalUniformContinuity f → LocalUniformContinuity (η Y ∘ f).
Proof. intros Hf K V.
  pose proof local_entourage V (born_image f K) as [U HU]; change ( apos (π₁* (f⁎ K) ⊓ powerset_pt U ⊆ V) ) in HU.
  pose proof Hf K U as [U' HU'].
  exists U'. rew (meet_le_meet_l_alt HU'). intros [x x'].
  change (x ∊ K ∧ near U (f x) (f x') ⊸ (f x, f x') ∊ powerset_pt V).
  rew <-HU.
  change ((f x, f x') ∊ π₁* (f⁎ K) ⊓ powerset_pt U) with (f x ∊ f⁎ K ∧ near U (f x) (f x')).
  now rew <-(image_el f _ _).
Qed.

Lemma localize_functorial@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ} (f:ℒ X ⇾ Y)
  `{!UniformlyContinuous f} `{!Bornological f}
  : UniformlyContinuous (η Y ∘ f).
Proof. change (η Y ∘ f) with f.
  now apply localized_uc, (local_uc_localize_codomain (f:X ⇾ Y)), (localized_uc_conv (f:X ⇾ Y)).
Qed.

Lemma localize_functorial_alt@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ} (f:X ⇾ Y)
  `{!LocallyUnifBorn f} : UnifBornMorphism (η Y ∘ f ∘ ε X).
Proof. split; try exact _. refine (localize_functorial (f ∘ ε X)). now apply localized_uc. Qed.

(** Localizing the domain of the intrinsic reflecting condition costs
    [BornologyReflecting]: the domain lift of the monad. *)
Lemma local_ur_localize_domain@{u} {X Y:set@{u}} `{@UnifBornSpace@{u} X Φ 𝒜} {Ψ:Uniformity Y} {ℬ:Bornology Y}
  (f:X ⇾ Y) `{!BornologyReflecting f}
  : LocalUniformReflection f → LocalUniformReflection (f ∘ ε X).
Proof. intros Hf L U.
  pose proof local_entourage U (born_preimage f L) as [U_K HU_K].
  destruct (Hf L U_K) as [W HW].
  exists W. change (f ∘ ε X) with f. rew <-HU_K.
  apply meet_glb; split; trivial. now rew (meet_lb_l _ _).
Qed.

Lemma localize_functorial_refl@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ} (f:X ⇾ Y)
  `{!Dense f} `{!BornologyReflecting f}
  (Hf : UniformlyReflecting (η Y ∘ f))
  : UniformlyReflecting (η Y ∘ f ∘ ε X).
Proof.
  pose proof (local_ur_localize_domain f (localized_ur_conv f Hf)) as P.
  assert (LocallyUniformlyReflecting (f : ℒ X ⇾ Y)) by now split.
  exact (localized_ur (f:=(f : ℒ X ⇾ Y))).
Qed.

Lemma localize_functorial_refl_alt@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ} (f:X ⇾ Y)
  `{!LocallyUnifBornReflecting f, !Dense f} : UnifBornReflecting (η Y ∘ f ∘ ε X).
Proof. split; try exact _. refine (localize_functorial_refl f _). now apply localized_ur. Qed.

Lemma localize_functorial_initial_alt@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ} (f:X ⇾ Y)
  `{!LocallyUnifBornInitial f, !Dense f} : UnifBornInitial (η Y ∘ f ∘ ε X).
Proof. split.
+ now apply localize_functorial_alt.
+ now apply localize_functorial_refl_alt.
Qed.


(** * The intrinsic dense-initial descent

    The [ufm_dense_local_reflection] family ([unif_born/local_maps.v]) with
    *both* legs weakened to the all-local classes, as corollaries through
    the comonad.  The [f]-leg: [localized_uc] upgrades a locally uniformly
    continuous [f] to the globally uniformly continuous lift [f ∘ ε X], and
    the descent's conclusion never mentions the domain, so the localization
    is invisible.  The [g]-leg (bornology component): lift the middle space
    to [ℒ Y] — the [f]-leg becomes [η Y ∘ f ∘ ε X], whose density is free
    ([to_localization_dense]: [η] is carrier-identity, so density survives
    the finer localized topology by weak surjectivity), and [g ∘ ε Y] is
    globally uniformly continuous by [localized_uc].  The uniform component
    needs no lift at all: the int/cl-chain proof consumes [g] only through
    [continuous_preimage_interior], so [Continuous g] suffices. *)

Section dense_descent.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜}.

  Local Instance dense_local_reflection {Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
    `{@UniformSpace@{u} Y Ψ} `{@UnifBornSpace@{u} Z Ξ 𝒵, !WCUnifSpace Z}
    `{!LocalUniformContinuity f, !Dense f}
    `{!Continuous g}
    `{!LocalUniformReflection (g ∘ f), !BornologyReflecting (g ∘ f)}
    : LocalUniformReflection g.
  Proof.
    pose proof (localized_uc f _).
    pose proof (local_ur_localize_domain (g ∘ f) _).
    refine (ufm_dense_local_reflection (f ∘ ε X) g); exact _.
  Qed.

  Local Instance dense_bornology_reflecting {Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
    `{@UnifBornSpace@{u} Y Ψ ℬ, !WCUnifSpace Y} `{@UnifBornSpace@{u} Z Ξ 𝒵, !WCUnifSpace Z}
    `{!LocallyUnifBorn f, !Dense f}
    `{!LocallyUniformlyContinuous g}
    `{!BornologyReflecting (g ∘ f)}
    : BornologyReflecting g.
  Proof.
    pose proof (localize_functorial_alt f).
    pose proof (localized_uc g _).
    exact (ufm_dense_bornology_reflecting (η Y ∘ f ∘ ε X) (g ∘ ε Y)).
  Qed.

  Lemma dense_locally_initial {Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
    `{@UnifBornSpace@{u} Y Ψ ℬ, !WCUnifSpace Y} `{@UnifBornSpace@{u} Z Ξ 𝒵, !WCUnifSpace Z}
    `{!LocallyUnifBorn f, !Dense f}
    `{!LocallyUnifBorn g}
    `{!LocallyUnifBornReflecting (g ∘ f)}
    : LocallyUnifBornInitial g.
  Proof. repeat (split; try exact _). Qed.
End dense_descent.


Lemma localization_filter_idempotent@{u} `{@UnifBornSpace@{u} X Φ 𝒜} : localization_filter (ℒ X) = localization_filter X.
Proof. rew <-(le_antisym_iff _ _). split.
- intros V. change (V ∊ localization_filter (Φ:=?Φ) _) with (∏ K:𝒜, ∐ U:Φ, π₁* K ⊓ powerset_pt U ⊆ V).
  rew <-all_adj; intros K. rew (all_lb _ K). rew <-aex_adj; intros U'.
  pose proof local_entourage U' K as [U'' HU''].
  rew <-(aex_ub _ U''). now rew (meet_le_meet_l_alt HU'').
- intros V. change (V ∊ localization_filter (Φ:=?Φ) _) with (∏ K:𝒜, ∐ U:Φ, π₁* K ⊓ powerset_pt U ⊆ V).
  rew <-all_adj; intros K. rew (all_lb _ K). rew <-aex_adj; intros U.
  let U' := constr:(ufm_preimage (ε X) U) in now rew <-(aex_ub _ U').
Qed.

Lemma localized_uniformity_idempotent@{u} `{@UnifBornSpace@{u} X Φ 𝒜}
  : localized_uniformity (ℒ X) = localized_uniformity X.
Proof. unfold localized_uniformity at 1 3. now rew localization_filter_idempotent. Qed.


Lemma localization_idempotent@{u} `{@UnifBornSpace@{u} X Φ 𝒜} : UniformlyContinuous (η (ℒ X)).
Proof. apply (localized_uc (η (ℒ X) : X ⇾ ℒ (ℒ X))). intros K W.
  pose proof local_entourage (X:=ℒ X) W K as [U' HU'].
  pose proof local_entourage U' K as [U HU].
  exists U.
  change ((η (ℒ X))♯ (powerset_pt W)) with (powerset_pt W).
  now rew (meet_le_meet_l_alt HU).
Qed.
#[global] Hint Extern 2 (UniformlyContinuous (Φ:=@localized_uniformity ?X ?Φ ?𝒜) (η (ℒ _))) => simple notypeclasses refine (@localization_idempotent X Φ 𝒜 _) : typeclass_instances.

Lemma to_localization_idempotent_ub_embedding@{u} `{@UnifBornSpace@{u} X Φ 𝒜}
  : UnifBornEmbedding (η (ℒ X)).
Proof. repeat (split; try exact _). Qed.
#[global] Hint Extern 2 (UnifBornEmbedding  (Φ:=@localized_uniformity ?X ?Φ ?𝒜) (η (ℒ _))) => simple notypeclasses refine (@to_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial    (Φ:=@localized_uniformity ?X ?Φ ?𝒜) (η (ℒ _))) => simple notypeclasses refine (@to_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism   (Φ:=@localized_uniformity ?X ?Φ ?𝒜) (η (ℒ _))) => simple notypeclasses refine (@to_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding (Φ:=@localized_uniformity ?X ?Φ ?𝒜) (η (ℒ _))) => simple notypeclasses refine (@to_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial   (Φ:=@localized_uniformity ?X ?Φ ?𝒜) (η (ℒ _))) => simple notypeclasses refine (@to_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.

Lemma from_localization_idempotent_ub_embedding@{u} `{@UnifBornSpace@{u} X Φ 𝒜}
  : UnifBornEmbedding (ε (ℒ X)).
Proof. now change (UnifBornEmbedding (inverse (η (ℒ X)))). Qed.
#[global] Hint Extern 2 (UnifBornEmbedding   (Ψ:=@localized_uniformity ?X ?Φ ?𝒜) (ε (ℒ _))) => simple notypeclasses refine (@from_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial     (Ψ:=@localized_uniformity ?X ?Φ ?𝒜) (ε (ℒ _))) => simple notypeclasses refine (@from_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting  (Ψ:=@localized_uniformity ?X ?Φ ?𝒜) (ε (ℒ _))) => simple notypeclasses refine (@from_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (Ψ:=@localized_uniformity ?X ?Φ ?𝒜) (ε (ℒ _))) => simple notypeclasses refine (@from_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding  (Ψ:=@localized_uniformity ?X ?Φ ?𝒜) (ε (ℒ _))) => simple notypeclasses refine (@from_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (Ψ:=@localized_uniformity ?X ?Φ ?𝒜) (ε (ℒ _))) => simple notypeclasses refine (@from_localization_idempotent_ub_embedding X Φ 𝒜 _) : typeclass_instances.

Lemma from_localization_idempotent@{u} `{@UnifBornSpace@{u} X Φ 𝒜}
  : UniformlyReflecting (ε (ℒ X)).
Proof. exact _. Qed.

