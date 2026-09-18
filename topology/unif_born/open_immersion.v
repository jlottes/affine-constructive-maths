(** The open immersion construction (doc/wcunif.md): a pair (X, S) of a
    UnifBorn space and an open subset yields the subspace carrier with the
    pullback uniformity and the well-containment bornology
    [{K | ι⁎K ∊ 𝒜 ∧ ι⁎K ◁ S}] — bounded sets are the ambient-bounded sets
    uniformly inside S, so the immersion "remembers the boundary".  The
    inclusion is a uniform embedding and bornological, but deliberately NOT
    bornology-reflecting. *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base topology.uniform.uniformly_below.
Require Import uniform.basis uniform.subspace.
Require Import bornology.base bornology.subspace.
Require Import unif_born.base unif_born.local_maps unif_born.well_contained.
Require Import easy rewrite replc simplify strip_coercions tactics.misc.

Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Local Open Scope subset_scope.

Import thicken_notation.
Import image_notation.
Import tensor_map_notation.

Local Abbreviation id := (id_fun _).
Local Abbreviation int := interior.
Local Abbreviation cl := closure.

(** The bornology of well-contained sets, [𝒲 S]. *)
Definition open_immersion_bornology {X:set} {Φ:Uniformity X} {𝒜:Bornology X} (S:𝒫 X) : Bornology S
  := { K : 𝒫 S | (from_subset S)⁎ K ∊ 𝒜 ∧ (from_subset S)⁎ K ◁ S }.
Local Abbreviation 𝒲 := open_immersion_bornology.

(** The open immersion as a phantom carrier (cf. [localization]): [𝒪 S] — via
    [Local Abbreviation 𝒪 := (open_immersion X)] — is the subset carrier [S]
    with the pullback uniformity and the well-containment bornology [𝒲 S]
    keyed on the name. *)
Definition open_immersion {X:set} {Φ:Uniformity X} {𝒜:Bornology X} (S:𝒫 X) : set := S.
Global Typeclasses Opaque open_immersion.
Local Abbreviation 𝒪 := open_immersion.

#[global] Hint Extern 0 (Uniformity (@open_immersion ?X ?Φ ?𝒜 ?S)) => exact (pullback_uniformity (from_subset S)) : typeclass_instances.
#[global] Hint Extern 0 (Bornology (@open_immersion ?X ?Φ ?𝒜 ?S)) => exact (@open_immersion_bornology X Φ 𝒜 S) : typeclass_instances.

Definition from_open_immersion {X:set} {Φ:Uniformity X} {𝒜:Bornology X} (S:𝒫 X)
  : 𝒪 S ⇾ X := from_subset S.
Local Abbreviation j := from_open_immersion.

Local Instance open_immersion_incl_unif_emb `{@UniformSpace X Φ} {𝒜:Bornology X} {S:𝒫 X} : UniformlyEmbedding (j S).
Proof. now unfold j. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding  (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.

#[global] Hint Extern 2 (Injective (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (YN:=UniformNeighborhood) (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (YN:=UniformNeighborhood) (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.
#[global] Hint Extern 2 (Continuous             (YN:=UniformNeighborhood) (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (YN:=UniformNeighborhood) (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_unif_emb X Φ _ 𝒜 S) : typeclass_instances.

Section open_immersion.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜} (S : 𝒫 X).
  Local Abbreviation ι := (from_subset S).

  Local Ltac unfold_B := change (?K ∊ 𝒲 _) with (ι⁎ K ∊ 𝒜 ∧ ι⁎ K ◁ S).

  Local Instance open_immersion_bornology_ideal : Ideal (𝒲 S).
  Proof. apply Build_Ideal.
  + apply Build_DownSet. intros K K'. unfold_B.
    rew (order_preserving ι⁎ K K').
    rew <-(aprod_adj _ _ _). apply aand_intro.
    * rew (aandl _ _). rew (aprod_adj _ _ _). exact (down_closed 𝒜 _ _).
    * rew (aandr _ _). exact (unif_below_le_l _ _ _).
  + apply Build_UpDirectedSubset.
    * exists ⊥. unfold_B. rew (preserves_bottom ι⁎). split.
      - exact sub_bot_closed.
      - exact (unif_below_empty S).
    * intros K K'. rew <-(aex_ub _ (K ⊔ K')). unfold_B.
      rew (preserves_join ι⁎ K K').
      rew (aprod_true_r (join_ub_r K K')), (aprod_true_r (join_ub_l K K')).
      apply aand_intro.
      - rew [(aandl _ _)|(aandl _ _)]. exact (sub_join_closed _ _).
      - rew [(aandr _ _)|(aandr _ _)]. exact (unif_below_join _ _ _).
  Qed.

  Local Instance open_immersion_incl_locally_ur : LocallyUniformlyReflecting (j S).
  Proof. unfold j. exact ur_locally_ur. Qed.

  Context {HS:open S}.

  Local Instance open_immersion_born_space : BornologicalSpace (𝒪 S).
  Proof. apply Build_BornologicalSpace; [ exact open_immersion_bornology_ideal |].
    intros x. unfold_B.
    assert (ι x ∊ interior S) as el by now rew (HS : interior S = S).
    rew (image_singleton_alt ι x). split.
    * exact (bornology_singleton _).
    * exact (singleton_unif_below _ _).
  Qed.

  Local Instance open_immersion_unif_born : UnifBornSpace (𝒪 S).
  Proof. now split. Qed.

  Local Instance open_immersion_incl_bornological : Bornological (j S).
  Proof. split; try exact _. intros A. exact (andl (subset_pt_is_el A)). Qed.

  Local Instance open_immersion_incl_unif_born : UnifBornMorphism (j S).
  Proof. now split. Qed.

  Local Instance open_immersion_incl_locally_ub : LocallyUnifBorn (j S).
  Proof. split; try exact _. unfold j. exact uc_locally_uc. Qed.
End open_immersion.
#[global] Hint Extern 2 (@BornologicalSpace _ (@open_immersion_bornology ?X ?Φ ?𝒜 ?S))
  => simple notypeclasses refine (@open_immersion_born_space X Φ 𝒜 _ S _) : typeclass_instances.
#[global] Hint Extern 2 (@UnifBornSpace _ (pullback_uniformity (Ψ:=?Φ) (from_subset ?S)) (@open_immersion_bornology ?X ?Φ ?𝒜 ?S))
  => simple notypeclasses refine (@open_immersion_unif_born X Φ 𝒜 _ S _) : typeclass_instances.

#[global] Hint Extern 2 (Bornological (@from_open_immersion ?X ?Φ ?𝒜 ?S))
  => simple notypeclasses refine (@open_immersion_incl_bornological X Φ 𝒜 _ S _) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism (@from_open_immersion ?X ?Φ ?𝒜 ?S))
  => simple notypeclasses refine (@open_immersion_incl_unif_born X Φ 𝒜 _ S _) : typeclass_instances.

#[global] Hint Extern 2 (LocallyUniformlyContinuous (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_locally_ub X Φ 𝒜 _ S _) : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformContinuity (@from_open_immersion ?X ?Φ ?𝒜 ?S))     => simple notypeclasses refine (@open_immersion_incl_locally_ub X Φ 𝒜 _ S _) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_locally_ur X Φ 𝒜 _ S) : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformReflection (@from_open_immersion ?X ?Φ ?𝒜 ?S))     => simple notypeclasses refine (@open_immersion_incl_locally_ur X Φ 𝒜 _ S) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn (@from_open_immersion ?X ?Φ ?𝒜 ?S))            => simple notypeclasses refine (@open_immersion_incl_locally_ub X Φ 𝒜 _ S _) : typeclass_instances.

Section open_immersion.
  Universes u.
  Context `{@WCUnifSpace@{u} X Φ 𝒜} (S : 𝒫 X) {HS:open S}.
  Local Abbreviation ι := (from_subset S).

  Local Instance open_immersion_wcunif : WCUnifSpace (𝒪 S).
  Proof. split; try exact _. intros A.
    pose proof (subset_pt_is_el A) as [HAb HA].
    pose (A' := to_subset (U:=𝒜) (ι⁎ A)).
    assert (A' ⋐ S) as HA' by assumption.
    rew (wc_interpolate _ _) in HA'. destruct HA' as [L [[U HL1] HL2]].
    unshelve eexists.
    + unshelve esplit. exact (ufm_preimage ι U). now exists U.
    + change ((ufm_preimage ι U).[powerset_pt A] ∊ 𝒲 S).
      split; now rew (image_thicken_uc_le ι U _), HL1.
  Qed.
  
  Lemma open_immersion_incl_wcunif_mor : WCUnifMorphism (j S).
  Proof. now split. Qed.
End open_immersion.

#[global] Hint Extern 2 (WCUnifSpace (@open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_wcunif X Φ 𝒜 _ S _) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifMorphism (@from_open_immersion ?X ?Φ ?𝒜 ?S)) => simple notypeclasses refine (@open_immersion_incl_wcunif_mor X Φ 𝒜 _ S _) : typeclass_instances.

Definition open_immersion_restrict@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}
  (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T} : 𝒪 S ⇾ 𝒪 T := restrict f S T (H:=H:MapsTo f S T).

Local Abbreviation 𝒪₁ := open_immersion_restrict.

Lemma open_immersion_natural@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}
  (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T}
  : j T ∘ 𝒪₁ f S T = f ∘ j S.
Proof. refl. Qed.

Lemma open_immersion_compose@{u} {X Y Z:set@{u}}
  {Φ:Uniformity X} {Ψ:Uniformity Y} {Ξ:Uniformity Z}
  {𝒜:Bornology X} {ℬ:Bornology Y} {𝒞:Bornology Z}
  (g:Y ⇾ Z) (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) (V:𝒫 Z)
  {HST:S ⊆ f* T} {HTV:T ⊆ g* V} {HSV:S ⊆ (g ∘ f)* V}
  :  𝒪₁ (g ∘ f) S V =  𝒪₁ g T V ∘  𝒪₁ f S T .
Proof. refl. Qed.

#[global] Hint Extern 8 (apos (?A ≤ (func_op id*) ?B)) => change (A ⊆ B) : typeclass_instances.

Lemma open_immersion_id@{u} {X:set@{u}} {Φ:Uniformity X} {𝒜:Bornology X} (S:𝒫 X)
  :  𝒪₁ id S S = id .
Proof. refl. Qed.

Section restrict_classes.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}.
  Context (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T}.

  Local Instance open_immersion_restrict_ufm_cont `{!UniformlyContinuous f} : UniformlyContinuous (𝒪₁ f S T).
  Proof. apply pullback_uniformity_initial. now change (UniformlyContinuous (f ∘ j S)). Qed.

  Local Instance open_immersion_restrict_ufm_refl `{!UniformlyReflecting f} : UniformlyReflecting (𝒪₁ f S T).
  Proof. apply (ufm_refl_factor _ (j T)). now change (UniformlyReflecting (f ∘ j S)). Qed.

  Local Instance open_immersion_restrict_ufm_initial `{!UniformlyInitial f} : UniformlyInitial (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_ufm_emb `{!UniformlyEmbedding f} : UniformlyEmbedding (𝒪₁ f S T).
  Proof. split; try exact _.
    apply (injective_factor _ (j T)). now change (Injective (f ∘ j S)).
  Qed.
End restrict_classes.

#[global] Hint Extern 2 (UniformlyContinuous (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_ufm_cont X Y Φ Ψ 𝒜 ℬ f S T H _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_ufm_refl X Y Φ Ψ 𝒜 ℬ f S T H _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_ufm_initial X Y Φ Ψ 𝒜 ℬ f S T H _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_ufm_emb X Y Φ Ψ 𝒜 ℬ f S T H _) : typeclass_instances.
#[global] Hint Extern 2 (Injective (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_ufm_emb X Y Φ Ψ 𝒜 ℬ f S T H _) : typeclass_instances.

Section restrict_locally.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}.
  Context `{!UnifBornSpace X} `{!UnifBornSpace Y}.
  Context (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T}.

  Local Instance open_immersion_restrict_local_uc {HS:open S} `{!LocalUniformContinuity f} : LocalUniformContinuity (𝒪₁ f S T).
  Proof. apply (local_uc_factor _ (j T)).
    change (LocalUniformContinuity (f ∘ j S)).
    apply local_uc_compose; exact _.
  Qed.

  Local Instance open_immersion_restrict_local_ur {HT:open T} `{!LocalUniformReflection f} : LocalUniformReflection (𝒪₁ f S T).
  Proof. apply (local_ur_factor _ (j T)).
    change (LocalUniformReflection (f ∘ j S)).
    apply local_ur_compose_ur; exact _.
  Qed.

  Local Instance open_immersion_restrict_locally_uc {HS:open S} `{!LocallyUniformlyContinuous f} : LocallyUniformlyContinuous (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_locally_ur {HT:open T} `{!LocallyUniformlyReflecting f} : LocallyUniformlyReflecting (𝒪₁ f S T).
  Proof. now split. Qed.
End restrict_locally.

#[global] Hint Extern 2 (LocalUniformContinuity (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_local_uc X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _) : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformReflection (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_local_ur X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_locally_uc X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_locally_ur X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _) : typeclass_instances.

Section restrict_dense.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}.
  Context `{!UniformSpace Y}.
  Context (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T} {E:f* T ⊆ S}.

  Lemma open_immersion_restrict_dense {HT:open T} `{!Dense f} : Dense (𝒪₁ f S T).
  Proof. exact (dense_open_restrict f S T). Qed.
End restrict_dense.


Section restrict_born_refl.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}.
  Context `{!UnifBornSpace X} `{!UnifBornSpace Y}.
  Context (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T} {E:f* T ⊆ S}.

  Local Abbreviation ι := from_subset.

  Let HS_from_E : Continuous f → open T → open S.
  Proof. intros ??.
    assert (S = f* T) as E' by now apply (le_antisym (X:=𝒫 X)).
    rew E'. now apply (continuity_alt f).
  Qed.
  #[local] Hint Extern 4 (apos (open S)) => simple notypeclasses refine (HS_from_E _ _) : typeclass_instances.

  Lemma open_immersion_restrict_born_refl {HT:open T}
    `{!UniformlyContinuous f, !BornologyReflecting f} : BornologyReflecting (𝒪₁ f S T).
  Proof. split; try exact _. intros L.
    pose (L' := @to_subset _ _ ((ι T)⁎ L) (andl (subset_pt_is_el L))).
    pose proof andr (subset_pt_is_el L) : L' ⋐ T as HL'.
    rew <-(injective_preimage_image_alt _ _ : (ι T)* L' = powerset_pt L).
    change ((ι S)* (f* L') ∊ 𝒲 S).
    split; rew (image_preimage_counit _ _).
    + exact (subset_pt_is_el (born_preimage f L')).
    + destruct HL' as [U HU]. exists (ufm_preimage f U).
      rew (preimage_thicken_uc_le f _ _). now rew <-E, HU.
  Qed.
End restrict_born_refl.

#[global] Hint Extern 2 (Dense (func_op (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H))) => simple notypeclasses refine (@open_immersion_restrict_dense X Y Φ Ψ 𝒜 ℬ _ f S T H _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_born_refl X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _ _ _) : typeclass_instances.

(** * Bornological: the boundary-condition theorem.  The apartness kit —
    [thicken_apart_swap], [thicken_apart_split], [image_reflect_apart] — lives
    in uniform/base.v.

    The boundary condition [(cl f⁎(Sᗮ))ᗮ ⊆ T] is exactly what makes the
    restriction bornological: margins of bounded sets inside [S] push forward
    to margins inside [T]. *)
Section restrict_bornological.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}.
  Context `{!UnifBornSpace X} `{!UnifBornSpace Y}.
  Context (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T}.

  Local Abbreviation ι := from_subset.

  Lemma open_immersion_restrict_bornological {HS:open S} {HT:open T}
    `{!Bornological f, !UniformlyReflecting f}
    {HB : interior (∀.[f] S) ⊆ T}
    : Bornological (𝒪₁ f S T).
  Proof. split; try exact _. intros K.
    pose (K' := @to_subset _ 𝒜 ((ι S)⁎ K) (andl (subset_pt_is_el K))).
    pose proof andr (subset_pt_is_el K) : (ι S)⁎ K ◁ S as HK.
    change ((ι T)⁎ ((𝒪₁ f S T)⁎ K) ∊ ℬ ∧ (ι T)⁎ ((𝒪₁ f S T)⁎ K) ◁ T).
    rew <-(image_compose_alt (𝒪₁ f S T) (ι T) _).
    change (ι T ∘ 𝒪₁ f S T) with (f ∘ ι S).
    rew (image_compose_alt (ι S) f _). change (f⁎ K' ∊ ℬ ∧ f⁎ K' ◁ T).
    split.
    + exact (subset_pt_is_el (born_image f K')).
    + destruct HK as [U HU].
      rew (image_reflect_apart f U _ (S ᗮ)) in HU.
      change ((ι S)⁎ K) with (powerset_pt K') in HU. destruct HU as [W HW].
      rew (thicken_apart_split _ _ _) in HW. destruct HW as [V HV].
      exists V. rew HV.
      now rew <-(closure_sub_thicken V (f⁎ (S ᗮ))).
  Qed.
End restrict_bornological.

#[global] Hint Extern 2 (Bornological (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_bornological X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _ _ _ _) : typeclass_instances.

(** * Bundles.  Each one-sided bundle needs the OPPOSITE global uniform class
    (the bornology transfers run on the crossed polarity: Bornological rides
    reflection, BornologyReflecting rides continuity), so in the two-sided
    bundles the crossings merge and the premises collapse to the ambient
    bundle: [UnifBornInitial f] alone (+ the pair conditions).  The Locally
    two-sided bundles collapse likewise and are provided by the
    [unif_born_*_local] coercions via hints. *)
Section restrict_bundles.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}.
  Context `{!UnifBornSpace X} `{!UnifBornSpace Y}.
  Context (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T} {HT:open T}.

  Let HS_from_E : Continuous f → f* T ⊆ S → open S.
  Proof. intros ??.
    assert (S = f* T) as E' by now apply (le_antisym (X:=𝒫 X)).
    rew E'. now apply (continuity_alt f).
  Qed.
  #[local] Hint Extern 4 (apos (open S)) => simple notypeclasses refine (HS_from_E _ _) : typeclass_instances.

  Local Instance open_immersion_restrict_unif_born {HS:open S} {HB : interior (∀.[f] S) ⊆ T}
    `{!UnifBornMorphism f, !UniformlyReflecting f} : UnifBornMorphism (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_unif_born_refl {E:f* T ⊆ S}
    `{!UnifBornReflecting f, !UniformlyContinuous f} : UnifBornReflecting (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_unif_born_initial {E:f* T ⊆ S} {HB : interior (∀.[f] S) ⊆ T}
    `{!UnifBornInitial f} : UnifBornInitial (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_unif_born_emb {E:f* T ⊆ S} {HB : interior (∀.[f] S) ⊆ T}
    `{!UnifBornEmbedding f} : UnifBornEmbedding (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_locally_unif_born {HS:open S} {HB : interior (∀.[f] S) ⊆ T}
    `{!LocallyUnifBorn f, !UniformlyReflecting f} : LocallyUnifBorn (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_locally_unif_born_refl {E:f* T ⊆ S}
    `{!LocallyUnifBornReflecting f, !UniformlyContinuous f} : LocallyUnifBornReflecting (𝒪₁ f S T).
  Proof. now split. Qed.
End restrict_bundles.

#[global] Hint Extern 2 (UnifBornMorphism (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_unif_born X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _ _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_unif_born_refl X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_unif_born_initial X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornEmbedding (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_unif_born_emb X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_locally_unif_born X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _ _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_locally_unif_born_refl X Y Φ Ψ 𝒜 ℬ _ _ f S T H _ _ _ _) : typeclass_instances.

(** The Locally two-sided bundles collapse to the global ones (see above):
    resolve them through the [unif_born_*_local] coercions. *)
#[global] Hint Extern 2 (LocallyUnifBornInitial (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine unif_born_initial_local : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine unif_born_emb_local : typeclass_instances.

(** The WCUnif bundles: the one-sided pair takes the WCUnif class of [f] plus
    the crossed global uniform leg; the two-sided pair takes the global bundle
    between WC endpoints — the Ini/Emb classes of the (unformalized) global
    WCUnif pair.  A separate section: the ambient [UnifBornSpace] premises of
    [restrict_bundles] are redundant here (the WCUnif hypotheses carry them). *)
Section restrict_wcunif_bundles.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}.
  Context (f:X ⇾ Y) (S:𝒫 X) (T:𝒫 Y) {H:S ⊆ f* T} {HT:open T}.

  Let HS_from_E : Continuous f → f* T ⊆ S → open S.
  Proof. intros ??.
    assert (S = f* T) as E' by now apply (le_antisym (X:=𝒫 X)).
    rew E'. now apply (continuity_alt f).
  Qed.
  #[local] Hint Extern 4 (apos (open S)) => simple notypeclasses refine (HS_from_E _ _) : typeclass_instances.

  Local Instance open_immersion_restrict_wcunif {HS:open S} {HB : interior (∀.[f] S) ⊆ T}
    `{!WCUnifMorphism f, !UniformlyReflecting f} : WCUnifMorphism (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_wcunif_refl {E:f* T ⊆ S}
    `{!WCUnifReflecting f, !UniformlyContinuous f} : WCUnifReflecting (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_wcunif_initial {E:f* T ⊆ S} {HB : interior (∀.[f] S) ⊆ T}
    `{!UnifBornInitial f, !WCUnifSpace X, !WCUnifSpace Y} : WCUnifInitial (𝒪₁ f S T).
  Proof. now split. Qed.

  Local Instance open_immersion_restrict_wcunif_emb {E:f* T ⊆ S} {HB : interior (∀.[f] S) ⊆ T}
    `{!UnifBornEmbedding f, !WCUnifSpace X, !WCUnifSpace Y} : WCUnifEmbedding (𝒪₁ f S T).
  Proof. now split. Qed.
End restrict_wcunif_bundles.

#[global] Hint Extern 2 (WCUnifMorphism (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_wcunif X Y Φ Ψ 𝒜 ℬ f S T H _ _ _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_wcunif_refl X Y Φ Ψ 𝒜 ℬ f S T H _ _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifInitial (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_wcunif_initial X Y Φ Ψ 𝒜 ℬ f S T H _ _ _ _ _ _) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifEmbedding (@open_immersion_restrict ?X ?Y ?Φ ?Ψ ?𝒜 ?ℬ ?f ?S ?T ?H)) => simple notypeclasses refine (@open_immersion_restrict_wcunif_emb X Y Φ Ψ 𝒜 ℬ f S T H _ _ _ _ _ _) : typeclass_instances.

(** * Transitivity.  For [S ⊆ T] with [T] open, the open immersion inside
    [𝒪 T] of the preimage [S' := (j T)* S] compares with [𝒪 S] along the
    restriction [𝒪₁ (j T) S' S]: a uniform isomorphism (bijective uniform
    embedding) that is bornology-reflecting. *)
Section open_immersion_transitive.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜} (S T : 𝒫 X) {HT:open T} {HS:open S} {HST:S ⊆ T}.
  Local Abbreviation S' := ((j T)* S).

  Definition open_immersion_nest : 𝒪 S' ⇾ 𝒪 S := 𝒪₁ (j T) S' S.
  Local Abbreviation φ := open_immersion_nest.

  Local Instance open_immersion_nest_ufm_emb : UniformlyEmbedding φ.
  Proof. unfold φ. exact _. Qed.

  Local Instance open_immersion_nest_maps_into : MapsInto (j S) T := λ s, aimpl_impl_pos (HST _) (subset_pt_is_el s).
  Local Instance open_immersion_nest_inverse : Inverse φ := corestrict (corestrict (j S) T) S' (H:=λ s, subset_pt_is_el s).

  Local Instance open_immersion_nest_bij : Bijective φ.
  Proof. apply alt_Build_Bijective; unfold inverse; refl. Qed.

  Local Instance open_immersion_nest_open : open S'.
  Proof. now apply (continuity_alt (j T)). Qed.

  Lemma open_immersion_nest_born_refl : BornologyReflecting φ.
  Proof. split; try exact _. intros L.
    pose (L' := @to_subset _ 𝒜 ((j S)⁎ L) (andl (subset_pt_is_el L))).
    pose proof andr (subset_pt_is_el L) : (j S)⁎ L ◁ S as HL'.
    rew <-(injective_preimage_image_alt (j S) _ : (j S)* L' = powerset_pt L).
    change ((j S')* ((j T)* L') ∊ 𝒲 S').
    change ((j S')⁎ ((j S')* ((j T)* L')) ∊ 𝒲 T ∧ (j S')⁎ ((j S')* ((j T)* L')) ◁ S').
    split.
    + change ((j T)⁎ ((j S')⁎ ((j S')* ((j T)* L'))) ∊ 𝒜 ∧ (j T)⁎ ((j S')⁎ ((j S')* ((j T)* L'))) ◁ T).
      split; rew (image_preimage_counit (j S') _), (image_preimage_counit (j T) _).
      * exact (subset_pt_is_el L').
      * rew <-HST. exact HL'.
    + rew (image_preimage_counit (j S') _).
      destruct HL' as [U HU]. exists (ufm_preimage (j T) U).
      rew (preimage_thicken_uc_le (j T) _ _). now rew HU.
  Qed.

  (** The converse — every set bounded in the nested immersion is bounded in
      [𝒪 S], i.e. [Bornological φ] — is classical.  At a point [x] apart from
      [S], the contrapositive component of [W.[K'] ⊆ S] asks for [x] apart
      from [T] or apart from the thickening, and the two hypotheses speak only
      about points of [T] (via [S']) or points apart from [T] (via
      [K' ◁ T]); deciding [x ∊ T] is exactly what is missing.  So affinely
      the direct bornology is contained in the nested one, and the two agree
      classically. *)
End open_immersion_transitive.
#[global] Hint Extern 2 (Inverse (@open_immersion_nest ?X ?Φ ?𝒜 ?S ?T)) => simple notypeclasses refine (@open_immersion_nest_inverse X Φ 𝒜 S T _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding  (@open_immersion_nest ?X ?Φ ?𝒜 ?S ?T)) => simple notypeclasses refine (@open_immersion_nest_ufm_emb X Φ 𝒜 _ S T) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (@open_immersion_nest ?X ?Φ ?𝒜 ?S ?T)) => simple notypeclasses refine (@open_immersion_nest_ufm_emb X Φ 𝒜 _ S T) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (@open_immersion_nest ?X ?Φ ?𝒜 ?S ?T)) => simple notypeclasses refine (@open_immersion_nest_ufm_emb X Φ 𝒜 _ S T) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (@open_immersion_nest ?X ?Φ ?𝒜 ?S ?T)) => simple notypeclasses refine (@open_immersion_nest_ufm_emb X Φ 𝒜 _ S T) : typeclass_instances.
#[global] Hint Extern 2 (Injective (@open_immersion_nest ?X ?Φ ?𝒜 ?S ?T)) => simple notypeclasses refine (@open_immersion_nest_ufm_emb X Φ 𝒜 _ S T) : typeclass_instances.
#[global] Hint Extern 2 (Bijective (@open_immersion_nest ?X ?Φ ?𝒜 ?S ?T)) => simple notypeclasses refine (@open_immersion_nest_bij X Φ 𝒜 S T _) : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (@open_immersion_nest ?X ?Φ ?𝒜 ?S ?T)) => simple notypeclasses refine (@open_immersion_nest_born_refl X Φ 𝒜 _ S T _ _ _) : typeclass_instances.

