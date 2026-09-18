(** The trapped region of the localized completion (cont3's D′,
    doc/extension_theorem.md §4): the ℒ-Cauchy filters carrying a bounded
    member, as a subcarrier 𝒯 X of 𝒞 (ℒ X) with the projected (full affine)
    closeness equality.  The embedding, the corestriction kit through it,
    and the unit ℒ X ⇾ 𝒯 X factoring κ (ℒ X) — uniformly initial, and an
    embedding under separation.  Saturation (trapped is a property of the
    completion point) is the one consumer of [wcunif_thicken]; the unit
    needs only the covering leg of the bornology. *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born.
Require Import theory.set projected_set.
Require Import orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.interior.
Require Import uniform.base uniform.basis uniform.product uniform.subspace uniformly_below.
Require Import uniform.cauchy_completion uniform.completion.
Require Import bornology.base bornology.basis.
Require Import unif_born.base unif_born.local_maps unif_born.localization.
Require Import easy rewrite replc simplify strip_coercions tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope grp_scope.
Local Open Scope sg_op_scope.
Import image_notation.
Import tensor_map_notation.
Import thicken_notation.

Local Abbreviation ℒ := localization.
Local Abbreviation Λ := localized_uniformity.
Local Abbreviation ε := from_localization.
Local Abbreviation η := to_localization.
Local Abbreviation κ := to_cauchy.
Local Abbreviation 𝒞 := cauchy_filter_set.
Local Abbreviation 𝒞₁ := cauchy_map.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Abbreviation π₁ := (tensor_proj1 _ _).

(** ** Trapped Cauchy filters.

    The ℒ-Cauchy filters carrying a bounded member — the completion-side
    counterpart of the well-contained regions (cont3's D′).  The predicate
    respects closeness only positively (a positive farness witness cannot be
    manufactured from a refutation of boundedness), so the subset lives on
    the [of_course] carrier via the weak_spred pipeline.  Properness is paid
    for by [wcunif_thicken]: a bounded member of F transfers to a nearby G
    as its thickening. *)
Definition TrappedCauchyFilter {X Φ} {𝒜:Bornology X} {H:@UniformSpace X Φ} (F : 𝒞 (ℒ X)) : SProp 
  := ∐ K:𝒜, powerset_pt K ∊ F.

Record trapped_cauchy_filter X {Φ 𝒜 H} :=
{ trapped_filter :> 𝒞 (ℒ X)
; #[reversible=no, canonical=no] trapped_prop :> @TrappedCauchyFilter X Φ 𝒜 H trapped_filter
}.
Arguments trapped_filter {_ _ _ _} _.
Arguments trapped_prop {_ _ _ _} _.

#[global] Hint Extern 2 (StripCoercions (trapped_filter ?F)) => strip_coercions_chain F : strip_coercions.
#[global] Hint Extern 4 (TrappedCauchyFilter ?F) => exact_strip_coercions F : typeclass_instances.

Coercion trapped_cauchy_filter_CauchyFilter `(F:@trapped_cauchy_filter X Φ 𝒜 H) : CauchyFilter (trapped_filter F).
Proof. exact (trapped_filter F). Qed.

#[global] Hint Extern 1 (Equiv (@trapped_cauchy_filter ?X ?Φ ?𝒜 ?H)) => refine (projected_set_eq (@trapped_filter X Φ 𝒜 H)) : typeclass_instances.

Definition trapped_cauchy_filter_set X {Φ 𝒜 H} := @set_make (@trapped_cauchy_filter X Φ 𝒜 H) (projected_set_eq (@trapped_filter X Φ 𝒜 H)) _.
Local Abbreviation 𝒯 := trapped_cauchy_filter_set.

#[global] Hint Extern 1 (IsProjectedSet (set_T (𝒯 _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Canonical Structure trapped_embedding X {Φ 𝒜 H} : 𝒯 X ⇾ 𝒞 (ℒ X)
  := Eval red in projected_set_project (@trapped_cauchy_filter_set X Φ 𝒜 H).
Local Abbreviation β := trapped_embedding.
Definition trapped_embedding_inj {X Φ 𝒜 H} : Injective (@trapped_embedding X Φ 𝒜 H)
  := projected_set_project_injective (𝒯 X).
#[global] Hint Extern 2 (Injective (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_inj : typeclass_instances.

Definition trapped_uniformity X {Φ:Uniformity X} {𝒜:Bornology X} {H:@UniformSpace X Φ} : Uniformity (𝒯 X)
  := pullback_uniformity (β X).
#[global] Hint Extern 0 (Uniformity (@trapped_cauchy_filter_set ?X ?Φ ?𝒜 ?H)) =>
  simple notypeclasses refine (@trapped_uniformity X Φ 𝒜 H) : typeclass_instances.

Lemma trapped_uniform_space X {Φ:Uniformity X} {𝒜:Bornology X} {H:@UniformSpace X Φ} : UniformSpace (𝒯 X).
Proof. exact pullback_uniform_space. Qed.
#[global] Hint Extern 2 (UniformSpace    (trapped_cauchy_filter_set _)) => simple notypeclasses refine (trapped_uniform_space _) : typeclass_instances.
#[global] Hint Extern 2 (PreUniformSpace (trapped_cauchy_filter_set _)) => simple notypeclasses refine (trapped_uniform_space _) : typeclass_instances.
#[global] Hint Extern 2 (@Topology _ (@UniformNeighborhood _ (@trapped_uniformity ?X ?Φ ?𝒜 ?H))) =>
  simple notypeclasses refine (@trapped_uniform_space X Φ 𝒜 H) : typeclass_instances.

Lemma trapped_embedding_ue {X Φ 𝒜 H} : UniformlyEmbedding (@trapped_embedding X Φ 𝒜 H).
Proof. exact pullback_map_emb. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding  (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_ue : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_ue : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_ue : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_ue : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_ue : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_ue : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_ue : typeclass_instances.
#[global] Hint Extern 2 (Continuous             (trapped_embedding _)) => simple notypeclasses refine trapped_embedding_ue : typeclass_instances.

Lemma trapped_separated `{@UnifBornSpace X Φ 𝒜} : SeparatedUniformSpace (𝒯 X).
Proof. exact (uniform_reflects_hausdorff (trapped_embedding X)). Qed.
#[global] Hint Extern 2 (SeparatedUniformSpace (trapped_cauchy_filter_set _)) => simple notypeclasses refine trapped_separated : typeclass_instances.
#[global] Hint Extern 2 (Hausdorff (trapped_cauchy_filter_set _)) => simple notypeclasses refine trapped_separated : typeclass_instances.
#[global] Hint Extern 2 (Separation_T₀ (trapped_cauchy_filter_set _)) => simple notypeclasses refine trapped_separated : typeclass_instances.

(** T X : Φ ⇾ trapped_uniformity X, the "image" of X uniformities in 𝒯 X *)

Local Abbreviation C := cauchy_entourage.
Definition trapped_entourage X `{@UnifBornSpace X Φ 𝒜} := ufm_preimage (β X) ∘ C (ℒ X) ∘ ufm_preimage (ε X).
Local Abbreviation T := trapped_entourage.

Section trapped_entourage.
  Context `{@UnifBornSpace X Φ 𝒜}.

  Local Instance trapped_entourage_mono : OrderPreserving (T X).
  Proof. now unfold T. Qed.

  Lemma trapped_entourage_flip (U:Φ) : T X U⁻¹ = (T X U)⁻¹.
  Proof. unfold T.
    change ( (β X)♯ (C (ℒ X) (ufm_preimage (ε X) U⁻¹)) = (β X)♯ (C (ℒ X) (ufm_preimage (ε X) U))⁻¹ ).
    apply (is_fun (β X)♯). now rew <-(cauchy_entourage_flip _).
  Qed.
  
  Lemma trapped_entourage_split (U V:Φ) : V ∙ V ∙ V ≤ U ⊸ T X V ∙ T X V ≤ T X U.
  Proof.
    pose (V' := ufm_preimage (ε X) V). pose (U' := ufm_preimage (ε X) U).
    change (V' ∙ V' ∙ V' ≤ U' ⊸ powerset_pt (T X V) ⋄ powerset_pt (T X V) ⊆ powerset_pt (T X U)).
    change (powerset_pt (T X V)) with ( (β X)♯ (C (ℒ X) V') ).
    change (powerset_pt (T X U)) with ( (β X)♯ (C (ℒ X) U') ).
    rew [(cauchy_entourage_split U' V') | (preimage_compose_rel_lax _ _ _ _ _)].
    exact (order_preserving (β X)♯ _ _).
  Qed.

  Lemma trapped_entourage_split_alt (U:Φ) : ∐ V:Φ, V⁻¹ = V ⊠ T X V ∙ T X V ≤ T X U.
  Proof. pose proof uniform_split_sym3 U as [V[EV HV]]. exists V. now rew <-(trapped_entourage_split _ _). Qed.

  Lemma trapped_entourage_compose  (U V:Φ) (F E G : 𝒯 X)
    : V ∙ V ∙ V ≤ U ⊸ (F, E) ∊ T X V ⊠ (E, G) ∊ T X V ⊸ (F, G) ∊ T X U.
  Proof.
    rew (trapped_entourage_split _ _). change (?a ≤ ?b) with (∏ p, p ∊ a ⊸ p ∊ b).
    rew (all_lb _ (F, G)).
    change ( (F, G) ∊ T X V ∙ T X V ) with (∐ E, (F, E) ∊ T X V ⊠ (E, G) ∊ T X V).
    now rew <-(aex_ub _ E).
  Qed.

  Lemma trapped_entourage_compose_alt  (U V:Φ) (F E G : 𝒯 X)
    : V ∙ V ∙ V ≤ U → (F, E) ∊ T X V ⊠ (E, G) ∊ T X V ⊸ (F, G) ∊ T X U.
  Proof. exact (aimpl_impl_pos (trapped_entourage_compose _ _ _ _ _)). Qed.
End trapped_entourage.
#[global] Hint Extern 2 (OrderPreserving (T _)) => simple notypeclasses refine trapped_entourage_mono : typeclass_instances.


(** generic corestriction for functions into 𝒞 (ℒ X) that map to the 𝒯 X subcarrier *)

Class MapsIntoTrapped@{u} {A:Type@{u}} {X:set@{u}} {Φ:Uniformity X} {𝒜:Bornology X} {H:UniformSpace X} (f:A → 𝒞 (ℒ X)) : SProp
  := maps_into_trapped x : TrappedCauchyFilter (f x).

Section corestrict.
  Universes u.
  Context {Z X:set@{u}} {Φ:Uniformity X} {𝒜:Bornology X} {H:UniformSpace X}.
  Context (f:Z ⇾ 𝒞 (ℒ X)) {Hf:MapsIntoTrapped f}.
  
  Let mk := (λ z, {| trapped_filter := f z; trapped_prop := Hf z |}).
  
  Definition trapped_corestrict : Z ⇾ 𝒯 X := Eval red in
    (subcarrier_corestrict (T:=𝒯 X) f mk ltac:(intros; refl) ).

  Lemma trapped_corestrict_factor : trapped_embedding X ∘ trapped_corestrict = f.
  Proof. exact (subcarrier_corestrict_factor (T:=𝒯 X) f mk ltac:(intros; refl)). Qed.
End corestrict.

(** The unit τ X : X ⇾ 𝒯 X *)

Lemma to_cauchy_trapped `{@UnifBornSpace X Φ 𝒜} : MapsIntoTrapped (κ (ℒ X)).
Proof. intros x. exists (born_pt x). now change (x ∊ singleton x). Qed.
#[global] Hint Extern 2 (MapsIntoTrapped (func_op (κ _))) => simple notypeclasses refine to_cauchy_trapped : typeclass_instances.

Definition trapped_unit `{@UnifBornSpace X Φ 𝒜} : ℒ X ⇾ 𝒯 X := trapped_corestrict (κ (ℒ X)).
Arguments trapped_unit X {_ _ _}.
Local Abbreviation τ := trapped_unit.
Lemma trapped_unit_factor `{@UnifBornSpace X Φ 𝒜} : trapped_embedding X ∘ trapped_unit X = κ (ℒ X).
Proof. exact (trapped_corestrict_factor (κ (ℒ X))). Qed.

Lemma trapped_unit_ufm_cont `{@UnifBornSpace X Φ 𝒜} : UniformlyContinuous (trapped_unit X).
Proof. refine (pullback_uniformity_initial (f:=trapped_embedding X) _). now rew trapped_unit_factor. Qed.
#[global] Hint Extern 2 (UniformlyContinuous (trapped_unit _)) => simple notypeclasses refine trapped_unit_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (UniformContinuity (func_op (trapped_unit _))) => simple notypeclasses refine trapped_unit_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (trapped_unit _)) => simple notypeclasses refine trapped_unit_ufm_cont : typeclass_instances.

Lemma trapped_unit_initial `{@UnifBornSpace X Φ 𝒜} : UniformlyInitial (trapped_unit X).
Proof. split; try exact _. apply (ufm_refl_factor _ (trapped_embedding X)). now rew trapped_unit_factor. Qed.
#[global] Hint Extern 2 (UniformlyInitial    (trapped_unit _)) => simple notypeclasses refine trapped_unit_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (trapped_unit _)) => simple notypeclasses refine trapped_unit_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (trapped_unit _))) => simple notypeclasses refine trapped_unit_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (trapped_unit _)) => simple notypeclasses refine trapped_unit_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (trapped_unit _)) => simple notypeclasses refine trapped_unit_initial : typeclass_instances.

Lemma trapped_unit_emb `{@UnifBornSpace X Φ 𝒜, !SeparatedUniformSpace X} : UniformlyEmbedding (trapped_unit X).
Proof. split; [ exact _ |]. refine (injective_factor _ (trapped_embedding X) _). now rew trapped_unit_factor. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding (trapped_unit _)) => simple notypeclasses refine trapped_unit_emb : typeclass_instances.
#[global] Hint Extern 2 (Injective (trapped_unit _)) => simple notypeclasses refine trapped_unit_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (trapped_unit _)) => simple notypeclasses refine trapped_unit_emb : typeclass_instances.

Lemma trapped_unit_dense `{@UnifBornSpace X Φ 𝒜} : Dense (trapped_unit X).
Proof. pose proof (trapped_embedding_ue (X:=X)).
  refine (Dense_factor_left _ (trapped_embedding X)); try exact _.
  now rew trapped_unit_factor.
Qed.
#[global] Hint Extern 2 (Dense (func_op (τ _))) => simple notypeclasses refine trapped_unit_dense : typeclass_instances.


(** ** 𝒯-side transports of the completion atoms.

    Thin definitional wrappers moving [cauchy_basis_near_member_l],
    entourage composition, and [cauchy_basis_points] to the [T]-entourages,
    so 𝒯-level proofs never mention β, [C] or [cauchy_basis]. *)
Lemma trapped_near_member_l `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (V:Φ)
  (A : trapped_filter F) {x : X} (elx : x ∊ A) (PA : A ⊗ A ⊆ V) : (τ X x, F) ∊ T X V.
Proof. exact (cauchy_basis_near_member_l (trapped_filter F) (ufm_preimage (ε X) V) A elx PA). Qed.

Lemma trapped_near_member_r `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (V:Φ)
  (A : trapped_filter F) {x : X} (elx : x ∊ A) (PA : A ⊗ A ⊆ V) : (F, τ X x) ∊ T X V.
Proof. exact (cauchy_basis_near_member_r (trapped_filter F) (ufm_preimage (ε X) V) A elx PA). Qed.

Lemma trapped_entourage_points_alt `{@UnifBornSpace X Φ 𝒜} (U V:Φ)
  (EV : V⁻¹ = V) (PV : V ∙ V ∙ V ≤ U) (x y : X)
  : (τ X x, τ X y) ∊ T X V ⊸ (x, y) ∊ U.
Proof. pose (U' := ufm_preimage (ε X) U). pose (V' := ufm_preimage (ε X) V).
  exact (cauchy_basis_points_alt U' V' EV PV x y).
Qed.

Lemma trapped_entourage_points `{@UnifBornSpace X Φ 𝒜} (U V:Φ)
  (EV : V⁻¹ = V) (PV : V ∙ V ∙ V ≤ U) : (τ X)♯ (T X V) ⊆ U.
Proof. intros [x y]. exact (trapped_entourage_points_alt U V EV PV x y). Qed.

(** Near-member at a general localized entourage: trapped filters are
    Cauchy in [ℒ X], so small members — and hence [T]-nearness to their
    points — exist at every localized scale, not just the ambient ones.
    This is what feeds uniform continuity of maps out of [𝒯 X]. *)
Lemma trapped_near_member_loc_l `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (E : localized_uniformity X)
  (A : trapped_filter F) {x : X} (elx : x ∊ A) (PA : A ⊗ A ⊆ E)
  : (κ (ℒ X) x, β X F) ∊ C (ℒ X) E.
Proof. exact (cauchy_basis_near_member_l (trapped_filter F) E A elx PA). Qed.

Lemma trapped_near_member_loc_r `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (E : localized_uniformity X)
  (A : trapped_filter F) {x : X} (elx : x ∊ A) (PA : A ⊗ A ⊆ E)
  : (β X F, κ (ℒ X) x) ∊ C (ℒ X) E.
Proof. exact (cauchy_basis_near_member_r (trapped_filter F) E A elx PA). Qed.

(** One point simultaneously [T]-near a trapped filter at a localized
    scale and at an ambient scale, in both orientations — the member-meet
    trick packaged once.  This is the per-filter anchor the functoriality
    lemmas consume. *)
Lemma trapped_near_point `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (E : localized_uniformity X) (V : Φ)
  : ∐ x : X, ((κ (ℒ X) x, β X F) ∊ C (ℒ X) E ∧ (β X F, κ (ℒ X) x) ∊ C (ℒ X) E)
           ∧ ((τ X x, F) ∊ T X V ∧ (F, τ X x) ∊ T X V).
Proof.
  pose proof cauchy_alt (trapped_filter F) E as [A₁ PA₁].
  pose proof cauchy_alt (trapped_filter F) (ufm_preimage (ε X) V) as [A₂ PA₂].
  pose (Ax := A₁ ⊓ A₂ : trapped_filter F).
  pose proof inhabited Ax as [x _].
  pose proof subset_pt_is_el x : subset_pt x ∊ A₁ ∧ subset_pt x ∊ A₂ as [elA₁ elA₂].
  exists (subset_pt x). split; split.
  + exact (trapped_near_member_loc_l F E A₁ elA₁ PA₁).
  + exact (trapped_near_member_loc_r F E A₁ elA₁ PA₁).
  + exact (trapped_near_member_l F V A₂ elA₂ PA₂).
  + exact (trapped_near_member_r F V A₂ elA₂ PA₂).
Qed.


(** ** The trapped bornology.

    [K ⊆ 𝒯 X] is bounded when, at some ambient scale [U : Φ], the points
    of [ℒ X] approximating a member of [K] form a bounded set — the
    reflect-form comprehension, intrinsically an ideal.  Covering is
    trappedness itself (the witness bounds the approximants, up to a
    [wcunif_thicken]); together with thickenability this makes [𝒯 X] a
    WCUnif space, with [τ] a bornological map. *)
Definition trapped_bornology X `{@UnifBornSpace X Φ 𝒜} : Bornology (𝒯 X)
  := { K : 𝒫 (𝒯 X) | ∐ U:Φ, (τ X)* (T X U).[K] ∊ 𝒜 }.

#[global] Hint Extern 0 (Bornology (@trapped_cauchy_filter_set ?X ?Φ ?𝒜 ?H)) =>
  refine (@trapped_bornology X Φ 𝒜 _) : typeclass_instances.

Lemma trapped_bornology_ideal `{@UnifBornSpace X Φ 𝒜} : Ideal (trapped_bornology X).
Proof. apply Build_Ideal.
+ apply Build_DownSet. intros K K'.
  change ((K ⊆ K') ⊸ (∐ U:Φ, (τ X)* (T X U).[K'] ∊ 𝒜) ⊸ (∐ U:Φ, (τ X)* (T X U).[K] ∊ 𝒜)).
  rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj; intros U. rew <-(aex_ub _ U), (aprod_adj _ _ _).
  rew <-(down_closed 𝒜 _ _), <-(order_preserving (τ X)* _ _), <-(order_preserving thicken _ _).
  unfold_pair_le. now simplify.
+ apply Build_UpDirectedSubset.
  * exists ⊥. exists ⊤. now rew (thicken_empty _), (preserves_bottom _).
  * intros K₁ K₂. rew <-(aex_ub _ (K₁ ⊔ K₂)).
    rew (aprod_true_r (join_ub_r K₁ K₂)), (aprod_true_r (join_ub_l K₁ K₂)).
    change ((∐ U:Φ, (τ X)* (T X U).[K₁] ∊ 𝒜) ⊠ (∐ U:Φ, (τ X)* (T X U).[K₂] ∊ 𝒜)
               ⊸ (∐ U:Φ, (τ X)* (T X U).[K₁ ⊔ K₂] ∊ 𝒜)).
    rew <-aex_adj2; intros U₁ U₂. rew <-(aex_ub _ (U₁ ⊓ U₂)).
    rew (preserves_meet_lax (T X) _ _), (thicken_join_le _ _ _ _), (preserves_join (τ X)* _ _).
    apply sub_join_closed.
Qed.
#[global] Hint Extern 2 (Ideal (trapped_bornology _)) => simple notypeclasses refine trapped_bornology_ideal : typeclass_instances.

(** Covering, factored: (near your members at a point) ∘ split ∘ (points
    reflect).  The trapping witness enters only through the meet [A ⊓ K];
    [wcunif_thicken] pays for the final ambient bound. *)
Lemma trapped_unif_born_space `{@WCUnifSpace X Φ 𝒜} : UnifBornSpace (𝒯 X).
Proof. do 2 (split; try exact _). intros F.
  pose proof trapped_prop F as [K HK].
  pose proof wcunif_thicken X K as [U HU].
  pose proof uniform_split_sym3 U as [V [EV HV]].
  pose proof uniform_split_sym3 V as [W [EW HW]].
  exists W. rew (thicken_singleton _ _).
  enough ((τ X)* (near (T X W) F) ⊆ U.[powerset_pt K]) as E by now rew E.
  intros x.
  pose proof cauchy_alt (trapped_filter F) (ufm_preimage (ε X) W) as [A PA].
  pose (Ax := A ⊓ to_subset (U:=trapped_filter F) K : trapped_filter F).
  pose proof inhabited Ax as [a _].
  pose proof subset_pt_is_el a : subset_pt a ∊ A ∧ subset_pt a ∊ K as [elA elK].
  pose proof (trapped_near_member_l F W A elA PA) as NM.
  change ((F, τ X x) ∊ T X W ⊸ ∐ y, y ∊ powerset_pt K ⊠ (y, x) ∊ U).
  rew <-(aex_ub _ (subset_pt a)), (aprod_true_l elK).
  rew <-(trapped_entourage_points_alt U V EV HV _ _).
  rew <-(trapped_entourage_compose_alt V W _ F _ HW).
  now rew (aprod_true_l NM).
Qed.
#[global] Hint Extern 2 (UnifBornSpace (𝒯 _)) => simple notypeclasses refine trapped_unif_born_space : typeclass_instances.
#[global] Hint Extern 2 (BornologicalSpace (𝒯 _)) => simple notypeclasses refine trapped_unif_born_space : typeclass_instances.

(** The thicken axiom needs no well-containment of X: boundedness of a
    𝒯-set is itself an ambient thickening, so thickening once more is
    pure entourage composition. *)
Lemma trapped_unif_open_born `{@UnifBornSpace X Φ 𝒜} : UniformlyOpenBornology (𝒯 X).
Proof. intros K.
  pose proof subset_pt_is_el K as [U HU].
  pose proof trapped_entourage_split_alt U as [V [_ HV]].
  exists (T X V). exists V.
  now rew (thicken_compose _ _ _), HV.
Qed.
#[global] Hint Extern 2 (UniformlyOpenBornology (𝒯 _)) => simple notypeclasses refine trapped_unif_open_born : typeclass_instances.

Lemma trapped_wcunif_space `{@WCUnifSpace X Φ 𝒜} : WCUnifSpace (𝒯 X).
Proof. now split. Qed.
#[global] Hint Extern 2 (WCUnifSpace (𝒯 _)) => simple notypeclasses refine trapped_wcunif_space : typeclass_instances.

(** τ is a full UnifBorn-initial morphism: images of bounded sets are
    bounded at the scale [wcunif_thicken] provides (via
    [preimage_thicken_image_le] and the points-transport), and preimages
    of bounded sets are bounded because the trapped bornology is made of
    ambient thickenings ([thicken_expanding]). *)
Lemma trapped_unit_born_initial `{@WCUnifSpace X Φ 𝒜} : UnifBornInitial (τ X).
Proof. do 3 (split; try exact _).
+ intros A. pose proof (wcunif_thicken X A) as [U HU].
  pose proof uniform_split_sym3 U as [V [EV HV]]. exists V.
  enough ( (τ X)* (T X V).[(τ X)⁎ A] ⊆ U.[powerset_pt A] ) as P by now rew P.
  rew <-(preimage_thicken_image_le (τ X) U (T X V) A).
  exact (trapped_entourage_points U V EV HV).
+ intros K. pose proof subset_pt_is_el K as [U HU].
  enough ((τ X)* K ⊆ (τ X)* (T X U).[powerset_pt K]) as E by now rew E.
  rew <-(order_preserving (τ X)* _ _). apply thicken_expanding.
Qed.
#[global] Hint Extern 2 (UnifBornInitial     (τ _)) => simple notypeclasses refine trapped_unit_born_initial : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism    (τ _)) => simple notypeclasses refine trapped_unit_born_initial : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting  (τ _)) => simple notypeclasses refine trapped_unit_born_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial    (τ _)) => simple notypeclasses refine trapped_unit_born_initial : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (τ _)) => simple notypeclasses refine trapped_unit_born_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (τ _)) => simple notypeclasses refine trapped_unit_born_initial : typeclass_instances.

(** Bounded 𝒯-sets are uniformly trapped: the filters of a bounded set
    share a single bounded member — a thickening of the approximant set.
    (The analogue of cont3's lem:patch-wc, with filter membership playing
    "eventually contained"; the functoriality lemmas below end up not
    needing it, but it is the conceptual reading of the bornology.) *)
Lemma trapped_bounded_common_member `{@WCUnifSpace X Φ 𝒜} (L : trapped_bornology X)
  : ∐ K:𝒜, ∏ F : 𝒯 X, F ∊ L ⊸ powerset_pt K ∊ trapped_filter F.
Proof.
  pose proof subset_pt_is_el L as [U HU].
  pose proof (wcunif_thicken X (@to_subset _ 𝒜 _ HU)) as [V HV];
    change (apos (V.[(τ X)* (T X U).[powerset_pt L]] ∊ 𝒜)) in HV.
  exists (@to_subset _ 𝒜 _ HV). intros F. change (F ∊ L ⊸ V.[(τ X)* (T X U).[powerset_pt L]] ∊ trapped_filter F).
  pose (W := U ⊓ V).
  pose proof cauchy_alt (trapped_filter F) (ufm_preimage (ε X) W) as [A PA];
    change (apos (A ⊗ A ⊆ powerset_pt W)) in PA.
  pose proof inhabited A as [a _].
  enough (F ∊ L ⊸ A ⊆ V.[(τ X)* (T X U).[powerset_pt L]]) as E by (rew E; now apply up_closed_alt).
  change (?a ≤ ?b) with (∏ x, x ∊ a ⊸ x ∊ b). rew <-all_adj; intros a'.
  rew <-(aprod_adj _ _ _). change (F ∊ L ⊠ a' ∊ A ⊸ ∐ x, (∐ G, G ∊ L ⊠ (G, τ X x) ∊ T X U) ⊠ (x, a') ∊ V).
  rew <-(aex_ub _ (subset_pt a)), <-(aex_ub _ F).
  rew <-(meet_lb_l U V : W ≤ U), (aprod_true_r (trapped_near_member_r F W A (_ : subset_pt a ∊ A) PA)).
  apply aprod_proper_aimpl; [easy |].
  assert (powerset_pt W ⊆ powerset_pt V) as E by exact (meet_lb_r U V); rew <-E; clear E.
  rew <-PA. change (a' ∊ A ⊸ subset_pt a ∊ A ⊠ a' ∊ A). now simplify.
Qed.

(** The scale-graded form: a bounded 𝒯-set is uniformly *banded* — one
    bounded set contains, for every localized scale, a near-point of each
    of its filters.  Unlike the common-member form this needs no
    thickening (the approximant set itself serves), so it lives over a
    plain [UnifBornSpace]. *)
Lemma trapped_bounded_band `{@UnifBornSpace X Φ 𝒜} (L : trapped_bornology X)
  : ∐ K:𝒜, ∏ (E : Λ X) (F : 𝒯 X), F ∊ L ⊸
      ∐ x, x ∊ powerset_pt K
           ⊠ ((κ (ℒ X) x, β X F) ∊ C (ℒ X) E ∧ (β X F, κ (ℒ X) x) ∊ C (ℒ X) E).
Proof.
  pose proof subset_pt_is_el L as [U HU].
  exists (@to_subset _ 𝒜 _ HU). intros E F.
  pose proof trapped_near_point F E U as [x [[NEl NEr] [_ NUr]]].
  rew <-(aex_ub _ x), (aprod_true_r (ltac:(now split):(κ (ℒ X) x, β X F) ∊ C X E ∧ (β X F, κ (ℒ X) x) ∊ C X E)).
  change (F ∊ L ⊸ ∐ G, G ∊ L ⊠ (G, τ X x) ∊ T X U).
  rew <-(aex_ub _ F). now rew (aprod_true_r NUr).
Qed.

(** ** Functoriality.

    [𝒞₁ f] restricts to the trapped subcarriers along the two bornological
    morphism classes: [Bornological f] (images of bounded sets bounded)
    corestricts it to [𝒯₁ f : 𝒯 X ⇾ 𝒯 Y], and [BornologyReflecting f]
    (preimages of bounded sets bounded) reflects trappedness.  These are
    the hypotheses [localize_functorial] consumes: 𝒯 is a functor on the
    category of uniformly continuous bornological maps between localized
    spaces. *)
Section functor.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ}.
  Context (f : ℒ X ⇾ ℒ Y).

  Local Instance cauchy_map_trapped `{!UnifBornMorphism f} : MapsIntoTrapped (𝒞₁ f ∘ β X).
  Proof. intros F.
    pose proof (trapped_prop F) as [K HK].
    exists (born_image f K); change (f* (f⁎ K) ∊ trapped_filter F).
    now rew <-(preimage_image_unit f (powerset_pt K)).
  Qed.

  Lemma cauchy_map_trapped_reflect `{!UniformlyContinuous f} `{!BornologyReflecting f} (F : 𝒞 (ℒ X))
    : TrappedCauchyFilter (𝒞₁ f F) → TrappedCauchyFilter F.
  Proof. intros [K HK]. now exists (born_preimage f K). Qed.

  Context `{!UnifBornMorphism f}.

  Definition trapped_map : 𝒯 X ⇾ 𝒯 Y := trapped_corestrict (𝒞₁ f ∘ β X).

  Lemma trapped_map_factor : β Y ∘ trapped_map = 𝒞₁ f ∘ β X.
  Proof. exact (trapped_corestrict_factor _). Qed.

  Local Instance trapped_map_ufm_cont : UniformlyContinuous trapped_map.
  Proof. refine (pullback_uniformity_initial (f:=β Y) _). now rew trapped_map_factor. Qed.

  Lemma trapped_map_unit : trapped_map ∘ τ X = τ Y ∘ f.
  Proof. apply (injective_compose_cancel (β Y) _ _).
    change ((β Y ∘ trapped_map) ∘ τ X = (β Y ∘ τ Y) ∘ f).
    rew trapped_map_factor.
    change (𝒞₁ f ∘ (β X ∘ τ X) = (β Y ∘ τ Y) ∘ f).
    rew trapped_unit_factor.
    exact (cauchy_map_spec f).
  Qed.

  Lemma trapped_map_dense `{!Dense f} : Dense trapped_map.
  Proof. apply (Dense_factor_right (τ X)). now rew trapped_map_unit. Qed.

  Lemma trapped_map_initial `{!UniformlyInitial f} : UniformlyInitial trapped_map.
  Proof. refine (ufm_dense_initial (τ X) _); try exact _. now rew trapped_map_unit. Qed.
End functor.
Local Abbreviation 𝒯₁ := trapped_map.

#[global] Hint Extern 2 (MapsIntoTrapped (func_op (cauchy_map _ ∘ trapped_embedding _))) => simple notypeclasses refine (cauchy_map_trapped _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (trapped_map _)) => simple notypeclasses refine (trapped_map_ufm_cont _) : typeclass_instances.
#[global] Hint Extern 2 (UniformContinuity (func_op (trapped_map _))) => simple notypeclasses refine (trapped_map_ufm_cont _) : typeclass_instances.
#[global] Hint Extern 2 (Continuous (trapped_map _)) => simple notypeclasses refine (trapped_map_ufm_cont _) : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (trapped_map ?f))) => simple notypeclasses refine (trapped_map_dense f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial (trapped_map ?f)) => simple notypeclasses refine (trapped_map_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (trapped_map ?f)) => simple notypeclasses refine (trapped_map_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (trapped_map ?f))) => simple notypeclasses refine (trapped_map_initial f) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (trapped_map ?f)) => simple notypeclasses refine (trapped_map_initial f) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (trapped_map ?f)) => simple notypeclasses refine (trapped_map_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding (trapped_map _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (trapped_map _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.


Lemma trapped_map_id@{u} `{@UnifBornSpace@{u} X Φ 𝒜} : 𝒯₁ (id_fun (ℒ X)) = id_fun (𝒯 X).
Proof. refl. Qed.

Lemma trapped_map_compose@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ, @UnifBornSpace@{u} Z Ξ 𝒟}
  (f : ℒ X ⇾ ℒ Y) (g : ℒ Y ⇾ ℒ Z)
  `{!UnifBornMorphism f} `{!UnifBornMorphism g} `{!Bornological g}
  : 𝒯₁ (g ∘ f) = 𝒯₁ g ∘ 𝒯₁ f.
Proof. refl. Qed.


Section functor.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ}.
  Context (f : ℒ X ⇾ ℒ Y) `{!UnifBornMorphism f}.

  (** Band transport: the ambient band [T Y V] pulls back along [𝒯₁ f] to
      a band at some localized scale of [X] — pure uniform continuity of
      [trapped_map], unwinding the presentation of the 𝒯-uniformity. *)
  Lemma trapped_map_entourage (V : Ψ) : ∐ E : Λ X, (β X)♯ (C (ℒ X) E) ⊆ (𝒯₁ f)♯ (T Y V).
  Proof.
    pose proof (subset_pt_is_el (ufm_preimage (𝒯₁ f) (T Y V))) as [D HD].
    pose proof cauchy_entourage_basis D as [E HE].
    exists E. now rew HE.
  Qed.

  (** The transport with the unit square pre-composed, both orientations:
      nearness to [F] at the localized scale becomes nearness of
      [τ Y (f x)] to [𝒯₁ f F] at the target band. *)
  Lemma trapped_map_entourage_unit (V : Ψ) : ∐ E : Λ X, ∏ (F : 𝒯 X) (x : ℒ X),
      ((κ (ℒ X) x, β X F) ∊ C (ℒ X) E ⊸ (τ Y (f x), 𝒯₁ f F) ∊ T Y V)
    ∧ ((β X F, κ (ℒ X) x) ∊ C (ℒ X) E ⊸ (𝒯₁ f F, τ Y (f x)) ∊ T Y V).
  Proof.
    pose proof trapped_map_entourage V as [E HE]. exists E. intros F x.
    change ( τ Y (f x) ) with ((τ Y ∘ f) x); rew <-(trapped_map_unit f); split.
    + exact (HE (τ X x, F)).
    + exact (HE (F, τ X x)).
  Qed.
End functor.

(** [𝒯₁ f] is bornological: a bounded 𝒯-set [B] is uniformly banded in
    its approximant set [K]; pushing each band point through [f] lands
    the image in a thickening of [f⁎ K]. *)
Lemma trapped_map_bornological@{u} `{@WCUnifSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}
  (f : ℒ X ⇾ ℒ Y) `{!UnifBornMorphism f} : UnifBornMorphism (𝒯₁ f).
Proof. do 2 (split; try exact _). intros B.
  pose proof trapped_bounded_band B as [K HK].
  pose proof wcunif_thicken Y (born_image f K) as [W HW]; change (apos (W.[f⁎ K] ∊ ℬ)) in HW.
  pose proof uniform_split_sym3 W as [V [EV HV]].
  pose proof uniform_split_sym3 V as [U [EU HU]].
  exists U. enough ((τ Y)* (T Y U).[(𝒯₁ f)⁎ B] ⊆ W.[f⁎ K]) as P by now rew P.
  intros y.
  change ((∐ G, G ∊ (𝒯₁ f)⁎ B ⊠ (G, τ Y y) ∊ T Y U)  ⊸ ∐ m, m ∊ f⁎ K ⊠ (m, y) ∊ W).
  rew [( aex_image (𝒯₁ f) B set:(λ G, (G, τ Y y) ∊ T Y U) ) | ( aex_image f K set:(λ m, (m, y) ∊ W) )]; unfold set_lambda, func_op.
  rew <-aex_adj; intros F.
  pose proof trapped_map_entourage_unit f U as [E HE].
  rew (HK E F); clear HK.
  rew aex_frob_r, <-aex_adj; intros x.
  rew <-(aex_ub _  x), (aandl _ _), (andl (HE F x)), (aprod_assoc _ _ _); clear HE E.
  now rew (trapped_entourage_compose_alt V U _ _ _ HU), (trapped_entourage_points_alt W V EV HV _ _).
Qed.
#[global] Hint Extern 2 (UnifBornMorphism (𝒯₁ ?f)) => simple notypeclasses refine (trapped_map_bornological f) : typeclass_instances.
#[global] Hint Extern 2 (Bornological     (𝒯₁ ?f)) => simple notypeclasses refine (trapped_map_bornological f) : typeclass_instances.

(** Mirror: preimages of bounded 𝒯-sets are bounded when [f] reflects
    the ambient bornologies — the near-point anchors the preimage in a
    thickening of [f* A₀]. *)
Lemma trapped_map_born_refl@{u} `{@WCUnifSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}
  (f : ℒ X ⇾ ℒ Y) `{!UnifBornMorphism f} `{!BornologyReflecting f} : BornologyReflecting (𝒯₁ f).
Proof. split; try exact _. intros K.
  pose proof subset_pt_is_el K as [W HW].
  pose (L := born_preimage f (@to_subset _ ℬ _ HW)).
  pose proof wcunif_thicken X L as [U HU].
  pose proof uniform_split_sym3 U as [V [EV HV]].
  pose proof uniform_split_sym3 V as [V' [EV' HV']].
  exists V'. enough ((τ X)* (T X V').[(𝒯₁ f)* K] ⊆ U.[powerset_pt L]) as P by now rew P.
  intros x. change ((∐ F, 𝒯₁ f F ∊  K ⊠ (F, τ X x) ∊ T X V') ⊸ ∐ m, m ∊ L ⊠ (m, x) ∊ U).
  rew <-aex_adj; intros F.
  pose proof trapped_map_entourage_unit f W as [E HE].
  pose proof trapped_near_point F E V' as [a [[_ Ha1] [Ha2 _]]].
  specialize (HE F a) as [_ HE]; rew HE in Ha1; clear HE.
  rew <-(aex_ub _ a).
  change (a ∊ L) with (∐ G, G ∊ K ⊠ (G, τ Y (f a)) ∊ T Y W).
  rew <-(aex_ub _ (𝒯₁ f F)), (aprod_true_r Ha1).
  apply aprod_proper_aimpl; [ easy |].
  rew <-(trapped_entourage_points_alt U V EV HV _ _).
  rew <-(trapped_entourage_compose_alt V V' _ F _ HV').
  now rew (aprod_true_l Ha2).
Qed.
#[global] Hint Extern 2 (BornologyReflecting (trapped_map ?f)) => simple notypeclasses refine (trapped_map_born_refl f) : typeclass_instances.

Lemma trapped_map_unif_born_initial@{u} `{@WCUnifSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}
  (f : ℒ X ⇾ ℒ Y) `{!UnifBornInitial f} : UnifBornInitial (𝒯₁ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornInitial    (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born_initial f) : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial   (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born_initial f) : typeclass_instances.


(** ** Reflection.

    The third completion construction: for [ι : ℒ X ⇾ Y] dense and
    uniformly reflecting, [cauchy_reflect ι] corestricts to 𝒯 X under
    [BornologyReflecting ι] plus well-containment of the codomain:
    [wcunif_thicken] at a singleton gives every point a bounded
    neighborhood, whose trace is then a bounded member of the reflected
    filter (the witnessed-traces condition).  The same hypotheses
    [localize_functorial_refl] consumes. *)
Section reflect.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}.
  Context (ι : ℒ X ⇾ Y) `{!Dense ι, !UnifBornReflecting ι}.

  Local Instance cauchy_reflect_trapped : MapsIntoTrapped (cauchy_reflect ι).
  Proof. intros y.
    pose proof (wcunif_thicken Y (born_pt y)) as [U HU].
    rew (thicken_singleton U y) in HU.
    exists (born_preimage ι (@to_subset _ _ _ HU)).
    change (ι* (near U y) ∊ cauchy_reflect ι y).
    exact (cauchy_reflect_basis_elt _ _).
  Qed.

  Definition trapped_reflect : Y ⇾ 𝒯 X := trapped_corestrict (cauchy_reflect ι).

  Lemma trapped_reflect_factor : β X ∘ trapped_reflect = cauchy_reflect ι.
  Proof. exact (trapped_corestrict_factor _). Qed.

  Local Instance trapped_reflect_ufm_cont : UniformlyContinuous trapped_reflect.
  Proof. refine (pullback_uniformity_initial (f:=β X) _). now rew trapped_reflect_factor. Qed.

  Lemma trapped_reflect_spec : trapped_reflect ∘ ι = τ X.
  Proof. apply (injective_compose_cancel (β X) _ _).
    change ((β X ∘ trapped_reflect) ∘ ι = β X ∘ τ X).
    rew trapped_reflect_factor, trapped_unit_factor.
    exact (cauchy_reflect_spec ι).
  Qed.

  Lemma trapped_reflect_dense : Dense trapped_reflect.
  Proof. apply (Dense_factor_right ι). now rew trapped_reflect_spec. Qed.

  Lemma trapped_reflect_initial `{!UniformlyInitial ι} : UniformlyInitial trapped_reflect.
  Proof. refine (ufm_dense_initial ι _); try exact _. now rew trapped_reflect_spec. Qed.
End reflect.

#[global] Hint Extern 2 (MapsIntoTrapped (func_op (cauchy_reflect _))) => simple notypeclasses refine (cauchy_reflect_trapped _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (trapped_reflect _)) => simple notypeclasses refine (trapped_reflect_ufm_cont _) : typeclass_instances.
#[global] Hint Extern 2 (Continuous (trapped_reflect _)) => simple notypeclasses refine (trapped_reflect_ufm_cont _) : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (trapped_reflect ?f))) => simple notypeclasses refine (trapped_reflect_dense f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (trapped_reflect ?f))) => simple notypeclasses refine (trapped_reflect_initial f) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial f) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding (trapped_reflect _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (trapped_reflect _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.

Local Abbreviation ℛ := trapped_reflect.

(** The reflect-side near-point: a trace point of [trapped_reflect y],
    [T]-near it at any ambient scale and ι-mapped W-near y, all
    positively — the mirror of [trapped_near_point], with the trace as
    the small member. *)
Lemma trapped_reflect_near_point@{u}
 `{@UnifBornSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}
 (ι : ℒ X ⇾ Y) `{!Dense ι, !UnifBornReflecting ι}
 (y : Y) (U : Φ) (W : Ψ)
  : ∐ z : ℒ X, ((ℛ ι y, τ X z) ∊ T X U ∧ (τ X z, ℛ ι y) ∊ T X U)
             ∧ ((y, ι z) ∊ W ∧ (ι z, y) ∊ W).
Proof.
  pose proof (cauchy_alt (trapped_filter (ℛ ι y)) (ufm_preimage (ε X) U)) as [A PA].
  pose proof uniform_sym_alt W as [V [EV HV]].
  pose proof cauchy_reflect_basis_elt _ _ : ι* (near V y) ∊ trapped_filter (ℛ ι y) as HT.
  pose proof _ : CauchyFilter (trapped_filter (ℛ ι y)).
  pose (Az := A ⊓ @to_subset _ _ _ HT : trapped_filter (ℛ ι y)).
  pose proof inhabited Az as [z _].
  pose proof subset_pt_is_el z : subset_pt z ∊ A ∧ (y, ι z) ∊ V as [elA elT].
  exists (subset_pt z).
  split; [split | split].
  + exact (trapped_near_member_r (ℛ ι y) U A elA PA).
  + exact (trapped_near_member_l (ℛ ι y) U A elA PA).
  + now apply HV.
  + apply HV. now rew <-EV.
Qed.


(** [trapped_reflect ι] is bornological for free: the image of a
    ℬ-bounded set rides on the reflected traces — the [ι]-preimage of a
    thickening, bounded by exactly the [BornologyReflecting ι] the
    construction already assumes. *)
Lemma trapped_reflect_bornological@{u} `{@WCUnifSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}
  (ι : ℒ X ⇾ Y) `{!Dense ι, !UnifBornReflecting ι} : UnifBornMorphism (ℛ ι).
Proof. do 2 (split; try exact _). intros B.
  pose proof wcunif_thicken Y B as [W HW].
  pose proof wcunif_thicken X (born_preimage ι (@to_subset _ ℬ _ HW)) as [U HU];
    change (apos (U.[ι*(W.[powerset_pt B])] ∊ 𝒜)) in HU.
  pose proof uniform_split_sym3 U as [V [EV HV]].
  pose proof uniform_split_sym3 V as [V' [EV' HV']].
  exists V'.
  enough ((τ X)* (T X V').[(ℛ ι)⁎ (powerset_pt B)] ⊆ U.[ι* W.[powerset_pt B]]) as P by now rew P.
  intros x.
  change ((∐ G, G ∊ (ℛ ι)⁎ B ⊠ (G, τ X x) ∊ T X V') ⊸ ∐ m, (∐ y, y ∊ B ⊠ (y, ι m) ∊ W) ⊠ (m, x) ∊ U).
  rew (aex_image (ℛ ι) B set:(λ G, (G, τ X x) ∊ T X V')); unfold set_lambda, func_op.
  rew <-aex_adj; intros y.
  pose proof trapped_reflect_near_point ι y V' W as [z [[_ N2] [Nw _]]].
  rew <-(aex_ub _ z), <-(aex_ub _ y), (aprod_true_r Nw).
  apply aprod_proper_aimpl; [easy |].
  rew <-(trapped_entourage_points_alt U V EV HV _ _).
  rew <-(trapped_entourage_compose_alt V V' _ (ℛ ι y) _ HV').
  now rew (aprod_true_l N2).
Qed.
#[global] Hint Extern 2 (UnifBornMorphism (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_bornological f) : typeclass_instances.
#[global] Hint Extern 2 (Bornological     (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_bornological f) : typeclass_instances.

(** Mirror, at the cost of [Bornological ι]: the preimage of a bounded
    𝒯-set is caught by pushing its band points forward through ι. *)
Lemma trapped_reflect_born_refl@{u} `{@WCUnifSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}
  (ι : ℒ X ⇾ Y) `{!Dense ι, !UnifBornReflecting ι} `{!Bornological ι}
  : BornologyReflecting (ℛ ι).
Proof. split; try exact _. intros L.
  pose proof trapped_bounded_band L as [K HK].
  pose proof wcunif_thicken X K as [U HU].
  pose proof uniform_split_sym3 U as [V [EV HV]].
  pose proof uniform_split_sym3 V as [W [EW HW]].
  pose proof wcunif_thicken Y (born_image ι (@to_subset _ 𝒜 _ HU)) as [S HS];
    change (apos (S.[ι⁎ U.[powerset_pt K]] ∊ ℬ)) in HS.
  enough ((ℛ ι)* L ⊆ S.[ι⁎ U.[powerset_pt K]]) as P by now rew P.
  intros y. change (ℛ ι y ∊ L ⊸ ∐ m, m ∊ ι⁎ U.[powerset_pt K] ⊠ (m, y) ∊ S).
  rew (aex_image ι _ set:(λ m, (m, y) ∊ S)); unfold set_lambda, func_op.
  pose proof trapped_reflect_near_point ι y W S as [z [[N1 _] [_ Nw]]].
  rew <-(aex_ub _ z), (aprod_true_r Nw).
  change (ℛ ι y ∊ L ⊸ ∐ k, k ∊ K ⊠ (k, z) ∊ U).
  rew (HK (ufm_preimage (ε X) W) _); clear HK.
  rew <-aex_adj; intros x. rew <-(aex_ub _ x), (aandl _ _).
  apply aprod_proper_aimpl; [easy |]. change ( (τ X x, ℛ ι y) ∊ T X W ⊸ (x, z) ∊ U ).
  rew <-(trapped_entourage_points_alt U V EV HV _ _).
  rew <-(trapped_entourage_compose_alt V W _ (ℛ ι y) _ HW).
  now rew (aprod_true_r N1).
Qed.
#[global] Hint Extern 2 (BornologyReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_born_refl f) : typeclass_instances.

Lemma trapped_reflect_unif_born_initial@{u} `{@WCUnifSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}
  (ι : ℒ X ⇾ Y) `{!Dense ι, !UnifBornInitial ι}
  : UnifBornInitial (ℛ ι).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornInitial    (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_unif_born_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_unif_born_initial f) : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial   (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_unif_born_initial f) : typeclass_instances.

(** ** Anchored coarse-to-fine transport.

    Ambient-scale shared small members upgrade to localized-scale shared
    small members at a trapped anchor: the localized entourage contributes
    its band at the anchor, and the anchor refines the coarse member.  The
    common core of the Φ-saturation of trappedness and of the separation
    properties of the comparison map [𝒯 X ⇾ 𝒞 X]. *)

Lemma trapped_transport `{@WCUnifSpace X Φ 𝒜} (F : 𝒞 (ℒ X)) (K:𝒜)
  (HK : powerset_pt K ∊ F) (V : Λ X)
  : ∐ U:Φ, ∏ G : 𝒞 (ℒ X), (∐ (A:F) (B:G), A ⊗ B ⊆ U) ⊸ ∐ (A:F) (B:G), A ⊗ B ⊆ V.
Proof. pose proof local_entourage V K as [U HU]. exists U. intros G.
  rew <-aex_adj; intros A. rew <-aex_adj; intros B.
  rew <-(aex_ub _ (A ⊓ to_subset (U:=F) K)), <-(aex_ub _ B).
  rew <-HU. rew (order_preserving_simp (π₁* K ⊓) (A ⊗ B) U).
  now rew <-(cylinder_meet_tensor_subset K A B), (commutativity (⊓) (powerset_pt K) _).
Qed.

(** Corollary: at a trapped anchor, ambient-scale equivalence refines to
    localized-scale equivalence. *)
Lemma trapped_transport_equiv `{@WCUnifSpace X Φ 𝒜} (F G : 𝒞 (ℒ X)) (K:𝒜)
  (HK : powerset_pt K ∊ F) (E : ∏ U:Φ, ∐ (A:F) (B:G), A ⊗ B ⊆ U)
  : F = G.
Proof. intros V. pose proof trapped_transport F K HK V as [U P]. apply P, E. Qed.

(** Trappedness is saturated at the ambient scale: it descends along
    Φ-equivalence, not merely along the (finer) localized equivalence. *)
Lemma trapped_saturated `{@WCUnifSpace X Φ 𝒜} (F G : 𝒞 (ℒ X))
  (E : ∏ U:Φ, ∐ (A:F) (B:G), A ⊗ B ⊆ U)
  : TrappedCauchyFilter F → TrappedCauchyFilter G.
Proof. intros [K HK].
  pose proof (wcunif_thicken X K) as [U HU].
  exists (@to_subset _ _ _ HU). change (U.[powerset_pt K] ∊ G).
  pose proof (E U) as [A [B P]]; change (apos (A ⊗ B ⊆ U)) in P.
  pose (Ax := A ⊓ to_subset (U:=F) K : powerset_el F).
  pose proof inhabited Ax as [a _].
  pose proof subset_pt_is_el a : subset_pt a ∊ A ∧ subset_pt a ∊ K as [elA elK].
  enough (B ⊆ U.[powerset_pt K]) as SB by now rew <-SB.
  intros b. change (b ∊ B ⊸ ∐ x, x ∊ K ⊠ (x, b) ∊ U).
  rew <-(aex_ub _ (subset_pt a)), (aprod_true_l elK), <-P.
  change (b ∊ B ⊸ subset_pt a ∊ A ⊠ b ∊ B).
  now rew (aprod_true_l elA).
Qed.

Lemma TrappedCauchyFilter_proper_impl `{@WCUnifSpace X Φ 𝒜} (F G : 𝒞 (ℒ X))
  : F = G → sprop.impl (TrappedCauchyFilter F, TrappedCauchyFilter G).
Proof. intros E. refine (trapped_saturated F G _). intros U. exact (E (ufm_preimage (ε X) U)). Qed.


(** ** Factorization criterion: the retraction form inverts the unit.

    A uniformly continuous retraction [r : 𝒯 X ⇾ X] with [r ∘ τ X = ε X]
    makes the trapped unit bijective, with inverse [η X ∘ r] — η is merely
    continuous, but uniform continuity of the inverse rides the initiality
    of τ.  Mirror of [locally_complete_factorization_prop], one floor down,
    with 𝒯 in place of 𝒞 (ℒ ─). *)
Section trapped_factorization.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜, !SeparatedUniformSpace X}.
  Context (r : 𝒯 X ⇾ X) `{!UniformlyContinuous r}.
  Context (Er : r ∘ τ X = ε X).

  #[local] Hint Extern 0 (Inverse (trapped_unit X)) => exact (η X ∘ r) : typeclass_instances.

  Lemma trapped_factorization_prop : Bijective (τ X).
  Proof. split; [ exact _ |]. change (τ X ∘ (η X ∘ r) = id_fun (𝒯 X)).
    apply (cont_dense_epi _ _ (τ X)).
    change (τ X ∘ ((η X ∘ r) ∘ τ X) = τ X).
    enough ((η X ∘ r) ∘ τ X = id_fun (ℒ X)) as E' by now rew E'.
    change (η X ∘ (r ∘ τ X) = id_fun (ℒ X)). now rew Er.
  Qed.
End trapped_factorization.
