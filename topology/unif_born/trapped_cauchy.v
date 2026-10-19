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
Require Import unif_born.base unif_born.well_contained.
Require Import interfaces.reflection_pair reflection_pair.base topology.reflection_pair.completion.
Require Import easy rewrite replc simplify strip_coercions tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope grp_scope.
Local Open Scope sg_op_scope.
Import image_notation.
Import tensor_map_notation.
Import thicken_notation.

(*
Local Abbreviation ℒ := localization.
Local Abbreviation Λ := localized_uniformity.
Local Abbreviation ε := from_localization.
Local Abbreviation η := to_localization.
*)
Local Abbreviation κ := to_cauchy.
Local Abbreviation 𝒞 := cauchy_filter_set.
Local Abbreviation 𝒞₁ := cauchy_map.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Abbreviation π₁ := (tensor_proj1 _ _).

(** Trapped Cauchy filters. *)
Definition TrappedCauchyFilter {X Φ} {𝒜:Bornology X} {H:@UniformSpace X Φ} (F : 𝒞 X) : SProp 
  := ∐ K:𝒜, powerset_pt K ∊ F.

Record trapped_cauchy_filter X {Φ 𝒜 H} :=
{ trapped_filter :> 𝒞 X
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

Canonical Structure from_trapped X {Φ 𝒜 H} : 𝒯 X ⇾ 𝒞 X
  := Eval red in projected_set_project (@trapped_cauchy_filter_set X Φ 𝒜 H).
Local Abbreviation β := from_trapped.
Definition from_trapped_inj {X Φ 𝒜 H} : Injective (@from_trapped X Φ 𝒜 H)
  := projected_set_project_injective (𝒯 X).
#[global] Hint Extern 2 (Injective (from_trapped _)) => simple notypeclasses refine from_trapped_inj : typeclass_instances.

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

Lemma from_trapped_ue {X Φ 𝒜 H} : UniformlyEmbedding (@from_trapped X Φ 𝒜 H).
Proof. exact pullback_map_emb. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding  (from_trapped _)) => simple notypeclasses refine from_trapped_ue : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (from_trapped _)) => simple notypeclasses refine from_trapped_ue : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (from_trapped _)) => simple notypeclasses refine from_trapped_ue : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (from_trapped _)) => simple notypeclasses refine from_trapped_ue : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (from_trapped _)) => simple notypeclasses refine from_trapped_ue : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (from_trapped _)) => simple notypeclasses refine from_trapped_ue : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (from_trapped _)) => simple notypeclasses refine from_trapped_ue : typeclass_instances.
#[global] Hint Extern 2 (Continuous             (from_trapped _)) => simple notypeclasses refine from_trapped_ue : typeclass_instances.

Lemma trapped_separated `{@UnifBornSpace X Φ 𝒜} : SeparatedUniformSpace (𝒯 X).
Proof. exact (uniform_reflects_hausdorff (from_trapped X)). Qed.
#[global] Hint Extern 2 (SeparatedUniformSpace (trapped_cauchy_filter_set _)) => simple notypeclasses refine trapped_separated : typeclass_instances.
#[global] Hint Extern 2 (Hausdorff (trapped_cauchy_filter_set _)) => simple notypeclasses refine trapped_separated : typeclass_instances.
#[global] Hint Extern 2 (Separation_T₀ (trapped_cauchy_filter_set _)) => simple notypeclasses refine trapped_separated : typeclass_instances.

(** T X : Φ ⇾ trapped_uniformity X, the "image" of X uniformities in 𝒯 X *)

Local Abbreviation C := cauchy_entourage.
Definition trapped_entourage X `{@UnifBornSpace X Φ 𝒜} := ufm_preimage (β X) ∘ C X.
Local Abbreviation T := trapped_entourage.

Section trapped_entourage.
  Context `{@UnifBornSpace X Φ 𝒜}.

  Local Instance trapped_entourage_mono : OrderPreserving (T X).
  Proof. now unfold T. Qed.

  Local Instance trapped_entourage_basis_correct : UniformityBasis (T X).
  Proof. intros W.
    pose proof subset_pt_is_el W as [D HD].
    pose proof cauchy_entourage_basis D as [U HU].
    exists U. change ((β X)♯ (C X U) ⊆ subset_pt W).
    now rew HU.
  Qed.

  Lemma trapped_entourage_basis (W : trapped_uniformity X) : ∐ U:Φ, T X U ≤ W.
  Proof. exact (uniformity_basis W). Qed.

  Lemma trapped_entourage_flip (U:Φ) : T X U⁻¹ = (T X U)⁻¹.
  Proof. unfold T.
    change ( (β X)♯ (C X U⁻¹) = (β X)♯ (C X U)⁻¹ ).
    apply (is_fun (β X)♯). now rew <-(cauchy_entourage_flip _).
  Qed.
  
  Lemma trapped_entourage_split (U V:Φ) : V ∙ V ∙ V ≤ U ⊸ T X V ∙ T X V ≤ T X U.
  Proof.
    change (V ∙ V ∙ V ≤ U ⊸ powerset_pt (T X V) ⋄ powerset_pt (T X V) ⊆ powerset_pt (T X U)).
    change (powerset_pt (T X ?V)) with ( (β X)♯ (C X V) ).
    rew [(cauchy_entourage_split U V) | (preimage_compose_rel_lax _ _ _ _ _)].
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

  (** Shared members put two trapped filters within the entourage. *)
  Lemma trapped_entourage_members_aimpl (F G : 𝒯 X) (V:Φ) (A : trapped_filter F) (B : trapped_filter G)
    : A ⊗ B ⊆ V ⊸ (F, G) ∊ T X V.
  Proof.
    change (A ⊗ B ⊆ V ⊸ ∏ S : Φ, ∐ (A' : trapped_filter F) (B' : trapped_filter G), A' ⊗ B' ⊆ powerset_pt (S⁻¹ ∙ V ∙ S)).
    rew <-all_adj; intros S. rew <-(aex_ub _ A), <-(aex_ub _ B).
    rew <-(ufm_compose_ub_l _ _), <-(ufm_compose_ub_r _ _). refl.
  Qed.

  Lemma trapped_entourage_members (F G : 𝒯 X) (V:Φ) (A : trapped_filter F) (B : trapped_filter G)
    : A ⊗ B ⊆ V → (F, G) ∊ T X V.
  Proof. exact (aimpl_impl_pos (trapped_entourage_members_aimpl F G V A B)). Qed.

  (** Entourages compose up to a fudge [W] on each side. *)
  Lemma trapped_entourage_compose_gen (U V W Z : Φ) (HZ : U ∙ W ∙ W⁻¹ ∙ V ≤ Z)
    : T X U ∙ T X V ≤ T X Z.
  Proof. intros [F G].
    change ((∐ E:𝒯 X, (∏ (S:Φ), ∐ (A:trapped_filter F) (B:trapped_filter E), A ⊗ B ⊆ powerset_pt (S⁻¹ ∙ U ∙ S))
                     ⊠ (∏ (S:Φ), ∐ (A:trapped_filter E) (B:trapped_filter G), A ⊗ B ⊆ powerset_pt (S⁻¹ ∙ V ∙ S)) )
          ⊸ ∏ (S:Φ), ∐ (A:trapped_filter F) (B:trapped_filter G), A ⊗ B ⊆ powerset_pt (S⁻¹ ∙ Z ∙ S)).
    rew <-all_adj; intros S.
    rew <-aex_adj; intros E.
    pose (S' := S ⊓ W). rew [(all_lb _ S')|(all_lb _ S')].
    rew (cauchy_compose _ _ _ _ _).
    rew <-aex_adj; intros A. rew <-aex_adj; intros B.
    rew <-(aex_ub _ A), <-(aex_ub _ B).
    enough (S'⁻¹ ∙ U ∙ S' ∙ (S'⁻¹ ∙ V ∙ S') ≤ S⁻¹ ∙ Z ∙ S) as Q by now rew <-Q.
    pose proof meet_lb_l S W : S' ≤ S as H1.
    pose proof meet_lb_r S W : S' ≤ W as H2.
    rew H1 at 1 4. rew H2.
    rew <-HZ.
    now rew ?(associativity (∙) _ _ _).
  Qed.
End trapped_entourage.
#[global] Hint Extern 2 (OrderPreserving (T _)) => simple notypeclasses refine trapped_entourage_mono : typeclass_instances.
#[global] Hint Extern 2 (UniformityBasis (T _)) => simple notypeclasses refine trapped_entourage_basis_correct : typeclass_instances.


(** generic corestriction for functions into 𝒞 X that map to the 𝒯 X subcarrier *)
Class MapsIntoTrapped@{u} {A:Type@{u}} {X:set@{u}} {Φ:Uniformity X} {𝒜:Bornology X} {H:UniformSpace X} (f:A → 𝒞 X) : SProp
  := maps_into_trapped x : TrappedCauchyFilter (f x).

Section corestrict.
  Universes u.
  Context {Z X:set@{u}} {Φ:Uniformity X} {𝒜:Bornology X} {H:UniformSpace X}.
  Context (f:Z ⇾ 𝒞 X) {Hf:MapsIntoTrapped f}.
  
  Let mk := (λ z, {| trapped_filter := f z; trapped_prop := Hf z |}).
  
  Definition trapped_corestrict : Z ⇾ 𝒯 X := Eval red in
    (subcarrier_corestrict (T:=𝒯 X) f mk ltac:(intros; refl) ).

  Lemma trapped_corestrict_factor : β X ∘ trapped_corestrict = f.
  Proof. exact (subcarrier_corestrict_factor (T:=𝒯 X) f mk ltac:(intros; refl)). Qed.
End corestrict.

(** The unit τ X : X ⇾ 𝒯 X *)

Lemma to_cauchy_trapped `{@UnifBornSpace X Φ 𝒜} : MapsIntoTrapped (κ X).
Proof. intros x. exists (born_pt x). now change (x ∊ singleton x). Qed.
#[global] Hint Extern 2 (MapsIntoTrapped (func_op (κ _))) => simple notypeclasses refine to_cauchy_trapped : typeclass_instances.

Definition to_trapped `{@UnifBornSpace X Φ 𝒜} : X ⇾ 𝒯 X := trapped_corestrict (κ X).
Arguments to_trapped X {_ _ _}.
Local Abbreviation τ := to_trapped.
Lemma to_trapped_factor `{@UnifBornSpace X Φ 𝒜} : β X ∘ τ X = κ X.
Proof. exact (trapped_corestrict_factor (κ X)). Qed.

Lemma to_trapped_ufm_cont `{@UnifBornSpace X Φ 𝒜} : UniformlyContinuous (τ X).
Proof. refine (pullback_uniformity_initial (f:=β X) _). now rew to_trapped_factor. Qed.
#[global] Hint Extern 2 (UniformlyContinuous (τ _)) => simple notypeclasses refine to_trapped_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (UniformContinuity (func_op (τ _))) => simple notypeclasses refine to_trapped_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (τ _)) => simple notypeclasses refine to_trapped_ufm_cont : typeclass_instances.

Lemma to_trapped_ufm_initial `{@UnifBornSpace X Φ 𝒜} : UniformlyInitial (τ X).
Proof. split; try exact _. apply (ufm_refl_factor _ (β X)). now rew to_trapped_factor. Qed.
#[global] Hint Extern 2 (UniformlyInitial    (τ _)) => simple notypeclasses refine to_trapped_ufm_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (τ _)) => simple notypeclasses refine to_trapped_ufm_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (τ _))) => simple notypeclasses refine to_trapped_ufm_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (τ _)) => simple notypeclasses refine to_trapped_ufm_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (τ _)) => simple notypeclasses refine to_trapped_ufm_initial : typeclass_instances.

Lemma to_trapped_ufm_emb `{@UnifBornSpace X Φ 𝒜, !SeparatedUniformSpace X} : UniformlyEmbedding (τ X).
Proof. split; [ exact _ |]. refine (injective_factor _ (from_trapped X) _). now rew to_trapped_factor. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding (to_trapped _)) => simple notypeclasses refine to_trapped_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (Injective (to_trapped _)) => simple notypeclasses refine to_trapped_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (to_trapped _)) => simple notypeclasses refine to_trapped_ufm_emb : typeclass_instances.

Lemma to_trapped_dense `{@UnifBornSpace X Φ 𝒜} : Dense (τ X).
Proof. pose proof (from_trapped_ue (X:=X)).
  refine (Dense_factor_left _ (β X)); try exact _.
  now rew to_trapped_factor.
Qed.
#[global] Hint Extern 2 (Dense (func_op (τ _))) => simple notypeclasses refine to_trapped_dense : typeclass_instances.

(** The 𝒯 transports of [to_cauchy_eq_ball] and [to_cauchy_eq_closure]. *)
Lemma to_trapped_eq_ball `{@UnifBornSpace X Φ 𝒜} (x : X) (G : 𝒯 X) (E : τ X x = G) (U : Φ)
  : near U x ∊ trapped_filter G.
Proof. exact (to_cauchy_eq_ball x (β X G) E U). Qed.

Lemma to_trapped_eq_closure `{@UnifBornSpace X Φ 𝒜} (x : X) (G : 𝒯 X) (E : τ X x = G) (A : trapped_filter G)
  : x ∊ closure (powerset_pt A : 𝒫 X).
Proof. exact (to_cauchy_eq_closure x (β X G) E A). Qed.

Lemma to_trapped_singleton `{@UnifBornSpace X Φ 𝒜} (x : X) : singleton x ∊ trapped_filter (τ X x).
Proof. change (apos (x = x)). refl. Qed.


(** ** 𝒯-side transports of the completion atoms.

    Thin definitional wrappers moving [cauchy_basis_near_member_l],
    entourage composition, and [cauchy_basis_points] to the [T]-entourages,
    so 𝒯-level proofs never mention β, [C] or [cauchy_basis]. *)
Lemma trapped_near_member_l `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (V:Φ)
  (A : trapped_filter F) {x : X} (elx : x ∊ A) (PA : A ⊗ A ⊆ V) : (τ X x, F) ∊ T X V.
Proof. exact (cauchy_basis_near_member_l (trapped_filter F) V A elx PA). Qed.

Lemma trapped_near_member_r `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (V:Φ)
  (A : trapped_filter F) {x : X} (elx : x ∊ A) (PA : A ⊗ A ⊆ V) : (F, τ X x) ∊ T X V.
Proof. exact (cauchy_basis_near_member_r (trapped_filter F) V A elx PA). Qed.

Lemma trapped_entourage_points_alt `{@UnifBornSpace X Φ 𝒜} (U V:Φ)
  (EV : V⁻¹ = V) (PV : V ∙ V ∙ V ≤ U) (x y : X)
  : (τ X x, τ X y) ∊ T X V ⊸ (x, y) ∊ U.
Proof. exact (cauchy_basis_points_alt U V EV PV x y). Qed.

Lemma trapped_entourage_points `{@UnifBornSpace X Φ 𝒜} (U V:Φ)
  (EV : V⁻¹ = V) (PV : V ∙ V ∙ V ≤ U) : (τ X)♯ (T X V) ⊆ U.
Proof. intros [x y]. exact (trapped_entourage_points_alt U V EV PV x y). Qed.

Lemma trapped_near_member_thicken `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (A : trapped_filter F) (W S : Φ)
  : (τ X)* (near (T X W) F) ⊆ (S⁻¹ ∙ W ∙ S).[powerset_pt A].
Proof. exact (cauchy_near_member_thicken (trapped_filter F) A W S). Qed.

Lemma trapped_small_member_near `{@UnifBornSpace X Φ 𝒜} (F : 𝒯 X) (A : trapped_filter F) (W : Φ)
  (PA : A ⊗ A ⊆ W)
  : A ⊆ W.[(τ X)* (near (T X W) F)].
Proof. exact (cauchy_small_member_near (trapped_filter F) A W PA). Qed.


(** ** The trapped bornology.

    [K ⊆ 𝒯 X] is bounded when, at some ambient scale [U : Φ], the points
    of [X] approximating a member of [K] form a bounded set.  Covering is
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
+ split; try exact _.
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
#[global] Hint Extern 2 (DownSet (trapped_bornology _)) => simple notypeclasses refine trapped_bornology_ideal : typeclass_instances.
#[global] Hint Extern 2 (UpDirectedSubset (trapped_bornology _)) => simple notypeclasses refine trapped_bornology_ideal : typeclass_instances.

Lemma trapped_unif_born_space `{@WCUnifSpace X Φ 𝒜} : UnifBornSpace (𝒯 X).
Proof. do 2 (split; try exact _). intros F.
  pose proof trapped_prop F as [K HK].
  pose proof wcunif_thicken X K as [U HU].
  pose proof uniform_split_sym3 U as [V [EV HV]].
  exists V. rew (thicken_singleton _ _).
  now rew (trapped_near_member_thicken F (to_subset (U:=trapped_filter F) K) V V), EV, HV.
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


Lemma trapped_bounded_entourage `{@UnifBornSpace X Φ 𝒜} (S : 𝒫 (𝒯 X)) (W : trapped_uniformity X)
  : (τ X)* W.[S] ∊ 𝒜 ⊸ S ∊ trapped_bornology X.
Proof.
  pose proof trapped_entourage_basis W as [U HU].
  change ((τ X)* W.[S] ∊ 𝒜 ⊸ ∐ U:Φ, (τ X)* (T X U).[S] ∊ 𝒜).
  rew <-(aex_ub _ U). now rew HU.
Qed.

(** τ is a full UnifBorn-initial morphism: images of bounded sets are
    bounded at the scale [wcunif_thicken] provides (via
    [preimage_thicken_image_le] and the points-transport), and preimages
    of bounded sets are bounded because the trapped bornology is made of
    ambient thickenings ([thicken_expanding]). *)
Lemma to_trapped_initial `{@WCUnifSpace X Φ 𝒜} : GlobalWCUnifInitial (τ X).
Proof. do 4 (split; try exact _).
+ intros A. pose proof (wcunif_thicken X A) as [U HU].
  pose proof (ufm_reflection_alt (τ X) U) as [V HV].
  rew <-(trapped_bounded_entourage _ V).
  rew (preimage_thicken_image_le (τ X) U V A) in HV.
  now rew HV.
+ intros K. pose proof subset_pt_is_el K as [U HU].
  enough ((τ X)* K ⊆ (τ X)* (T X U).[powerset_pt K]) as E by now rew E.
  rew <-(order_preserving (τ X)* _ _). apply thicken_expanding.
Qed.
#[global] Hint Extern 2 (GlobalWCUnifInitial    (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (GlobalWCUnifMorphism   (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (GlobalWCUnifReflecting (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial     (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism    (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting  (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial    (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.

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
  pose proof cauchy_alt (trapped_filter F) W as [A PA];
    change (apos (A ⊗ A ⊆ powerset_pt W)) in PA.
  enough (F ∊ L ⊸ A ⊆ V.[(τ X)* (T X U).[powerset_pt L]]) as E by (rew E; now apply up_closed_alt).
  rew (trapped_small_member_near F A W PA).
  rew (near_sub_thicken (T X U) L F).
  rew <-(meet_lb_l U V : W ≤ U) at 1.
  rew <-(meet_lb_r U V : W ≤ V).
  exact (order_preserving ((ap1 thicken W) ∘ (τ X)*) _ _).
Qed.

Lemma trapped_bounded_closure `{@UnifBornSpace X Φ 𝒜} (L : trapped_bornology X)
  : ∐ K:𝒜, powerset_pt L ⊆ closure ((τ X)⁎ (powerset_pt K)).
Proof.
  pose proof subset_pt_is_el L as [U HU].
  exists (@to_subset _ 𝒜 _ HU). exact (dense_image_preimage_unit (τ X) L (T X U)).
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
  Context `{@UnifBornMorphism@{u} X Y Φ Ψ 𝒜 ℬ f}.

  Local Instance cauchy_map_trapped : MapsIntoTrapped (𝒞₁ f ∘ β X).
  Proof. intros F.
    pose proof (trapped_prop F) as [K HK].
    exists (born_image f K); change (f* (f⁎ K) ∊ trapped_filter F).
    now rew <-(preimage_image_unit f (powerset_pt K)).
  Qed.
  
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
    rew to_trapped_factor.
    exact (cauchy_map_spec f).
  Qed.

  Lemma trapped_map_dense `{!Dense f} : Dense trapped_map.
  Proof. apply (Dense_factor_right (τ X)). now rew trapped_map_unit. Qed.

  Lemma trapped_map_unif_initial `{!UniformlyInitial f} : UniformlyInitial trapped_map.
  Proof. refine (ufm_dense_initial (τ X) _); try exact _. now rew trapped_map_unit. Qed.
End functor.
Arguments trapped_map {X Y Φ Ψ 𝒜 ℬ} f {_}.
Local Abbreviation 𝒯₁ := trapped_map.

#[global] Hint Extern 2 (MapsIntoTrapped (func_op (cauchy_map _ ∘ from_trapped _))) => simple notypeclasses refine cauchy_map_trapped : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (trapped_map _)) => simple notypeclasses refine trapped_map_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (UniformContinuity (func_op (trapped_map _))) => simple notypeclasses refine trapped_map_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (trapped_map _)) => simple notypeclasses refine trapped_map_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (trapped_map ?f))) => simple notypeclasses refine trapped_map_dense : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial (trapped_map ?f)) => simple notypeclasses refine trapped_map_unif_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (trapped_map ?f)) => simple notypeclasses refine trapped_map_unif_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (trapped_map ?f))) => simple notypeclasses refine trapped_map_unif_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (trapped_map ?f)) => simple notypeclasses refine trapped_map_unif_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (trapped_map ?f)) => simple notypeclasses refine trapped_map_unif_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding (trapped_map _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (trapped_map _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (Injective (trapped_map _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.

Lemma trapped_map_unif_born@{u} `{@GlobalWCUnifMorphism@{u} X Y Φ Ψ 𝒜 ℬ f} : GlobalWCUnifMorphism (𝒯₁ f).
Proof. do 3 (split; try exact _). intros L.
  pose proof trapped_bounded_closure L as [K HK].
  rew HK. rew (continuous_image_closure _ _). rew <-(image_compose_alt _ _ _). rew trapped_map_unit.
  exact ( wcunif_closure_bounded (born_image (τ Y ∘ f) K) ).
Qed.
#[global] Hint Extern 2 (GlobalWCUnifMorphism (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (Bornological     (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born (f:=f)) : typeclass_instances.

Lemma trapped_map_born_initial@{u} `{@GlobalWCUnifMorphism@{u} X Y Φ Ψ 𝒜 ℬ f, !BornologyReflecting f}
  : BornologyInitial (𝒯₁ f).
Proof. do 2 (split; try exact _). intros K.
  pose proof subset_pt_is_el K as [V HV].
  rew <-(trapped_bounded_entourage _ (ufm_preimage (𝒯₁ f) (T Y V))).
  rew (preimage_thicken_uc_le (𝒯₁ f) _ _).
  change ( (𝒯₁ f ∘ τ X)* (T Y V).[powerset_pt K] ∊ 𝒜).
  rew trapped_map_unit.
  exact ( bornology_reflecting f (to_subset _ (el:=HV)) ).
Qed.
#[global] Hint Extern 2 (BornologyInitial    (trapped_map ?f)) => simple notypeclasses refine (trapped_map_born_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (trapped_map ?f)) => simple notypeclasses refine (trapped_map_born_initial (f:=f)) : typeclass_instances.

Lemma trapped_map_emb@{u} `{@GlobalWCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ f} : GlobalWCUnifEmbedding (𝒯₁ f).
Proof. repeat (split; try exact _). Qed.
#[global] Hint Extern 2 (GlobalWCUnifEmbedding  (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (GlobalWCUnifInitial    (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (GlobalWCUnifReflecting (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornEmbedding  (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial    (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.


Lemma trapped_map_id@{u} `{@UnifBornSpace@{u} X Φ 𝒜} : 𝒯₁ (id_fun X) = id_fun (𝒯 X).
Proof. refl. Qed.

Lemma trapped_map_compose@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ, @UnifBornSpace@{u} Z Ξ 𝒟}
  (f : X ⇾ Y) (g : Y ⇾ Z) `{!UnifBornMorphism f} `{!UnifBornMorphism g}
  : 𝒯₁ (g ∘ f) = 𝒯₁ g ∘ 𝒯₁ f.
Proof. refl. Qed.


(** ** Reflection.

    The third completion construction: for [ι : X ⇾ Y] dense and
    uniformly reflecting, [cauchy_reflect ι] corestricts to 𝒯 X under
    [BornologyReflecting ι] plus well-containment of the codomain:
    [wcunif_thicken] at a singleton gives every point a bounded
    neighborhood, whose trace is then a bounded member of the reflected
    filter (the witnessed-traces condition).  The same hypotheses
    [localize_functorial_refl] consumes. *)
Section reflect.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ}.
  Context (ι : X ⇾ Y) `{!Dense ι, !UnifBornReflecting ι}.

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
    rew trapped_reflect_factor, to_trapped_factor.
    exact (cauchy_reflect_spec ι).
  Qed.

  Lemma trapped_reflect_dense : Dense trapped_reflect.
  Proof. apply (Dense_factor_right ι). now rew trapped_reflect_spec. Qed.

  Lemma trapped_reflect_unif_initial `{!UniformlyContinuous ι} : UniformlyInitial trapped_reflect.
  Proof. refine (ufm_dense_initial ι _); try exact _. now rew trapped_reflect_spec. Qed.
End reflect.

#[global] Hint Extern 2 (MapsIntoTrapped (func_op (cauchy_reflect _))) => simple notypeclasses refine (cauchy_reflect_trapped _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (trapped_reflect _)) => simple notypeclasses refine (trapped_reflect_ufm_cont _) : typeclass_instances.
#[global] Hint Extern 2 (Continuous (trapped_reflect _)) => simple notypeclasses refine (trapped_reflect_ufm_cont _) : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (trapped_reflect ?f))) => simple notypeclasses refine (trapped_reflect_dense f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_unif_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_unif_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (trapped_reflect ?f))) => simple notypeclasses refine (trapped_reflect_unif_initial f) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_unif_initial f) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_unif_initial f) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding (trapped_reflect _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (trapped_reflect _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (Injective (trapped_reflect _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.

Local Abbreviation ℛ := trapped_reflect.

Lemma trapped_reflect_bornological@{u} `{@GlobalWCUnifReflecting@{u} X Y Φ Ψ 𝒜 ℬ ι, !Dense ι}
  : GlobalWCUnifMorphism (ℛ ι).
Proof. do 3 (split; try exact _). intros B.
  pose proof wcunif_thicken Y B as [V HV].
  rew (dense_image_preimage_unit ι B V).
  rew (continuous_image_closure (ℛ ι) _).
  rew <-(image_compose_alt ι _ _).
  rew (trapped_reflect_spec ι).
  exact (wcunif_closure_bounded (born_image (τ X) (born_preimage ι (to_subset _ (el:=HV))))).
Qed.
#[global] Hint Extern 2 (GlobalWCUnifMorphism (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_bornological (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism     (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_bornological (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (Bornological         (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_bornological (ι:=f)) : typeclass_instances.

Lemma trapped_reflect_born_initial@{u} `{@GlobalWCUnifReflecting@{u} X Y Φ Ψ 𝒜 ℬ ι, !Dense ι, !Bornological ι}
  : BornologyInitial (ℛ ι).
Proof. pose proof _ : WCUnifSpace Y.
  do 2 (split; try exact _). intros L.
  pose proof subset_pt_is_el L as [U HU].
  rew (dense_image_preimage_unit ι ((ℛ ι)* L) (ufm_preimage (ℛ ι) (T X U))).
  rew (preimage_thicken_uc_le (ℛ ι) _ _).
  change (closure (ι⁎ ((ℛ ι ∘ ι)* (T X U).[powerset_pt L])) ∊ ℬ).
  rew (trapped_reflect_spec ι).
  exact (wcunif_closure_bounded (born_image ι (to_subset _ (el:=HU)))).
Qed.
#[global] Hint Extern 2 (BornologyInitial    (trapped_reflect ?f)) => simple notypeclasses refine trapped_reflect_born_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (trapped_reflect ?f)) => simple notypeclasses refine trapped_reflect_born_initial : typeclass_instances.

Lemma trapped_reflect_initial@{u} `{@GlobalWCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ ι, !Dense ι}
  : GlobalWCUnifInitial (ℛ ι).
Proof. repeat (split; try exact _). Qed.
#[global] Hint Extern 2 (GlobalWCUnifInitial    (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (GlobalWCUnifReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial    (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.

Lemma trapped_reflect_emb@{u} `{@GlobalWCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ ι, !Dense ι, !SeparatedUniformSpace Y}
  : GlobalWCUnifEmbedding (ℛ ι).
Proof. now split. Qed.
#[global] Hint Extern 2 (GlobalWCUnifEmbedding (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_emb (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornEmbedding     (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_emb (ι:=f)) : typeclass_instances.


(** * The canonical completion of 𝐖𝐂𝐔𝐧𝐢𝐟_gbl: (𝒯, τ, trapped_map, trapped_reflect). *)

Definition gbl_wcunif_canonical_completor@{u} : CanonicalCompletor@{u} 𝐖𝐂𝐔𝐧𝐢𝐟_gbl (U:=λ (X:set@{u}) '(Φ, 𝒜), @UniformNeighborhood@{u} X Φ).
Proof. unshelve esplit.
+ intros X [Φ 𝒜] HX. exact (𝒯 X).
+ intros X [Φ 𝒜] HX. now split.
+ intros X [Φ 𝒜] HX. exact (τ X).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f Hf. exact (𝒯₁ f).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX f Hf1 Hf2. change (GlobalWCUnifReflecting f) in Hf1. exact (ℛ f).
Defined.
#[global] Hint Extern 2 (CanonicalCompletor 𝐖𝐂𝐔𝐧𝐢𝐟_gbl) => exact gbl_wcunif_canonical_completor : typeclass_instances.

Lemma gbl_wcunif_canonical_completion : CanonicalCompletion 𝐖𝐂𝐔𝐧𝐢𝐟_gbl.
Proof. split.
+ intros X [Φ 𝒜] HX. now change (Hausdorff (𝒯 X)).
+ intros X [Φ 𝒜] HX. now change (GlobalWCUnifInitial (τ X)).
+ intros X [Φ 𝒜] HX. now change (Dense (τ X)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f Hf. now change (GlobalWCUnifMorphism (𝒯₁ f)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f Hf. change (GlobalWCUnifMorphism f) in Hf. exact (trapped_map_unit (f:=f)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f HR HD. change (GlobalWCUnifReflecting f) in HR.
  now change (GlobalWCUnifMorphism (ℛ f)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f HR HD. change (GlobalWCUnifReflecting f) in HR.
  exact (trapped_reflect_spec f).
Qed.
#[global] Hint Extern 2 (CanonicalCompletion 𝐖𝐂𝐔𝐧𝐢𝐟_gbl) => simple notypeclasses refine gbl_wcunif_canonical_completion : typeclass_instances.

(** (K3): [trapped_map_emb] already preserves the initial class. *)
Lemma gbl_wcunif_canonical_map_initial : CanonicalCompletionMapInitial 𝐖𝐂𝐔𝐧𝐢𝐟_gbl.
Proof. split. intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f Hf.
  change (GlobalWCUnifInitial f) in Hf. now change (GlobalWCUnifInitial (𝒯₁ f)).
Qed.
#[global] Hint Extern 2 (CanonicalCompletionMapInitial 𝐖𝐂𝐔𝐧𝐢𝐟_gbl) => simple notypeclasses refine gbl_wcunif_canonical_map_initial : typeclass_instances.
