Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base uniform.subspace uniform.product.
Require Import easy rewrite replc simplify tactics.misc.

Import image_notation.
Local Open Scope subset_scope.
Local Open Scope topology_scope.

(** * (E, M) image factorization of a uniformly continuous map

    Every uniformly continuous [f : X ⇾ Y] factors as [f = m ∘ e] through the
    closure of its image:

      X --[image_corestrict]--> closure (range f) --[from_subset]--> Y

    with [e = image_corestrict f] a dense UC map (the E-part) and
    [m = from_subset (closure (range f))] a closed uniform embedding (the M-part).
    This is the factorization structure of doc/factorization.md §"design question". *)

Section image_factorization.
  Universes u.
  Context `{@UniformSpace@{u} X Φ} `{@UniformSpace@{u} Y Ψ} (f:X ⇾ Y) `{!UniformlyContinuous f}.

  Definition image_closure : 𝒫 Y := closure (range f).

  Lemma image_closure_closed : closed image_closure.
  Proof. exact (closure_closed (range f)). Qed.
  Lemma image_corestrict_el (x:X) : f x ∊ image_closure.
  Proof. unfold image_closure. rew <-(subset_closure (range f)). exact range_el. Qed.

  Local Instance image_corestrict_is_fun
    : @IsFun X image_closure (λ x, @to_subset _ image_closure (f x) (image_corestrict_el x)).
  Proof. intros x₁ x₂. exact (is_fun f x₁ x₂). Qed.

  Definition image_corestrict : X ⇾ image_closure
    := func_make (λ x, @to_subset _ image_closure (f x) (image_corestrict_el x)).

  Lemma image_factor : from_subset image_closure ∘ image_corestrict = f.
  Proof. refl. Qed.

  Local Instance image_corestrict_ufm : UniformlyContinuous image_corestrict.
  Proof.
    assert (UniformlyContinuous (from_subset image_closure ∘ image_corestrict)) by (rew image_factor; exact _). exact (pullback_uniformity_initial (f:=from_subset image_closure) image_corestrict). Qed.

  Local Instance image_corestrict_dense : Dense image_corestrict.
  Proof. split; try exact _.
    change (apos (closure (range image_corestrict) = ⊤)).
    apply (above_top _).
    rew <-(reflection_preimage_closure (from_subset image_closure) (range image_corestrict)).
    rew (range_image image_corestrict), <-(image_compose_alt image_corestrict (from_subset image_closure) ⊤).
    rew image_factor, <-(range_image f).
    change (⊤ ⊆ (from_subset image_closure)* image_closure).
    change (∏ a:image_closure, a ∊ ⊤ ⊸ a ∊ (from_subset image_closure)* image_closure). intros a.
    rew (aimpl_true_l (_ : a ∊ ⊤)). change (from_subset image_closure a ∊ image_closure). exact (subset_pt_is_el a).
  Qed.
End image_factorization.

(** Continuous image of a closure lands in the closure of the image — the image
    counterpart of [continuous_preimage_closure], via the image/preimage
    adjunction.  (General enough to belong beside [continuous_preimage_closure]
    in [interior.v]; kept here for now.) *)
Lemma continuous_image_closure@{u} {X Y:set@{u}} `{@Continuous@{u} X Y NX NY g} (U:𝒫 X)
  : g⁎ (closure U) ⊆ closure (g⁎ U).
Proof.
  rew (image_preimage_adj g (closure U) (closure (g⁎ U))).
  rew <-(continuous_preimage_closure g (g⁎ U)).
  exact (aimpl_impl_pos (order_preserving closure U (g* (g⁎ U))) (preimage_image_unit g U)).
Qed.

(** The image of any subset under a subspace inclusion lands in the subset: the
    range of [from_subset K] is contained in [K]. *)
Lemma from_subset_image_sub@{v} {D:set@{v}} (K:𝒫 D) (S:𝒫 (subset_to_set K)) : (from_subset K)⁎ S ⊆ K.
Proof.
  change (∏ y:D, y ∊ (from_subset K)⁎ S ⊸ y ∊ K). intros y.
  change (y ∊ (from_subset K)⁎ S) with (∐ a:subset_to_set K, from_subset K a = y ⊠ a ∊ S).
  rew <-aex_adj; intros a.
  rew <-(equal_element K (from_subset K a) y).
  apply aprod_proper_aimpl; [ easy |].
  now apply aimpl_true_r.
Qed.

(** * Diagonalization

    The (E, M)-diagonalization property, in its honest constructive form: the
    M-part is represented as an actual subspace inclusion [from_subset K] (K
    closed), so the diagonal is a corestriction-with-certificate and needs no
    unique choice; uniqueness is separation-free, resting on injectivity of the
    inclusion alone.  See doc/factorization.md §"design question". *)

Section diagonalization.
  Universes u.
  Context `{@UniformSpace@{u} A ΦA} `{@UniformSpace@{u} B ΦB} `{@UniformSpace@{u} D ΦD}.
  Context (e:A ⇾ B) `{!UniformlyContinuous e, !Dense e}.
  Context (K:𝒫 D) (HK : closed K).
  Context (g:B ⇾ D) `{!UniformlyContinuous g}.
  Context (f':A ⇾ subset_to_set K) `{!UniformlyContinuous f'}.
  Context (Hcomm : g ∘ e = from_subset K ∘ f').

  Lemma diagonal_range_sub : range g ⊆ K.
  Proof.
    rew <-HK.
    rew (range_image g), <-(dense_range : closure (range e) = ⊤).
    assert (g⁎ (range e) ⊆ K) as Hsub.
    { rew (range_image e), <-(image_compose_alt e g ⊤), Hcomm, (image_compose_alt f' (from_subset K) ⊤).
      exact (from_subset_image_sub K (f'⁎ ⊤)). }
    rew <-(aimpl_impl_pos (order_preserving closure (g⁎ (range e)) K) Hsub). exact (continuous_image_closure (g:=g) (range e)).
  Qed.

  Lemma diagonal_el (b:B) : g b ∊ K.
  Proof. rew <-diagonal_range_sub. exact range_el. Qed.

  Local Instance diagonal_is_fun
    : @IsFun B (subset_to_set K) (λ b, @to_subset _ K (g b) (diagonal_el b)).
  Proof. intros b₁ b₂. exact (is_fun g b₁ b₂). Qed.

  Definition diagonal : B ⇾ K := func_make (λ b, @to_subset _ K (g b) (diagonal_el b)).

  Lemma diagonal_factor_m : from_subset K ∘ diagonal = g.
  Proof. refl. Qed.

  Lemma diagonal_factor_e : diagonal ∘ e = f'.
  Proof. change (∏ a:A, diagonal (e a) = f' a). intros a.
    change (g (e a) = subset_pt (f' a)). exact (Hcomm a).
  Qed.

  Local Instance diagonal_ufm : UniformlyContinuous diagonal.
  Proof.
    assert (UniformlyContinuous (from_subset K ∘ diagonal)) by (rew diagonal_factor_m; exact _).
    exact (pullback_uniformity_initial (f:=from_subset K) diagonal).
  Qed.

  (** Uniqueness is separation-free: it rests on injectivity of the inclusion
      [from_subset K] alone (the M-side mono), not on any separation of the
      codomain. *)
  Lemma diagonal_unique (d':B ⇾ subset_to_set K) : from_subset K ∘ d' = g → diagonal = d'.
  Proof. intros Hd'.
    rew <-(injective_compose_cancel (from_subset K) diagonal d').
    rew diagonal_factor_m, Hd'. refl.
  Qed.
End diagonalization.

(** * Essential uniqueness of the factorization

    Any two dense-corestriction factorizations of the same map through closed
    subspaces are related by a unique uniform isomorphism of the M-objects.  As
    with [diagonal_unique], the round-trip identities are forced by injectivity
    of the inclusions alone — no separation of the ambient space. *)
Section essential_uniqueness.
  Universes u.
  Context `{@UniformSpace@{u} X ΦX} `{@UniformSpace@{u} Y ΦY}.
  Context (K₁ K₂:𝒫 Y) (HK₁ : closed K₁) (HK₂ : closed K₂).
  Context (e₁:X ⇾ subset_to_set K₁) `{!UniformlyContinuous e₁, !Dense e₁}.
  Context (e₂:X ⇾ subset_to_set K₂) `{!UniformlyContinuous e₂, !Dense e₂}.
  Context (Hcomm : from_subset K₁ ∘ e₁ = from_subset K₂ ∘ e₂).

  Lemma ess_comm_sym : from_subset K₂ ∘ e₂ = from_subset K₁ ∘ e₁.
  Proof. now rew Hcomm. Qed.

  Definition ess_iso : K₁ ⇾ K₂ := diagonal e₁ K₂ HK₂ (from_subset K₁) e₂ Hcomm.
  #[local] Instance ess_iso_inverse : Inverse ess_iso
    := diagonal e₂ K₁ HK₁ (from_subset K₂) e₁ ess_comm_sym.

  Lemma ess_iso_factor_m : from_subset K₂ ∘ ess_iso = from_subset K₁.
  Proof. exact (diagonal_factor_m e₁ K₂ HK₂ (from_subset K₁) e₂ Hcomm). Qed.
  Local Open Scope fun_inv_scope.
  Lemma ess_iso_inv_factor_m : from_subset K₁ ∘ ess_iso⁻¹ = from_subset K₂.
  Proof. exact (diagonal_factor_m e₂ K₁ HK₁ (from_subset K₂) e₁ ess_comm_sym). Qed.

  Local Instance ess_iso_ufm : UniformlyContinuous ess_iso.
  Proof. exact (diagonal_ufm e₁ K₂ HK₂ (from_subset K₁) e₂ Hcomm). Qed.
  Local Instance ess_iso_inv_ufm : UniformlyContinuous ess_iso⁻¹.
  Proof. exact (diagonal_ufm e₂ K₁ HK₁ (from_subset K₂) e₁ ess_comm_sym). Qed.

  Lemma ess_iso_bijective : Bijective ess_iso.
  Proof. apply alt_Build_Bijective.
    + rew <-(injective_compose_cancel (from_subset K₁) (ess_iso⁻¹ ∘ ess_iso) (id_fun K₁)).
      change (from_subset K₁ ∘ ess_iso⁻¹ ∘ ess_iso = from_subset K₁ ∘ id_fun K₁).
      rew ess_iso_inv_factor_m, ess_iso_factor_m. refl.
    + rew <-(injective_compose_cancel (from_subset K₂) (ess_iso ∘ ess_iso⁻¹) (id_fun K₂)).
      change (from_subset K₂ ∘ ess_iso ∘ ess_iso⁻¹ = from_subset K₂ ∘ id_fun K₂).
      rew ess_iso_factor_m, ess_iso_inv_factor_m. refl.
  Qed.
End essential_uniqueness.

(** * Firmness of the completion (Brümmer–Giuli)

    Completions are firm: any two completions of the same space are related by a
    unique uniform isomorphism compatible with the embeddings.  This is the
    completion-side instance of essential uniqueness — the reflect maps go both
    ways, and the round-trip identities are forced by [cont_dense_epi] (two maps
    agreeing on a dense subspace of a separated target are equal). *)
Section firmness.
  Universes u.
  Context `{@UniformSpace@{u} X Φ}
          `{@UniformSpace@{u} Y₁ Ψ₁} (ι₁:X ⇾ Y₁) `{!@CompletionReflect@{u} X Y₁ Φ Ψ₁ ι₁, !Completion ι₁}
          `{@UniformSpace@{u} Y₂ Ψ₂} (ι₂:X ⇾ Y₂) `{!@CompletionReflect@{u} X Y₂ Φ Ψ₂ ι₂, !Completion ι₂}.
  Local Open Scope fun_inv_scope.

  Definition firm_iso : Y₁ ⇾ Y₂ := completion_reflect_initial ι₂ ι₁.
  #[local] Instance firm_iso_inverse : Inverse firm_iso := completion_reflect_initial ι₁ ι₂.

  Lemma firm_iso_spec : firm_iso ∘ ι₁ = ι₂.
  Proof. exact (completion_reflect_initial_spec ι₂ ι₁). Qed.
  Lemma firm_iso_inv_spec : firm_iso⁻¹ ∘ ι₂ = ι₁.
  Proof. exact (completion_reflect_initial_spec ι₁ ι₂). Qed.

  Local Instance firm_iso_ufm : UniformlyContinuous firm_iso.
  Proof. change (UniformlyContinuous (completion_reflect_initial ι₂ ι₁)). exact _. Qed.
  Local Instance firm_iso_inv_ufm : UniformlyContinuous firm_iso⁻¹.
  Proof. change (UniformlyContinuous (completion_reflect_initial ι₁ ι₂)). exact _. Qed.

  Local Instance firm_iso_cont : Continuous firm_iso := firm_iso_ufm.
  Local Instance firm_iso_inv_cont : Continuous firm_iso⁻¹ := firm_iso_inv_ufm.

  Lemma firm_iso_bijective : Bijective firm_iso.
  Proof. apply alt_Build_Bijective.
    + destruct (aiff_iff_pos (cont_dense_epi (NX:=@UniformNeighborhood Y₁ Ψ₁) (NY:=@UniformNeighborhood Y₁ Ψ₁) (firm_iso⁻¹ ∘ firm_iso) (id_fun Y₁) ι₁)) as [Hfwd _].
      apply Hfwd. change (firm_iso⁻¹ ∘ (firm_iso ∘ ι₁) = id_fun Y₁ ∘ ι₁).
      rew firm_iso_spec, firm_iso_inv_spec. refl.
    + destruct (aiff_iff_pos (cont_dense_epi (NX:=@UniformNeighborhood Y₂ Ψ₂) (NY:=@UniformNeighborhood Y₂ Ψ₂) (firm_iso ∘ firm_iso⁻¹) (id_fun Y₂) ι₂)) as [Hfwd _].
      apply Hfwd. change (firm_iso ∘ (firm_iso⁻¹ ∘ ι₂) = id_fun Y₂ ∘ ι₂).
      rew firm_iso_inv_spec, firm_iso_spec. refl.
  Qed.

  (** The compatible iso is unique — the completion is a firm reflection. *)
  Lemma firm_iso_unique (φ:Y₁ ⇾ Y₂) `{!UniformlyContinuous φ} : φ ∘ ι₁ = ι₂ → φ = firm_iso.
  Proof. intros Hφ.
    pose proof (uniformly_continuous_continuous (f:=φ)) as Hφc.
    destruct (aiff_iff_pos (cont_dense_epi (NX:=@UniformNeighborhood Y₁ Ψ₁) (NY:=@UniformNeighborhood Y₂ Ψ₂) φ firm_iso ι₁)) as [Hfwd _].
    apply Hfwd. rew Hφ, firm_iso_spec. refl.
  Qed.
End firmness.

(** * E-cancellation of M: closed embeddings cancel on the left along E

    If [g ∘ f] is a closed uniform embedding and [f] is dense UC, then [g] is a
    closed uniform embedding.  The closed-image half reuses [continuous_image_closure]
    ([range g = range (g∘f)]); [UniformlyInitial g] is the kernel [ufm_dense_initial];
    and injectivity follows from initiality into/over a separated space
    ([uniform_initial_embedding]).  This is the M-cancellation shell of
    doc/factorization.md. *)
Section closed_embedding_cancel.
  Universes u.
  Context `{@UniformSpace@{u} A ΦA} `{@SeparatedUniformSpace@{u} B ΦB} `{@UniformSpace@{u} C ΦC}.
  Context (f:A ⇾ B) (g:B ⇾ C) `{!UniformlyContinuous f, !Dense f, !UniformlyContinuous g}.
  Context `{!UniformlyEmbedding (g ∘ f)} (Hclosed : closed (range (g ∘ f))).

  Lemma cancel_image_eq : g⁎ (range f) = range (g ∘ f).
  Proof. rew (range_image f), <-(image_compose_alt f g ⊤), <-(range_image (g ∘ f)). refl. Qed.

  Lemma cancel_range_eq : range g = range (g ∘ f).
  Proof.
    rew <-(le_antisym_iff _ _). split.
    + rew <-Hclosed, <-cancel_image_eq.
      rew (range_image g), <-(dense_range : closure (range f) = ⊤).
      exact (continuous_image_closure (g:=g) (range f)).
    + rew <-cancel_image_eq, (range_image g).
      exact (aimpl_impl_pos (order_preserving (g⁎) (range f) ⊤) (below_top _)).
  Qed.

  Lemma cancel_closed_range : closed (range g).
  Proof. rew cancel_range_eq. exact Hclosed. Qed.

  Local Instance cancel_initial : UniformlyInitial g.
  Proof. exact (ufm_dense_initial f g). Qed.

  Lemma cancel_embedding : UniformlyEmbedding g.
  Proof. exact uniform_initial_embedding. Qed.
End closed_embedding_cancel.
