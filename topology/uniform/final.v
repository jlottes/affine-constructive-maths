Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.subgroups.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base uniform.basis uniform.subspace.
Require Import easy rewrite replc simplify strip_coercions.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Import projection_notation.
Import image_notation.
Import tensor_map_notation.

(** The subset of pre-uniformities, as a weak spred on !(Uniformity X). *)
Lemma PreUniformSpace_proper_impl@{u} {X:set@{u}} (Φ₁ Φ₂:Uniformity X)
  : Φ₁ = Φ₂ → sprop.impl (@PreUniformSpace X Φ₁, @PreUniformSpace X Φ₂).
Proof. intros E [???]; split; now rew <-E. Qed.
Canonical Structure PreUniformSpace_fun {X} : of_course_set (Uniformity X) ⇾ SProp
  := make_weak_spred (@PreUniformSpace X) PreUniformSpace_proper_impl.

Definition PreUniformity X : 𝒫 (of_course_set (Uniformity X))
  := of_course_counit _ ∘ of_course_fun ∘ PreUniformSpace_fun.
#[global] Hint Extern 2 (@PreUniformSpace _ (subset_pt ?Φ)) =>
  simple notypeclasses refine (subset_pt_is_el Φ) : typeclass_instances.

(** The largest uniformity contained in a given filter [L] of entourages.

    The construction takes the union of all pre-uniformities lying below [L],
    closed upward.  The pre-uniformity axioms (reflexivity, symmetry, the
    triangle/splitting axiom) are supplied entirely by those witnessing
    pre-uniformities; the only thing required of [L] itself is that it be a
    [Filter] — up-closed, meet-closed, and containing [⊤].  In particular [L]
    need not be symmetric, reflexive, or closed under splitting. *)
Definition uniformity_of_filter {Y:set} : 𝒫² (Y ⊗ Y) ⇾ 𝒫² (Y ⊗ Y)
  := set:(λ L:𝒫² (Y ⊗ Y), { U : 𝒫 (Y ⊗ Y) | ∐ Ψ:PreUniformity Y, subset_pt Ψ ⊆ L ⊠ ∐ V, V ∊ Ψ ⊠ V ⊆ U }).


Definition preuniformity_join (X:set)
  := set:(λ '(Φ₁, Φ₂) : set_T (𝒫² (X ⊗ X) ⊗ 𝒫² (X ⊗ X)),
              { W : 𝒫 (X ⊗ X) | ∐ U V : 𝒫 (X ⊗ X), U ∊ Φ₁ ⊠ V ∊ Φ₂ ⊠ U ⊓ V ⊆ W }).

Local Ltac unfold_preufm_join :=
   change (?W ∊ func_op (preuniformity_join ?X) (?Φ₁, ?Φ₂))
     with ( ∐ U V : 𝒫 (X ⊗ X), U ∊ Φ₁ ⊠ V ∊ Φ₂ ⊠ U ⊓ V ⊆ W ).

Lemma preuniformity_join_prop {X:set} {Φ₁ Φ₂} `{!@PreUniformSpace X Φ₁} `{!@PreUniformSpace X Φ₂}
  : PreUniformity X (preuniformity_join X (Φ₁, Φ₂)).
Proof. split.
+ intros W. unfold_preufm_join. rew <-aex_adj; intros U; rew <-aex_adj; intros V.
  rew <-(transitivity (≤) (id_rel X) (U ⊓ V) W).
  rew <-(aprod_assoc _ _ _). apply aprod_proper_aimpl; [| easy].
  rew <-(meet_glb _ _ _).
  apply aprod_proper_aimpl; apply uniform_refl.
+ intros W. unfold_preufm_join. rew <-aex_adj; intros U; rew <-aex_adj; intros V.
  rew <-(aex_ub _ U⁻¹), <-(aex_ub _ V⁻¹).
  apply aprod_proper_aimpl; [| apply aprod_proper_aimpl ]; [ apply uniform_sym .. |].
  now rew (order_preserving inv _ W), (preserves_meet inv _ _).
+ intros [W HW]; revert HW. unfold_preufm_join. intros [U₁ [U₂ [HU1 [HU2 PU]]]].
  change (∐ V:powerset_el (preuniformity_join X (Φ₁, Φ₂)), powerset_pt V ∙ powerset_pt V ⊆ W).
  enough (∐ V:𝒫 (X ⊗ X), V ∊ preuniformity_join X (Φ₁, Φ₂) ⊠ V ∙ V ⊆ W) as [V[HV PV]] by now exists (to_subset V).
  pose proof (uniform_split (@to_subset _ _ _ HU1)) as [[V₁ HV1] PV1]; change (apos (V₁ ∙ V₁ ⊆ U₁)) in PV1.
  pose proof (uniform_split (@to_subset _ _ _ HU2)) as [[V₂ HV2] PV2]; change (apos (V₂ ∙ V₂ ⊆ U₂)) in PV2.
  exists (V₁ ⊓ V₂). split.
  * unfold_preufm_join. exists V₁. exists V₂. now simplify.
  * rew (preserves_meet_lax2 (∙) _ _ _ _). now rew [PV1 | PV2].
Qed.

Lemma uniformity_of_filter_mono {Y} : OrderPreserving (@uniformity_of_filter Y).
Proof. apply alt_Build_OrderPreserving. intros L₁ L₂.
  change (L₁ ⊆ L₂ ⊸ ∏ U, (∐ Ψ:PreUniformity Y, subset_pt Ψ ⊆ L₁ ⊠ ∐ V, V ∊ Ψ ⊠ V ⊆ U)
                        ⊸ ∐ Ψ:PreUniformity Y, subset_pt Ψ ⊆ L₂ ⊠ ∐ V, V ∊ Ψ ⊠ V ⊆ U).
  rew <-all_adj; intros U.
  rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj; intros Ψ. rew <-(aex_ub _ Ψ).
  enough (subset_pt Ψ ⊆ L₁ ⊠ L₁ ⊆ L₂ ⊸ subset_pt Ψ ⊆ L₂) as P by (revert P; tautological).
  now apply transitivity.
Qed.
#[global] Hint Extern 2 (OrderPreserving uniformity_of_filter) => simple notypeclasses refine uniformity_of_filter_mono : typeclass_instances.

Section uniformity_of_filter.
  Universes u.
  Context {Y:set@{u}} (L:𝒫² (Y ⊗ Y)).

  Local Abbreviation Θ := (func_op (@uniformity_of_filter Y) L).

  #[local] Hint Extern 0 (Uniformity Y) => exact Θ : typeclass_instances.

  Local Ltac unfold_uniformity_of_filter :=
    change (?a ∊ Θ) with ( ∐ Ψ:PreUniformity Y, subset_pt Ψ ⊆ L ⊠ ∐ V, V ∊ Ψ ⊠ V ⊆ a ).

  Context `{!Filter L}.

  Let inst2 : SubLattice L.  Proof. exact filter_sub_lattice. Qed.
  Let inst3 : MeetSubBoundedSemiLattice L.  Proof. exact filter_bounded_meet_sub_sl. Qed.

  Lemma uniformity_of_filter_sub : Θ ⊆ L.
  Proof. intros U. unfold_uniformity_of_filter. rew <-aex_adj.
    intros Ψ. rew aex_frob_l, <-aex_adj. intros V.
    rew (up_closed L V U), <-(subset_apply V (subset_pt Ψ) L).
    tautological.
  Qed.

  Lemma uniformity_of_filter_meet U V : U ∊ Θ ⊠ V ∊ Θ ⊸ U ⊓ V ∊ Θ.
  Proof. unfold_uniformity_of_filter. rew <-aex_adj2; intros Ψ₁ Ψ₂.
    pose (Ψ := preuniformity_join Y (subset_pt Ψ₁, subset_pt Ψ₂)).
    pose proof preuniformity_join_prop : PreUniformity Y Ψ as HΨ.
    rew <-(aex_ub _ (@to_subset _ (PreUniformity Y) _ HΨ)).
    refine ((tautology : ∀ P₁ P₂ Q₁ Q₂ P Q : Ω, (P₁ ⊠ P₂ ⊸ P) → (Q₁ ⊠ Q₂ ⊸ Q) → (P₁ ⊠ Q₁) ⊠ (P₂ ⊠ Q₂) ⊸ P ⊠ Q)
            _ _ _ _ _ _ _ _).
  + clear U V.
    change (subset_pt Ψ₁ ⊆ L ⊠ subset_pt Ψ₂ ⊆ L ⊸ Ψ ⊆ L); change (?x ≤ ?y) with (∏ z, z ∊ x ⊸ z ∊ y).
    rew <-all_adj. intros W. rew <-(aprod_adj _ _ _).
    change (W ∊ Ψ) with (∐ U V : 𝒫 (Y ⊗ Y), U ∊ Ψ₁ ⊠ V ∊ Ψ₂ ⊠ U ⊓ V ⊆ W).
    rew aex_frob_l, <-aex_adj; intros U.
    rew aex_frob_l, <-aex_adj; intros V.
    rew (all_lb _ U) at 1. rew (all_lb _ V).
    refine ((tautology : ∀ P₁ Q₁ P₂ Q₂ R S, (R ⊸ (Q₁ ⊠ Q₂ ⊸ S)) → ((P₁ ⊸ Q₁) ⊠ (P₂ ⊸ Q₂)) ⊠ P₁ ⊠ P₂ ⊠ R ⊸ S)
            _ _ _ _ _ _ _).
    rew (sub_meet_closed (U:=L) U V). exact (up_closed _ _ _).
  + rew <-aex_adj2. intros A B. rew <-(aex_ub _ (A ⊓ B)).
    refine ((tautology : ∀ P₁ P₂ Q₁ Q₂ P Q : Ω, (P₁ ⊠ P₂ ⊸ P) → (Q₁ ⊠ Q₂ ⊸ Q) → (P₁ ⊠ Q₁) ⊠ (P₂ ⊠ Q₂) ⊸ P ⊠ Q)
            _ _ _ _ _ _ _ _).
    * clear U V. change (A ∊ Ψ₁ ⊠ B ∊ Ψ₂ ⊸  ∐ U V : 𝒫 (Y ⊗ Y), U ∊ Ψ₁ ⊠ V ∊ Ψ₂ ⊠ U ⊓ V ⊆ A ⊓ B).
      rew <-(aex_ub _ A), <-(aex_ub _ B). now simplify.
    * exact (order_preserving (⊓) (A, B) (U, V)).
  Qed.

  Local Instance uniformity_of_filter_filter : Filter Θ.
  Proof. split.
  + apply Build_UpSet. intros U V. unfold_uniformity_of_filter.
    rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj; intros Ψ.
    rew <-(aex_ub _ Ψ).
    refine ((tautology : ∀ P Q R S : Ω, (P ⊠ R ⊸ S) → (P ⊠ Q ⊠ R ⊸ Q ⊠ S)) _ _ _ _ _).
    rew aex_frob_l, <-aex_adj; intros W; rew <-(aex_ub _ W).
    refine ((tautology : ∀ P Q R S : Ω, (R ⊠ P ⊸ S) → (P ⊠ Q ⊠ R ⊸ Q ⊠ S)) _ _ _ _ _).
    now apply transitivity.
  + apply Build_DownDirectedSubset.
    - exists ⊤. unfold_uniformity_of_filter.
      exists (@to_subset _ (PreUniformity Y) (indiscrete_uniformity Y) indiscrete_uniform_space).
      split.
      * intros U. change (U ∊ indiscrete_uniformity Y ⊸ U ∊ L).
        rew (indiscrete_entourage_alt _).
        rew <-(equal_element L ⊤ U). enough (⊤ ∊ L) by (simplify; now apply symmetry).
        exact filter_top.
      * exists ⊤. split; [ now exists tt | easy ].
    - intros U V. rew <-(aex_ub _ (U ⊓ V)).
      rew (aprod_true_r (meet_lb_r _ _)), (aprod_true_r (meet_lb_l _ _)).
      apply uniformity_of_filter_meet.
  Qed.

  Local Instance uniformity_of_filter_space : UniformSpace Y.
  Proof. split; try exact _. split.
  + intros W. unfold_uniformity_of_filter. rew <-aex_adj; intros Ψ.
    rew aex_frob_l, <-aex_adj; intros  U.
    rew <-(transitivity (≤) (id_rel Y) U W).
    refine ((tautology : ∀ P Q R S : Ω, (Q ⊸ S) → (P ⊠ Q ⊠ R ⊸ S ⊠ R)) _ _ _ _ _).
    apply uniform_refl.
  + intros W. unfold_uniformity_of_filter. rew <-aex_adj; intros Ψ; rew <-(aex_ub _ Ψ).
    apply aprod_proper_aimpl; [ easy |].
    rew <-aex_adj; intros U. rew <-(aex_ub _ U⁻¹). apply aprod_proper_aimpl.
    * apply uniform_sym.
    * exact (order_preserving inv _ _).
  + intros [U HU]. change (∐ V:powerset_el Θ, powerset_pt V ⋄ powerset_pt V ⊆ U).
    enough (∐ V:𝒫 (Y ⊗ Y), V ∊ Θ ⊠ V ∙ V ⊆ U) as [V[HV PV]] by now exists (to_subset V).
    revert HU. intros [Ψ [HΨ1 [V [HV PV]]]].
    pose proof uniform_split (@to_subset _ _ V HV) as [[W HW] PW]; change (apos (W ∙ W ⊆ V)) in PW.
    exists W; split.
    * exists Ψ. split; trivial. now exists W.
    * now rew <-PV.
  Qed.
End uniformity_of_filter.

Section final.
  Universes u.
  Context {Λ:Type@{u}} {X:Λ → set@{u}} {Φ:∀ i, Uniformity (X i)} {Y:set@{u}} (f:∀ i, X i ⇾ Y).

  Definition final_semiuniformity := { U : 𝒫 (Y ⊗ Y) | ∏ i, ⟨f i, f i⟩* U ∊ Φ i }.
  Local Abbreviation L := final_semiuniformity.
  
  Definition final_uniformity := uniformity_of_filter L.
  Local Abbreviation Θ := final_uniformity.
  
  #[local] Hint Extern 0 (Uniformity Y) => exact Θ : typeclass_instances.

  Local Ltac unfold_final_semiuniformity :=
    change (?a ∊ L) with ( ∏ i, ⟨f i, f i⟩* a ∊ Φ i ).

  Context `{∀ i, UniformSpace (X i)}.

  Local Instance final_semiuniformity_filter : Filter L.
  Proof. split.
  + apply Build_UpSet. intros U V. unfold_final_semiuniformity.
    rew <-(aprod_adj _ _ _). rew <-all_adj. intros i. rew (aprod_adj _ _ _). 
    rew (all_lb _ i). rew (order_preserving ⟨f i, f i⟩* U V).
    pose proof _ : UniformSpace (X i).
    exact (up_closed _ _ _).
  + apply Build_DownDirectedSubset.
    * exists ⊤. intros i. rew (preserves_top _). now pose proof _ : UniformSpace (X i).
    * intros U V. rew <-(aex_ub _ (U ⊓ V)).
      rew (aprod_true_r (meet_lb_r _ _)), (aprod_true_r (meet_lb_l _ _)).
      unfold_final_semiuniformity. rew <-all_adj; intros i. pose proof _ : UniformSpace (X i).
      rew (all_lb _ i).
      rew (preserves_meet ⟨f i, f i⟩* U V).
      apply sub_meet_closed.
  Qed.
  
  Lemma final_uniformity_sub_semi : Θ ⊆ L.
  Proof. exact (uniformity_of_filter_sub L). Qed.

  Local Instance final_uniformity_filter : Filter Θ
    := uniformity_of_filter_filter L.
  Local Instance final_uniformity_space : UniformSpace Y
    := uniformity_of_filter_space L.

  Local Instance sink_map_ufm_cont i : UniformlyContinuous (f i).
  Proof. pose proof _ : UniformSpace (X i).
    apply (uniformly_continuous_alt _).
    intros [V HV]. change (⟨f i, f i⟩* V ∊ Φ i).
    rew final_uniformity_sub_semi in HV. exact (HV i).
  Qed.
  
  (** Universal Property *)
  
  Context `{@UniformSpace@{u} Z Ξ} (g:Y ⇾ Z).
  Context (P:∀ i, UniformlyContinuous (g ∘ f i)).
  
  Lemma final_uniformity_final : UniformlyContinuous g.
  Proof. pose proof _ : UniformSpace Z.
    pose (Ψ := pullback_uniformity g).
    assert (UniformSpace Y) as HΨ by now unfold Ψ.
    apply uniformly_continuous_alt. intros V.
    unshelve eexists; [ now exists Ψ |]; unfold subset_pt.
    split.
    + intros U. unfold_final_semiuniformity. rew <-all_adj; intros i.
      pose proof _ : UniformSpace (X i).
      change ((∐ W:Ξ, ⟨ g, g ⟩* W ⊆ U) ⊸ ⟨f i, f i⟩* U ∊ Φ i).
      rew <-aex_adj; intros W.
      rew (order_preserving ⟨f i, f i⟩* _ U).
      change (⟨ g ∘ f i, g ∘ f i⟩* W ⊆ ⟨f i, f i⟩* U ⊸ ⟨f i, f i⟩* U ∊ Φ i).
      rew (up_closed (Φ i) (⟨ g ∘ f i, g ∘ f i⟩* W) _).
      enough (⟨ g ∘ f i, g ∘ f i⟩* W ∊ Φ i) by now simplify.
      now apply uniformly_continuous_alt.
    + exists (⟨g,g⟩* V). split; [| easy ]. now exists V.
  Qed.
End final.

