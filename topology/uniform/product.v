Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology.
Require Import topology.uniform.base uniform.basis.
Require Import easy rewrite replc simplify tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope grp_scope.
Local Open Scope sg_op_scope.
Import projection_notation.
Import image_notation.
Import tensor_map_notation.

Local Abbreviation tsr_pres  := tensor_product_uniform_presentation.
Local Abbreviation cart_pres := cartesian_product_uniform_presentation.

Local Abbreviation id := (id_fun _).
Local Abbreviation π₁ := (prod_proj1 _ _).
Local Abbreviation π₂ := (prod_proj2 _ _).
Local Abbreviation m := (tensor_medial _ _ _ _).
Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Notation "f ♭" := ((func_op ⟨f,f⟩)⁎) (at level 1, left associativity, format "f ♭").

(** Canonical product uniformities *)

Section default_uniformity.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y}.

  Definition tensor_product_uniformity : Uniformity (X ⊗ Y) := presented_uniformity tsr_pres.
  Definition cartesian_product_uniformity : Uniformity (X × Y) := presented_uniformity cart_pres.

  Lemma tensor_product_uniformity_correct : TensorProductUniformity _ _ tensor_product_uniformity.
  Proof. now unfold TensorProductUniformity, tensor_product_uniformity. Qed.
  Lemma cartesian_product_uniformity_correct : CartesianProductUniformity _ _ cartesian_product_uniformity.
  Proof. now unfold CartesianProductUniformity, cartesian_product_uniformity. Qed.
End default_uniformity.

#[global] Hint Extern 20 (Uniformity (_ ⊗ _)) => notypeclasses refine tensor_product_uniformity : typeclass_instances.
#[global] Hint Extern 2 (TensorProductUniformity _ _ tensor_product_uniformity) => simple notypeclasses refine tensor_product_uniformity_correct : typeclass_instances.

#[global] Hint Extern 20 (Uniformity (_ × _)) => notypeclasses refine cartesian_product_uniformity : typeclass_instances.
#[global] Hint Extern 2 (CartesianProductUniformity _ _ cartesian_product_uniformity) => simple notypeclasses refine cartesian_product_uniformity_correct : typeclass_instances.

(** tsr_pres / cart_pres are monotone *)

Lemma tensor_product_uniform_presentation_monotone {X Y Φ Ψ} : OrderPreserving (@tsr_pres X Y Φ Ψ).
Proof. now change (OrderPreserving ((tensor_medial X Y X Y)* ∘ tensor_subset ∘ ⟨from_subset Φ, from_subset Ψ⟩)). Qed.
#[global] Hint Extern 2 (OrderPreserving tsr_pres ) => simple notypeclasses refine tensor_product_uniform_presentation_monotone    : typeclass_instances.

Lemma cartesian_product_uniform_presentation_monotone {X Y Φ Ψ} : OrderPreserving (@cart_pres X Y Φ Ψ).
Proof. now change (OrderPreserving ( (⊓) ∘ ⟨(prod_proj1 X Y)♯, (prod_proj2 X Y)♯⟩ ∘ ⟨from_subset Φ, from_subset Ψ⟩)). Qed.
#[global] Hint Extern 2 (OrderPreserving cart_pres) => simple notypeclasses refine cartesian_product_uniform_presentation_monotone : typeclass_instances.

(** Layered Bases *)

Section layered_bases.
  Universes u.
  Context {Λ₁:set@{u}} `{Φ:Uniformity@{u} X} (α:Λ₁ ⇾ Φ)
          {Λ₂:set@{u}} `{Ψ:Uniformity@{u} Y} (β:Λ₂ ⇾ Ψ).
  
  Definition tensor_product_uniform_basis `{H:@TensorProductUniformity X Y Φ Ψ Θ}
    := set:(λ '(i, j):(Λ₁ ⊗ Λ₂)%set, filter_presentation_basis Θ (@tsr_pres X Y Φ Ψ) (H:=H) (α i, β j)).

  Definition cartesian_product_uniform_basis `{H:@CartesianProductUniformity X Y Φ Ψ Θ}
    := set:(λ '(i, j):(Λ₁ ⊗ Λ₂)%set, filter_presentation_basis Θ (@cart_pres X Y Φ Ψ) (H:=H) (α i, β j)).
End layered_bases.

Local Abbreviation tsr_basis  := tensor_product_uniform_basis.
Local Abbreviation cart_basis := cartesian_product_uniform_basis.

Section layered_bases.
  Universes u.
  Context {Λ₁:set@{u}} `{Φ:Uniformity@{u} X} {α:Λ₁ ⇾ Φ}
          {Λ₂:set@{u}} `{Ψ:Uniformity@{u} Y} {β:Λ₂ ⇾ Ψ}.
  Context `{HX:@UniformityBasis@{u} X Φ Λ₁ α, HY:@UniformityBasis@{u} Y Ψ Λ₂ β}.
  
  Lemma tensor_product_uniform_basis_correct `{H:@TensorProductUniformity X Y Φ Ψ Θ}
    : UniformityBasis (tsr_basis α β).
  Proof. now change (FilterBasis ( filter_presentation_basis_fun Θ (@tsr_pres X Y Φ Ψ) (H:=H) ∘ ⟨α, β⟩ )). Qed.

  Lemma cartesian_product_uniform_basis_correct `{H:@CartesianProductUniformity X Y Φ Ψ Θ}
    : UniformityBasis (cart_basis α β).
  Proof. now change (FilterBasis ( filter_presentation_basis_fun Θ (@cart_pres X Y Φ Ψ) (H:=H) ∘ ⟨α, β⟩ )). Qed.
End layered_bases.
#[global] Hint Extern 0 (UniformityBasis (X:=?X × ?Y) (Φ:=?Θ) _) =>
  let H := constr:(_ : CartesianProductUniformity (X:=X) (Y:=Y) _ _ Θ) in
  notypeclasses refine (cartesian_product_uniform_basis_correct (H:=H)) : typeclass_instances.
#[global] Hint Extern 0 (UniformityBasis (X:=?X ⊗ ?Y) (Φ:=?Θ) _) =>
  let H := constr:(_ : TensorProductUniformity (X:=X) (Y:=Y) _ _ Θ) in
  notypeclasses refine (tensor_product_uniform_basis_correct (H:=H)) : typeclass_instances.

(** Cartesian Product *)
Section cartesian_product.
  Universes u.
  Context `{@UniformSpace@{u} X Φ} `{@UniformSpace@{u} Y Ψ}.
  Local Abbreviation β := (@cart_pres X Y Φ Ψ).

  Context `{@CartesianProductUniformity X Y Φ Ψ Θ}.

  Local Ltac unfold_β := change (β (?U, ?V)) with ( π₁♯ U ⊓ π₂♯ V ).

  Local Instance cartesian_product_uniform_space : UniformSpace (X × Y).
  Proof. apply presented_uniform_space.
  + intros [U V]. unfold_β.
    now rew [<-(uniform_refl_alt U : _ ⊆ subset_pt U)| <-(uniform_refl_alt V : _ ⊆ subset_pt V)].
  + intros [U V]. now exists (U⁻¹, V⁻¹).
  + intros [U₁ U₂].
    pose proof uniform_split_alt U₁ as [V₁ PV1].
    pose proof uniform_split_alt U₂ as [V₂ PV2].
    rew [<-PV1 | <-PV2].
    exists (V₁, V₂).
    unfold_β. rew (preserves_meet_lax2 (∙) _ _ _ _).
    now rew (preimage_compose_rel_lax_alt _ _ _).
  Qed.

  Lemma prod_proj1_ufm_cont : UniformlyContinuous (prod_proj1 X Y).
  Proof. apply uniformly_continuous_alt.
    intros U. rew (filter_presentation Θ _ _).
    exists (U, ⊤). unfold_β. exact (meet_lb_l _ _).
  Qed.

  Lemma prod_proj2_ufm_cont : UniformlyContinuous (prod_proj2 X Y).
  Proof. apply uniformly_continuous_alt.
    intros U. rew (filter_presentation Θ _ _).
    exists (⊤, U). unfold_β. exact (meet_lb_r _ _).
  Qed.
  
  Lemma cartesian_product_uniformity_initial `{@UniformSpace@{u} Z Ξ} (f:Z ⇾ X × Y) :
    UniformlyContinuous (π₁ ∘ f)
  → UniformlyContinuous (π₂ ∘ f)
  → UniformlyContinuous f.
  Proof. set (f₁ := π₁ ∘ f). set (f₂ := π₂ ∘ f).
    rew (uniformly_continuous_alt _).
    intros Hf1 Hf2. intros W.
    pose proof uniformity_basis W as [[U V] HW].
    apply (up_closed Ξ ( (π₁ ∘ f)♯ U ⊓ (π₂ ∘ f)♯ V )).
    + change (f♯ (π₁♯ U) ⊓ f♯ (π₂♯ V) ⊆ f♯ W).
      now rew <-(preserves_meet f♯ _ _), <-(order_preserving f♯ _ _).
    + apply sub_meet_closed. split; [ exact (Hf1 U) | exact (Hf2 V) ].
  Qed.

  (** The induced topology of a cartesian product uniformity satisfies the
      cartesian-product UP at the topological level. *)
  Lemma cartesian_product_uniformity_topology
    : CartesianProductTopology (NX:=@UniformNeighborhood X Φ) (NY:=@UniformNeighborhood Y Ψ) (@UniformNeighborhood (X × Y) Θ).
  Proof. split.
  + exact prod_proj1_ufm_cont.
  + exact prod_proj2_ufm_cont.
  + intros Z NZ HZ f. set (f₁ := prod_proj1 _ _ ∘ f). set (f₂ := prod_proj2 _ _ ∘ f). intros Hf1 Hf2.
    pose proof _ : UniformSpace (X × Y). split; try exact _.
    intros z N. change ((∐ U:Θ, ∏ p, near U (f z) p ⊸ p ∊ N) ⊸ z ⪽ f* N).
    rew <-aex_adj. intros W.
    pose proof uniformity_basis W as [[U V] PW].
    change ((∏ p : (X × Y)%set, (f z, p) ∊ W ⊸ p ∊ N) ⊸ z ⪽ f* N). 
    rew <-(PW : powerset_pt _ ⊆ powerset_pt W); clear W PW.
    change ((∏ p : (X × Y)%set, near U (f₁ z) (π₁ p) ∧ near V (f₂ z) (π₂ p) ⊸ p ∊ N) ⊸ z ⪽ f* N).
    enough (z ⪽ f₁* (near U (f₁ z)) ⊓ f₂* (near V (f₂ z))) as P.
    * rew <-(top_isotony z (f₁* (near U (f₁ z)) ⊓ f₂* (near V (f₂ z))) (f* N)), (aprod_true_l P).
      change (?A ≤ ?B) with (∏ q, q ∊ A ⊸ q ∊ B); rew <-all_adj; intros q. exact (all_lb _ (f q)).
    * rew <-(top_binary_additivity _ _ _), <-(continuity _ _ _). now split.
  Qed.
End cartesian_product.
#[global] Hint Extern 2 (UniformSpace (_ × _)) => simple notypeclasses refine cartesian_product_uniform_space : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (CartesianProductTopology UniformNeighborhood) => simple notypeclasses refine cartesian_product_uniformity_topology : typeclass_instances.

Lemma cartesian_product_separated@{u}
  `{@SeparatedUniformSpace@{u} X Φ, @SeparatedUniformSpace@{u} Y Ψ}
  `{@CartesianProductUniformity X Y Φ Ψ Θ}
  : SeparatedUniformSpace@{u} (X × Y).
Proof. pose proof _ : UniformSpace (X × Y).
  apply uniform_T₀_separated, Hausdorff_T₀. exact (cartesian_product_hausdorff (HP:=cartesian_product_uniformity_topology)).
Qed.

#[global] Hint Extern 2 (SeparatedUniformSpace (_ × _)) => simple notypeclasses refine cartesian_product_separated : typeclass_instances.

Lemma to_prod_ufm_cont@{u} `{Hf:@UniformlyContinuous@{u} X Y₁ Φ Ψ₁ f, Hg:@UniformlyContinuous@{u} X Y₂ Φ Ψ₂ g}
  `{@CartesianProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyContinuous (to_prod (f, g)).
Proof. apply cartesian_product_uniformity_initial; [ exact Hf | exact Hg ]. Qed.
#[global] Hint Extern 2 (UniformlyContinuous (func_op to_prod (_, _))) => simple notypeclasses refine to_prod_ufm_cont : typeclass_instances.

Lemma prod_map_ufm_cont@{u} `{@UniformlyContinuous@{u} X₁ Y₁ Φ₁ Ψ₁ f} `{@UniformlyContinuous@{u} X₂ Y₂ Φ₂ Ψ₂ g}
  `{@CartesianProductUniformity X₁ X₂ Φ₁ Φ₂ Φ} `{@CartesianProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyContinuous (prod_map (f, g)).
Proof. now change (prod_map (f, g)) with (to_prod (f ∘ prod_proj1 X₁ X₂, g ∘ prod_proj2 X₁ X₂)). Qed.
#[global] Hint Extern 2 (UniformlyContinuous (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_ufm_cont : typeclass_instances.

Lemma prod_map_ufm_refl@{u} `{@UniformlyReflecting@{u} X₁ Y₁ Φ₁ Ψ₁ f} `{@UniformlyReflecting@{u} X₂ Y₂ Φ₂ Ψ₂ g}
  `{@CartesianProductUniformity X₁ X₂ Φ₁ Φ₂ Φ} `{@CartesianProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyReflecting (prod_map (f, g)).
Proof. apply ufm_refl_by_basis. intros [U₁ U₂].
  pose proof ufm_reflection f U₁ as [V₁ PV₁].
  pose proof ufm_reflection g U₂ as [V₂ PV₂].
  exists (V₁, V₂). intros [x₁ x₂][y₁ y₂].
  change ( near V₁ (f x₁) (f y₁) ∧ near V₂ (g x₂) (g y₂) ⊸ near U₁ x₁ y₁ ∧ near U₂ x₂ y₂ ).
  now rew [(PV₁ _ _)|(PV₂ _ _)].
Qed.
#[global] Hint Extern 2 (UniformlyReflecting (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_ufm_refl : typeclass_instances.

Lemma prod_map_ufm_initial@{u} `{@UniformlyInitial@{u} X₁ Y₁ Φ₁ Ψ₁ f} `{@UniformlyInitial@{u} X₂ Y₂ Φ₂ Ψ₂ g}
  `{@CartesianProductUniformity X₁ X₂ Φ₁ Φ₂ Φ} `{@CartesianProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyInitial (prod_map (f, g)).
Proof. now split. Qed.
#[global] Hint Extern 2 (UniformlyInitial (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_ufm_initial : typeclass_instances.

Lemma prod_map_ufm_emb@{u} `{@UniformlyEmbedding@{u} X₁ Y₁ Φ₁ Ψ₁ f} `{@UniformlyEmbedding@{u} X₂ Y₂ Φ₂ Ψ₂ g}
  `{@CartesianProductUniformity X₁ X₂ Φ₁ Φ₂ Φ} `{@CartesianProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyEmbedding (prod_map (f, g)).
Proof. now split. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_ufm_emb : typeclass_instances.


(** Tensor Product *)
Section tensor_product.
  Universes u.
  Context `{@UniformSpace@{u} X Φ} `{@UniformSpace@{u} Y Ψ}.
  Local Abbreviation β := (@tsr_pres X Y Φ Ψ).
  (*Local Abbreviation m := (@tensor_medial X Y X Y).*)

  Context `{@TensorProductUniformity X Y Φ Ψ Θ}.

  Local Instance tensor_product_uniform_space : UniformSpace (X ⊗ Y).
  Proof. apply presented_uniform_space.
  + intros [U V]. change (id_rel (X ⊗ Y) ⊆ m* (powerset_pt U ⊗ powerset_pt V)).
    now rew [<-(uniform_refl_alt U)|<-(uniform_refl_alt V)].
  + intros [U V]. now exists (U⁻¹, V⁻¹).
  + intros [U₁ U₂].
    pose proof uniform_split_alt U₁ as [V₁ PV1].
    pose proof uniform_split_alt U₂ as [V₂ PV2].
    rew [<-PV1 | <-PV2].
    exists (V₁, V₂). change (β (?a, ?b)) with (m* (powerset_pt a ⊗ powerset_pt b)).
    change (powerset_pt (?a ∙ ?b)) with (powerset_pt a ∙ powerset_pt b).
    now rew (medial_preimage_compose_alt _ _ _ _).
  Qed.

  (** The induced topology of a tensor product uniformity is the tensor
      product topology. *)
  Local Abbreviation α := (tensor_product_neighborhood_basis (@UniformNeighborhood X Φ) (@UniformNeighborhood Y Ψ)).
  Lemma tensor_product_uniformity_neighborhood : TensorProductNeighborhood Φ Ψ Θ.
  Proof. intros [x y] N. split.
  + change ((∐ W:Θ, ∏ p, ((x, y), p) ∊ W ⊸ p ∊ N) ⊸ ∐ i, (x, y) ∊ α i ⊠ α i ⊆ N).
    rew <-aex_adj; intros W.
    pose proof uniformity_basis W as [[U V] PW].
    rew <-(PW : powerset_pt _ ⊆ powerset_pt _); clear W PW.
    rew <-(aex_ub _ (near U x, near V y)).
    rew (aprod_true_l ( _ : x ⪽ near U x ⊠ y ⪽ near V y) ).
    change (?A ⊆ ?B) with (∏ q, q ∊ A ⊸ q ∊ B).
    rew <-all_adj; intros [x' y']. rew (all_lb _ (x', y')).
    change ((near U x x' ⊠ near V y y' ⊸ (x', y') ∊ N)
      ⊸ (x' ⪽ near U x ⊠ y' ⪽ near V y) ⊸ (x', y') ∊ N).
    now rew [(top_refl x' (near U x)) | (top_refl y' (near V y))].
  + rew <-aex_adj; intros [M₁ M₂].
    change ( (x, y) ∊ α (M₁, M₂) ) with ( x ⪽ M₁ ⊠ y ⪽ M₂ ).
    rew [(top_trans x M₁) | (top_trans y M₂)].
    change (((∐ U:Φ, ∏ x', near U x x' ⊸ x' ⪽ M₁) ⊠ (∐ V:Ψ, ∏ y', near V y y' ⊸ y' ⪽ M₂))
      ⊠ α (M₁, M₂) ⊆ N ⊸ ∐ W:Θ, ∏ p, near W (x, y) p ⊸ p ∊ N).
    rew (aprod_adj _ _ _), <-aex_adj2; intros U V.
    rew <-(aex_ub _ (tsr_basis (id_fun _) (id_fun _) (U, V))).
    rew <-(aprod_adj _ _ _), <-all_adj; intros [x' y'].
    rew [(all_lb _ x') | (all_lb _ y')].
    change (?A ⊆ ?B) with (∏ q, q ∊ A ⊸ q ∊ B); rew (all_lb _ (x', y')).
    change (((near U x x' ⊸ x' ⪽ M₁) ⊠ (near V y y' ⊸ y' ⪽ M₂))
      ⊠ (x' ⪽ M₁ ⊠ y' ⪽ M₂ ⊸ (x', y') ∊ N)
      ⊸ near U x x' ⊠ near V y y' ⊸ (x', y') ∊ N).
    tautological.
  Qed.
End tensor_product.
#[global] Hint Extern 2 (UniformSpace (_ ⊗ _)) => simple notypeclasses refine tensor_product_uniform_space : typeclass_instances.
#[global] Hint Extern 2 (TensorProductNeighborhood UniformNeighborhood UniformNeighborhood UniformNeighborhood) => simple notypeclasses refine tensor_product_uniformity_neighborhood : typeclass_instances.

Lemma tensor_map_ufm_cont@{u} `{@UniformlyContinuous@{u} X₁ Y₁ Φ₁ Ψ₁ f} `{@UniformlyContinuous@{u} X₂ Y₂ Φ₂ Ψ₂ g}
  `{@TensorProductUniformity X₁ X₂ Φ₁ Φ₂ Φ} `{@TensorProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyContinuous ⟨f, g⟩.
Proof. apply ufm_cont_by_basis. intros [V₁ V₂].
  pose proof ufm_continuity f V₁ as [U₁ HU1].
  pose proof ufm_continuity g V₂ as [U₂ HU2].
  exists (U₁, U₂). intros [x₁ x₂][y₁ y₂].
  change (near U₁ x₁ y₁ ⊠ near U₂ x₂ y₂ ⊸ near V₁ (f x₁) (f y₁) ⊠ near V₂ (g x₂) (g y₂)).
  now rew [ <-(HU1 _ _) | <-(HU2 _ _) ].
Qed.
#[global] Hint Extern 2 (UniformlyContinuous ⟨_, _⟩) => simple notypeclasses refine tensor_map_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_ufm_cont : typeclass_instances.

Lemma tensor_map_ufm_refl@{u} `{@UniformlyReflecting@{u} X₁ Y₁ Φ₁ Ψ₁ f} `{@UniformlyReflecting@{u} X₂ Y₂ Φ₂ Ψ₂ g}
  `{@TensorProductUniformity X₁ X₂ Φ₁ Φ₂ Φ} `{@TensorProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyReflecting ⟨f, g⟩.
Proof. apply ufm_refl_by_basis. intros [U₁ U₂].
  pose proof ufm_reflection f U₁ as [V₁ HV1].
  pose proof ufm_reflection g U₂ as [V₂ HV2].
  exists (V₁, V₂). intros [x₁ x₂][y₁ y₂].
  change (near V₁ (f x₁) (f y₁) ⊠ near V₂ (g x₂) (g y₂) ⊸ near U₁ x₁ y₁ ⊠ near U₂ x₂ y₂).
  now rew [ <-(HV1 _ _) | <-(HV2 _ _) ].
Qed.
#[global] Hint Extern 2 (UniformlyReflecting ⟨_, _⟩) => simple notypeclasses refine tensor_map_ufm_refl : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_ufm_refl : typeclass_instances.

Lemma tensor_map_ufm_initial@{u} `{@UniformlyInitial@{u} X₁ Y₁ Φ₁ Ψ₁ f} `{@UniformlyInitial@{u} X₂ Y₂ Φ₂ Ψ₂ g}
  `{@TensorProductUniformity X₁ X₂ Φ₁ Φ₂ Φ} `{@TensorProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyInitial ⟨f, g⟩.
Proof. now split. Qed.
#[global] Hint Extern 2 (UniformlyInitial ⟨_, _⟩) => simple notypeclasses refine tensor_map_ufm_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_ufm_initial : typeclass_instances.

Lemma tensor_map_ufm_emb@{u} `{@UniformlyEmbedding@{u} X₁ Y₁ Φ₁ Ψ₁ f} `{@UniformlyEmbedding@{u} X₂ Y₂ Φ₂ Ψ₂ g}
  `{@TensorProductUniformity X₁ X₂ Φ₁ Φ₂ Φ} `{@TensorProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : UniformlyEmbedding ⟨f, g⟩.
Proof. now split. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding ⟨_, _⟩) => simple notypeclasses refine tensor_map_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_ufm_emb : typeclass_instances.


(** Unitors *)
Section unitors.
  Universes u.
  Context `{@UniformSpace@{u} X Φ} `{@UniformSpace@{u} 𝟏 Ψ}.
  Local Abbreviation uₗ := (tensor_unit_l X).
  Local Abbreviation uᵣ := (tensor_unit_r X).
  
  Lemma tensor_unit_l_emb `{@TensorProductUniformity@{u} 𝟏 X Ψ Φ Θ}
    : UniformlyEmbedding uₗ.
  Proof. do 2 (split; try exact _).
  + apply ufm_cont_by_basis. intros U. exists (tt, U). intros [[] x][[] y].
    change (𝐓 ⊠ near U x y ⊸ near U x y). now simplify.
  + apply ufm_refl_by_basis. intros [[] U]. exists U. intros [[] x][[] y].
    change (near U x y ⊸ 𝐓 ⊠ near U x y). now simplify.
  Qed. 

  Lemma tensor_unit_r_emb `{@TensorProductUniformity@{u} X 𝟏 Φ Ψ Θ}
    : UniformlyEmbedding uᵣ.
  Proof. do 2 (split; try exact _).
  + apply ufm_cont_by_basis. intros U. exists (U, tt). intros [x []][y []].
    change (near U x y ⊠ 𝐓 ⊸ near U x y). now simplify.
  + apply ufm_refl_by_basis. intros [U []]. exists U. intros [x []][y []].
    change (near U x y ⊸ near U x y ⊠ 𝐓). now simplify.
  Qed.
End unitors.
#[global] Hint Extern 2 (UniformlyEmbedding  (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_emb : typeclass_instances.  
#[global] Hint Extern 2 (UniformlyContinuous (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_emb : typeclass_instances.  
#[global] Hint Extern 2 (UniformlyReflecting (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_emb : typeclass_instances.  
#[global] Hint Extern 2 (UniformlyInitial    (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_emb : typeclass_instances.  

#[global] Hint Extern 2 (UniformlyEmbedding  (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_emb : typeclass_instances.  
#[global] Hint Extern 2 (UniformlyContinuous (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_emb : typeclass_instances.  
#[global] Hint Extern 2 (UniformlyReflecting (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_emb : typeclass_instances.  
#[global] Hint Extern 2 (UniformlyInitial    (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_emb : typeclass_instances.  

(** Braid *)
Lemma tensor_swap_ufm_cont@{u} `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ}
  `{@TensorProductUniformity X Y Φ Ψ Θ_XY}
  `{@TensorProductUniformity Y X Ψ Φ Θ_YX}
  : UniformlyContinuous (tensor_swap X Y).
Proof. apply ufm_cont_by_basis. intros [U V]. exists (V, U). intros [a b][c d].
  change (near V a c ⊠ near U b d ⊸ near U b d ⊠ near V a c).
  now rew (aprod_com _ _).
Qed.
#[global] Hint Extern 2 (UniformlyContinuous (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_ufm_cont : typeclass_instances.

Lemma tensor_swap_ufm_emb@{u} `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ}
  `{@TensorProductUniformity X Y Φ Ψ Θ_XY}
  `{@TensorProductUniformity Y X Ψ Φ Θ_YX}
  : UniformlyEmbedding (tensor_swap X Y).
Proof. do 2 (split; try exact _). now change (UniformlyReflecting (inverse (tensor_swap Y X))). Qed.
#[global] Hint Extern 2 (UniformlyEmbedding  (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_ufm_emb : typeclass_instances.

(** Associators *)
Section associators.
  Universes u.
  Context `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ, @UniformSpace@{u} Z Ξ}.
  Context `{@TensorProductUniformity@{u} X Y Φ Ψ Θ_XY}.
  Context `{@TensorProductUniformity@{u} Y Z Ψ Ξ Θ_YZ}.
  Context `{@TensorProductUniformity@{u} X (Y ⊗ Z) Φ Θ_YZ Θ_X_YZ}.
  Context `{@TensorProductUniformity@{u} (X ⊗ Y) Z Θ_XY Ξ Θ_XY_Z}.
  Local Abbreviation αₗ := (tensor_assoc_l X Y Z).
  Local Abbreviation αᵣ := (tensor_assoc_r X Y Z).
  
  Local Instance tensor_assoc_l_ufm_cont : UniformlyContinuous αₗ.
  Proof. apply ufm_cont_by_basis. intros [U[V W]]. exists (U,V,W).
    intros [[a b] c][[d e] f].
    change ((near U a d ⊠ near V b e) ⊠ near W c f ⊸ near U a d ⊠ (near V b e ⊠ near W c f)).
    tautological.
  Qed.

  Local Instance tensor_assoc_r_ufm_cont : UniformlyContinuous αᵣ.
  Proof. apply ufm_cont_by_basis. intros [[U V] W]. exists (U,(V,W)).
    intros [a [b c]][d [e f]].
    change (near U a d ⊠ (near V b e ⊠ near W c f) ⊸ (near U a d ⊠ near V b e) ⊠ near W c f).
    tautological.
  Qed.
  
  Lemma tensor_assoc_l_ufm_emb : UniformlyEmbedding αₗ.
  Proof. do 2 (split; try exact _). now change (UniformlyReflecting (inverse αᵣ)). Qed.

  Lemma tensor_assoc_r_ufm_emb : UniformlyEmbedding αᵣ.
  Proof. do 2 (split; try exact _). now change (UniformlyReflecting (inverse αₗ)). Qed.
End associators.
#[global] Hint Extern 2 (UniformlyContinuous (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_ufm_cont : typeclass_instances.

#[global] Hint Extern 2 (UniformlyEmbedding  (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_ufm_emb : typeclass_instances.

#[global] Hint Extern 2 (UniformlyEmbedding  (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_ufm_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_ufm_emb : typeclass_instances.

(** Derived structure maps *)

Lemma tensor_proj1_ufm_cont@{u} `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ}
  `{@TensorProductUniformity X Y Φ Ψ Θ}
  : UniformlyContinuous (tensor_proj1 X Y).
Proof. now change (tensor_proj1 X Y) with (tensor_unit_r X ∘ ⟨id, to_Unit Y⟩). Qed.
#[global] Hint Extern 2 (UniformlyContinuous (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_ufm_cont : typeclass_instances.

Lemma tensor_proj2_ufm_cont@{u} `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ}
  `{@TensorProductUniformity X Y Φ Ψ Θ}
  : UniformlyContinuous (tensor_proj2 X Y).
Proof. now change (tensor_proj2 X Y) with (tensor_unit_l Y ∘ ⟨to_Unit X, id⟩). Qed.
#[global] Hint Extern 2 (UniformlyContinuous (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_ufm_cont : typeclass_instances.

Lemma tensor_to_prod_ufm_cont@{u} `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ}
  `{@TensorProductUniformity X Y Φ Ψ Θ}
  `{@CartesianProductUniformity X Y Φ Ψ Ξ}
  : UniformlyContinuous (tensor_to_prod X Y).
Proof. now change (tensor_to_prod X Y) with (to_prod (tensor_proj1 X Y, tensor_proj2 X Y)). Qed.
#[global] Hint Extern 2 (UniformlyContinuous (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_ufm_cont : typeclass_instances.

Local Abbreviation int := interior.
Local Abbreviation cl := closure.

Section interior_entourage.
  #[local] Hint Extern 0 (Neighborhood _) => exact UniformNeighborhood : typeclass_instances.

  Lemma interior_entourage `{@UniformSpace X Φ} `{!TensorProductUniformity Φ Φ Φ₂} (U:Φ) : interior U ∊ Φ.
  Proof.
    pose proof uniform_split_sym3 U as [V[EV PV]]. apply (up_closed Φ V); [| exact _ ].
    intros [x y]. rew uniform_basis_interior_applied2. rew <-(aex_ub _ (V, V)).
    change (?a ⊆ ?b) with (∏ p, p ∊ a ⊸ p ∊ b). rew <-all_adj; intros [a b].
    change ( near V x y ⊸ near V x a ⊠ near V y b ⊸ (a, b) ∊ U).
    rew <-EV at 2. change ( near V⁻¹ x a ) with (near V a x).
    enough ( near V a x ⊠ near V x y ⊠ near V y b ⊸ (a, b) ∊ U ) as G by (revert G; tautological).
    now rew [(near_compose3 _ _ _ _ _ _ _)|<-(PV : _ ⊆ powerset_pt U)].
  Qed.

  Lemma ufm_split_interior `{@UniformSpace X Φ} `{!TensorProductUniformity Φ Φ Φ₂} (U:Φ)
     : ∐ (V:Φ), V⁻¹ = V ⊠ V ⊆ interior U.
  Proof. exact ( uniform_sym_alt (@to_subset _ _ _ (interior_entourage U)) ). Qed.

  Import projection_notation.
  Lemma closure_intersect_thicken `{@UniformSpace X Φ, @UniformSpace Y Ψ}
    `{!TensorProductUniformity Φ Ψ Ξ} (A : 𝒫 (X ⊗ Y))
    : closure A = { '(x,y) : (X ⊗ Y)%set | ∏ (U:Φ) (V:Ψ), (x,y) ∊  powerset_pt U ⋄ A ⋄ powerset_pt V }.
  Proof. rew uniform_basis_closure_applied.
    intros [x y].
    change ( (∏ i : (Φ ⊗ Ψ)%set, ∐ p : (X ⊗ Y)%set, ((x, π₁ p) ∊ (π₁ i) ⊠ (y, π₂ p) ∊ π₂ i) ⊠ p ∊ A)
            ⧟ ∏ (U:Φ) (V:Ψ), (x, y) ∊ powerset_pt U ⋄ A ⋄ powerset_pt V ); split.
  + rew <-all_adj; intros U; rew <-all_adj; intros V.
    rew (all_lb _ (U, V⁻¹)). rew <-aex_adj; intros [a b].
    change ( ( (x, a) ∊ U ⊠ (b, y) ∊ V) ⊠ (a, b) ∊ A ⊸ (x, y) ∊ powerset_pt U ⋄ A ⋄ powerset_pt V ).
    rew <-( rel_compose3 _ _ _ x a b y).
    tautological.
  + rew <-all_adj; intros [U V]. rew (all_lb _ U), (all_lb _ V⁻¹).
    change (_ ⊸ ?Q) with ( (∐ b, (∐ a, (x, a) ∊ U ⊠ (a, b) ∊ A)  ⊠ (y, b) ∊ V) ⊸ Q ).
    rew <-aex_adj; intros b. rew aex_frob_r, <-aex_adj; intros a.
    rew <-(aex_ub _ (a, b)); unfold proj1, proj2. tautological.
  Qed.

  Lemma closure_subset_thicken `{@UniformSpace X Φ} `{!TensorProductUniformity Φ Φ Φ₂} (A:𝒫 (X ⊗ X)) (V:Φ)
     : closure A ⊆ powerset_pt V ∙ A ∙ powerset_pt V⁻¹.
  Proof. rew (closure_intersect_thicken _). intros [x y].
    change ( ( ∏ U W : Φ, (x, y) ∊ powerset_pt U ⋄ A ⋄ powerset_pt W ) ⊸ (x, y) ∊ powerset_pt V ⋄ A ⋄ powerset_pt V⁻¹ ).
    rew (all_lb _ V). exact (all_lb _ V⁻¹).
  Qed.

  Lemma ufm_split_closure `{@UniformSpace X Φ} `{!TensorProductUniformity Φ Φ Φ₂} (U:Φ)
     : ∐ (V:Φ), V⁻¹ = V ⊠ closure V ⊆ U.
  Proof. pose proof uniform_split_sym3 U as [V[EV HV]].
    exists V; split; trivial. now rew (closure_subset_thicken V V), EV.
  Qed.

  Lemma sub_closure_thicken `{@UniformSpace X Φ} `{!TensorProductUniformity Φ Φ Φ₂} (S A : 𝒫 (X ⊗ X))
    : (∀ V:Φ, S ⊆ powerset_pt V ∙ A ∙ powerset_pt V⁻¹) → S ⊆ closure A.
  Proof. intros P. rew (closure_intersect_thicken A).
    intros [x y]. change ((x, y) ∊ S ⊸ ∏ U V : Φ, (x, y) ∊ U ⋄ A ⋄ V).
    rew <-all_adj; intros U. rew <-all_adj; intros V.
    enough (S ⊆ powerset_pt U ∙ A ∙ powerset_pt V) as E by now rew E.
    rew (P (U ⊓ V⁻¹)). rew (meet_lb_l U V⁻¹) at 1. now rew (meet_lb_r U V⁻¹).
  Qed.

  Lemma sub_interior_thicken `{@UniformSpace X Φ} `{!TensorProductUniformity Φ Φ Φ₂}
    (S A : 𝒫 (X ⊗ X)) (U V:Φ)
    : powerset_pt U ∙ S ∙ powerset_pt V ⊆ A ⊸ S ⊆ int A.
  Proof. change (?a ≤ ?b) with (∏ p, p ∊ a ⊸ p ∊ b).
    rew <-all_adj; intros [x y]. rew <-(aprod_adj _ _ _).
    rew uniform_basis_interior_applied2. rew <-(aex_ub _ (U⁻¹, V)).
    change (?a ≤ ?b) with (∏ p, p ∊ a ⊸ p ∊ b).
    rew <-all_adj. intros [a b]. rew (all_lb _ (a, b)).
    change ( ((a, b) ∊ powerset_pt U ∙ S ∙ powerset_pt V ⊸ (a, b) ∊ A) ⊠ (x, y) ∊ S ⊸ (a, x) ∊ U ⊠ (y, b) ∊ V ⊸ (a, b) ∊ A ).
    rew <-(rel_compose3 U S V a x y b).
    tautological.
  Qed.

  Lemma ufm_dense_image_pair_closure_test@{u} {X₁ Y₁ X₂ Y₂:set@{u}} `{@UniformSpace Y₁ Ψ₁, @UniformSpace Y₂ Ψ₂}
    `{!TensorProductUniformity Ψ₁ Ψ₂ Ψ}
    (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂) `{!Dense f₁, !Dense f₂}
    (V₁:Ψ₁) (V₂:Ψ₂) (P:Ω) (S:𝒫 (X₁ ⊗ X₂)) (y₁:Y₁) (y₂:Y₂)
    : (∀ x₁ x₂, near V₁ y₁ (f₁ x₁) → near V₂ y₂ (f₂ x₂) → (P ⊸ (x₁, x₂) ∊ S)) → (P ⊸ (y₁, y₂) ∊ closure (⟨f₁,f₂⟩⁎ S)) .
  Proof. intros Hy.
    pose (V := tensor_product_uniform_basis (id_fun Ψ₁) (id_fun Ψ₂) (V₁, V₂)).
    apply (ufm_dense_image_closure_test ⟨f₁,f₂⟩ V P S (y₁, y₂)).
    intros [x₁ x₂]. change (near V₁ y₁ (f₁ x₁) ⊠ near V₂ y₂ (f₂ x₂) → P ⊸ (x₁, x₂) ∊ S).
    intros [??]. now apply Hy.
  Qed.

  Local Instance ufm_dense_reflecting@{u} {X Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
    `{@UniformlyContinuous X Y Φ Ψ f, !Dense f, @UniformSpace Z Ξ, !Continuous g}
    `{!UniformlyReflecting (g ∘ f)}
    : UniformlyReflecting g.
  Proof. split; try exact _.
    rew (uniform_reflection_alt _). intros U.
    pose proof uniform_split_sym3 U as [V [EV PV]].
    pose proof ufm_reflection_alt (g ∘ f) (ufm_preimage f V) as [W PW];
      change (apos (f♯ (g♯ W) ⊆ f♯ V)) in PW.
    pose proof ufm_split_interior W as [W'[_ PW']]; exists W'; rew PW'; clear W' PW'.
    rew (continuous_preimage_interior ⟨g,g⟩ _).
    rew (dense_interior_closure_unit ⟨f,f⟩ _).
    rew PW.
    rew (image_preimage_counit _ _).
    now rew (closure_subset_thicken V V), EV.
  Qed.

  Lemma ufm_dense_initial@{u} {X Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
    `{@UniformlyContinuous X Y Φ Ψ f, !Dense f}
    `{@UniformlyContinuous Y Z Ψ Ξ g}
    `{!UniformlyReflecting (g ∘ f)}
    : UniformlyInitial g.
  Proof. now split. Qed.

  Lemma ufm_dense_continuous@{u} {X Y Z:set@{u}} (f:X ⇾ Y) (g:Y ⇾ Z)
    `{@UniformlyReflecting X Y Φ Ψ f, !Dense f, @UniformSpace Z Ξ, !Continuous g}
    `{!UniformlyContinuous (g ∘ f)}
    : UniformlyContinuous g.
  Proof. apply (uniformly_continuous_alt _). intros W.
    pose proof uniform_split_sym3 W as [W₁ [EW PW]].
    pose proof ufm_reflection_alt f (ufm_preimage (g ∘ f) W₁) as [V PV];
      change (apos (f♯ V ⊆ f♯ (g♯ W₁))) in PV.
    pose proof ufm_split_interior V as [V'[_ PV']].
    pose proof _ : UniformSpace Y.
    enough (V' ⊆ g♯ W) as E by now rew <-E.
    rew PV', (dense_interior_closure_unit ⟨f,f⟩ _), PV.
    rew (image_preimage_counit _ _).
    rew (continuous_closure_unit ⟨g,g⟩ _).
    rew (image_preimage_counit _ _).
    now rew (closure_subset_thicken W₁ W₁), EW, <-PW.
  Qed.
End interior_entourage.

