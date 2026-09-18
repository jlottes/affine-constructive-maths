Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.srelations logic.aprop relations.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology.
Require Import theory.set orders.orders orders.maps orders.subset.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices.
Require Import topology.base topology.interior topology.maps topology.basis.
Require Import easy rewrite simplify.

Local Open Scope topology_scope.
Local Open Scope fun_inv_scope.
Import image_notation.

Local Abbreviation tsr_basis  := tensor_product_neighborhood_basis.

(** Canonical product neighborhoods *)

Section default_neighborhood.
  Universes u.
  Context {X Y:set@{u}} {NX:Neighborhood@{u} X} {NY:Neighborhood@{u} Y}.

  Definition tensor_product_neighborhood    : Neighborhood@{u} (X ⊗ Y) := basis_neighborhood (tsr_basis _ _).

  Lemma tensor_product_neighborhood_correct    : TensorProductNeighborhood _ _ tensor_product_neighborhood.
  Proof. now unfold TensorProductNeighborhood, tensor_product_neighborhood. Qed.
End default_neighborhood.

#[global] Hint Extern 20 (Neighborhood (_ ⊗ _)) => notypeclasses refine tensor_product_neighborhood : typeclass_instances.
#[global] Hint Extern 2 (TensorProductNeighborhood _ _ tensor_product_neighborhood) => simple notypeclasses refine tensor_product_neighborhood_correct : typeclass_instances.
#[global] Hint Extern 2 (NeighborhoodBasis (XN:=tensor_product_neighborhood) _) => simple notypeclasses refine tensor_product_neighborhood_correct : typeclass_instances.



(** Tensor product topology *)

Section tensor_product.
  Universes u.
  Context `{@Topology@{u} X NX, @Topology@{u} Y NY}.
  Local Abbreviation β := (tsr_basis NX NY).

  Local Instance tensor_product_basis_order_preserving : OrderPreserving β.
  Proof. apply alt_Build_OrderPreserving. intros [N₁ M₁] [N₂ M₂].
    change (N₁ ⊆ N₂ ⊠ M₁ ⊆ M₂ ⊸ ∏ p, p ∊  β (N₁, M₁) ⊸ p ∊ β (N₂, M₂)).
    rew <-all_adj; intros [x y].
    change (N₁ ⊆ N₂ ⊠ M₁ ⊆ M₂ ⊸ x ⪽ N₁ ⊠ y ⪽ M₁ ⊸ x ⪽ N₂ ⊠ y ⪽ M₂).
    rew [<-(top_isotony x N₁ N₂)|<-(top_isotony y M₁ M₂)]; tautological.
  Qed.
  
  Context {NXY:Neighborhood@{u} (X ⊗ Y)}.
  Context {TPN:TensorProductNeighborhood@{u} NX NY NXY}.
 
  Local Open Scope subset_scope.

  Lemma tensor_product_topology : Topology@{u} (X ⊗ Y).
  Proof. apply topology_by_basis.
    + (* basis_inhabited *)
      intros [x y]. rew <-(aex_ub _ (⌈X⌉, ⌈Y⌉)).
      split; apply top_nullary_additivity.
    + (* basis_meet *)
      intros [x y] [N₁ M₁] [N₂ M₂].
      rew <-(aex_ub _ (N₁ ⊓ N₂, M₁ ⊓ M₂)).
      rew (aprod_true_r (preserves_meet_lax2 β _ _ _ _)).
      change ((x ⪽ N₁ ⊠ y ⪽ M₁) ⊠ (x ⪽ N₂ ⊠ y ⪽ M₂) ⊸
              (x ⪽ N₁ ⊓ N₂ ⊠ y ⪽ M₁ ⊓ M₂)).
      rew <-(top_binary_additivity _ _ _); tautological.
  Qed.
End tensor_product.
#[global] Hint Extern 2 (OrderPreserving (tsr_basis _ _)) => simple notypeclasses refine tensor_product_basis_order_preserving : typeclass_instances.
#[global] Hint Extern 2 (Topology (_ ⊗ _)) => simple notypeclasses refine tensor_product_topology : typeclass_instances.


Section layered_basis.
  Universes u.
  Context `{NBX:@NeighborhoodBasis@{u} X NX Λ₁ α, NBY:@NeighborhoodBasis@{u} Y NY Λ₂ β}.

  Definition tensor_product_neighborhood_basis_alt := λ '(i, j):Λ₁ ∗ Λ₂, (α i ⊗ β j)%subset.
  Local Abbreviation γ := tensor_product_neighborhood_basis_alt.
  
  Local Abbreviation τ := (tsr_basis NX NY).
  Local Open Scope subset_scope.
  
  Lemma tpn_basis_alt_prop i j U V :
    α i ⊆ U ⊠ β j ⊆ V ⊸ α i ⊗ β j ⊆ τ (U, V).
  Proof.
    change (?X ≤ ?Y) with (∏ p, p ∊ X ⊸ p ∊ Y) at 3.
    rew <-all_adj; intros [x y].
    change ( α i ⊆ U ⊠ β j ⊆ V ⊸ (x ∊ α i ⊠  y ∊ β j) ⊸ (x ⪽ U ⊠ y ⪽ V)).
    rew [(neighborhood_basis_open i x)|(neighborhood_basis_open j y)].
    rew [<-(neighborhood_basis_isotony x (α i) U)|<-(neighborhood_basis_isotony y (β j) V)].
    tautological.
  Qed.
    
  Lemma tensor_product_neighborhood_basis_alt_correct
    `{TPN:!TensorProductNeighborhood@{u} NX NY NXY}
    : NeighborhoodBasis@{u} tensor_product_neighborhood_basis_alt.
  Proof. intros [x y] N. rew (TPN (x, y) N). split.
  + rew <-aex_adj. intros [U V].
    change ((x,y) ∊ τ (U, V)) with (x ⪽ U ⊠ y ⪽ V).
    rew [(NBX x U)|(NBY y V)]. rew !2aex_frob_r. rew <-aex_adj; intros i.
    rew aex_frob_l, aex_frob_r, <-aex_adj; intros j.
    rew <-(aex_ub _ (i, j)).
    change ( ((x ∊ α i ⊠ α i ⊆ U) ⊠ y ∊ β j ⊠ β j ⊆ V) ⊠ τ (U, V) ⊆ N ⊸ (x ∊ α i ⊠ y ∊  β j) ⊠ α i ⊗ β j ⊆ N ).
    enough ( (α i ⊆ U ⊠ β j ⊆ V) ⊠ τ (U, V) ⊆ N ⊸ α i ⊗ β j ⊆ N ) as P by (revert P; tautological); clear x y.
    rew (tpn_basis_alt_prop _ _ _ _). now apply transitivity.
  + rew <-aex_adj. intros [i j]. rew <-(aex_ub _ (α i, β j)).
    change ((x ∊ α i ⊠ y ∊ β j) ⊠ α i ⊗ β j ⊆ N ⊸ (x ⪽ α i ⊠ y ⪽ β j) ⊠ τ (α i, β j) ⊆ N).
    apply aprod_proper_aimpl.
    * now rew [(neighborhood_basis_open i x)|(neighborhood_basis_open j y)].
    * clear x y. enough (τ (α i, β j) ⊆ α i ⊗ β j) as E by now rew E.
      intros [x y]. change (x ⪽ α i ⊠ y ⪽ β j ⊸ x ∊ α i ⊠ y ∊ β j).
      now rew [(neighborhood_basis_open_iff i x)|(neighborhood_basis_open_iff j y)].
  Qed.
End layered_basis.
Local Abbreviation tsr_basis2 := tensor_product_neighborhood_basis_alt.
#[global] Hint Extern 0 (NeighborhoodBasis tensor_product_neighborhood_basis_alt) =>
  simple notypeclasses refine tensor_product_neighborhood_basis_alt_correct : typeclass_instances.

  
Section tensor_product.
  Universes u.
  Local Abbreviation β := (tsr_basis _ _).

  Context {NU : Neighborhood@{u} 𝟏} {UN:Discrete@{u} NU} `{@Topology@{u} X NX}.
  Local Abbreviation uₗ := (tensor_unit_l X).
  Local Abbreviation uᵣ := (tensor_unit_r X).
  
  Lemma tensor_unit_l_emb `{@TensorProductNeighborhood@{u} 𝟏 X NU NX NUX}
    : ContinuouslyEmbedding uₗ.
  Proof. do 2 (split; try exact _).
  + apply cont_by_basis_dom. intros [[] x] N.
    rew <-(aex_ub _ (⊤:𝒫 𝟏, N)).
    change ( x ⪽ N ⊸ (tt ⪽ ⊤ ⊠ x ⪽ N) ⊠ β (⊤, N) ⊆ uₗ* N).
    rew is_discrete_nbrhood.
    change ( x ⪽ N ⊸ (𝐓 ⊠ x ⪽ N) ⊠ β (⊤, N) ⊆ uₗ* N).
    enough (β (⊤, N) ⊆ uₗ* N) as E by (revert E; tautological).
    clear x; intros [[] x].
    change ( (tt ⪽ ⊤ ⊠ x ⪽ N) ⊸ x ∊ N).
    rew is_discrete_nbrhood. simplify. apply top_refl.
  + refine (invert_continuous (f:=uₗ⁻¹)); try exact _.
    apply cont_by_basis_codom. intros x [P N].
    change ( tt ⪽ P ⊠ x ⪽ N ⊸ x ⪽ { x':X | tt ⪽ P ⊠ x' ⪽ N } ).
    rew <-(top_isotony x { x':X | x' ⪽ N } { x':X | tt ⪽ P ⊠ x' ⪽ N }).
    rew <-(top_trans x N), (aprod_com (tt ⪽ P) _).
    apply aprod_proper_aimpl; [ easy |]; clear x.
    change ( tt ⪽ P ⊸ ∏ x':X, x' ⪽ N ⊸ tt ⪽ P ⊠ x' ⪽ N ).
    rew <-all_adj; intros x'; rew <-(aprod_adj _ _ _).
    tautological.
  Qed.
    
  Lemma tensor_unit_r_emb `{@TensorProductNeighborhood@{u} X 𝟏 NX NU NXU}
    : ContinuouslyEmbedding uᵣ.
  Proof. do 2 (split; try exact _).
  + apply cont_by_basis_dom. intros [x []] N.
    rew <-(aex_ub _ (N, ⊤:𝒫 𝟏)).
    change ( x ⪽ N ⊸ (x ⪽ N ⊠ tt ⪽ ⊤) ⊠ β (N, ⊤) ⊆ uᵣ* N).
    rew is_discrete_nbrhood.
    change ( x ⪽ N ⊸ (x ⪽ N ⊠ 𝐓) ⊠ β (N, ⊤) ⊆ uᵣ* N).
    enough (β (N, ⊤) ⊆ uᵣ* N) as E by (revert E; tautological).
    clear x; intros [x []].
    change ( (x ⪽ N ⊠ tt ⪽ ⊤) ⊸ x ∊ N).
    rew is_discrete_nbrhood. simplify. apply top_refl.
  + refine (invert_continuous (f:=uᵣ⁻¹)); try exact _.
    apply cont_by_basis_codom. intros x [N P].
    change ( x ⪽ N ⊠ tt ⪽ P ⊸ x ⪽ { x':X | x' ⪽ N ⊠ tt ⪽ P } ).
    rew <-(top_isotony x { x':X | x' ⪽ N } { x':X | x' ⪽ N ⊠ tt ⪽ P }).
    rew <-(top_trans x N).
    apply aprod_proper_aimpl; [ easy |]; clear x.
    change ( tt ⪽ P ⊸ ∏ x':X, x' ⪽ N ⊸ x' ⪽ N ⊠ tt ⪽ P ).
    rew <-all_adj; intros x'; rew <-(aprod_adj _ _ _).
    tautological.
  Qed.
End tensor_product.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_emb : typeclass_instances.
#[global] Hint Extern 2 (Continuous             (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_emb : typeclass_instances.

#[global] Hint Extern 2 (ContinuouslyEmbedding  (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_emb : typeclass_instances.
#[global] Hint Extern 2 (Continuous             (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_emb : typeclass_instances.

(** Tensor symmetry *)

Lemma tensor_swap_cont@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY}
  `{TPN_XY:!TensorProductNeighborhood@{u} NX NY NXY}
  `{TPN_YX:!TensorProductNeighborhood@{u} NY NX NYX}
  : Continuous (tensor_swap X Y).
Proof. apply cont_by_basis. intros [x y] [M N]. rew <-(aex_ub _ (N, M)).
  assert ( tsr_basis NX NY (N, M) ⊆ (tensor_swap X Y)* (tsr_basis NY NX (M, N)) ).
  * clear x y. intros [x y]. change (x ⪽ N ⊠ y ⪽ M ⊸ y ⪽ M ⊠ x ⪽ N). tautological.
  * simplify. change ( y ⪽ M ⊠ x ⪽ N ⊸ (x ⪽ N ⊠ y ⪽ M) ). tautological.
Qed.
#[global] Hint Extern 2 (Continuous (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_cont : typeclass_instances.

Lemma tensor_swap_emb@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY}
  `{TPN_XY:!TensorProductNeighborhood@{u} NX NY NXY}
  `{TPN_YX:!TensorProductNeighborhood@{u} NY NX NYX}
  : ContinuouslyEmbedding (tensor_swap X Y).
Proof. do 2 (split; try exact _). exact (invert_continuous (f := tensor_swap Y X)). Qed.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_emb : typeclass_instances.

(** Projections *)

Lemma tensor_proj1_cont@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY}
  `{TPN:!TensorProductNeighborhood@{u} NX NY NXY}
  : Continuous (tensor_proj1 X Y).
Proof. apply cont_by_basis_dom. intros [x y] N.
  rew <-(aex_ub _ (N, full_subset Y)).
  match goal with |- apos (_ ⊸ _ ⊠ ?P) => enough P as Q; [ rew (aprod_true_r Q); clear Q |] end.
+ change ( x ⪽ N ⊸ x ⪽ N ⊠ y ⪽ full_subset Y ).
  rew (aprod_true_r (top_nullary_additivity y)). easy.
+ clear x y. intros [x y].
  change ( x ⪽ N ⊠ y ⪽ full_subset Y ⊸ x ∊ N ).
  rew (top_refl x N). tautological.
Qed.

Lemma tensor_proj2_cont@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY}
  `{TPN:!TensorProductNeighborhood@{u} NX NY NXY}
  : Continuous (tensor_proj2 X Y).
Proof. apply cont_by_basis_dom. intros [x y] N.
  rew <-(aex_ub _ (full_subset X, N)).
  match goal with |- apos (_ ⊸ _ ⊠ ?P) => enough P as Q; [ rew (aprod_true_r Q); clear Q |] end.
+ change ( y ⪽ N ⊸ x ⪽ full_subset X ⊠ y ⪽ N ).
  rew (aprod_true_l (top_nullary_additivity x)). easy.
+ clear x y. intros [x y].
  change ( x ⪽ full_subset X ⊠ y ⪽ N ⊸ y ∊ N ).
  rew (top_refl y N). tautological.
Qed.
#[global] Hint Extern 2 (Continuous (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_cont : typeclass_instances.

(** Associators *)
Section tensor_assoc.
  Universes u.
  Context `{@Topology@{u} X NX, @Topology@{u} Y NY, @Topology@{u} Z NZ}.
  Context `{TPN_XY:!TensorProductNeighborhood@{u} NX NY NXY}.
  Context `{TPN_YZ:!TensorProductNeighborhood@{u} NY NZ NYZ}.
  Context `{TPN_l:!TensorProductNeighborhood@{u} NXY NZ NlXYZ}.
  Context `{TPN_r:!TensorProductNeighborhood@{u} NX NYZ NrXYZ}.
  Local Open Scope subset_scope.

  Lemma tensor_assoc_l_cont : Continuous (tensor_assoc_l X Y Z).
  Proof.
    apply (cont_by_basis (α := tsr_basis2) (β := tsr_basis2)).
    intros [[x y] z] [N₁ [N₂ N₃]]. rew <-(aex_ub _ (N₁, N₂, N₃)).
    match goal with |- apos (_ ⊸ _ ⊠ ?P) => enough P as Q; [ rew (aprod_true_r Q); clear Q |] end.
  + change (x ⪽ N₁ ⊠ (y ⪽ N₂ ⊠ z ⪽ N₃) ⊸ (x ⪽ N₁ ⊠ y ⪽ N₂) ⊠ z ⪽ N₃). tautological.
  + clear x y z. intros [[x y] z].
    change ((x ⪽ N₁ ⊠ y ⪽ N₂) ⊠ z ⪽ N₃ ⊸ x ⪽ N₁ ⊠ (y ⪽ N₂ ⊠ z ⪽ N₃)). tautological.
  Qed.

  Lemma tensor_assoc_r_cont : Continuous (tensor_assoc_r X Y Z).
  Proof.
    apply (cont_by_basis (α := tsr_basis2) (β := tsr_basis2)).
    intros [x [y z]] [[N₁ N₂] N₃]. rew <-(aex_ub _ (N₁, (N₂, N₃))).
    match goal with |- apos (_ ⊸ _ ⊠ ?P) => enough P as Q; [ rew (aprod_true_r Q); clear Q |] end.
  + change ((x ⪽ N₁ ⊠ y ⪽ N₂) ⊠ z ⪽ N₃ ⊸ x ⪽ N₁ ⊠ (y ⪽ N₂ ⊠ z ⪽ N₃)). tautological.
  + clear x y z. intros [x [y z]].
    change (x ⪽ N₁ ⊠ (y ⪽ N₂ ⊠ z ⪽ N₃) ⊸ (x ⪽ N₁ ⊠ y ⪽ N₂) ⊠ z ⪽ N₃). tautological.
  Qed.

  Local Hint Extern 2 (Continuous (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_cont : typeclass_instances.
  Local Hint Extern 2 (Continuous (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_cont : typeclass_instances.

  Lemma tensor_assoc_l_emb : ContinuouslyEmbedding (tensor_assoc_l X Y Z).
  Proof. split; [ split | exact _ ].
  + exact _.
  + exact (invert_continuous (f := tensor_assoc_r X Y Z)).
  Qed.

  Lemma tensor_assoc_r_emb : ContinuouslyEmbedding (tensor_assoc_r X Y Z).
  Proof. split; [ split | exact _ ].
  + exact _.
  + exact (invert_continuous (f := tensor_assoc_l X Y Z)).
  Qed.
End tensor_assoc.

#[global] Hint Extern 2 (Continuous             (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_cont : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_emb : typeclass_instances.

#[global] Hint Extern 2 (Continuous             (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_cont : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_emb : typeclass_instances.

(** Tensor functoriality *)

Section tensor_map.
  Universes u.
  Import tensor_map_notation.
  Context `{@Topology@{u} X₁ NX₁, @Topology@{u} X₂ NX₂, @Topology@{u} Y₁ NY₁, @Topology@{u} Y₂ NY₂}.
  Context `{TPNX:!TensorProductNeighborhood@{u} NX₁ NX₂ NX}.
  Context `{TPNY:!TensorProductNeighborhood@{u} NY₁ NY₂ NY}.
  Context {f:X₁ ⇾ Y₁} {g:X₂ ⇾ Y₂}.
  Local Open Scope subset_scope.

  Lemma tensor_map_cont `{!Continuous f, !Continuous g} : Continuous ⟨f, g⟩.
  Proof.  apply cont_by_basis. intros [x₁ x₂] [N M].
    rew <-(aex_ub _ (f* { y₁ : Y₁ | y₁ ⪽ N }, g* { y₂ : Y₂ | y₂ ⪽ M })).
    match goal with |- apos (_ ⊸ _ ⊠ ?P) => enough P as Q; [ rew (aprod_true_r Q); clear Q |] end.
  + change ( f x₁ ⪽ N ⊠ g x₂ ⪽ M ⊸ x₁ ⪽ f* { y₁ : Y₁ | y₁ ⪽ N } ⊠ x₂ ⪽ g* { y₂ : Y₂ | y₂ ⪽ M } ).
    rew [<-(continuity f x₁ { y₁ : Y₁ | y₁ ⪽ N })|<-(continuity g x₂ { y₂ : Y₂ | y₂ ⪽ M })].
    rew [<-(top_trans (f x₁) N)|<-(top_trans (g x₂) M)].
    tautological.
  + clear x₁ x₂. intros [x₁ x₂].
    change ( x₁ ⪽ f* { y₁ : Y₁ | y₁ ⪽ N } ⊠ x₂ ⪽ g* { y₂ : Y₂ | y₂ ⪽ M } ⊸ f x₁ ⪽ N ⊠ g x₂ ⪽ M ).
    rew [(top_refl x₁ (f* { y₁ : Y₁ | y₁ ⪽ N }))|(top_refl x₂ (g* { y₂ : Y₂ | y₂ ⪽ M }))].
    tautological.
  Qed.
  #[local] Hint Extern 2 (Continuous ⟨_, _⟩) => simple notypeclasses refine tensor_map_cont : typeclass_instances.

  Lemma tensor_map_reflecting `{!ContinuouslyReflecting f, !ContinuouslyReflecting g} : ContinuouslyReflecting ⟨f, g⟩.
  Proof. apply refl_by_basis. intros [x₁ x₂] [A B].
    change ( x₁ ⪽ A ⊠ x₂ ⪽ B ⊸ ∐ j : (𝒫 Y₁ ⊗ 𝒫 Y₂)%set, ⟨ f, g ⟩ (x₁, x₂) ∊ tsr_basis NY₁ NY₂ j ⊠ ⟨ f, g ⟩* (tsr_basis NY₁ NY₂ j) ⊆ tsr_basis NX₁ NX₂ (A, B) ).
    rew [(top_trans x₁ A)|(top_trans x₂ B)].
    rew [(cont_reflection f x₁ { y₁ : X₁ | y₁ ⪽ A })|(cont_reflection g x₂ { y₂ : X₂ | y₂ ⪽ B })].
    rew <-aex_adj2; intros V₁ V₂.
    rew <-(aex_ub _ (V₁, V₂)).
    enough ( f* V₁ ⊆ { y₁ : X₁ | y₁ ⪽ A } ⊠ g* V₂ ⊆ { y₂ : X₂ | y₂ ⪽ B } ⊸ ⟨ f, g ⟩* (tsr_basis NY₁ NY₂ (V₁, V₂)) ⊆ tsr_basis NX₁ NX₂ (A, B) ) as Einc.
  + rew <-Einc.
    change ( (f x₁ ⪽ V₁ ⊠ f* V₁ ⊆ { y₁ : X₁ | y₁ ⪽ A }) ⊠ (g x₂ ⪽ V₂ ⊠ g* V₂ ⊆ { y₂ : X₂ | y₂ ⪽ B }) ⊸ (f x₁ ⪽ V₁ ⊠ g x₂ ⪽ V₂) ⊠ (f* V₁ ⊆ { y₁ : X₁ | y₁ ⪽ A } ⊠ g* V₂ ⊆ { y₂ : X₂ | y₂ ⪽ B }) ).
    now rew (aprod_medial _ _ _ _).
  + clear x₁ x₂.
    change ( f* V₁ ⊆ { y₁ : X₁ | y₁ ⪽ A } ⊠ g* V₂ ⊆ { y₂ : X₂ | y₂ ⪽ B } ⊸ ∏ p : (X₁ ⊗ X₂)%set, p ∊ ⟨ f, g ⟩* (tsr_basis NY₁ NY₂ (V₁, V₂)) ⊸ p ∊ tsr_basis NX₁ NX₂ (A, B) ).
    rew <-all_adj; intros [x₁ x₂].
    change ( f* V₁ ⊆ { y₁ : X₁ | y₁ ⪽ A } ⊠ g* V₂ ⊆ { y₂ : X₂ | y₂ ⪽ B } ⊸ (f x₁ ⪽ V₁ ⊠ g x₂ ⪽ V₂) ⊸ x₁ ⪽ A ⊠ x₂ ⪽ B ).
    rew [(top_refl (f x₁) V₁)|(top_refl (g x₂) V₂)].
    rew <-(aprod_adj _ _ _), (aprod_medial _ _ _ _).
    apply aprod_proper_aimpl.
    * rew (aprod_com _ _). exact (subset_apply x₁ (f* V₁) { y₁ : X₁ | y₁ ⪽ A }).
    * rew (aprod_com _ _). exact (subset_apply x₂ (g* V₂) { y₂ : X₂ | y₂ ⪽ B }).
  Qed.

  #[local] Hint Extern 2 (ContinuouslyReflecting ⟨_, _⟩) => simple notypeclasses refine tensor_map_reflecting : typeclass_instances.

  Lemma tensor_map_initial `{!ContinuouslyInitial f, !ContinuouslyInitial g} : ContinuouslyInitial ⟨f, g⟩.
  Proof. split.
  + exact tensor_map_cont.
  + exact tensor_map_reflecting.
  Qed.

  #[local] Hint Extern 2 (ContinuouslyInitial ⟨_, _⟩) => simple notypeclasses refine tensor_map_initial : typeclass_instances.
  Lemma tensor_map_emb `{!ContinuouslyEmbedding f, !ContinuouslyEmbedding g} : ContinuouslyEmbedding ⟨f, g⟩.
  Proof. now split. Qed.
End tensor_map.
Import tensor_map_notation.
#[global] Hint Extern 2 (Continuous ⟨_, _⟩) => simple notypeclasses refine tensor_map_cont : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting ⟨_, _⟩) => simple notypeclasses refine tensor_map_reflecting : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial ⟨_, _⟩) => simple notypeclasses refine tensor_map_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding ⟨_, _⟩) => simple notypeclasses refine tensor_map_emb : typeclass_instances.

Local Open Scope subset_scope.

Lemma dense_tensor_map@{u} {X₁ X₂:set@{u}}
  `{@Topology@{u} Y₁ NY₁, @Topology@{u} Y₂ NY₂} `{HT:@TensorProductNeighborhood Y₁ Y₂ NY₁ NY₂ NY}
   {f:X₁ ⇾ Y₁} {g:X₂ ⇾ Y₂} `{!Dense f, !Dense g} : Dense ⟨f, g⟩.
Proof. apply Dense_by_basis. intros [y₁ y₂] [N M].
  change ( y₁ ⪽ N ⊠ y₂ ⪽ M ⊸ ∐ p : (X₁ ⊗ X₂)%set, ⟨f, g⟩ p ∊ tsr_basis NY₁ NY₂ (N, M) ).
  rew [(Dense_meets f y₁ N)|(Dense_meets g y₂ M)].
  rew <-aex_adj2; intros x₁ x₂.
  now rew <-(aex_ub _ (x₁, x₂)).
Qed.
#[global] Hint Extern 2 (Dense (func_op ⟨_, _⟩)) => simple notypeclasses refine  dense_tensor_map : typeclass_instances.

(** * Tensor to product

    The canonical comparison map [c = tensor_to_prod : X ⊗ Y ⇾ X × Y],
    when the cartesian product exists ([CartesianProductTopology]), is
    continuous — by the universal property, with the tensor projections as
    the cone — and dense (it is the identity on points; that much needs no
    universal property at all).  It is *not* in general reflecting or
    injective: both contrapositives demand the additive disjunction
    [(a⁺→b⁻) ∧ (b⁺→a⁻) ⊢ a⁻ ∨ b⁻] — deciding which coordinate fails — the
    gap that makes the product a certificate rather than a construction
    (see counterexamples/cartesian_product.v). *)

Lemma tensor_to_prod_cont@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY}
  `{TPN:!TensorProductNeighborhood@{u} NX NY NXY}
  `{CPT : !CartesianProductTopology@{u} (NX:=NX) (NY:=NY) NP}
  : Continuous (tensor_to_prod X Y).
Proof. destruct CPT as [_ _ Hup].
  apply (Hup _ _ _ (tensor_to_prod X Y)); [ exact tensor_proj1_cont | exact tensor_proj2_cont ].
Qed.
#[global] Hint Extern 2 (Continuous (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_cont : typeclass_instances.

Lemma tensor_to_prod_dense@{u} {X Y : set@{u}} 
  `{HT : !Topology@{u} (X × Y) (XN:=NP)}
  : Dense (tensor_to_prod X Y).
Proof. split; try exact _.
  change ( closure (range (tensor_to_prod X Y)) = ⊤ ).
  enough ( range (tensor_to_prod X Y) = ⊤ ) as E by (rew E; exact closure_space).
  rew <-(above_top _). intros [x y].
  change ( 𝐓 ⊸ ∐ p, tensor_to_prod X Y p = (x, y) ). simplify.
  now exists (x, y).
Qed.
#[global] Hint Extern 2 (Dense (func_op (tensor_to_prod _ _))) => simple notypeclasses refine tensor_to_prod_dense : typeclass_instances.

(** Density of [prod_map] follows by naturality: [prod_map (f,g) ∘ tensor_to_prod]
    is definitionally [tensor_to_prod ∘ ⟨f, g⟩], which is dense ∘ dense
    (with [tensor_to_prod] continuous by the universal property). *)

Lemma dense_prod_map@{u} {X₁ X₂ : set@{u}}
  `{@Topology@{u} Y₁ NY₁, @Topology@{u} Y₂ NY₂}
  `{CPT : !CartesianProductTopology@{u} (NX:=NY₁) (NY:=NY₂) NP}
  {f:X₁ ⇾ Y₁} {g:X₂ ⇾ Y₂} `{!Dense f, !Dense g}
  : Dense (prod_map (f, g)).
Proof.
  refine (Dense_factor_right (tensor_to_prod X₁ X₂) (prod_map (f, g))).
  now change (Dense (tensor_to_prod Y₁ Y₂ ∘ ⟨f, g⟩)).
Qed.
#[global] Hint Extern 2 (Dense (func_op (func_op prod_map _))) => simple notypeclasses refine dense_prod_map : typeclass_instances.

(** Cartesian conveniences, under product certificates: the pairing of
    continuous maps, the diagonal, and the functorial action are continuous.
    Each is the universal property plus a definitional naturality square. *)

Lemma to_prod_cont@{u}
  `{@Topology@{u} Z NZ, @Topology@{u} X NX, @Topology@{u} Y NY}
  `{CPT : !CartesianProductTopology@{u} (NX:=NX) (NY:=NY) NP}
  {f:Z ⇾ X} {g:Z ⇾ Y} `{Cf:!Continuous f, Cg:!Continuous g}
  : Continuous (to_prod (f, g)).
Proof. destruct CPT as [_ _ Hup].
  apply (Hup _ _ _ (to_prod (f, g))); [ exact Cf | exact Cg ].
Qed.
#[global] Hint Extern 2 (Continuous (to_prod _)) => simple notypeclasses refine to_prod_cont : typeclass_instances.

Lemma prod_diag_cont@{u} `{@Topology@{u} Z NZ}
  `{CPT : !CartesianProductTopology@{u} (NX:=NZ) (NY:=NZ) NP}
  : Continuous (prod_diag Z).
Proof. exact (to_prod_cont (f:=id_fun Z) (g:=id_fun Z)). Qed.
#[global] Hint Extern 2 (Continuous (prod_diag _)) => simple notypeclasses refine prod_diag_cont : typeclass_instances.

Lemma prod_map_cont@{u}
  `{@Topology@{u} X₁ NX₁, @Topology@{u} X₂ NX₂, @Topology@{u} Y₁ NY₁, @Topology@{u} Y₂ NY₂}
  `{CPX : !CartesianProductTopology@{u} (NX:=NX₁) (NY:=NX₂) NPX}
  `{CPY : !CartesianProductTopology@{u} (NX:=NY₁) (NY:=NY₂) NPY}
  {f:X₁ ⇾ Y₁} {g:X₂ ⇾ Y₂} `{Cf:!Continuous f, Cg:!Continuous g}
  : Continuous (prod_map (f, g)).
Proof. destruct CPY as [_ _ Hup].
  apply (Hup _ _ _ (prod_map (f, g))).
  + exact (compose_cont (f:=prod_proj1 X₁ X₂) (g:=f)).
  + exact (compose_cont (f:=prod_proj2 X₁ X₂) (g:=g)).
Qed.
#[global] Hint Extern 2 (Continuous (prod_map _)) => simple notypeclasses refine prod_map_cont : typeclass_instances.


(** Relations *)

Local Open Scope grp_scope.
Local Open Scope sg_op_scope.

Local Abbreviation τ := (tensor_product_neighborhood_basis _ _).
Local Abbreviation int := interior.
Local Abbreviation cl := closure.

Lemma interior_flip@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY, !TensorProductNeighborhood NX NY NXY, !TensorProductNeighborhood NY NX NYX}
  : int ∘ (@flip X Y) = flip ∘ int.
Proof. intros U; simplify; apply le_antisym; split.
+ change (flip (flip (interior (flip U))) ⊆ flip (interior U)).
  rew <-(order_preserving flip _ _).
  exact (continuous_preimage_interior (tensor_swap X Y) (flip U)).
+ exact (continuous_preimage_interior (tensor_swap _ _) U).
Qed.

Lemma closure_flip@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY, !TensorProductNeighborhood NX NY NXY, !TensorProductNeighborhood NY NX NYX}
  : cl ∘ (@flip X Y) = flip ∘ cl.
Proof. intros A; simplify; apply le_antisym; split.
+ exact (continuous_preimage_closure (tensor_swap Y X) A).
+ rew <-(flip_involutive (closure (flip A))), <-(order_embedding flip _ _).
  change (closure A ⊆ (tensor_swap _ _)* (closure ( (tensor_swap _ _)* A))).
  now rew <-(continuous_preimage_closure _ _).
Qed.

Lemma interior_flip_alt@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY, !TensorProductNeighborhood NX NY NXY, !TensorProductNeighborhood NY NX NYX}
  (U:𝒫 (X ⊗ Y)) : interior (flip U) = flip (interior U).
Proof. exact (interior_flip U). Qed.

Lemma closure_flip_alt@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY, !TensorProductNeighborhood NX NY NXY, !TensorProductNeighborhood NY NX NYX}
  (U:𝒫 (X ⊗ Y)) : closure (flip U) = flip (closure U).
Proof. exact (closure_flip U). Qed.

Lemma interior_inv@{u} `{@Topology@{u} X NX, !TensorProductNeighborhood NX NX NXX}
  : @interior _ NXX ∘ (⁻¹) = (⁻¹) ∘ interior.
Proof. exact interior_flip. Qed.

Lemma interior_inv_alt@{u} `{@Topology@{u} X NX, !TensorProductNeighborhood NX NX NXX}
  (U:𝒫 (X ⊗ X)) : interior U⁻¹ = (interior U)⁻¹.
Proof. exact (interior_inv U). Qed.

Lemma closure_inv@{u} `{@Topology@{u} X NX, !TensorProductNeighborhood NX NX NXX}
  : @closure _ NXX ∘ (⁻¹) = (⁻¹) ∘ closure.
Proof. exact closure_flip. Qed.

Lemma closure_inv_alt@{u} `{@Topology@{u} X NX, !TensorProductNeighborhood NX NX NXX}
  (U:𝒫 (X ⊗ X)) : closure U⁻¹ = (closure U)⁻¹.
Proof. exact (closure_inv U). Qed.

Section closure_compose_thicken.
  Universes u.
  Context 
   `{@Topology@{u} X NX, @Topology@{u} Y NY, @Topology@{u} Z NZ}
   `{!TensorProductNeighborhood NX NY NXY}
   `{!TensorProductNeighborhood NY NZ NYZ}
   `{!TensorProductNeighborhood NX NZ NXZ}
   `{!TensorProductNeighborhood NY NY NYY}
   (A : 𝒫 (X ⊗ Y)) (S : 𝒫 (Y ⊗ Y)) (B : 𝒫 (Y ⊗ Z)).

  Lemma closure_compose_thicken
    : id_rel Y ⊆ int S ⊸ cl A ⋄ cl B  ⊆  cl (A ⋄ S ⋄ B).
  Proof.
    change (id_rel Y ⊆ interior S ⊸ ∏ p, p ∊ (closure A ⋄ closure B) ⊸ p ∊ closure (A ⋄ S ⋄ B)).
    rew <-all_adj; intros [a c]. rew <-(aprod_adj _ _ _).
    change ( id_rel Y ⊆ interior S ⊠ (∐ b, (a, b) ∊ closure A ⊠ (b, c) ∊ closure B) ⊸ (a, c) ∊ closure (A ⋄ S ⋄ B) ).
    rew aex_frob_l, <-aex_adj; intros b.
    rew (in_closure_meets (A ⋄ S ⋄ B) (a, c)), <-all_adj; intros N. rew <-(aprod_adj _ _ _).
    rew (neighborhood_basis_find (a, c) N).
    rew aex_frob_l, <-aex_adj; intros [N₁ N₂].
    change (id_rel Y ⊆ interior S) with (∏ p, p ∊ id_rel Y ⊸ p ⪽ S); rew (all_lb _ (b, b)).
    change ((b, b) ∊ id_rel Y) with (b = b); let t := constr:(ltac:(refl):b = b) in rew (aimpl_true_l t).
    rew (neighborhood_basis_find (b, b) S).
    rew aex_frob_r, aex_frob_r, <-aex_adj; intros [P Q].
    change ((?a, ?b) ∊ τ (?A, ?B)) with (a ⪽ A ⊠ b ⪽ B).
    rew (in_closure_meets _ _).
    rew [(all_lb _ (τ (N₁, P)))|(all_lb _ (τ (Q, N₂)))].
    rew [<-(neighborhood_basis_open (N₁, P) (a, b))|<-(neighborhood_basis_open (Q, N₂) (b, c))].
    change ((?a, ?b) ∊ τ (?A, ?B)) with (a ⪽ A ⊠ b ⪽ B).
    enough ( (∐ z, z ∊ τ (N₁, P) ⊠ z ∊ A) ⊠ (∐ z, z ∊ τ (Q, N₂) ⊠ z ∊ B)
             ⊸ ((τ (P, Q) ⊆ S ⊠ τ (N₁, N₂) ⊆ N ) ⊸ ∐ z, z ∊ N ⊠ z ∊ A ⋄ S ⋄ B )) as G by (revert G; tautological).
    rew <-aex_adj2; intros [a' b'][b'' c'].
    change ((?a, ?b) ∊ τ (?A, ?B)) with (a ⪽ A ⊠ b ⪽ B).
    enough ( ((a' ⪽ N₁ ⊠ c' ⪽ N₂) ⊠ τ (N₁, N₂) ⊆ N) ⊠ ((b' ⪽ P ⊠ b'' ⪽ Q) ⊠ τ (P, Q) ⊆ S) ⊠ (a', b') ∊ A  ⊠ (b'', c') ∊ B
             ⊸ ∐ z : (X ⊗ Z)%set, z ∊ N ⊠ z ∊ A ⋄ S ⋄ B ) as G by (revert G; tautological).
    change (?a ⪽ ?A ⊠ ?b ⪽ ?B) with ((a, b) ∊ τ (A, B)).
    rew [(subset_apply _ (τ (N₁, N₂)) _) | (subset_apply _ (τ (P, Q)) _)].
    rew <-(aex_ub _ (a', c')).
    enough (((a', b') ∊ A ⊠ (b', b'') ∊ S) ⊠ (b'', c') ∊ B ⊸ (a', c') ∊ A ⋄ S ⋄ B) as G by (revert G; tautological).
    change ( (?a, ?c) ∊ ?A ⋄ ?B ) with (∐ b, (a, b) ∊ A ⊠ (b, c) ∊ B).
    rew <-(aex_ub _ b''). apply aprod_proper_aimpl; [| easy ].
    exact (aex_ub _ b').
  Qed.

  Lemma closure_compose_thicken_alt
    : id_rel Y ⊆ int S → cl A ⋄ cl B  ⊆  cl (A ⋄ S ⋄ B).
  Proof. now rew closure_compose_thicken. Qed.
End closure_compose_thicken.


(** The interior-side companion: relational composition is lax for interiors
    on the outer factors — interiors on the flanks confine the whole
    composite inside its interior. *)
Lemma int_compose_both@{u}
 `{@Topology@{u} X NX, @Topology@{u} W NW}
 {Y Z:set@{u}} {NY:Neighborhood@{u} Y} {NZ:Neighborhood@{u} Z}
 `{!TensorProductNeighborhood NX NY NXY}
 `{!TensorProductNeighborhood NZ NW NZW}
 `{!TensorProductNeighborhood NX NW NXW}
 (A : 𝒫 (X ⊗ Y)) (B : 𝒫 (Y ⊗ Z)) (C : 𝒫 (Z ⊗ W))
 : int A ⋄ B ⋄ int C ⊆ int (A ⋄ B ⋄ C).
Proof.
  change (int A ⋄ B ⋄ int C ⊆ int (A ⋄ B ⋄ C)) with (∏ p, p ∊ int A ⋄ B ⋄ int C ⊸ p ∊ int (A ⋄ B ⋄ C)).
  intros [x z].
  change ((x, z) ∊ int A ⋄ B ⋄ int C) with (∐ b0, (x, b0) ∊ int A ⋄ B ⊠ (b0, z) ∊ int C).
  rew <-aex_adj; intros b.
  change ((x, b) ∊ int A ⋄ B) with (∐ a0, (x, a0) ∊ int A ⊠ (a0, b) ∊ B).
  rew aex_frob_r, <-aex_adj; intros a.
  change ((x, a) ∊ int A) with ((x, a) ⪽ A).
  change ((b, z) ∊ int C) with ((b, z) ⪽ C).
  change ((x, z) ∊ int (A ⋄ B ⋄ C)) with ((x, z) ⪽ A ⋄ B ⋄ C).
  rew (neighborhood_basis_find (x, a) A).
  rew aex_frob_r, aex_frob_r, <-aex_adj; intros [U V].
  rew (neighborhood_basis_find (b, z) C).
  rew aex_frob_l, <-aex_adj; intros [U' V'].
  rew <-(top_isotony (x, z) (τ (U, V')) (A ⋄ B ⋄ C)).
  rew <-(neighborhood_basis_open (U, V') (x, z)).
  change ((?a, ?b) ∊ τ (?A, ?B)) with (a ⪽ A ⊠ b ⪽ B).
  enough ( ((a ⪽ V ⊠ (a, b) ∊ B) ⊠ b ⪽ U') ⊠ (τ (U, V) ⊆ A ⊠ τ (U', V') ⊆ C)
           ⊸ τ (U, V') ⊆ A ⋄ B ⋄ C ) as G by (revert G; tautological).
  change (τ (U, V') ⊆ A ⋄ B ⋄ C) with (∏ q, q ∊ τ (U, V') ⊸ q ∊ A ⋄ B ⋄ C).
  rew <-all_adj; intros [x' z'].
  change ((x', z') ∊ τ (U, V')) with (x' ⪽ U ⊠ z' ⪽ V').
  change ((x', z') ∊ A ⋄ B ⋄ C) with (∐ b1, (x', b1) ∊ A ⋄ B ⊠ (b1, z') ∊ C).
  rew <-(aex_ub _ b).
  change ((x', b) ∊ A ⋄ B) with (∐ a1, (x', a1) ∊ A ⊠ (a1, b) ∊ B).
  rew <-(aex_ub _ a).
  enough ( ((x' ⪽ U ⊠ a ⪽ V) ⊠ τ (U, V) ⊆ A) ⊠ (a, b) ∊ B ⊠ ((b ⪽ U' ⊠ z' ⪽ V') ⊠ τ (U', V') ⊆ C)
           ⊸ ((x', a) ∊ A ⊠ (a, b) ∊ B) ⊠ (b, z') ∊ C ) as G' by (revert G'; tautological).
  change (?a ⪽ ?A ⊠ ?b ⪽ ?B) with ((a, b) ∊ τ (A, B)).
  rew [(subset_apply _ (τ (U, V)) _) | (subset_apply _ (τ (U', V')) _)].
  tautological.
Qed.

(** A cartesian product topology with Hausdorff factors is Hausdorff.  The
    pair equality of [X × Y] is additive, so the meeting-neighborhoods
    premise is spent once per coordinate, through the continuous projection;
    the tensor product, whose equality is multiplicative, has no such
    lemma. *)
Lemma cartesian_product_hausdorff@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY}
  `{!Hausdorff X, !Hausdorff Y} `{HP:@CartesianProductTopology@{u} X Y NX NY NXY}
  : Hausdorff (X × Y).
Proof. intros p q.
  change ((∏ U V, of_course (p ⪽ U ⊠ q ⪽ V) ⊸ ∐ z, z ∊ U ⊠ z ∊ V)
    ⊸ prod_proj1 X Y p = prod_proj1 X Y q ∧ prod_proj2 X Y p = prod_proj2 X Y q).
  apply aand_intro; [ exact (cont_hausdorff_meet (prod_proj1 X Y) p q)
                    | exact (cont_hausdorff_meet (prod_proj2 X Y) p q) ].
Qed.
#[global] Hint Extern 2 (Hausdorff (_ × _)) => simple notypeclasses refine cartesian_product_hausdorff : typeclass_instances.

