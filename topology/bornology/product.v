Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.bornology.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import bornology.base bornology.basis.
Require Import easy rewrite replc simplify tactics.misc.

Import projection_notation.
Import image_notation.
Import tensor_map_notation.

Local Abbreviation tsr_pres  := tensor_product_bornology_presentation.
Local Abbreviation cart_pres := cartesian_product_bornology_presentation.

(** Canonical product bornologies *)

Section default_bornology.
  Universes u.
  Context {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y}.

  Definition tensor_product_bornology : Bornology (X ⊗ Y) := presented_bornology (tsr_pres _ _).
  Definition cartesian_product_bornology : Bornology (X × Y) := presented_bornology (cart_pres _ _).

  Lemma tensor_product_bornology_correct : TensorProductBornology _ _ tensor_product_bornology.
  Proof. now unfold TensorProductBornology, tensor_product_bornology. Qed.
  Lemma cartesian_product_bornology_correct : CartesianProductBornology _ _ cartesian_product_bornology.
  Proof. now unfold CartesianProductBornology, cartesian_product_bornology. Qed.
End default_bornology.

#[global] Hint Extern 20 (Bornology (_ ⊗ _)) => notypeclasses refine tensor_product_bornology : typeclass_instances.
#[global] Hint Extern 2 (TensorProductBornology _ _ tensor_product_bornology) => simple notypeclasses refine tensor_product_bornology_correct : typeclass_instances.

#[global] Hint Extern 20 (Bornology (_ × _)) => notypeclasses refine cartesian_product_bornology : typeclass_instances.
#[global] Hint Extern 2 (CartesianProductBornology _ _ cartesian_product_bornology) => simple notypeclasses refine cartesian_product_bornology_correct : typeclass_instances.

(** tsr_pres / cart_pres are monotone *)

Section monotone.
  Universes u.
  Context {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y}.

  Lemma tensor_product_bornology_presentation_monotone : OrderPreserving (tsr_pres 𝒜 ℬ).
  Proof. now change (OrderPreserving (tensor_subset ∘ ⟨from_subset 𝒜, from_subset ℬ⟩)). Qed.

  Lemma cartesian_product_bornology_presentation_monotone : OrderPreserving (cart_pres 𝒜 ℬ).
  Proof. now change (OrderPreserving ((⊓) ∘ ⟨(prod_proj1 X Y)*, (prod_proj2 X Y)*⟩ ∘ ⟨from_subset 𝒜, from_subset ℬ⟩)). Qed.
End monotone.
#[global] Hint Extern 2 (OrderPreserving (tsr_pres  _ _)) => simple notypeclasses refine tensor_product_bornology_presentation_monotone    : typeclass_instances.
#[global] Hint Extern 2 (OrderPreserving (cart_pres _ _)) => simple notypeclasses refine cartesian_product_bornology_presentation_monotone : typeclass_instances.

(** Layered Bases *)

Section layered_bases.
  Universes u.
  Context {Λ₁:Type@{u}} `{𝒜:Bornology@{u} X} (α:Λ₁ → 𝒜)
          {Λ₂:Type@{u}} `{ℬ:Bornology@{u} Y} (β:Λ₂ → ℬ).

  Definition tensor_product_bornology_basis `{H:@TensorProductBornology X Y 𝒜 ℬ 𝒞}
    := λ '(i, j), ideal_presentation_basis _ (tsr_pres 𝒜 ℬ) (H:=H) (α i, β j).
  Definition cartesian_product_bornology_basis `{H:@CartesianProductBornology X Y 𝒜 ℬ 𝒞}
    := λ '(i, j), ideal_presentation_basis _ (cart_pres 𝒜 ℬ) (H:=H) (α i, β j).
End layered_bases.

Local Abbreviation tsr_basis  := tensor_product_bornology_basis.
Local Abbreviation cart_basis := cartesian_product_bornology_basis.

Section layered_bases.
  Universes u.
  Context `{HX:@BornologyBasis@{u} X 𝒜 Λ₁ α, HY:@BornologyBasis@{u} Y ℬ Λ₂ β}.

  Lemma tensor_product_bornology_basis_correct `{H:@TensorProductBornology X Y 𝒜 ℬ 𝒞}
    : BornologyBasis (tsr_basis α β).
  Proof. apply Build_IdealBasis. intros W.
    pose proof ideal_basis (ideal_presentation_basis 𝒞 (tsr_pres 𝒜 ℬ)) W as [[A B] P].
    pose proof ideal_basis α A as [i Pi].
    pose proof ideal_basis β B as [j Pj].
    exists (i, j). rew P.
    change (tsr_pres 𝒜 ℬ (A, B) ⊆ tsr_pres 𝒜 ℬ (α i, β j)).
    rew <-(order_preserving (tsr_pres _ _) _ _). now split.
  Qed.

  Lemma cartesian_product_bornology_basis_correct `{H:@CartesianProductBornology X Y 𝒜 ℬ 𝒞}
    : BornologyBasis (cart_basis α β).
  Proof. apply Build_IdealBasis. intros W.
    pose proof ideal_basis (ideal_presentation_basis 𝒞 (cart_pres 𝒜 ℬ)) W as [[A B] P].
    pose proof ideal_basis α A as [i Pi].
    pose proof ideal_basis β B as [j Pj].
    exists (i, j). rew P.
    change (cart_pres 𝒜 ℬ (A, B) ⊆ cart_pres 𝒜 ℬ (α i, β j)).
    rew <-(order_preserving (cart_pres _ _) _ _). now split.
  Qed.
End layered_bases.
#[global] Hint Extern 0 (BornologyBasis (X:=_ ⊗ _) _) => notypeclasses refine tensor_product_bornology_basis_correct : typeclass_instances.
#[global] Hint Extern 0 (BornologyBasis (X:=_ × _) _) => notypeclasses refine cartesian_product_bornology_basis_correct : typeclass_instances.

(** Cartesian Product *)

Lemma cartesian_product_bornological_space@{u}
  `{@BornologicalSpace@{u} X 𝒜} `{@BornologicalSpace@{u} Y ℬ}
  `{@CartesianProductBornology X Y 𝒜 ℬ 𝒞}
  : BornologicalSpace (X × Y).
Proof. apply presented_bornological_space.
  intros [x y]. exists (born_singleton_alt 𝒜 x, born_singleton_alt ℬ y).
  change (x ∊ singleton x ∧ y ∊ singleton y). now split.
Qed.

#[global] Hint Extern 2 (BornologicalSpace (_ × _)) => simple notypeclasses refine cartesian_product_bornological_space : typeclass_instances.

Section cartesian_product.
  Universes u.
  Context `{@BornologicalSpace@{u} X 𝒜} `{@BornologicalSpace@{u} Y ℬ}.
  Context `{@CartesianProductBornology X Y 𝒜 ℬ 𝒞}.

  Lemma prod_proj1_bornological : Bornological (prod_proj1 X Y).
  Proof. apply born_by_basis. intros [A B]. exists A.
    rew (image_preimage_adj _ _ _).
    intros [a b]. now change (a ∊ A ∧ b ∊ B ⊸ a ∊ A).
  Qed.

  Lemma prod_proj2_bornological : Bornological (prod_proj2 X Y).
  Proof. apply born_by_basis. intros [A B]. exists B.
    rew (image_preimage_adj _ _ _).
    intros [a b]. now change (a ∊ A ∧ b ∊ B ⊸ b ∊ B).
  Qed.

  Local Open Scope subset_scope.
  Lemma cartesian_product_bornology_initial `{@BornologicalSpace@{u} Z 𝒵} (f:Z ⇾ X × Y) :
    Bornological (prod_proj1 _ _ ∘ f)
  → Bornological (prod_proj2 _ _ ∘ f)
  → Bornological f.
  Proof. set (f₁ := prod_proj1 _ _ ∘ f). set (f₂ := prod_proj2 _ _ ∘ f).
    intros Hf1 Hf2. apply born_by_basis. intros C.
    exists (born_image f₁ C, born_image f₂ C).
    change (f⁎ C ⊆ f₁⁎ C × f₂⁎ C).
    subst f₁ f₂. rew (image_compose _ _).
    exact (sub_proj_image_prod (f⁎ C)).
  Qed.
End cartesian_product.
#[global] Hint Extern 2 (Bornological (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_bornological : typeclass_instances.
#[global] Hint Extern 2 (Bornological (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_bornological : typeclass_instances.


Lemma to_prod_bornological@{u} `{Hf:@Bornological@{u} X Y₁ 𝒜 ℬ₁ f, Hg:@Bornological@{u} X Y₂ 𝒜 ℬ₂ g}
  `{@CartesianProductBornology Y₁ Y₂ ℬ₁ ℬ₂ ℬ}
  : Bornological (to_prod (f, g)).
Proof. apply cartesian_product_bornology_initial; [ exact Hf | exact Hg ]. Qed.
#[global] Hint Extern 2 (Bornological (func_op to_prod (_, _))) => simple notypeclasses refine to_prod_bornological : typeclass_instances.

Lemma prod_map_bornological@{u} `{@Bornological@{u} X₁ Y₁ 𝒜₁ ℬ₁ f} `{@Bornological@{u} X₂ Y₂ 𝒜₂ ℬ₂ g}
  `{@CartesianProductBornology X₁ X₂ 𝒜₁ 𝒜₂ 𝒜} `{@CartesianProductBornology Y₁ Y₂ ℬ₁ ℬ₂ ℬ}
  : Bornological (prod_map (f, g)).
Proof. now change (prod_map (f, g)) with (to_prod (f ∘ prod_proj1 X₁ X₂, g ∘ prod_proj2 X₁ X₂)). Qed.
#[global] Hint Extern 2 (Bornological (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_bornological : typeclass_instances.

Lemma prod_map_bornology_reflecting@{u} `{@BornologyReflecting@{u} X₁ Y₁ 𝒜₁ ℬ₁ f} `{@BornologyReflecting@{u} X₂ Y₂ 𝒜₂ ℬ₂ g}
  `{@CartesianProductBornology X₁ X₂ 𝒜₁ 𝒜₂ 𝒜} `{@CartesianProductBornology Y₁ Y₂ ℬ₁ ℬ₂ ℬ}
  : BornologyReflecting (prod_map (f, g)).
Proof. apply bornology_refl_by_basis. intros [B₁ B₂].
  now exists (born_preimage f B₁, born_preimage g B₂).
Qed.
#[global] Hint Extern 2 (BornologyReflecting (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_bornology_reflecting : typeclass_instances.

Lemma prod_map_bornology_initial@{u} `{@BornologyInitial@{u} X₁ Y₁ 𝒜₁ ℬ₁ f} `{@BornologyInitial@{u} X₂ Y₂ 𝒜₂ ℬ₂ g}
  `{@CartesianProductBornology X₁ X₂ 𝒜₁ 𝒜₂ 𝒜} `{@CartesianProductBornology Y₁ Y₂ ℬ₁ ℬ₂ ℬ}
  : BornologyInitial (prod_map (f, g)).
Proof. now split. Qed.
#[global] Hint Extern 2 (BornologyInitial (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_bornology_initial : typeclass_instances.

(** Tensor Product *)
Lemma tensor_product_bornological_space@{u}
 `{@BornologicalSpace@{u} X 𝒜} `{@BornologicalSpace@{u} Y ℬ}
 `{@TensorProductBornology X Y 𝒜 ℬ 𝒞}
 : BornologicalSpace (X ⊗ Y).
Proof. apply presented_bornological_space.
  intros [x y]. exists (born_singleton_alt 𝒜 x, born_singleton_alt ℬ y).
  change (x ∊ singleton x ⊠ y ∊ singleton y). now split.
Qed.

#[global] Hint Extern 2 (BornologicalSpace (_ ⊗ _)) => simple notypeclasses refine tensor_product_bornological_space : typeclass_instances.

Import tensor_map_notation.
Local Open Scope subset_scope.

Lemma tensor_map_bornological@{u} `{@Bornological@{u} X₁ Y₁ 𝒜₁ ℬ₁ f} `{@Bornological@{u} X₂ Y₂ 𝒜₂ ℬ₂ g}
  `{@TensorProductBornology X₁ X₂ 𝒜₁ 𝒜₂ 𝒜} `{@TensorProductBornology Y₁ Y₂ ℬ₁ ℬ₂ ℬ}
  : Bornological ⟨f, g⟩.
Proof. apply born_by_basis. intros [A₁ A₂].
  exists (born_image f A₁, born_image g A₂).
  change (⟨f,g⟩⁎ (A₁ ⊗ A₂) ⊆ f⁎ A₁ ⊗ g⁎ A₂).
  now rew (image_tensor_map _ _ _ _).
Qed.
#[global] Hint Extern 2 (Bornological ⟨_, _⟩) => simple notypeclasses refine tensor_map_bornological : typeclass_instances.
#[global] Hint Extern 2 (Bornological (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_bornological : typeclass_instances.

Lemma tensor_map_bornology_reflecting@{u} `{@BornologyReflecting@{u} X₁ Y₁ 𝒜₁ ℬ₁ f} `{@BornologyReflecting@{u} X₂ Y₂ 𝒜₂ ℬ₂ g}
  `{@TensorProductBornology X₁ X₂ 𝒜₁ 𝒜₂ 𝒜} `{@TensorProductBornology Y₁ Y₂ ℬ₁ ℬ₂ ℬ}
  : BornologyReflecting ⟨f, g⟩.
Proof. apply bornology_refl_by_basis. intros [B₁ B₂].
  now exists (born_preimage f B₁, born_preimage g B₂).
Qed.
#[global] Hint Extern 2 (BornologyReflecting ⟨_, _⟩) => simple notypeclasses refine tensor_map_bornology_reflecting : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_bornology_reflecting : typeclass_instances.

Lemma tensor_map_bornology_initial@{u} `{@BornologyInitial@{u} X₁ Y₁ 𝒜₁ ℬ₁ f} `{@BornologyInitial@{u} X₂ Y₂ 𝒜₂ ℬ₂ g}
  `{@TensorProductBornology X₁ X₂ 𝒜₁ 𝒜₂ 𝒜} `{@TensorProductBornology Y₁ Y₂ ℬ₁ ℬ₂ ℬ}
  : BornologyInitial ⟨f, g⟩.
Proof. now split. Qed.
#[global] Hint Extern 2 (BornologyInitial ⟨_, _⟩) => simple notypeclasses refine tensor_map_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_bornology_initial : typeclass_instances.

(** Unitors *)
Section unitors.
  Universes u.
  Context `{@BornologicalSpace@{u} X 𝒜} `{@BornologicalSpace 𝟏 ℬ}.
  Local Abbreviation uₗ := (tensor_unit_l X).
  Local Abbreviation uᵣ := (tensor_unit_r X).

  Lemma tensor_unit_l_bornology_initial `{@TensorProductBornology@{u} 𝟏 X ℬ 𝒜 𝒞}
    : BornologyInitial uₗ.
  Proof. split.
  + apply born_by_basis. intros [[] A]. exists A.
    rew (image_preimage_adj _ _ _).
    intros [[] a]. change (𝐓 ⊠ a ∊ A ⊸ a ∊ A). tautological.
  + apply bornology_refl_by_basis. intros A. exists (tt, A).
    intros [[] a]. change (a ∊ A ⊸ 𝐓 ⊠ a ∊ A). tautological.
  Qed.

  Lemma tensor_unit_r_bornology_initial `{@TensorProductBornology@{u} X 𝟏 𝒜 ℬ 𝒞}
    : BornologyInitial uᵣ.
  Proof. split.
  + apply born_by_basis. intros [A []]. exists A.
    rew (image_preimage_adj _ _ _).
    intros [a []]. change (a ∊ A ⊠ 𝐓 ⊸ a ∊ A). tautological.
  + apply bornology_refl_by_basis. intros A. exists (A, tt).
    intros [a []]. change (a ∊ A ⊸ a ∊ A ⊠ 𝐓). tautological.
  Qed.
End unitors.
#[global] Hint Extern 2 (BornologyInitial    (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial    (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_bornology_initial : typeclass_instances.

(** Braid *)
Lemma tensor_swap_bornological@{u} `{@BornologicalSpace@{u} X 𝒜, @BornologicalSpace@{u} Y ℬ}
  `{@TensorProductBornology X Y 𝒜 ℬ 𝒞_XY}
  `{@TensorProductBornology Y X ℬ 𝒜 𝒞_YX}
  : Bornological (tensor_swap X Y).
Proof. apply born_by_basis. intros [A B]. exists (B, A).
  rew (image_preimage_adj _ _ _).
  intros [x y]. change ((x ∊ A ⊠ y ∊ B) ⊸ y ∊ B ⊠ x ∊ A).
  now rew (aprod_com _ _).
Qed.
#[global] Hint Extern 2 (Bornological (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_bornological : typeclass_instances.

Lemma tensor_swap_bornology_initial@{u} `{@BornologicalSpace@{u} X 𝒜, @BornologicalSpace@{u} Y ℬ}
  `{@TensorProductBornology X Y 𝒜 ℬ 𝒞_XY}
  `{@TensorProductBornology Y X ℬ 𝒜 𝒞_YX}
  : BornologyInitial (tensor_swap X Y).
Proof. split; try exact _. now change (BornologyReflecting (inverse (tensor_swap Y X))). Qed.
#[global] Hint Extern 2 (BornologyInitial    (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_bornology_initial : typeclass_instances.

(** Associators *)
Section associators.
  Universes u.
  Context `{@BornologicalSpace@{u} X 𝒜, @BornologicalSpace@{u} Y ℬ, @BornologicalSpace@{u} Z 𝒵}.
  Context `{@TensorProductBornology@{u} X Y 𝒜 ℬ 𝒞_XY}.
  Context `{@TensorProductBornology@{u} Y Z ℬ 𝒵 𝒞_YZ}.
  Context `{@TensorProductBornology@{u} X (Y ⊗ Z) 𝒜 𝒞_YZ 𝒞_X_YZ}.
  Context `{@TensorProductBornology@{u} (X ⊗ Y) Z 𝒞_XY 𝒵 𝒞_XY_Z}.
  Local Abbreviation αₗ := (tensor_assoc_l X Y Z).
  Local Abbreviation αᵣ := (tensor_assoc_r X Y Z).

  Local Instance tensor_assoc_l_bornological : Bornological αₗ.
  Proof.
    apply born_by_basis. intros [[A B] C]. exists (A, (B, C)).
    rew (image_preimage_adj _ _ _).
    intros [[a b] c]. change (((a ∊ A ⊠ b ∊ B) ⊠ c ∊ C) ⊸ a ∊ A ⊠ (b ∊ B ⊠ c ∊ C)).
    now rew (aprod_assoc _ _ _).
  Qed.

  Local Instance tensor_assoc_r_bornological : Bornological αᵣ.
  Proof.
    apply born_by_basis. intros [A [B C]]. exists ((A, B), C).
    rew (image_preimage_adj _ _ _).
    intros [a [b c]]. change ((a ∊ A ⊠ (b ∊ B ⊠ c ∊ C)) ⊸ (a ∊ A ⊠ b ∊ B) ⊠ c ∊ C).
    now rew <-(aprod_assoc _ _ _).
  Qed.
  
  Lemma tensor_assoc_l_bornology_initial : BornologyInitial αₗ.
  Proof. split; try exact _. now change (BornologyReflecting (inverse αᵣ)). Qed.

  Lemma tensor_assoc_r_bornology_initial : BornologyInitial αᵣ.
  Proof. split; try exact _. now change (BornologyReflecting (inverse αₗ)). Qed.
End associators.
#[global] Hint Extern 2 (Bornological        (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_bornological : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_bornological : typeclass_instances.

#[global] Hint Extern 2 (BornologyInitial    (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial    (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_bornology_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_bornology_initial : typeclass_instances.

(** Derived structure maps *)
Local Abbreviation id := (id_fun _).

Lemma tensor_proj1_bornological@{u} `{@BornologicalSpace@{u} X 𝒜, @BornologicalSpace@{u} Y ℬ}
  `{@TensorProductBornology X Y 𝒜 ℬ 𝒞}
  : Bornological (tensor_proj1 X Y).
Proof. now change (tensor_proj1 X Y) with (tensor_unit_r X ∘ ⟨id, to_Unit Y⟩). Qed.
#[global] Hint Extern 2 (Bornological (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_bornological : typeclass_instances.

Lemma tensor_proj2_bornological@{u} `{@BornologicalSpace@{u} X 𝒜, @BornologicalSpace@{u} Y ℬ}
  `{@TensorProductBornology X Y 𝒜 ℬ 𝒞}
  : Bornological (tensor_proj2 X Y).
Proof. now change (tensor_proj2 X Y) with (tensor_unit_l Y ∘ ⟨to_Unit X, id⟩). Qed.
#[global] Hint Extern 2 (Bornological (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_bornological : typeclass_instances.

Lemma tensor_to_prod_bornological@{u} `{@BornologicalSpace@{u} X 𝒜, @BornologicalSpace@{u} Y ℬ}
  `{@TensorProductBornology X Y 𝒜 ℬ 𝒞}
  `{@CartesianProductBornology X Y 𝒜 ℬ 𝒟}
  : Bornological (tensor_to_prod X Y).
Proof. now change (tensor_to_prod X Y) with (to_prod (tensor_proj1 X Y, tensor_proj2 X Y)). Qed.
#[global] Hint Extern 2 (Bornological (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_bornological : typeclass_instances.

