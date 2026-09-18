Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import topology.topology uniform.base uniform.basis uniform.product.
Require Import bornology.base bornology.basis bornology.product.
Require Import unif_born.base.
Require Import easy rewrite simplify tactics.misc.

Local Open Scope topology_scope.
Import projection_notation.
Import tensor_map_notation.

(** Tensor product *)

Lemma tensor_map_unif_born_mor@{u}
  `{@UnifBornMorphism@{u} X₁ Y₁ Φ₁ Ψ₁ 𝒜₁ ℬ₁ f} `{@UnifBornMorphism@{u} X₂ Y₂ Φ₂ Ψ₂ 𝒜₂ ℬ₂ g}
  `{@TensorProductUnifBorn X₁ X₂ Φ₁ Φ₂ 𝒜₁ 𝒜₂ Φ 𝒜} `{@TensorProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornMorphism ⟨f, g⟩.
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism ⟨_, _⟩) => simple notypeclasses refine tensor_map_unif_born_mor : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_unif_born_mor : typeclass_instances.

Lemma tensor_map_unif_born_reflecting@{u}
  `{@UnifBornReflecting@{u} X₁ Y₁ Φ₁ Ψ₁ 𝒜₁ ℬ₁ f} `{@UnifBornReflecting@{u} X₂ Y₂ Φ₂ Ψ₂ 𝒜₂ ℬ₂ g}
  `{@TensorProductUnifBorn X₁ X₂ Φ₁ Φ₂ 𝒜₁ 𝒜₂ Φ 𝒜} `{@TensorProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornReflecting ⟨f, g⟩.
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornReflecting ⟨_, _⟩) => simple notypeclasses refine tensor_map_unif_born_reflecting : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_unif_born_reflecting : typeclass_instances.

Lemma tensor_map_unif_born_initial@{u}
  `{@UnifBornInitial@{u} X₁ Y₁ Φ₁ Ψ₁ 𝒜₁ ℬ₁ f} `{@UnifBornInitial@{u} X₂ Y₂ Φ₂ Ψ₂ 𝒜₂ ℬ₂ g}
  `{@TensorProductUnifBorn X₁ X₂ Φ₁ Φ₂ 𝒜₁ 𝒜₂ Φ 𝒜} `{@TensorProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornInitial ⟨f, g⟩.
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornInitial ⟨_, _⟩) => simple notypeclasses refine tensor_map_unif_born_initial : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_unif_born_initial : typeclass_instances.

Lemma tensor_map_unif_born_embedding@{u}
  `{@UnifBornEmbedding@{u} X₁ Y₁ Φ₁ Ψ₁ 𝒜₁ ℬ₁ f} `{@UnifBornEmbedding@{u} X₂ Y₂ Φ₂ Ψ₂ 𝒜₂ ℬ₂ g}
  `{@TensorProductUnifBorn X₁ X₂ Φ₁ Φ₂ 𝒜₁ 𝒜₂ Φ 𝒜} `{@TensorProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornEmbedding ⟨f, g⟩.
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornEmbedding ⟨_, _⟩) => simple notypeclasses refine tensor_map_unif_born_embedding : typeclass_instances.
#[global] Hint Extern 2 (UnifBornEmbedding (func_op tensor_map_fun _)) => simple notypeclasses refine tensor_map_unif_born_embedding : typeclass_instances.

(** Cartesian product *)

Lemma to_prod_unif_born_mor@{u}
  `{Hf:@UnifBornMorphism@{u} X Y₁ Φ Ψ₁ 𝒜 ℬ₁ f} `{Hg:@UnifBornMorphism@{u} X Y₂ Φ Ψ₂ 𝒜 ℬ₂ g}
  `{@CartesianProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornMorphism (to_prod (f, g)).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (func_op to_prod (_, _))) => simple notypeclasses refine to_prod_unif_born_mor : typeclass_instances.

Lemma prod_map_unif_born_mor@{u}
  `{@UnifBornMorphism@{u} X₁ Y₁ Φ₁ Ψ₁ 𝒜₁ ℬ₁ f} `{@UnifBornMorphism@{u} X₂ Y₂ Φ₂ Ψ₂ 𝒜₂ ℬ₂ g}
  `{@CartesianProductUnifBorn X₁ X₂ Φ₁ Φ₂ 𝒜₁ 𝒜₂ Φ 𝒜} `{@CartesianProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornMorphism (prod_map (f, g)).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_unif_born_mor : typeclass_instances.

Lemma prod_map_unif_born_reflecting@{u}
  `{@UnifBornReflecting@{u} X₁ Y₁ Φ₁ Ψ₁ 𝒜₁ ℬ₁ f} `{@UnifBornReflecting@{u} X₂ Y₂ Φ₂ Ψ₂ 𝒜₂ ℬ₂ g}
  `{@CartesianProductUnifBorn X₁ X₂ Φ₁ Φ₂ 𝒜₁ 𝒜₂ Φ 𝒜} `{@CartesianProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornReflecting (prod_map (f, g)).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornReflecting (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_unif_born_reflecting : typeclass_instances.

Lemma prod_map_unif_born_initial@{u}
  `{@UnifBornInitial@{u} X₁ Y₁ Φ₁ Ψ₁ 𝒜₁ ℬ₁ f} `{@UnifBornInitial@{u} X₂ Y₂ Φ₂ Ψ₂ 𝒜₂ ℬ₂ g}
  `{@CartesianProductUnifBorn X₁ X₂ Φ₁ Φ₂ 𝒜₁ 𝒜₂ Φ 𝒜} `{@CartesianProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornInitial (prod_map (f, g)).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornInitial (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_unif_born_initial : typeclass_instances.

Lemma prod_map_unif_born_embedding@{u}
  `{@UnifBornEmbedding@{u} X₁ Y₁ Φ₁ Ψ₁ 𝒜₁ ℬ₁ f} `{@UnifBornEmbedding@{u} X₂ Y₂ Φ₂ Ψ₂ 𝒜₂ ℬ₂ g}
  `{@CartesianProductUnifBorn X₁ X₂ Φ₁ Φ₂ 𝒜₁ 𝒜₂ Φ 𝒜} `{@CartesianProductUnifBorn Y₁ Y₂ Ψ₁ Ψ₂ ℬ₁ ℬ₂ Ψ ℬ}
  : UnifBornEmbedding (prod_map (f, g)).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornEmbedding (func_op prod_map (_, _))) => simple notypeclasses refine prod_map_unif_born_embedding : typeclass_instances.

Lemma prod_proj1_unif_born_mor@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ}
  `{@CartesianProductUnifBorn X Y Φ Ψ 𝒜 ℬ Ξ 𝒞}
  : UnifBornMorphism (prod_proj1 X Y).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_unif_born_mor : typeclass_instances.

Lemma prod_proj2_unif_born_mor@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ}
  `{@CartesianProductUnifBorn X Y Φ Ψ 𝒜 ℬ Ξ 𝒞}
  : UnifBornMorphism (prod_proj2 X Y).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_unif_born_mor : typeclass_instances.

(** Unitors, braid, associators *)

Lemma tensor_unit_l_unif_born_emb@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} 𝟏 Ψ ℬ}
  `{@TensorProductUnifBorn 𝟏 X Ψ Φ ℬ 𝒜 Ξ 𝒞}
  : UnifBornEmbedding (tensor_unit_l X).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornEmbedding (tensor_unit_l _)) => simple notypeclasses refine tensor_unit_l_unif_born_emb : typeclass_instances.

Lemma tensor_unit_r_unif_born_emb@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} 𝟏 Ψ ℬ}
  `{@TensorProductUnifBorn X 𝟏 Φ Ψ 𝒜 ℬ Ξ 𝒞}
  : UnifBornEmbedding (tensor_unit_r X).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornEmbedding (tensor_unit_r _)) => simple notypeclasses refine tensor_unit_r_unif_born_emb : typeclass_instances.

Lemma tensor_swap_unif_born_emb@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ}
  `{@TensorProductUnifBorn X Y Φ Ψ 𝒜 ℬ Ξ_XY 𝒞_XY}
  `{@TensorProductUnifBorn Y X Ψ Φ ℬ 𝒜 Ξ_YX 𝒞_YX}
  : UnifBornEmbedding (tensor_swap X Y).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornEmbedding (tensor_swap _ _)) => simple notypeclasses refine tensor_swap_unif_born_emb : typeclass_instances.

Section associators.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ, @UnifBornSpace@{u} Z Ξ 𝒵}.
  Context `{@TensorProductUnifBorn@{u} X Y Φ Ψ 𝒜 ℬ Θ_XY 𝒟_XY}.
  Context `{@TensorProductUnifBorn@{u} Y Z Ψ Ξ ℬ 𝒵 Θ_YZ 𝒟_YZ}.
  Context `{@TensorProductUnifBorn@{u} X (Y ⊗ Z) Φ Θ_YZ 𝒜 𝒟_YZ Θ_X_YZ 𝒟_X_YZ}.
  Context `{@TensorProductUnifBorn@{u} (X ⊗ Y) Z Θ_XY Ξ 𝒟_XY 𝒵 Θ_XY_Z 𝒟_XY_Z}.

  Lemma tensor_assoc_l_unif_born_emb : UnifBornEmbedding (tensor_assoc_l X Y Z).
  Proof. now split. Qed.

  Lemma tensor_assoc_r_unif_born_emb : UnifBornEmbedding (tensor_assoc_r X Y Z).
  Proof. now split. Qed.
End associators.
#[global] Hint Extern 2 (UnifBornEmbedding (tensor_assoc_l _ _ _)) => simple notypeclasses refine tensor_assoc_l_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (UnifBornEmbedding (tensor_assoc_r _ _ _)) => simple notypeclasses refine tensor_assoc_r_unif_born_emb : typeclass_instances.

(** Derived structure maps *)

Lemma tensor_proj1_unif_born_mor@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ}
  `{@TensorProductUnifBorn X Y Φ Ψ 𝒜 ℬ Ξ 𝒞}
  : UnifBornMorphism (tensor_proj1 X Y).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_unif_born_mor : typeclass_instances.

Lemma tensor_proj2_unif_born_mor@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ}
  `{@TensorProductUnifBorn X Y Φ Ψ 𝒜 ℬ Ξ 𝒞}
  : UnifBornMorphism (tensor_proj2 X Y).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_unif_born_mor : typeclass_instances.

Lemma tensor_to_prod_unif_born_mor@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ}
  `{@TensorProductUnifBorn X Y Φ Ψ 𝒜 ℬ Ξ 𝒞}
  `{@CartesianProductUnifBorn X Y Φ Ψ 𝒜 ℬ Ξ' 𝒞'}
  : UnifBornMorphism (tensor_to_prod X Y).
Proof. now split. Qed.
#[global] Hint Extern 2 (UnifBornMorphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_unif_born_mor : typeclass_instances.


