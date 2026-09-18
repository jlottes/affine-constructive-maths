Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology uniform.base.
Require Import easy rewrite replc simplify tactics.misc.

Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Import image_notation.
Import tensor_map_notation.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").

Definition presented_uniformity@{u} {X:set@{u}} {Λ:Type@{u}} (β:Λ → 𝒫 (X ⊗ X)) : Uniformity@{u} X
  := presented_filter β.

Lemma presented_uniformity_prop@{u} {X:set@{u}} {Λ:Type@{u}} (β:Λ → 𝒫 (X ⊗ X))
  : UniformityPresentation X (Φ:=presented_uniformity β) β.
Proof. now unfold UniformityPresentation, presented_uniformity. Qed.
#[global] Hint Extern 2 (UniformityPresentation _ (Φ:=presented_uniformity _) _)
  => simple notypeclasses refine presented_uniformity_prop : typeclass_instances.

Definition uniformity_presentation_basis_correct `{@UniformityPresentation X Φ Λ β}
  : @UniformityBasis X Φ _ (filter_presentation_basis Φ β)
:= filter_presentation_basis_correct.
#[global] Hint Extern 2 (UniformityBasis (filter_presentation_basis _ _)) => simple notypeclasses refine uniformity_presentation_basis_correct : typeclass_instances.

Definition uniformity_basis@{u} `{H:@UniformityBasis@{u} X Φ Λ β}
  := @filter_basis _ _ _ _ H.

Section presented_pre_uniform_space.
  Universes u.
  Context `{@UniformityPresentation@{u} X Φ Λ β}.

  Context
    (refl: ∀ i, id_rel _ ⊆ β i)
    (sym:  ∀ i, ∐ j, (β j)⁻¹ ⊆ β i)
    (split: ∀ i, ∐ j, β j ∙ β j ⊆ β i).

  Local Coercion uniformity_presentation_basis_correct : UniformityPresentation >-> UniformityBasis.

  Lemma presented_pre_uniform_space: PreUniformSpace X.
  Proof. split; try exact _.
  + intros U. rew (filter_presentation Φ β U). rew <-aex_adj; intros i.
    now rew (refl i).
  + intros U. rew (filter_presentation Φ β _). rew <-aex_adj; intros i.
    pose proof (sym i) as [j Pj]. rew <-(aex_ub _ j).
    rew (order_preserving inv _ U). now rew <-Pj.
  + intros U. pose proof uniformity_basis U as [i Pi].
    rew <-(Pi : β i ⊆ U); clear Pi.
    pose proof split i as [j Hj].
    now exists (filter_presentation_basis Φ β j).
  Qed.
End presented_pre_uniform_space.

Section presented_uniform_space.
  Universes u.
  Context {Λ X:set@{u}} {Λle:Le Λ} {β:Λ ⇾ 𝒫 (X ⊗ X)} {Φ:Uniformity X}.
  Context `{!UniformityPresentation X β, !OrderPreserving β, !DownDirected Λ}.

  Local Instance presented_uniformity_filter: Filter Φ.
  Proof. exact presented_filter_filter. Qed.

  Context
    (refl: ∀ i, id_rel _ ⊆ β i)
    (sym:  ∀ i, ∐ j, (β j)⁻¹ ⊆ β i)
    (split: ∀ i, ∐ j, β j ∙ β j ⊆ β i).

  Lemma presented_uniform_space: UniformSpace X.
  Proof. split; try exact _. now apply presented_pre_uniform_space. Qed.
End presented_uniform_space.

Lemma uniform_basis_self `{Φ:Uniformity X} : @UniformityBasis X Φ Φ id.
Proof. exact filter_basis_self. Qed.
#[global] Hint Extern 100 (UniformityBasis _) => notypeclasses refine uniform_basis_self : typeclass_instances.

Lemma uniform_separated_by_basis `{@UniformityBasis X Φ Λ β, !UniformSpace X}
  (sep: ∀ x y, (∏ i, (x, y) ∊ β i) ⊸ x = y)
  : SeparatedUniformSpace X.
Proof. split; try exact _. intros x y. rew <-(sep x y).
  rew <-all_adj; intros i. now rew (all_lb _ (β i)).
Qed. 

Section uniform_basis_converse.
  Universes u.
  Context `{@UniformityBasis X Φ Λ β, !UniformSpace X}.

  Lemma uniform_basis_inhabited : Inhabited Λ.
  Proof. pose proof (_ : Inhabited Φ) as [U _].
    pose proof filter_basis β U as [i _]. now exists i.
  Qed.

  Lemma uniform_basis_down_directed i₁ i₂ :  ∐ i₃, β i₃ ⊆ β i₁ ⊠ β i₃ ⊆ β i₂.
  Proof. pose proof down_directed (β i₁) (β i₂) as [U [H1 H2]].
    pose proof filter_basis β U as [i₃ P]. exists i₃. now rew P.
  Qed.

  Lemma uniform_basis_split i :  ∐ j, ∏ x y z, near (β j) x y ⊠ near (β j) y z ⊸ near (β i) x z.
  Proof. pose proof near_split (β i) as [V P].
    pose proof filter_basis β V as [j Pj]. exists j. now rew Pj.
  Qed.

  Lemma uniform_basis_sym i :  ∐ j, ∏ x y, near (β j) y x ⊸ near (β i) x y.
  Proof. pose proof near_sym (β i) as [V P].
    pose proof filter_basis β V as [j Pj]. exists j. now rew Pj.
  Qed.
End uniform_basis_converse.

Lemma uniform_basis_separated `{@UniformityBasis X Φ Λ β, !SeparatedUniformSpace X}
  x y : x = y ⧟ ∏ i, near (β i) x y.
Proof. split.
+ rew <-all_adj; intros i. apply near_refl_alt.
+ rew (uniform_separated_iff _ _), <-all_adj; intros U.
  pose proof filter_basis β U as [i Pi]. now rew (all_lb _ i), Pi.
Qed.

Lemma ufm_conty_by_basis@{u} `{@UniformityBasis@{u} X Φ Λ₁ α, @UniformityBasis@{u} Y Ψ Λ₂ β} {f:X → Y}
  : (∀ j, ∐ i, ∏ x y, near (α i) x y ⊸ near (β j) (f x) (f y)) → UniformContinuity f.
Proof. intros P V.
  pose proof filter_basis β V as [j Pj]. pose proof (P j) as [i Pi]. exists (α i).
  intros x y. rew (Pi _ _). exact (Pj _).
Qed.

Lemma ufm_refln_by_basis@{u} `{@UniformityBasis@{u} X Φ Λ₁ α, @UniformityBasis@{u} Y Ψ Λ₂ β} {f:X → Y}
  : (∀ i, ∐ j, ∏ x y, near (β j) (f x) (f y) ⊸ near (α i) x y) → UniformReflection f.
Proof. intros P U.
  pose proof filter_basis α U as [i Pi]. pose proof (P i) as [j Pj]. exists (β j).
  intros x y. rew (Pj _ _). exact (Pi _).
Qed.


Lemma ufm_cont_by_basis@{u} `{@UniformityBasis@{u} X Φ Λ₁ α, @UniformityBasis@{u} Y Ψ Λ₂ β} {f:X ⇾ Y}
  `{!UniformSpace X, !UniformSpace Y}
  : (∀ j, ∐ i, ∏ x y, near (α i) x y ⊸ near (β j) (f x) (f y)) → UniformlyContinuous f.
Proof. intros P. split; try exact _. now apply ufm_conty_by_basis. Qed.

Lemma ufm_refl_by_basis@{u} `{@UniformityBasis@{u} X Φ Λ₁ α, @UniformityBasis@{u} Y Ψ Λ₂ β} {f:X ⇾ Y}
  `{!UniformSpace X, !UniformSpace Y}
  : (∀ i, ∐ j, ∏ x y, near (β j) (f x) (f y) ⊸ near (α i) x y) → UniformlyReflecting f.
Proof. intros P. split; try exact _. now apply ufm_refln_by_basis. Qed.

Lemma ufm_cont_by_basis_alt@{u} `{@UniformityBasis@{u} X Φ Λ₁ α, @UniformityBasis@{u} Y Ψ Λ₂ β} {f:X ⇾ Y}
  `{!UniformSpace X, !UniformSpace Y}
  : (∀ j, ∐ i, α i ⊆ f♯ (β j)) → UniformlyContinuous f.
Proof. intros P. apply ufm_cont_by_basis. intros j. specialize (P j) as [i Pi].
  exists i. intros x y. exact (Pi (x,y)).
Qed.

Lemma ufm_refl_by_basis_alt@{u} `{@UniformityBasis@{u} X Φ Λ₁ α, @UniformityBasis@{u} Y Ψ Λ₂ β} {f:X ⇾ Y}
  `{!UniformSpace X, !UniformSpace Y}
  : (∀ i, ∐ j, f♯ (β j) ⊆ α i) → UniformlyReflecting f.
Proof. intros P. apply ufm_refl_by_basis. intros i. specialize (P i) as [j Pj].
  exists j. intros x y. exact (Pj (x,y)).
Qed.


(** Topological notions *)

Section via_basis.
  Context `{@UniformityBasis X Φ Λ β}.

  Lemma uniform_basis_interior
    : interior = set:(λ A:𝒫 X, { x:X | ∐ i, near (β i) x ⊆ A}).
  Proof. intros A x.
    change ( (∐ (U:Φ), ∏ y, near U x y ⊸ y ∊ A) ⧟ (∐ i, ∏ y, (x, y) ∊ β i ⊸ y ∊ A) ); split.
  + rew <-aex_adj; intros U. pose proof filter_basis β U as [i Pi].
    rew <-(aex_ub _ i). now rew (Pi : powerset_pt (β i) ⊆ powerset_pt U).
  + rew <-aex_adj; intros i. now rew <-(aex_ub _ (β i)).
  Qed.

  Definition uniform_basis_interior_applied {A}
    : interior A = { x:X | ∐ i, near (β i) x ⊆ A}
  := uniform_basis_interior A.

  Definition uniform_basis_interior_applied2 {A} {x}
    : x ∊ interior A ⧟ ∐ i, near (β i) x ⊆ A
  := uniform_basis_interior A x.

  Lemma uniform_basis_closure
    : closure = set:(λ A:𝒫 X, { x:X | ∏ i, ∐ y, near (β i) x y ⊠ y ∊ A}).
  Proof. intros A x.
    change ( (∏ (U:Φ), ∐ y, near U x y ⊠ y ∊ A) ⧟ (∏ i, ∐ y, (x, y) ∊ β i ⊠ y ∊ A) ); split.
  + rew <-all_adj; intros i. now rew (all_lb _ (β i)).
  + rew <-all_adj; intros U. pose proof filter_basis β U as [i Pi].
    rew (all_lb _ i). now rew (Pi : powerset_pt (β i) ⊆ powerset_pt U).
  Qed.

  Definition uniform_basis_closure_applied {A}
    : closure A = { x:X | ∏ i, ∐ y, near (β i) x y ⊠ y ∊ A}
  := uniform_basis_closure A.

  Definition uniform_basis_closure_applied2 {A} {x}
    : x ∊ closure A ⧟ ∏ i, ∐ y, near (β i) x y ⊠ y ∊ A
  := uniform_basis_closure A x.

  Lemma uniform_basis_dense
    : dense = { A : 𝒫 X | ∏ (x:X) i, ∐ y, near (β i) x y ⊠ y ∊ A }.
  Proof. intros A.
    change (closure A = ⊤ ⧟ ∏ (x : X) (i : Λ), ∐ y : X,  near (β i) x y ⊠ y ∊ A).
    rew uniform_basis_closure.
    change ( (∏ x, (∏ i, ∐ y, (x, y) ∊ β i ⊠ y ∊ A) ⧟ 𝐓)
            ⧟ ∏ (x : X) (i : Λ), ∐ y : X, (x, y) ∊ β i ⊠ y ∊ A).
    now simplify.
  Qed.

  Definition uniform_basis_dense_applied A
    : dense A ⧟ ∏ (x:X) i, ∐ y, near (β i) x y ⊠ y ∊ A
  := uniform_basis_dense A.
End via_basis.

Lemma uniform_basis_Dense_iff@{u} {X Y:set@{u}} `{@UniformityBasis@{u} Y Ψ Λ β, !UniformSpace Y} {f:X ⇾ Y}
  : Dense f ↔ ∏ (y:Y) i, ∐ x, near (β i) y (f x).
Proof. rew (Dense_alt _), (uniform_basis_dense_applied _). split.
  * intros P y i. pose proof (P y i) as [y' [Py' [x Ex]]]. exists x. now rew Ex.
  * intros P y i. pose proof (P y i) as [x Px]. now exists (f x).
Qed.

Lemma uniform_basis_dense_range@{u} {X Y:set@{u}} `{@UniformityBasis@{u} Y Ψ Λ β, !UniformSpace Y} (f:X ⇾ Y)
  : ∀ `{!Dense f} (y:Y) i, ∐ x, near (β i) y (f x).
Proof. apply uniform_basis_Dense_iff. Qed.


(** Discrete and indiscrete uniformities *)

Definition discrete_uniformity@{u} (X:set@{u}) : Uniformity@{u} X
  := presented_uniformity set:(λ _:unit, id_rel X).
Definition indiscrete_uniformity@{u} (X:set@{u}) : Uniformity@{u} X
  := presented_uniformity set:(λ _:unit, full_subset (X ⊗ X)).

Lemma discrete_uniformity_correct@{u} {X:set@{u}} : DiscreteUniformity (discrete_uniformity X).
Proof. now unfold DiscreteUniformity, discrete_uniformity. Qed.
Lemma indiscrete_uniformity_correct@{u} {X:set@{u}} : IndiscreteUniformity (indiscrete_uniformity X).
Proof. now unfold IndiscreteUniformity, indiscrete_uniformity. Qed.

#[global] Hint Extern 2 (DiscreteUniformity (discrete_uniformity _)) => simple notypeclasses refine discrete_uniformity_correct : typeclass_instances.
#[global] Hint Extern 2 (UniformityPresentation _ (Φ:=discrete_uniformity _) _) => simple notypeclasses refine discrete_uniformity_correct : typeclass_instances.
#[global] Hint Extern 2 (IndiscreteUniformity (indiscrete_uniformity _)) => simple notypeclasses refine indiscrete_uniformity_correct : typeclass_instances.
#[global] Hint Extern 2 (UniformityPresentation _ (Φ:=indiscrete_uniformity _) _) => simple notypeclasses refine indiscrete_uniformity_correct : typeclass_instances.

#[global] Hint Extern 20 (Uniformity 𝟏) => notypeclasses refine (discrete_uniformity _) : typeclass_instances.

Coercion discrete_uniform_space `{@DiscreteUniformity X Φ} : UniformSpace X.
Proof. refine (presented_uniform_space _ _ _); try exact _.
+ now intros [].
+ intros []. exists tt. intros [x y]. exact (symmetry (=) _ _).
+ intros []. exists tt. change (id_rel X ⋄ id_rel X ⊆ id_rel X).
  now rew (left_identity (⋄) _).
Qed.
#[global] Hint Extern 2 (@UniformSpace _ (discrete_uniformity _)) => simple notypeclasses refine discrete_uniform_space : typeclass_instances.
#[global] Hint Extern 2 (@Topology _ (@UniformNeighborhood _ (discrete_uniformity _))) =>
  simple notypeclasses refine discrete_uniform_space : typeclass_instances.

Section discrete_uniformity.
  Universes u.
  Context `{H:@DiscreteUniformity@{u} X Φ}.

  Definition discrete_ufm_basis := filter_presentation_basis_fun _ _ (H:=H).
  Local Abbreviation β := discrete_ufm_basis.
  Local Instance discrete_ufm_basis_correct : UniformityBasis discrete_ufm_basis.
  Proof. now unfold β, UniformityBasis. Qed.

  (** The induced topology of a discrete uniformity is discrete. *)
  Lemma discrete_uniformity_nbrhood : Discrete (@UniformNeighborhood X Φ).
  Proof. intros [x N]. split.
  + exact (top_refl x N).
  + change (x ∊ N ⊸ ∐ U:Φ, ∏ y, near U x y ⊸ y ∊ N).
    rew <-(aex_ub _ (β tt)).
    rew <-all_adj; intros y.
    change (x ∊ N ⊸ x = y ⊸ y ∊ N).
    rew <-(aprod_adj _ _ _), (aprod_com _ _).
    exact (equal_element _ _ _).
  Qed.

  (** Every map out of a discretely-uniform space is uniformly continuous. *)
  Lemma discrete_ufm_cont `{@UniformSpace@{u} Y Ψ} (f:X ⇾ Y) : UniformlyContinuous f.
  Proof. apply uniformly_continuous_alt. intros V.
    rew (filter_presentation Φ _ _). exists tt.
    rew <-(uniform_refl_alt V).
    intros [x y]. exact (is_fun f x y).
  Qed.
End discrete_uniformity.
Coercion discrete_ufm_basis_correct : DiscreteUniformity >-> UniformityBasis.
#[global] Hint Extern 2 (Discrete (UniformNeighborhood _)) => simple notypeclasses refine discrete_uniformity_nbrhood : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (Φ:=discrete_uniformity _) _) => simple notypeclasses refine (discrete_ufm_cont _) : typeclass_instances.

Coercion indiscrete_uniform_space `{@IndiscreteUniformity X Φ} : UniformSpace X.
Proof. refine (presented_uniform_space _ _ _); try exact _; tautological. Qed.
#[global] Hint Extern 2 (@UniformSpace _ (indiscrete_uniformity _)) => simple notypeclasses refine indiscrete_uniform_space : typeclass_instances.
#[global] Hint Extern 2 (@Topology _ (@UniformNeighborhood _ (indiscrete_uniformity _))) =>
  simple notypeclasses refine indiscrete_uniform_space : typeclass_instances.

Section indiscrete_uniformity.
  Universes u.
  Context `{H:@IndiscreteUniformity@{u} X Φ}.

  Definition indiscrete_ufm_basis := filter_presentation_basis_fun _ _ (H:=H).
  Local Abbreviation β := indiscrete_ufm_basis.
  Local Instance indiscrete_ufm_basis_correct : UniformityBasis indiscrete_ufm_basis.
  Proof. now unfold β, UniformityBasis. Qed.

  (** The induced topology of an indiscrete uniformity is indiscrete. *)
  Lemma indiscrete_uniformity_nbrhood : Indiscrete (@UniformNeighborhood X Φ).
  Proof. pose proof _ : UniformSpace X. intros [x N]. split.
  + change ((∐ U:Φ, near U x ⊆ N) ⊸ ∏ y:X, y ∊ N).
    rew <-aex_adj; intros U. pose proof uniformity_basis U as [[] PU]. rew <-PU.
    change ((∏ y, 𝐓 ⊸ y ∊ N) ⊸ ∏ y : X, y ∊ N). now simplify.
  + change ((∏ y:X, y ∊ N) ⊸ ∐ U:Φ, ∏ y, near U x y ⊸ y ∊ N).
    rew <-(aex_ub _ (β tt)).
    change ((∏ y, y ∊ N) ⊸ ∏ y : X, 𝐓 ⊸ y ∊ N). now simplify.
  Qed.

  Lemma indiscrete_entourage_alt (U:𝒫 (X ⊗ X)) : U ∊ Φ ⧟ U = ⊤.
  Proof. rew [ (filter_presentation Φ _ U) | <-(above_top _)]. split.
  + rew <-aex_adj; intros []. now simplify.
  + rew <-(aex_ub _ tt). now simplify.
  Qed.
  
  Lemma indiscrete_entourage (A:Φ) : A = ⊤.
  Proof. change (A = ⊤ :> 𝒫 (X ⊗ X)). now rew <-(indiscrete_entourage_alt _). Qed.

  (** Every map into an indiscretely-uniform space is uniformly continuous. *)
  Lemma indiscrete_ufm_cont `{@UniformSpace@{u} Y Ψ} (f:Y ⇾ X) : UniformlyContinuous f.
  Proof. apply uniformly_continuous_alt. intros U. rew (indiscrete_entourage U).
    change (⟨f,f⟩* ⊤ ∊ Ψ). now rew (preserves_top _).
  Qed.
End indiscrete_uniformity.
#[global] Hint Extern 2 (Indiscrete (UniformNeighborhood _)) => simple notypeclasses refine indiscrete_uniformity_nbrhood : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (Φ:=indiscrete_uniformity _) _) => simple notypeclasses refine (indiscrete_ufm_cont _) : typeclass_instances.

(** Initial object *)

#[global] Hint Extern 20 (Uniformity 𝟎) => notypeclasses refine (discrete_uniformity _) : typeclass_instances.

Lemma from_empty_ufm_cont@{u} `{@UniformSpace@{u} 𝟎 Ψ} `{@UniformSpace@{u} X Φ}
  : UniformlyContinuous (from_Empty X).
Proof. apply uniformly_continuous_alt. intros U. 
  apply (up_closed Ψ ⊤); [ full_tautological | exact _ ].
Qed.
#[global] Hint Extern 2 (UniformlyContinuous (from_Empty _)) => simple notypeclasses refine from_empty_ufm_cont : typeclass_instances.

(** Terminal object: every uniform space structure on 𝟏 is indiscrete. *)

Section unit.
  Universes u.
  Context `{@UniformSpace@{u} 𝟏 Ψ}.

  Local Instance unit_uniform_indiscrete : IndiscreteUniformity Ψ.
  Proof. split; try exact _. intros W. split.
  + rew <-(aex_ub _ tt). now rew (uniform_refl W).
  + rew <-aex_adj; intros []. change (⊤ ≤ W ⊸ W ∊ Ψ).
    rew <-(equal_element _ ⊤ W), (aprod_true_r filter_top).
    rew (above_top _). now apply symmetry.
  Qed.
End unit.
#[global] Hint Extern 2 (@IndiscreteUniformity 𝟏 _) => simple notypeclasses refine unit_uniform_indiscrete : typeclass_instances.
#[global] Hint Extern 2 (@UniformityBasis 𝟏 _ _ _) => simple notypeclasses refine indiscrete_ufm_basis_correct : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (Y:=𝟏) _) => simple notypeclasses refine (indiscrete_ufm_cont _) : typeclass_instances.

(** Constant maps — in particular global points [𝟏 ⇾ X] — are uniformly continuous. *)

Lemma const_ufm_cont@{u} `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ} {y:Y}
  : UniformlyContinuous (const (X:=X) y).
Proof. apply uniformly_continuous_alt. intros V.
  apply (up_closed Φ ⊤); [| exact _].
  rew <-(uniform_refl_alt V).
  intros [x₁ x₂]. change ( 𝐓 ⊸ y = y). now simplify.
Qed.
#[global] Hint Extern 2 (UniformlyContinuous (func_op const _)) => simple notypeclasses refine const_ufm_cont : typeclass_instances.


