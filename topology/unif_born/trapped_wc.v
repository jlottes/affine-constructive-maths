(** The intrinsic (WCUnif-category) surface of the trapped completion: the
    kit of [trapped_cauchy.v] translated through the localization dictionary
    once and for all.  [to_trapped] is the unit [X ⇾ 𝒯 X];
    [wc_trapped_map] and [wc_trapped_reflect] are the functor action and the
    reflection, with hypotheses and conclusions in the intrinsic
    Locally-classes — consumers need not mention ℒ.  The band-level
    machinery stays in [trapped_cauchy.v].  The file ends with the canonical
    [LocalCompletion (to_trapped X)] instance, doubling as the test that the
    port machinery functions as intended. *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born.
Require Import theory.set orders.orders orders.maps orders.lattices orders.subset orders.closure orders.filters.
Require Import theory.subgroups.
Require Import topology.topology topology.uniform.base uniform.basis uniform.subspace.
Require Import uniform.cauchy_completion uniform.completion.
Require Import bornology.base.
Require Import unif_born.base unif_born.local_maps unif_born.localization unif_born.trapped_cauchy.
Require Import easy rewrite replc simplify strip_coercions.

Import image_notation.
Import tensor_map_notation.

Local Abbreviation id := (id_fun _).
Local Abbreviation ℒ := localization.
Local Abbreviation Λ := localized_uniformity.
Local Abbreviation ε := from_localization.
Local Abbreviation η := to_localization.
Local Abbreviation κ := to_cauchy.
Local Abbreviation 𝒞 := cauchy_filter_set.
Local Abbreviation 𝒞₁ := cauchy_map.

Local Abbreviation 𝒯 := trapped_cauchy_filter_set.
Local Abbreviation τ := to_trapped.
Local Abbreviation β := from_trapped.
Local Abbreviation 𝒯₁ := trapped_map.

(** Local classes of [τ]: the global battery is in [trapped_cauchy], which does not see the
    global-to-local coercions of [local_maps]. *)
#[global] Hint Extern 2 (WCUnifInitial              (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (WCUnifMorphism             (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (τ _)) => simple notypeclasses refine to_trapped_initial : typeclass_instances.

(** Local classes of [𝒯₁] and [trapped_reflect], likewise. *)
#[global] Hint Extern 2 (WCUnifMorphism             (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (trapped_map ?f)) => simple notypeclasses refine (trapped_map_unif_born (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifEmbedding            (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifInitial              (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding   (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (trapped_map ?f)) => simple notypeclasses refine (trapped_map_emb (f:=f)) : typeclass_instances.

#[global] Hint Extern 2 (WCUnifMorphism             (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_bornological (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_bornological (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_bornological (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifEmbedding            (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_emb (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding   (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_emb (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifInitial              (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (trapped_reflect ?f)) => simple notypeclasses refine (trapped_reflect_initial (ι:=f)) : typeclass_instances.

Local Open Scope topology_scope.
Local Open Scope sg_op_scope.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Abbreviation π₁ := (tensor_proj1 _ _).

#[local] Hint Extern 10 => match goal with
|  |- context [ η ?X ∘ ε ?X ] => change (η X ∘ ε X) with (id_fun X)
|  |- context [ ?f ∘ η ?X ∘ ε ?X ] => change (f ∘ η X ∘ ε X) with f
end : typeclass_instances.


(** ** The inverse of [𝒯₁ (ε X)]: a trapped Cauchy filter is Cauchy for the localized uniformity. *)

Section localize_trapped.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜}.
  
  Local Open Scope subset_scope.

  Lemma trapped_localized_cauchy (F:𝒯 X) : CauchyFilter (X:=ℒ X) (trapped_filter F : 𝒫² X).
  Proof. pose proof trapped_prop F as [K HK]. exact (cauchy_bounded_locally_cauchy (trapped_filter F) K). Qed.

  Definition trapped_localize_pt (F:𝒯 X) : 𝒯 (ℒ X)
    := {| trapped_filter := Build_cauchy_filter (ℒ X) _ (trapped_filter F : 𝒫² X) (trapped_localized_cauchy F)
        ; trapped_prop := trapped_prop F |}.

  Lemma trapped_localize_pt_is_fun : IsFun trapped_localize_pt.
  Proof. intros F G.
    change ((∏ U:Φ, ∐ (A:trapped_filter F) (B:trapped_filter G), A ⊗ B ⊆ U)
        ⊸ (∏ V:Λ X, ∐ (A:trapped_filter F) (B:trapped_filter G), A ⊗ B ⊆ V)).
    rew <-all_adj; intros V. pose proof trapped_prop F as [K HK].
    pose proof local_entourage_tensor V K as [U HU]. rew (all_lb _ U).
    rew <-aex_adj; intros A. rew <-aex_adj; intros B.
    rew <-(aex_ub _ (to_subset (powerset_pt K) ⊓ A)), <-(aex_ub _ B).
    exact (HU A B).
  Qed.

  Definition trapped_localize : 𝒯 X ⇾ 𝒯 (ℒ X) := @func_make _ _ _ trapped_localize_pt_is_fun.
End localize_trapped.
Arguments trapped_localize X {_ _ _}.

Local Open Scope fun_inv_scope.

#[global] Hint Extern 2 (Inverse (trapped_map (@from_localization ?X ?Φ ?𝒜))) => exact (@trapped_localize X Φ 𝒜 _) : typeclass_instances.
#[global] Hint Extern 2 (Inverse (@trapped_localize ?X ?Φ ?𝒜 _)) => exact (𝒯₁ (@from_localization X Φ 𝒜)) : typeclass_instances.

Lemma trapped_localize_bijective `{@UnifBornSpace X Φ 𝒜} : Bijective (trapped_localize X).
Proof. now apply alt_Build_Bijective. Qed.
#[global] Hint Extern 2 (Bijective  (trapped_localize _)) => simple notypeclasses refine trapped_localize_bijective : typeclass_instances.
#[global] Hint Extern 2 (Injective  (trapped_localize _)) => simple notypeclasses refine trapped_localize_bijective : typeclass_instances.
#[global] Hint Extern 2 (Surjective (trapped_localize _)) => simple notypeclasses refine trapped_localize_bijective : typeclass_instances.

Lemma trapped_localize_bijective_back `{@UnifBornSpace X Φ 𝒜} : Bijective (𝒯₁ (ε X)).
Proof. now change (Bijective (trapped_localize X)⁻¹). Qed.
#[global] Hint Extern 2 (Bijective  (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_bijective_back : typeclass_instances.
#[global] Hint Extern 2 (Injective  (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_bijective_back : typeclass_instances.
#[global] Hint Extern 2 (Surjective (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_bijective_back : typeclass_instances.

Lemma trapped_localize_back_emb `{@WCUnifSpace X Φ 𝒜} : WCUnifEmbedding (𝒯₁ (ε X)).
Proof.
  enough (LocallyUnifBornInitial (𝒯₁ (ε X))) by (repeat (split; try exact _)).
  refine (dense_locally_initial (τ (ℒ X)) (𝒯₁ (ε X))); try exact _.
  now rew trapped_map_unit.
Qed.
#[global] Hint Extern 2 (WCUnifEmbedding  (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifInitial    (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifMorphism   (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding   (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding      (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting     (trapped_map (from_localization _))) => simple notypeclasses refine trapped_localize_back_emb : typeclass_instances.

Lemma trapped_localize_emb `{@WCUnifSpace X Φ 𝒜} : WCUnifEmbedding (trapped_localize X).
Proof. now change (WCUnifEmbedding (𝒯₁ (ε X))⁻¹). Qed.
#[global] Hint Extern 2 (WCUnifEmbedding            (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifInitial              (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifMorphism             (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding   (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial           (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting        (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding      (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting     (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (trapped_localize _)) => simple notypeclasses refine trapped_localize_emb : typeclass_instances.


    
(** ** The functor action. *)

Section map.
  Universes u.
  Context `{@WCUnifMorphism@{u} X Y Φ Ψ 𝒜 ℬ f}.

  Local Existing Instance wcunif_localize_domain.
  #[local] Hint Extern 2 (UnifBornMorphism (_ ∘ ε _)) => simple notypeclasses refine (wcunif_localize_domain _) : typeclass_instances.

  Definition wc_trapped_map : 𝒯 X ⇾ 𝒯 Y := 𝒯₁ (f ∘ ε X) ∘ (𝒯₁ (ε X))⁻¹ .
  
  Lemma wc_trapped_map_mor : WCUnifMorphism wc_trapped_map.
  Proof. now unfold wc_trapped_map. Qed.

  Lemma wc_trapped_map_unit : wc_trapped_map ∘ τ X = τ Y ∘ f.
  Proof. change (𝒯₁ (f ∘ ε X) ∘ τ (ℒ X) ∘ η X = τ Y ∘ f). 
    now rew trapped_map_unit.
  Qed.

  Lemma wc_trapped_map_dense `{!Dense f} : Dense wc_trapped_map.
  Proof. apply (Dense_factor_right (τ X)). now rew wc_trapped_map_unit. Qed. 
End map.
Arguments wc_trapped_map {_ _ _ _ _ _} f {_}.
Arguments wc_trapped_map_unit {_ _ _ _ _ _} f {_}.
Local Abbreviation 𝒯ₗ := wc_trapped_map.
#[global] Hint Extern 2 (WCUnifMorphism             (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (𝒯ₗ _))) => simple notypeclasses refine wc_trapped_map_dense : typeclass_instances.

Lemma wc_trapped_map_initial@{u} `{@WCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ f} : WCUnifInitial (𝒯ₗ f).
Proof. enough (LocallyUnifBornInitial (𝒯ₗ f)) by now split.
    refine (dense_locally_initial (τ X) (𝒯ₗ f)); try exact _.
    now rew (wc_trapped_map_unit f).
Qed.
#[global] Hint Extern 2 (WCUnifInitial             (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial    (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial          (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting       (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial       (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting    (𝒯ₗ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.

Lemma wc_trapped_map_gbl@{u} `{@GlobalWCUnifMorphism@{u} X Y Φ Ψ 𝒜 ℬ f} : 𝒯ₗ f = 𝒯₁ f.
Proof. rew <-(cont_dense_epi (𝒯ₗ f) (𝒯₁ f) (τ X)).
  now rew (wc_trapped_map_unit f), trapped_map_unit.
Qed. 


(** ** The reflection. *)

Section reflect.
  Universes u.
  Context `{@WCUnifReflecting@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}.
  
  Local Existing Instance  wcunif_localize_codomain_refl.
  #[local] Hint Extern 2 (UnifBornReflecting (η _ ∘ _)) => simple notypeclasses refine (wcunif_localize_codomain_refl _) : typeclass_instances.

  Definition wc_trapped_reflect : Z ⇾ 𝒯 X := trapped_reflect (Y:=ℒ Z) (η Z ∘ f) ∘ η Z.

  Lemma wc_trapped_reflect_spec : wc_trapped_reflect ∘ f = τ X.
  Proof. exact (trapped_reflect_spec (η Z ∘ f)). Qed.

  Lemma wc_trapped_reflect_mor : WCUnifMorphism wc_trapped_reflect.
  Proof. now unfold wc_trapped_reflect. Qed.

  Lemma wc_trapped_reflect_dense : Dense wc_trapped_reflect.
  Proof. now unfold wc_trapped_reflect. Qed.
End reflect.
Arguments wc_trapped_reflect {_ _ _ _ _ _} f {_ _}.
Arguments wc_trapped_reflect_spec {_ _ _ _ _ _} f {_ _}.
#[global] Hint Extern 2 (WCUnifMorphism             (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (wc_trapped_reflect ?f))) => simple notypeclasses refine wc_trapped_reflect_dense : typeclass_instances.

Lemma wc_trapped_reflect_initial@{u} `{@WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}
  : WCUnifInitial (wc_trapped_reflect f).
Proof. enough (LocallyUnifBornInitial (wc_trapped_reflect f)) by now split.
  refine (dense_locally_initial f (wc_trapped_reflect f)); try exact _.
  now rew (wc_trapped_reflect_spec f).
Qed.
#[global] Hint Extern 2 (WCUnifInitial             (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial    (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial          (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting       (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial       (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting    (wc_trapped_reflect _)) => simple notypeclasses refine wc_trapped_reflect_initial : typeclass_instances.

(** ** The canonical LocalCompletion instance — the API test of the port. *)

Definition trapped_local_completion_reflect@{u} `{@WCUnifSpace@{u} X Φ 𝒜} : LocalCompletionReflect@{u} (τ X)
  := λ Z Ξ 𝒵 f H₁ H₂, wc_trapped_reflect f.

#[global] Hint Extern 2 (LocalCompletionReflect (to_trapped _)) => notypeclasses refine trapped_local_completion_reflect : typeclass_instances.
#[global] Hint Extern 2 (LocalCompletionReflect (X:=?X) (Y:=trapped_cauchy_filter_set ?X) _) => notypeclasses refine trapped_local_completion_reflect : typeclass_instances.

Lemma trapped_local_completion@{u} `{@WCUnifSpace@{u} X Φ 𝒜} : LocalCompletion@{u} (τ X).
Proof. split; try exact _; intros Z Ξ 𝒵 f H₁ H₂.
+ exact wc_trapped_reflect_mor.
+ exact (wc_trapped_reflect_spec f).
Qed.
#[global] Hint Extern 2 (LocalCompletion (τ _)) => simple notypeclasses refine trapped_local_completion : typeclass_instances.


