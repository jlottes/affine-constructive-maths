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
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
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
Local Abbreviation τ₀ := trapped_unit.
Local Abbreviation β := trapped_embedding.

Local Open Scope topology_scope.
Local Open Scope sg_op_scope.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").

(** ** The unit. *)

Definition to_trapped X `{@UnifBornSpace X Φ 𝒜} : X ⇾ 𝒯 X := τ₀ X ∘ η X.
Arguments to_trapped X {_ _ _}.
Local Abbreviation τ := to_trapped.

#[local] Hint Extern 10 => match goal with
|  |- context [ η ?X ∘ ε ?X ] => change (η X ∘ ε X) with (id_fun X)
|  |- context [ ?f ∘ η ?X ∘ ε ?X ] => change (f ∘ η X ∘ ε X) with f
end : typeclass_instances.

Lemma to_trapped_ubr `{@WCUnifSpace X Φ 𝒜} : UnifBornReflecting (τ X).
Proof. now unfold τ. Qed.
#[global] Hint Extern 2 (UnifBornReflecting         (τ _)) => simple notypeclasses refine to_trapped_ubr : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting        (τ _)) => simple notypeclasses refine to_trapped_ubr : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting        (τ _)) => simple notypeclasses refine to_trapped_ubr : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (τ _)) => simple notypeclasses refine to_trapped_ubr : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (τ _)) => simple notypeclasses refine to_trapped_ubr : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting     (τ _)) => simple notypeclasses refine to_trapped_ubr : typeclass_instances.

Lemma to_trapped_locally_initial `{@WCUnifSpace X Φ 𝒜} : WCUnifInitial (τ X).
Proof. split; [| now split ]. split; try exact _. unfold τ. now apply localized_unif_born_conv. Qed.
#[global] Hint Extern 2 (WCUnifInitial              (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (WCUnifMorphism             (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial           (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (τ _)) => simple notypeclasses refine to_trapped_locally_initial : typeclass_instances.

Lemma to_trapped_dense  `{@WCUnifSpace X Φ 𝒜} : Dense (τ X).
Proof. now unfold τ. Qed.
#[global] Hint Extern 2 (Dense (func_op (to_trapped _))) => simple notypeclasses refine to_trapped_dense : typeclass_instances.

Lemma to_trapped_emb `{@WCUnifSpace X Φ 𝒜, !SeparatedUniformSpace X} : WCUnifEmbedding (τ X).
Proof. split; try exact _. now unfold τ. Qed.
#[global] Hint Extern 2 (WCUnifEmbedding          (τ _)) => simple notypeclasses refine to_trapped_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding (τ _)) => simple notypeclasses refine to_trapped_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding    (τ _)) => simple notypeclasses refine to_trapped_emb : typeclass_instances.
#[global] Hint Extern 2 (Injective (τ _)) => simple notypeclasses refine to_trapped_emb : typeclass_instances.

(** ** τ-equality as a ball law.

    A trapped filter equal to [τ X x] contains every ambient ball at [x],
    and hence has [x] in the closure of each of its members — the trapping
    content of limits, in completeness-free form: completeness only ever
    manufactures the equality [τ X x = G]. *)
Section to_trapped_eq.
  Context `{@UnifBornSpace X Φ 𝒜}.
  Local Open Scope subset_scope.

  Lemma to_trapped_eq_ball (x : X) (G : 𝒯 X) (E : τ X x = G) (U : Φ) : near U x ∊ trapped_filter G.
  Proof.
    pose proof E (ufm_preimage (ε X) U) as [B [A P]]; change (apos (B ⊗ A ⊆ U)) in P.
    pose proof subset_pt_is_el B : x ∊ B as elxB.
    enough (A ⊆ near U x) as SA by (rew <-SA; exact (subset_pt_is_el A)).
    intros a. change (a ∊ A ⊸ (x, a) ∊ U). rew <-P.
    change (a ∊ A ⊸ x ∊ B ⊠ a ∊ A). now simplify.
  Qed.

  Lemma to_trapped_eq_closure (x : X) (G : 𝒯 X) (E : τ X x = G) (A : trapped_filter G)
    : x ∊ closure (powerset_pt A : 𝒫 X).
  Proof. rew uniform_closure_applied2. intros U.
    pose proof to_trapped_eq_ball x G E U as elU.
    pose (M := to_subset (U:=trapped_filter G) (near U x) ⊓ A : trapped_filter G).
    change (∐ y, y ∊ M). pose proof (inhabited M) as [y _]. now exists (subset_pt y).
  Qed.
End to_trapped_eq.

(** ** A "counit" with a twist.  *)

Definition from_trapped X `{@UnifBornSpace X Φ 𝒜} : 𝒯 X ⇾ 𝒞 X := 𝒞₁ (ε X) ∘ β X.
Arguments from_trapped X {_ _ _}.
Local Abbreviation ρ := from_trapped.

Lemma from_trapped_uc `{@UnifBornSpace X Φ 𝒜} : UniformlyContinuous (ρ X).
Proof. now unfold ρ. Qed.
#[global] Hint Extern 2 (UniformlyContinuous        (ρ _)) => simple notypeclasses refine from_trapped_uc : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (ρ _)) => simple notypeclasses refine from_trapped_uc : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (ρ _)) => simple notypeclasses refine from_trapped_uc : typeclass_instances.

Definition from_trapped_spec X `{@UnifBornSpace X Φ 𝒜} : ρ X ∘ τ X = κ X.
Proof. change ((𝒞₁ (ε X) ∘ κ (ℒ X)) ∘ η X = κ X). now rew (cauchy_map_spec _). Qed.

Section from_trapped.
  Context `{@WCUnifSpace X Φ 𝒜}.
  Local Open Scope subset_scope.
  Local Open Scope grp_scope.

  Local Abbreviation C := cauchy_entourage.

  (** The witnessed reflection: [ρ] reflects neighborhoods, the anchor
      supplied per-point by [trapped_prop]. *)
  Lemma from_trapped_cont_emb : ContinuouslyEmbedding (ρ X).
  Proof. refine cont_initial_embedding. do 2 (split; try exact _).
    intros F N. pose proof (trapped_prop F) as [K HK].
    change ( (∐ E : pullback_uniformity (β X), near E F ⊆ N)
             ⊸ ∐ M : 𝒫 (𝒞 X), (∐ W : cauchy_uniformity X, near W (ρ X F) ⊆ M) ⊠ (ρ X)* M ⊆ N ).
    rew <-aex_adj; intros E.
    pose proof (subset_pt_is_el E) as [D HD].
    pose proof cauchy_entourage_basis D as [V PV].
    pose proof trapped_transport (trapped_filter F) K HK V as [U P].
    pose proof uniform_split_sym3 U as [W [EW PW]].
    rew <-(aex_ub _ (near (C X W) (ρ X F))), <-(aex_ub _ (C X W)).
    rew (aprod_true_l (ltac:(refl):near (C X W) (ρ X F) ⊆ near (C X W) (ρ X F))).
    enough ((ρ X)* (near (C X W) (ρ X F)) ⊆ near E F) as Q by now rew Q.
    intros G. change ((ρ X F, ρ X G) ∊ C X W ⊸ (F, G) ∊ subset_pt E).
    rew <-HD, <-PV.
    change ( (∏ S : Φ, ∐ (A : ρ X F) (B : ρ X G), A ⊗ B ⊆ powerset_pt (S⁻¹ ∙ W ∙ S)) ⊸
                ∏ S : Λ X, ∐ (A : trapped_filter F) (B : trapped_filter G), A ⊗ B ⊆ powerset_pt (S⁻¹ ∙ V ∙ S )).
    rew <-all_adj; intros S. rew <-(ufm_compose_ub_l _ _), <-(ufm_compose_ub_r _ _); clear S.
    rew [(all_lb _ W) | <-(P _)].
    now rew EW, PW.
  Qed.
End from_trapped.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (from_trapped _)) => simple notypeclasses refine from_trapped_cont_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (from_trapped _)) => simple notypeclasses refine from_trapped_cont_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (from_trapped _)) => simple notypeclasses refine from_trapped_cont_emb : typeclass_instances.
#[global] Hint Extern 2 (Injective              (from_trapped _)) => simple notypeclasses refine from_trapped_cont_emb : typeclass_instances.

    
(** ** The functor action. *)

Section map.
  Universes u.
  Context `{@WCUnifMorphism@{u} X Y Φ Ψ 𝒜 ℬ f}.
  
  Local Existing Instance localize_functorial_alt.

  Definition wc_trapped_map : 𝒯 X ⇾ 𝒯 Y := trapped_map (η Y ∘ f ∘ ε X).

  Lemma wc_trapped_map_unit : wc_trapped_map ∘ to_trapped X = to_trapped Y ∘ f.
  Proof. exact (trapped_map_unit (η Y ∘ f ∘ ε X)). Qed.

  Lemma wc_trapped_map_mor : WCUnifMorphism wc_trapped_map.
  Proof. split; try exact _. apply localized_unif_born_conv. now unfold wc_trapped_map. Qed.

  Lemma wc_trapped_map_dense `{!Dense f} : Dense wc_trapped_map.
  Proof. now unfold wc_trapped_map. Qed.
End map.
Arguments wc_trapped_map {_ _ _ _ _ _} f {_}.
Arguments wc_trapped_map_unit {_ _ _ _ _ _} f {_}.
Local Abbreviation 𝒯₁ := wc_trapped_map.
#[global] Hint Extern 2 (WCUnifMorphism             (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_mor : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (𝒯₁ _))) => simple notypeclasses refine wc_trapped_map_dense : typeclass_instances.

Lemma wc_trapped_map_initial@{u} `{@WCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ f} : WCUnifInitial (𝒯₁ f).
Proof. enough (LocallyUnifBornInitial (𝒯₁ f)) by now split.
    refine (dense_locally_initial (τ X) (𝒯₁ f)); try exact _.
    now rew (wc_trapped_map_unit f).
Qed.
#[global] Hint Extern 2 (WCUnifInitial             (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial    (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial          (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting       (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial       (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting    (𝒯₁ _)) => simple notypeclasses refine wc_trapped_map_initial : typeclass_instances.


(** ** The reflection. *)

Section reflect.
  Universes u.
  Context `{@WCUnifReflecting@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}.

  Local Existing Instance localize_functorial_refl_alt.

  Local Instance wc_reflect_lift_dense : Dense (η Z ∘ f ∘ ε X).
  Proof. now change (Dense (η Z ∘ (f ∘ ε X))). Qed.

  Definition wc_trapped_reflect := trapped_reflect (η Z ∘ f ∘ ε X) ∘ η Z.

  Lemma wc_trapped_reflect_spec : wc_trapped_reflect ∘ f = τ X.
  Proof. exact (trapped_reflect_spec (η Z ∘ f ∘ ε X)). Qed.

  Lemma wc_trapped_reflect_mor : WCUnifMorphism wc_trapped_reflect.
  Proof. split; try exact _. unfold wc_trapped_reflect. now apply localized_unif_born_conv. Qed.

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

Section reflect.
  Universes u.
  Context `{@WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}.

  Local Existing Instance localize_functorial_initial_alt.

  Lemma wc_trapped_reflect_initial : WCUnifInitial (wc_trapped_reflect f).
  Proof. split; [exact _ |]. split; try exact _.
    unfold wc_trapped_reflect. now apply localized_unif_born_refl_conv.
  Qed. 
End reflect.
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

