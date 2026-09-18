Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.bornology interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.bornology.base.
Require Import reflection_pair.base.
Require Import easy rewrite replc simplify tactics.misc.

Import image_notation.

(** Initial (pullback) bornology: the largest bornology on [X] making [f]
    bounded — the sets whose image is bounded.  The Joy-of-Cats initial lift.
    "Pullback" refers to the base-change direction — the structure is carried
    from codomain to domain along [f] — not to a preimage formula: Born's
    fiber order runs opposite to Top's and Unif's, so the initial lift is
    computed with the image [f⁎] rather than the preimage.
    (The bornological analogue of [uniform/subspace.v]'s [pullback_uniformity].) *)
Definition pullback_bornology@{u} {X:set@{u}} `{ℬ:Bornology@{u} Y} (f:X ⇾ Y) : Bornology X
  := { K : 𝒫 X | f⁎ K ∊ ℬ }.

Section pullback_bornology.
  Universes u.
  Context {X:set@{u}} `{ℬ:Bornology@{u} Y} {f:X ⇾ Y} `{!BornologicalSpace Y}.
  Local Abbreviation 𝒜 := (@pullback_bornology X Y ℬ f).
  #[local] Hint Extern 0 (Bornology X) => exact 𝒜 : typeclass_instances.

  Local Ltac unfold_A := change (?K ∊ 𝒜) with (f⁎ K ∊ ℬ).

  Local Instance pullback_bornological_space : BornologicalSpace X.
  Proof. apply Build_BornologicalSpace.
  + apply Build_Ideal.
    * apply Build_DownSet. intros K K'. unfold_A. rew (order_preserving f⁎ K K'). exact (down_closed ℬ (f⁎ K) (f⁎ K')).
    * apply Build_UpDirectedSubset; try exact _.
      - exists ⊥. unfold_A. rew (preserves_bottom f⁎). exact sub_bot_closed.
      - intros K K'. rew <-(aex_ub _ (K ⊔ K')). unfold_A. rew (preserves_join f⁎ K K').
        rew (aprod_true_r (join_ub_r K K')), (aprod_true_r (join_ub_l K K')).
        exact (sub_join_closed (f⁎ K) (f⁎ K')).
  + intros x. unfold_A. rew (image_singleton_alt f x). exact (bornology_singleton (f x)).
  Qed.

  Local Instance pullback_born_bornological : Bornological f.
  Proof. split; try exact _. intros A. exact (subset_pt_is_el A). Qed.

  Local Instance pullback_born_initial : BornologyInitial f.
  Proof. split; try exact _. split; try exact _. intros B. unfold_A.
    now rew (image_preimage_counit f _).
  Qed.
End pullback_bornology.
#[global] Hint Extern 2 (@BornologicalSpace _ (pullback_bornology _)) => simple notypeclasses refine pullback_bornological_space : typeclass_instances.


#[global] Hint Extern 0 (Cleavage 𝐁𝐨𝐫𝐧) => exact @pullback_bornology : typeclass_instances.

Lemma born_cloven_pair : ClovenPair 𝐁𝐨𝐫𝐧.
Proof. unshelve esplit. intros. exact pullback_born_initial. Qed.
#[global] Hint Extern 0 (ClovenPair 𝐁𝐨𝐫𝐧) => exact born_cloven_pair : typeclass_instances.
#[global] Hint Extern 0 (SaturatedPair 𝐁𝐨𝐫𝐧) => exact born_cloven_pair : typeclass_instances.


Lemma bornology_initial_alt@{u} `{@BornologicalSpace@{u} X 𝒜, @BornologicalSpace@{u} Y ℬ} (f:X ⇾ Y)
  : BornologyInitial f ↔
    (∀ (Z:set@{u}) (𝒞:Bornology Z), BornologicalSpace Z → ∀ (g:Z ⇾ X),
       Bornological (f ∘ g) ↔ Bornological g).
Proof. exact (ini_lift_alt (C:=𝐁𝐨𝐫𝐧) f). Qed.

Lemma bornology_initial_alt2@{u} `{@Bornological@{u} X Y 𝒜 ℬ f}
  : BornologyInitial f ↔
    (∀ (Z:set@{u}) (𝒞:Bornology Z), BornologicalSpace Z → ∀ (g:Z ⇾ X),
       Bornological (f ∘ g) → Bornological g).
Proof. exact (ini_lift_alt2 (C:=𝐁𝐨𝐫𝐧) f). Qed.

(** Subspaces A ∊ 𝒫 X are the instance f = from_subset A
    (mirroring [uniform/subspace.v]). *)

#[global] Hint Extern 2 (Bornology (subset_to_set ?A)) =>
  notypeclasses refine (pullback_bornology (from_subset A)) : typeclass_instances.
#[global] Hint Extern 4 (BornologicalSpace (subset_to_set ?A)) =>
  notypeclasses refine pullback_bornological_space : typeclass_instances.

Lemma from_subset_born_emb `{@BornologicalSpace X 𝒜} {A:𝒫 X} : BornologyEmbedding (from_subset A).
Proof. split; [ exact pullback_born_initial | exact _ ]. Qed.
#[global] Hint Extern 2 (BornologyEmbedding  (from_subset _)) => simple notypeclasses refine from_subset_born_emb : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial    (from_subset _)) => simple notypeclasses refine from_subset_born_emb : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (from_subset _)) => simple notypeclasses refine from_subset_born_emb : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (from_subset _)) => simple notypeclasses refine from_subset_born_emb : typeclass_instances.

(** For bounded K ∊ 𝒜 the subspace bornology is trivial: down-closure makes
    every subset of K bounded in X.  So the bounded subspaces are exactly the
    subspaces whose subspace bornology collapses. *)
Lemma bounded_pullback_bornology_trivial `{@BornologicalSpace X 𝒜} (K:𝒜)
  : TrivialBornology (pullback_bornology (from_subset (powerset_pt K))).
Proof. apply Build_IdealPresentation; [ exact _ | intros A ].
  assert (A ∊ pullback_bornology (from_subset (powerset_pt K))) as p.
  { change ((from_subset (powerset_pt K))⁎ A ∊ 𝒜).
    apply (down_closed 𝒜 ((from_subset (powerset_pt K))⁎ A) K); [| exact _ ].
    rew (below_top A), <-(range_image (from_subset (powerset_pt K))).
    exact (of_course_subset_subset _). }
  assert (∐ i:𝟏, A ⊆ (λₛ _:𝟏, full_subset (subset_to_set (powerset_pt K))) i) as q by (exists tt; exact (below_top _)).
  rew (aiff_is_true p), (aiff_is_true q). refl.
Qed.
#[global] Hint Extern 2 (TrivialBornology (pullback_bornology (from_subset (powerset_pt ?K)))) =>
  simple notypeclasses refine (bounded_pullback_bornology_trivial K) : typeclass_instances.

