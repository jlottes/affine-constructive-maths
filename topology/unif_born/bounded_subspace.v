(** The bounded subspace kit: a bounded set [K : 𝒜] of a UnifBorn space,
    viewed as the subset carrier with the subspace (pullback) structure.
    The subspace bornology of a bounded set is trivial
    ([bounded_pullback_bornology_trivial]) — every subset of a bounded set
    is bounded — so the localization collapses over it ([ℒ K ≅ K]), making
    the inclusion into [ℒ X] uniformly continuous: the localization does
    not change bounded subspaces, and a locally uniformly continuous map is
    literally uniformly continuous on every bounded set. *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology uniform.base uniform.basis uniform.subspace.
Require Import bornology.base bornology.basis bornology.subspace.
Require Import unif_born.base unif_born.subspace unif_born.local_maps unif_born.localization.
Require Import easy rewrite simplify tactics.misc.

Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Local Open Scope subset_scope.

Import thicken_notation.
Import image_notation.
Import tensor_map_notation.

Local Abbreviation ℒ := localization.
Local Abbreviation η := to_localization.
Local Abbreviation ε := from_localization.

Local Abbreviation π₁ := (tensor_proj1 _ _).
Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").

Local Abbreviation ι := from_subset.

(** The subspace inclusion is locally anything a UnifBorn embedding is:
    the [Locally*] battery for [from_subset], routed through the
    [unif_born_*_local] coercions ([from_subset_unif_born_emb]). *)
#[global] Hint Extern 2 (LocallyUnifBorn            (from_subset ?A)) => simple notypeclasses refine (unif_born_mor_local     (H:=from_subset_unif_born_emb (A:=A))) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (from_subset ?A)) => simple notypeclasses refine (unif_born_mor_local     (H:=from_subset_unif_born_emb (A:=A))) : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformContinuity     (from_subset ?A)) => simple notypeclasses refine (unif_born_mor_local     (H:=from_subset_unif_born_emb (A:=A))) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (from_subset ?A)) => simple notypeclasses refine (unif_born_refl_local    (H:=from_subset_unif_born_emb (A:=A))) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (from_subset ?A)) => simple notypeclasses refine (unif_born_refl_local    (H:=from_subset_unif_born_emb (A:=A))) : typeclass_instances.
#[global] Hint Extern 2 (LocalUniformReflection     (from_subset ?A)) => simple notypeclasses refine (unif_born_refl_local    (H:=from_subset_unif_born_emb (A:=A))) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (from_subset ?A)) => simple notypeclasses refine (unif_born_initial_local (H:=from_subset_unif_born_emb (A:=A))) : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding   (from_subset ?A)) => simple notypeclasses refine (unif_born_emb_local     (H:=from_subset_unif_born_emb (A:=A))) : typeclass_instances.

(** The localization collapses over the trivial subspace bornology of a
    bounded set: companions of [localization]'s literal-keyed hints, keyed
    on the subspace bornology of a [powerset_pt]-provenanced subset
    ([bounded_pullback_bornology_trivial] supplies the [TrivialBornology]
    witness). *)
#[global] Hint Extern 2 (UniformlyContinuous (@to_localization ?S ?Φ (pullback_bornology (from_subset (powerset_pt ?K))))) => simple notypeclasses refine (@to_localization_trivial_uc S Φ _ (pullback_bornology (from_subset (powerset_pt K))) _) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (@from_localization ?S ?Φ (pullback_bornology (from_subset (powerset_pt ?K))))) => simple notypeclasses refine (@from_localization_trivial_ur S Φ _ (pullback_bornology (from_subset (powerset_pt K))) _) : typeclass_instances.

Section kit.
  Universes u.
  Context `{@UnifBornSpace@{u} X Φ 𝒜} (K:𝒜).

  (** The localization does not change bounded subspaces: the inclusion of
      the subspace at [K] into [ℒ X] is uniformly continuous
      ([localize_functorial_alt] at the inclusion, with [ℒ K ≅ K] over the
      trivial subspace bornology). *)
  Local Instance bounded_subspace_localized_uc : UniformlyContinuous (η X ∘ ι K).
  Proof.
    pose proof localize_functorial_alt (ι K).
    now change (UniformlyContinuous ((η X ∘ ι K ∘ ε K) ∘ η K)).
  Qed.

  Lemma bounded_subspace_localized_emb : UnifBornEmbedding (η X ∘ ι K).
  Proof. repeat (split; try exact _). Qed.
End kit.
#[global] Hint Extern 2 (UniformlyContinuous (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_uc K) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyEmbedding  (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornEmbedding   (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial     (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornMorphism    (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting  (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (Bornological        (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial    (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (BornologyEmbedding  (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.
#[global] Hint Extern 2 (Injective           (to_localization _ ∘ from_subset (powerset_pt ?K))) => simple notypeclasses refine (bounded_subspace_localized_emb K) : typeclass_instances.

Lemma locally_uc_bounded_restriction `{@LocallyUniformlyContinuous X Y Φ Ψ 𝒜 f} (K:𝒜) : UniformlyContinuous (f ∘ ι K).
Proof.
  pose proof (localized_uc f _).
  now change (UniformlyContinuous ((f ∘ ε X) ∘ (η X ∘ ι K))).
Qed.
Arguments locally_uc_bounded_restriction {_ _ _ _ _} f {_} K.

Lemma locally_ur_bounded_corestriction `{@LocallyUniformlyReflecting X Y Φ Ψ ℬ f} (K:ℬ) `{!MapsInto f K}
  : UniformlyReflecting (corestrict f K).
Proof. exact (local_ur_trivial _ (local_ur_factor _ (ι K) _)). Qed.
Arguments locally_ur_bounded_corestriction {_ _ _ _ _} f {_} K {_}.

Lemma locally_ur_bounded_restriction `{@LocallyUniformlyReflecting X Y Φ Ψ ℬ f} (K:ℬ)
  : UniformlyReflecting (restrict f (f* K) K).
Proof. assert (LocallyUniformlyReflecting (f ∘ ι (f* K))) by exact compose_ur_locally_ur.
  exact (locally_ur_bounded_corestriction (f ∘ ι (f* K)) K).
Qed. 
Arguments locally_ur_bounded_restriction {_ _ _ _ _} f {_} K.


(** The converse of [locally_uc_bounded_restriction], under regularity:
    uniform continuity on every bounded subspace upgrades to the cylinder
    form.  The two cover-form decisions mint the located escapes the
    cylinder's refutation demands; the thickening axiom supplies the
    collar room; classically both mints are trivial and the proof
    degenerates to the thickening argument. *)
Lemma bounded_restrictions_local_uc@{u} `{@RegularWCUnifSpace@{u} X Φ 𝒜} `{@UniformSpace@{u} Y Ψ} (f:X ⇾ Y)
  (Hf : ∀ K:𝒜, UniformlyContinuous (f ∘ from_subset K))
  : LocallyUniformlyContinuous f.
Proof. split; try exact _. intros K W.
  pose proof bornology_regularity_alt K as [K' [EK DK]].
  pose proof wcunif_thicken X K' as [U HT].
  pose (K'' := to_subset U.[powerset_pt K']).
  pose proof Hf K'' as HK''.
  pose proof subset_pt_is_el (ufm_preimage (f ∘ ι (powerset_pt K'')) W) as [V HV].
  pose proof uniform_regularity_alt (U ⊓ V) as [R [ER DR]].
  exists R. intros [x y].
  change (x ∊ K ∧ near R x y ⊸ near W (f x) (f y)).
  destruct (DK x) as [HxK'|HxK].
  + destruct (DR (x, y)) as [Hp|Hp].
    * apply aimpl_true_r.
      change (apos ((x,y) ∊ U ∧ (x,y) ∊ V)) in Hp. destruct Hp as [HpU HpV].
      assert (x ∊ U.[powerset_pt K']) as Hx2 by now rew <-(thicken_expanding _ _).
      assert (y ∊ U.[powerset_pt K']) as Hy2 by (exists x; now split).
      change ((to_subset x, to_subset y) ∊ ufm_preimage (f ∘ ι (powerset_pt K'')) W).
      now rew <-HV.
    * apply by_contrapositive, aimpl_true_r. now right.
  + apply by_contrapositive, aimpl_true_r. now left.
Qed.

(** The reflection converse: uniform reflection on every bounded
    restriction-corestriction upgrades to the cylinder form, by the same
    two mints, run on the codomain side. *)
Lemma bounded_restrictions_local_ur@{u} `{@UniformSpace@{u} X Φ} `{@RegularWCUnifSpace@{u} Y Ψ ℬ} (f:X ⇾ Y)
  (Hf : ∀ L:ℬ, UniformlyReflecting (restrict f (f* L) L))
  : LocallyUniformlyReflecting f.
Proof. split; try exact _. intros L U.
  pose proof bornology_regularity_alt L as [L' [EL DL]].
  pose proof wcunif_thicken Y L' as [V HT].
  pose (L'' := to_subset V.[powerset_pt L']).
  pose (g := restrict f (f* L'') (powerset_pt L'')).
  assert (UniformlyReflecting g) by exact (Hf L'').
  pose proof (ufm_reflection_alt g (ufm_preimage (ι (f* L'')) U)) as [B HB].
  pose proof subset_pt_is_el B as [W HW].
  rew <-(HW : _ ⊆ powerset_pt B) in HB.
  pose proof uniform_regularity_alt (V ⊓ W) as [R [ER DR]].
  exists R. intros [y y'].
  change (f y ∊ L ∧ near R (f y) (f y') ⊸ near U y y').
  destruct (DL (f y)) as [HyL'|HyL].
  + destruct (DR (f y, f y')) as [Hp|Hp].
    * apply aimpl_true_r.
      change (apos ((f y, f y') ∊ V ∧ (f y, f y') ∊ W)) in Hp; destruct Hp as [HpV HpW].
      assert (f y ∊ V.[powerset_pt L']) as Hy1 by now rew <-(thicken_expanding _ _).
      assert (f y' ∊ V.[powerset_pt L']) as Hy2 by (exists (f y); now split).
      change ((to_subset y, to_subset y') ∊ powerset_pt (ufm_preimage (ι (f* L'')) U)).
      now rew <-HB.
    * apply by_contrapositive, aimpl_true_r. now right.
  + apply by_contrapositive, aimpl_true_r. now left.
Qed.

