Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.uniform interfaces.bornology interfaces.unif_born interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology uniform.base bornology.base unif_born.base.
Require Import uniform.subspace bornology.subspace bornology.basis.
Require Import reflection_pair.base.
Require Import easy rewrite replc simplify tactics.misc.

Import image_notation.
Import thicken_notation.
Import tensor_map_notation.
Local Open Scope subset_scope.
Local Open Scope topology_scope.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").

(** Initial (pullback) unif-bornological structure: [UnifBorn] is the fiber
    product [Unif ×_Set PreBorn] over the carrier — no connecting axioms — so the
    initial lift is just the pair [(pullback_uniformity f, pullback_bornology f)]. *)

Section pullback_unif_born.
  Universes u.
  Context {X:set@{u}} `{Ψ:Uniformity@{u} Y} `{ℬ:Bornology@{u} Y} {f:X ⇾ Y}
          `{!UniformSpace Y, !BornologicalSpace Y}.
  #[local] Hint Extern 0 (Uniformity X) => exact (pullback_uniformity f) : typeclass_instances.
  #[local] Hint Extern 0 (Bornology X) => exact (pullback_bornology f) : typeclass_instances.

  Local Instance pullback_unif_born_space : UnifBornSpace X.
  Proof. now split. Qed.

  Local Instance pullback_unif_born_initial : UnifBornInitial f.
  Proof. enough (UniformlyInitial f ∧ BornologyInitial f)%sprop as [??] by now split. split.
  + exact pullback_map_initial.
  + exact pullback_born_initial.
  Qed.
End pullback_unif_born.
#[global] Hint Extern 2 (@UnifBornSpace _ (pullback_uniformity _) (pullback_bornology _)) =>
  simple notypeclasses refine pullback_unif_born_space : typeclass_instances.


#[global] Hint Extern 0 (Cleavage 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact (λ X Y '(Ψ, ℬ) f, (pullback_uniformity f, pullback_bornology f)) : typeclass_instances.

Lemma unifborn_cloven_pair : ClovenPair 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧.
Proof. unshelve esplit. intros. exact pullback_unif_born_initial. Qed.
#[global] Hint Extern 0 (ClovenPair 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact unifborn_cloven_pair : typeclass_instances.
#[global] Hint Extern 0 (SaturatedPair 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) => exact unifborn_cloven_pair : typeclass_instances.

Lemma unif_born_initial_alt@{u} `{@UnifBornSpace@{u} X Φ 𝒜, @UnifBornSpace@{u} Y Ψ ℬ} (f:X ⇾ Y)
  : UnifBornInitial f ↔
    (∀ (Z:set@{u}) (Θ:Uniformity Z) (𝒞:Bornology Z), UnifBornSpace Z → ∀ (g:Z ⇾ X),
       UnifBornMorphism (f ∘ g) ↔ UnifBornMorphism g).
Proof. change (UnifBornInitial f) with (Ini 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 f). rew (ini_lift_alt (C:=𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) f). split.
+ intros P Z Θ 𝒞 ? g. exact (P Z (Θ, 𝒞) _ g).
+ intros P Z [Θ 𝒞] ? g. exact (P Z Θ 𝒞 _ g).
Qed.


(** The WCUnif thickening axiom survives pullback: the pullback of a
    [WCUnifSpace] is a [WCUnifSpace]. *)
Section pullback_wcunif.
  Universes u.
  Context {X:set@{u}} `{Ψ:Uniformity@{u} Y} `{ℬ:Bornology@{u} Y} {f:X ⇾ Y} `{!WCUnifSpace Y}.
  #[local] Hint Extern 0 (Uniformity X) => exact (pullback_uniformity f) : typeclass_instances.
  #[local] Hint Extern 0 (Bornology X) => exact (pullback_bornology f) : typeclass_instances.

  Local Instance pullback_wc_unif_space : WCUnifSpace X.
  Proof. pose proof (pullback_unif_born_initial (f:=f)). exact (wcunif_transport f). Qed.
End pullback_wcunif.
#[global] Hint Extern 2 (@WCUnifSpace _ (pullback_uniformity _) (pullback_bornology _)) =>
  simple notypeclasses refine pullback_wc_unif_space : typeclass_instances.

(** Subspaces A ∊ 𝒫 X are the instance f = from_subset A: carrier-keyed
    companions of the slot-keyed hints above, filling the instance slots
    (mirroring [uniform/subspace.v] and [bornology/subspace.v]). *)
#[global] Hint Extern 4 (UnifBornSpace (subset_to_set ?A)) =>
  notypeclasses refine (pullback_unif_born_space (f:=from_subset A)) : typeclass_instances.
#[global] Hint Extern 4 (WCUnifSpace (subset_to_set ?A)) =>
  notypeclasses refine (pullback_wc_unif_space (f:=from_subset A)) : typeclass_instances.

(** The AHS initial-morphism characterization survives restriction to the WCUnif
    subcategory: for [f] between [WCUnifSpace]s, [UnifBornInitial f] is detected
    by WCUnif test objects alone — because the initial (pullback) structure is
    itself a [WCUnifSpace] ([pullback_wc_unif_space]).  So WCUnif is closed under
    the UnifBorn-initial lifts. *)
Lemma wcunif_initial_alt@{u} `{@WCUnifSpace@{u} X Φ 𝒜, @WCUnifSpace@{u} Y Ψ ℬ} (f:X ⇾ Y)
  : UnifBornInitial f ↔
    (∀ (Z:set@{u}) (Θ:Uniformity Z) (𝒞:Bornology Z), WCUnifSpace Z → ∀ (g:Z ⇾ X),
       UnifBornMorphism (f ∘ g) ↔ UnifBornMorphism g).
Proof.
  change (UnifBornInitial f) with (Ini 𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧 f).
  pose proof (ini_lift_alt_restrict (C:=𝐔𝐧𝐢𝐟𝐁𝐨𝐫𝐧) (λ Z '(Θ,𝒞), @WCUnifSpace Z Θ 𝒞)
        (λ S Z u '(Θ,𝒞) HZ HW, pullback_wc_unif_space) f H H0) as E.
  rew E.
  split.
+ intros P Z Θ 𝒞 HW g. exact (P Z (Θ, 𝒞) _ HW g).
+ intros P Z [Θ 𝒞] ? HW g. exact (P Z Θ 𝒞 HW g).
Qed.

Lemma from_subset_unif_born_emb `{@UnifBornSpace X Φ 𝒜} {A:𝒫 X} : UnifBornEmbedding (from_subset A).
Proof. repeat (split; try exact _). Qed.
#[global] Hint Extern 2 (UnifBornMorphism   (from_subset _)) => simple notypeclasses refine from_subset_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (UnifBornReflecting (from_subset _)) => simple notypeclasses refine from_subset_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (UnifBornInitial    (from_subset _)) => simple notypeclasses refine from_subset_unif_born_emb : typeclass_instances.
#[global] Hint Extern 2 (UnifBornEmbedding  (from_subset _)) => simple notypeclasses refine from_subset_unif_born_emb : typeclass_instances.
