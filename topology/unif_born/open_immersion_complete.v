(** Bounded completeness of the open immersion (cont3's D′ route;
    doc/extension_theorem.md §4, §7).  Over a complete ambient X, every
    *trapped* ℒ-Cauchy filter on 𝒪 S converges in 𝒪 S: the witness K ∊ 𝒲 S
    pins the ambient limit inside cl (j⁎ K) ⊆ S, by the ◁-leg of
    well-containment and closure algebra alone.  No intrinsic completeness
    of ℒ (𝒪 S) is claimed — that statement is scale-priced — and none is
    needed: the extension pipeline only ever takes limits of witnessed
    filters (bornological images of bounded filters, traces of
    apartness-witnessed points). *)

Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.unif_born.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.interior topology.subspace.
Require Import uniform.base uniform.basis uniform.product uniform.subspace.
Require Import uniform.uniformly_below.
Require Import uniform.cauchy_completion uniform.completion.
Require Import bornology.base bornology.basis.
Require Import unif_born.base unif_born.local_maps unif_born.localization.
Require Import unif_born.well_contained unif_born.open_immersion.
Require Import unif_born.trapped_cauchy unif_born.trapped_wc unif_born.local_completion.
Require Import easy rewrite replc simplify strip_coercions tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope fun_inv_scope.
Import image_notation.
Import tensor_map_notation.
Import thicken_notation.

Local Abbreviation id := (id_fun _).
Local Abbreviation ℒ := localization.
Local Abbreviation ε := from_localization.
Local Abbreviation η := to_localization.
Local Abbreviation κ := to_cauchy.
Local Abbreviation 𝒞 := cauchy_filter_set.
Local Abbreviation 𝒞₁ := cauchy_map.
Local Abbreviation cl := closure.
Local Abbreviation int := interior.
Local Abbreviation 𝒪 := open_immersion.
Local Abbreviation 𝒲 := open_immersion_bornology.
Local Abbreviation j := from_open_immersion.

Local Abbreviation 𝒯 := trapped_cauchy_filter_set.
Local Abbreviation τ := to_trapped.
Local Abbreviation ρ := from_trapped.
Local Abbreviation 𝒯₁ := wc_trapped_map.

Section open_immersion_complete.
  Context `{@WCUnifSpace X Φ 𝒜, !LocallyComplete X (Li:=Li)} (S : 𝒫 X) {HS:open S}.

  Definition open_immersion_ambient_limit : 𝒯 (𝒪 S) ⇾ X := (τ X)⁻¹ ∘ 𝒯₁ (j S) .
  Local Abbreviation k := open_immersion_ambient_limit.

  Local Instance open_immersion_complete_maps_into : MapsInto k S.
  Proof. unfold k. intros F.
    pose proof (trapped_prop F) as [K HK].
    pose (K' := (j S)⁎ K).
    pose proof andr (subset_pt_is_el K) : K' ◁ S as HKub.
    rew (unif_below_closure _ _) in HKub. rew <-HKub.
    assert (K' ∊ trapped_filter (𝒯₁ (j S) F)) as HKel. {
      change ( (j S)* ((j S)⁎ K) ∊ trapped_filter F ).
      now rew <-(preimage_image_unit _ _).
    }
    now pose proof (to_trapped_eq_closure _ _ (surjective_applied (τ X) (𝒯₁ (j S) F)) (@to_subset _ _ _ HKel)).
  Qed.

  Definition open_immersion_limit : 𝒯 (𝒪 S) ⇾ 𝒪 S := corestrict k S.
  Local Abbreviation r := open_immersion_limit.

  Lemma open_immersion_limit_unit : r ∘ τ (𝒪 S) = id.
  Proof. apply (injective_compose_cancel (j S)); try exact _.
    change ( (τ X)⁻¹ ∘ (𝒯₁ (j S) ∘ τ (𝒪 S)) = j S ).
    rew (wc_trapped_map_unit (j S)).
    change ( ((τ X)⁻¹ ∘ τ X) ∘ j S = j S ).
    now rew (bijective (τ X)).
  Qed.

  Local Instance open_immersion_limit_cont : Continuous r.
  Proof. apply (cont_factor _ (j S) _). now change (Continuous ((τ X)⁻¹ ∘ 𝒯₁ (j S))). Qed.

  Local Instance open_immersion_locally_complete_inverse : LocalCompleteInverse (𝒪 S)
    := to_trapped_retract_complete_inverse r open_immersion_limit_unit.
  
  Lemma open_immersion_locally_complete : LocallyComplete (𝒪 S).
  Proof. exact (to_trapped_retract_complete r open_immersion_limit_unit). Qed.
End open_immersion_complete.


