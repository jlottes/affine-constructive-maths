Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.subgroups.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base uniform.basis.
Require Import easy rewrite replc simplify strip_coercions tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Import projection_notation.
Import image_notation.
Import tensor_map_notation.

Local Abbreviation id := (id_fun _).
Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Notation "f ♭" := ((func_op ⟨f,f⟩)⁎) (at level 1, left associativity, format "f ♭").

Definition entourage_pushforward@{u} `{Φ:Uniformity@{u} X} {Y:set@{u}} (f:X ⇾ Y) := set:(λ U:Φ, f♭ U).
Lemma entourage_pushforward_order_preserving@{u} `{Φ:Uniformity@{u} X} {Y:set@{u}} {f:X ⇾ Y}
  : OrderPreserving (entourage_pushforward f).
Proof. apply alt_Build_OrderPreserving. intros U V. exact (order_preserving f♭ U V). Qed.
#[global] Hint Extern 2 (OrderPreserving (entourage_pushforward _)) => simple notypeclasses refine entourage_pushforward_order_preserving : typeclass_instances.


Definition quotient_uniformity@{u} `{Φ:Uniformity@{u} X} {Y:set@{u}} (f:X ⇾ Y)
  := presented_uniformity (entourage_pushforward f).

Lemma quotient_uniformity_presented@{u} `{Φ:Uniformity@{u} X} {Y:set@{u}} {f:X ⇾ Y}
  : @UniformityPresentation Y (quotient_uniformity f) _ (entourage_pushforward f).
Proof. now unfold quotient_uniformity. Qed.
#[global] Hint Extern 1 (UniformityPresentation _ (Φ:=quotient_uniformity _) _) => simple notypeclasses refine quotient_uniformity_presented : typeclass_instances.
#[global] Hint Extern 1 (FilterPresentation (quotient_uniformity _) _) => simple notypeclasses refine quotient_uniformity_presented : typeclass_instances.

Definition quotient_uniformity_basis@{u} `{Φ:Uniformity@{u} X} {Y:set@{u}} (f:X ⇾ Y)
  {Λ:set@{u}} (β:Λ ⇾ Φ)
:= set:(λ i:Λ, filter_presentation_basis_fun (quotient_uniformity f) (entourage_pushforward f) (β i)).

Lemma quotient_uniformity_basis_correct@{u}  `{Φ:Uniformity@{u} X} {Y:set@{u}} {f:X ⇾ Y}
  {Λ:set@{u}} {β:Λ ⇾ Φ} {H:UniformityBasis β}
  : UniformityBasis (quotient_uniformity_basis f β).
Proof. now change (FilterBasis ( filter_presentation_basis_fun (quotient_uniformity f) (entourage_pushforward f) ∘ β )). Qed.
#[global] Hint Extern 0 (@UniformityBasis ?X (@quotient_uniformity ?X ?Φ ?Y ?f) ?Λ _) =>
  let H := constr:(_ : @UniformityBasis X Φ Λ _) in
  simple notypeclasses refine (quotient_uniformity_basis_correct (f:=f) (H:=H)) : typeclass_instances.

Section quotient.
  Universes u.
  Context   `{Φ:Uniformity@{u} X} {Y:set@{u}} {f:X ⇾ Y}.

  Local Abbreviation Ψ := (@quotient_uniformity X Φ Y f).
  #[local] Hint Extern 0 (Uniformity Y) => exact Ψ : typeclass_instances.

  Context `{!UniformSpace X} `{!WeaklySurjective f}.
  Context (sep:∀ U:Φ, f♯ (id_rel Y) ⊆ U).

  Local Instance quotient_uniform_space : UniformSpace Y.
  Proof. apply presented_uniform_space; intros U; change (func_op (entourage_pushforward f) ?i) with (f♭ i).
  + now rew <-(uniform_refl_alt U : _ ⊆ subset_pt U), <-(weakly_surjective_id_rel _).
  + exists U⁻¹. enough ( (f♭ U⁻¹)⁻¹ = (f♭ U⁻¹⁻¹) ) as E by now rew E.
    exact (flip_image_tensor_map_alt _ _ _).
  + pose proof uniform_split_sym3 U as [V[EV PV]]. exists V. intros [a c].
    change ( (∐ b, (∐ p, ⟨f,f⟩ p = (a, b) ⊠ p ∊ V) ⊠ (∐ p, ⟨f,f⟩ p = (b, c) ⊠ p ∊ V)) ⊸ (a, c) ∊ f♭ U ).
    rew <-aex_adj; intros b; rew <-aex_adj2; intros [x x'][y y'].
    change (⟨f,f⟩ (?x,?y) = (?a, ?b)) with (f x = a ⊠ f y = b).
    trans exact:( ((x, x') ∊ V ⊠ f x = a) ⊠ (f x' = b ⊠ f y = b) ⊠ ( (y, y') ∊ V ⊠ f y' = c )); [ tautological |].
    rew (symmetry_iff (=) (f y) b), (transitivity (=) _ b _).
    rew (sep V (_, _) : f x' = f y ⊸ (x', y) ∊ V).
    clear b; change ((a, c) ∊ f♭ U) with (∐ p, ⟨f,f⟩ p = (a, c) ⊠ p ∊ U).
    rew <-(aex_ub _ (x, y')).  change (⟨f,f⟩ (?x,?y) = (?a, ?b)) with (f x = a ⊠ f y = b).
    trans exact:( ( f x = a ⊠ f y' = c) ⊠ ( (x, x') ∊ V ⊠ (x', y) ∊ V ⊠ (y, y') ∊ V ) ); [ tautological |].
    apply aprod_proper_aimpl; [ easy |].
    rew <-(PV : subset_pt V ∙ subset_pt V ∙ subset_pt V ⊆ subset_pt U).
    change ((?a, ?b) ∊ ?U ∙ ?V) with (∐ z, (a, z) ∊ U ⊠ (z, b) ∊ V). rew <-(aex_ub _ y).
    change ((?a, ?b) ∊ ?U ∙ ?V) with (∐ z, (a, z) ∊ U ⊠ (z, b) ∊ V). rew <-(aex_ub _ x').
    tautological.
  Qed.
  
  Local Instance quotient_map_ufm_cont : UniformlyContinuous f.
  Proof. apply uniformly_continuous_alt. intros [V [U HU]]; unfold powerset_pt, subset_pt.
    apply (up_closed Φ U); [| exact _ ].
    now rew <-(image_preimage_adj _ _ _).
  Qed.

  (** Universal Property *)
  
  Context `{@UniformSpace@{u} Z Ξ} (g:Y ⇾ Z).

  Lemma quotient_uniformity_final `{!UniformlyContinuous (g ∘ f)} : UniformlyContinuous g.
  Proof. apply uniformly_continuous_alt. intros W.
    assert ((g∘f)♯ W ∊ Φ) by now apply uniformly_continuous_alt.
    exists (to_subset ((g∘f)♯ W)); change (f♭ ((g∘f)♯ W) ⊆ g♯ W).
    now rew (image_preimage_adj _ _ _).
  Qed.
End quotient.


