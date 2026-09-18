Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.subgroups.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base uniform.basis.
Require Import reflection_pair.base.
Require Import easy rewrite replc simplify strip_coercions tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Import projection_notation.
Import image_notation.
Import tensor_map_notation.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").

Definition pullback_uniformity@{u} {X:set@{u}} `{Ψ:Uniformity@{u} Y} (f:X ⇾ Y) : Uniformity X
  := { U : 𝒫 (X ⊗ X) | ∐ W:Ψ, f♯ W ⊆ U }.


Definition entourage_pullback@{u} {X:set@{u}} `{Ψ:Uniformity@{u} Y} (f:X ⇾ Y) := set:(λ V:Ψ, f♯ V).
Lemma entourage_pullback_order_preserving@{u} {X:set@{u}} `{Ψ:Uniformity@{u} Y} {f:X ⇾ Y}
  : OrderPreserving (entourage_pullback f).
Proof. apply alt_Build_OrderPreserving. intros U V. exact (order_preserving f♯ U V). Qed.
#[global] Hint Extern 2 (OrderPreserving (entourage_pullback _)) => simple notypeclasses refine entourage_pullback_order_preserving : typeclass_instances.

(*Definition pullback_uniformity@{u} {X:set@{u}} `{Ψ:Uniformity@{u} Y} (f:X ⇾ Y) := presented_uniformity (entourage_pullback f).*)

Lemma pullback_uniformity_presented@{u} {X:set@{u}} `{Ψ:Uniformity@{u} Y} {f:X ⇾ Y}
  : @UniformityPresentation X (pullback_uniformity f) _ (entourage_pullback f).
Proof. now change (pullback_uniformity f) with (presented_uniformity (entourage_pullback f)). Qed.
#[global] Hint Extern 1 (UniformityPresentation _ (Φ:=pullback_uniformity ?f) _) => simple notypeclasses refine (pullback_uniformity_presented (f:=f)) : typeclass_instances.
#[global] Hint Extern 1 (FilterPresentation (pullback_uniformity ?f) _) => simple notypeclasses refine (pullback_uniformity_presented (f:=f)) : typeclass_instances.
#[global] Hint Extern 1 (LeastUpSet (pullback_uniformity ?f)) => simple notypeclasses refine (pullback_uniformity_presented (f:=f)) : typeclass_instances.
#[global] Hint Extern 1 (UpSet (pullback_uniformity ?f)) => simple notypeclasses refine (pullback_uniformity_presented (f:=f)) : typeclass_instances.

Definition pullback_uniformity_basis@{u} {X:set@{u}} `{Ψ:Uniformity@{u} Y} (f:X ⇾ Y)
  {Λ:set@{u}} (β:Λ ⇾ Ψ)
:= set:(λ i:Λ, filter_presentation_basis_fun (pullback_uniformity f) (entourage_pullback f) (β i)).

Lemma pullback_uniformity_basis_correct@{u} {X:set@{u}} `{Ψ:Uniformity@{u} Y} {f:X ⇾ Y}
  {Λ:set@{u}} {β:Λ ⇾ Ψ} {H:UniformityBasis β}
  : UniformityBasis (pullback_uniformity_basis f β).
Proof. now change (FilterBasis ( filter_presentation_basis_fun (pullback_uniformity f) (entourage_pullback f) ∘ β )). Qed.
#[global] Hint Extern 0 (@UniformityBasis ?X (@pullback_uniformity ?X ?Y ?Ψ ?f) ?Λ _) =>
  let H := constr:(_ : @UniformityBasis Y Ψ Λ _) in
  simple notypeclasses refine (pullback_uniformity_basis_correct (f:=f) (H:=H)) : typeclass_instances.

Section pullback.
  Universes u.
  Context  {X:set@{u}} `{Ψ:Uniformity@{u} Y} {f:X ⇾ Y}.

  Local Abbreviation Φ := (@pullback_uniformity X Y Ψ f).
  #[local] Hint Extern 0 (Uniformity X) => exact Φ : typeclass_instances.

  Context `{!UniformSpace Y}.

  Local Instance pullback_uniform_space : UniformSpace X.
  Proof. apply presented_uniform_space; intros V; change (func_op (entourage_pullback f) ?i) with (f♯ i).
  + rew <-(uniform_refl_alt V : id_rel _ ⊆ subset_pt V).
    intros [x y]. exact (is_fun f _ _).
  + now exists V⁻¹.
  + pose proof uniform_split_alt V as [U PU]. exists U.
    rew (preimage_compose_rel_lax_alt _ _ _).
    now rew <-(order_preserving f♯ _ _).
  Qed.

  Local Instance pullback_map_initial : UniformlyInitial f.
  Proof. split.
  + apply (uniformly_continuous_alt _). intros V. now exists V.
  + apply ufm_refl_by_basis. intros V. now exists V.
  Qed.

  Local Instance pullback_map_emb `{!Injective f} : UniformlyEmbedding f.
  Proof. now split. Qed.

  (** Universal Property *)
  
  Context `{@UniformSpace@{u} Z Ξ} (g:Z ⇾ X).

  Lemma pullback_uniformity_initial `{!UniformlyContinuous (f ∘ g)} : UniformlyContinuous g.
  Proof. apply uniformly_continuous_alt. intros U.
    pose proof uniformity_basis U as [V PV].
    change (apos (⟨f, f⟩* V ⊆ U)) in PV.
    apply (up_closed Ξ ((f ∘ g)♯ V)).
    * now rew <-PV.
    * now apply uniformly_continuous_alt.
  Qed.
End pullback.
#[global] Hint Extern 2 (@UniformSpace _ (pullback_uniformity _)) =>
  simple notypeclasses refine pullback_uniform_space : typeclass_instances.
#[global] Hint Extern 2 (@PreUniformSpace _ (pullback_uniformity _)) =>
  simple notypeclasses refine pullback_uniform_space : typeclass_instances.
#[global] Hint Extern 2 (@Topology _ (@UniformNeighborhood _ (pullback_uniformity _))) =>
  simple notypeclasses refine pullback_uniform_space : typeclass_instances.

#[global] Hint Extern 0 (Cleavage 𝐔𝐧𝐢𝐟) => exact @pullback_uniformity : typeclass_instances.

Lemma unif_cloven_pair : ClovenPair 𝐔𝐧𝐢𝐟.
Proof. unshelve esplit. intros. exact pullback_map_initial. Qed.
#[global] Hint Extern 0 (ClovenPair 𝐔𝐧𝐢𝐟) => exact unif_cloven_pair : typeclass_instances.
#[global] Hint Extern 0 (SaturatedPair 𝐔𝐧𝐢𝐟) => exact unif_cloven_pair : typeclass_instances.

Lemma uniformly_initial_alt@{u} `{@UniformSpace@{u} X Φ, @UniformSpace@{u} Y Ψ} (f:X ⇾ Y)
  : UniformlyInitial f ↔
    (∀ (Z:set@{u}) (Ξ:Uniformity Z), UniformSpace Z → ∀ (g:Z ⇾ X),
       UniformlyContinuous (f ∘ g) ↔ UniformlyContinuous g).
Proof. exact (ini_lift_alt (C:=𝐔𝐧𝐢𝐟) f). Qed.

Lemma uniformly_initial_alt2@{u} `{@UniformlyContinuous@{u} X Y Φ Ψ f}
  : UniformlyInitial f ↔
    (∀ (Z:set@{u}) (Ξ:Uniformity Z), UniformSpace Z → ∀ (g:Z ⇾ X),
       UniformlyContinuous (f ∘ g) → UniformlyContinuous g).
Proof. exact (ini_lift_alt2 (C:=𝐔𝐧𝐢𝐟) f). Qed.


(** Subspaces A ∊ 𝒫 X are the instance f = from_subset A *)

#[global] Hint Extern 2 (Uniformity (subset_to_set ?A)) =>
  notypeclasses refine (pullback_uniformity (from_subset A)) : typeclass_instances.
#[global] Hint Extern 4 (UniformSpace (subset_to_set ?A)) =>
  notypeclasses refine pullback_uniform_space : typeclass_instances.

Lemma from_subset_emb `{@UniformSpace X Φ} {A:𝒫 X} : UniformlyEmbedding (from_subset A).
Proof. exact pullback_map_emb. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding  (from_subset _)) => simple notypeclasses refine from_subset_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial    (from_subset _)) => simple notypeclasses refine from_subset_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (from_subset _)) => simple notypeclasses refine from_subset_emb : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (from_subset _)) => simple notypeclasses refine from_subset_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding  (YN:=UniformNeighborhood) (from_subset _)) => simple notypeclasses refine from_subset_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial    (YN:=UniformNeighborhood) (from_subset _)) => simple notypeclasses refine from_subset_emb : typeclass_instances.
#[global] Hint Extern 2 (Continuous             (YN:=UniformNeighborhood) (from_subset _)) => simple notypeclasses refine from_subset_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (YN:=UniformNeighborhood) (from_subset _)) => simple notypeclasses refine from_subset_emb : typeclass_instances.

Lemma separated_uniform_subspace `{@SeparatedUniformSpace X Φ} {A:𝒫 X} : SeparatedUniformSpace A.
Proof. exact (uniform_reflects_hausdorff (from_subset A)). Qed.
#[global] Hint Extern 2 (SeparatedUniformSpace (subset_to_set _)) => simple notypeclasses refine separated_uniform_subspace : typeclass_instances.


#[global] Hint Extern 8 (WeakMapsTo ?f ?S ?T) => match goal with H:apos(S ⊆ func_op f* T) |- _ => exact (H:MapsTo f S T) end : typeclass_instances.

Lemma dense_open_restrict@{u} {X Y:set@{u}} `{@UniformSpace Y Ψ} (f:X ⇾ Y) `{!Dense f}
  (S:𝒫 X) (T:𝒫 Y) {HT:open T} {HS₁:S ⊆ f* T} {HS₂:f* T ⊆ S} : Dense (restrict f S T).
Proof. apply uniform_Dense_iff. intros t [U' [U HU]].
  change (∐ x:S, (t, restrict f S T x) ∊ U'); rew <-HU.
  destruct t as [y ely]. change (∐ x:S, near U y (f x)). clear U' HU.
  enough (∐ x:X, x ∊ S ⊠ near U y (f x)) as [x[??]] by now exists (to_subset x).
  assert (y ∊ interior T) as ely' by now rew (HT:interior T = T).
  rew uniform_interior_applied2 in ely'; destruct ely' as [V P].
  pose proof (uniform_dense_range f y (U ⊓ V)) as [x Hx]. exists x. split.
  + rew <-HS₂. change (f x ∊ T). apply P. now rew <-(meet_lb_r U V).
  + now rew <-(meet_lb_l U V).
Qed.


