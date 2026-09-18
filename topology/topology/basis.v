Require Import interfaces.set interfaces.common_props algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology.
Require Import theory.set theory.common_props orders.orders orders.maps orders.subset.
Require Import orders.subset_images.
Require Import topology.base topology.interior.
Require Import easy rewrite simplify.

Local Open Scope topology_scope.
Import image_notation.

(** Basic access to neighborhood basis elements. *)

Section neighborhood_basis_basics.
  Universes u.
  Context `{XN:Neighborhood@{u} X} {Λ:Type@{u}} {β:Λ → 𝒫 X} {NB:NeighborhoodBasis β}.

  (** Forward direction: from a neighborhood [N] of [x], extract a basis
      element which contains [x] and is contained in [N]. *)
  Lemma neighborhood_basis_find (x:X) (N:𝒫 X) : x ⪽ N ⊸ ∐ i, x ∊ β i ⊠ β i ⊆ N.
  Proof. now rew (NB _ _). Qed.

  (** Reverse direction: any basis element containing [x] and contained in [N]
      witnesses that [N] is a neighborhood of [x]. *)
  Lemma neighborhood_basis_use (x:X) (N:𝒫 X) (i:Λ) : x ∊ β i ⊠ β i ⊆ N ⊸ x ⪽ N.
  Proof. now rew (NB _ _), <-(aex_ub _ i). Qed.

  Lemma neighborhood_basis_open i : ∏ p, p ∊ β i ⊸ p ⪽ β i.
  Proof. intros p. rew (NB _ _), <-(aex_ub _ i). now simplify. Qed.

  Lemma neighborhood_basis_open_alt i :  β i ⊆ interior (β i).
  Proof. exact (neighborhood_basis_open i). Qed.

  Lemma neighborhood_basis_open_iff i : ∏ p, p ∊ β i ⧟ p ⪽ β i.
  Proof. intros p. split; [ exact (neighborhood_basis_open i p) |].
    rew (NB _ _), <-aex_adj; intros j. apply subset_apply.
  Qed.
  
  Lemma neighborhood_basis_isotony (x:X) (U V : 𝒫 X) : x ⪽ U ⊠ U ⊆ V ⊸ x ⪽ V.
  Proof. rew (NB _ U), aex_frob_r, <-aex_adj; intros i.
    rew (NB x V), <-(aex_ub _ i).
    now rew (aprod_assoc _ _ _), (transitivity le _ _ _).
  Qed.
End neighborhood_basis_basics.


(** Continuity by neighborhood basis at the codomain.

    To prove [f : X ⇾ Y] is continuous, it suffices to exhibit, for each
    [x] and each basic neighborhood [β j] of [f x], that the preimage of
    [β j] is a neighborhood of [x] — phrased as the affine implication so
    it carries both polarities. *)

Lemma cont_by_basis_codom@{u}
  `{@Topology@{u} X NX, @Topology@{u} Y NY}
  {Λ:Type@{u}} {β:Λ → 𝒫 Y}
  {NB:NeighborhoodBasis β}
  (f:X ⇾ Y) :
  (∀ x j, f x ∊ β j ⊸ x ⪽ f* (β j)) → Continuous f.
Proof. intros P. split; try exact _. intros x N.
  rew (NB (f x) N), <-aex_adj; intros j.
  rew <-(top_isotony x (f* (β j)) _).
  now rew [<-(P _ _)|<-(order_preserving f* _ _)].
Qed.

(** Continuity by neighborhood basis at the domain.

    Dual to [cont_by_basis_codom]: with a basis [β] at the domain [X],
    it suffices that every neighborhood [N] of [f x] be refined by the
    preimage of some basic neighborhood [β i] of [x]. *)

Lemma cont_by_basis_dom@{u}
  `{@Topology@{u} X NX, @Topology@{u} Y NY}
  {Λ:Type@{u}} {β:Λ → 𝒫 X}
  {NB:NeighborhoodBasis β}
  (f:X ⇾ Y) :
  (∀ x N, f x ⪽ N ⊸ ∐ i, x ∊ β i ⊠ β i ⊆ f* N) → Continuous f.
Proof. intros P. split; try exact _. intros x N.
  trans (∐ i, x ∊ β i ⊠ β i ⊆ f* N).
  + exact (P x N).
  + rew <-aex_adj. exact (neighborhood_basis_use x (f* N)).
Qed.

Lemma cont_by_basis@{u}
  `{@Topology@{u} X NX, @Topology@{u} Y NY}
  {Λ₁:Type@{u}} {α:Λ₁ → 𝒫 X} {NBX:NeighborhoodBasis α}
  {Λ₂:Type@{u}} {β:Λ₂ → 𝒫 Y} {NBY:NeighborhoodBasis β}
  (f:X ⇾ Y) :
  (∀ x j, f x ∊ β j ⊸ ∐ i, x ∊ α i ⊠ α i ⊆ f* (β j)) → Continuous f.
Proof. intros P. apply cont_by_basis_dom. intros x N.
  rew (NBY (f x) N). rew <-aex_adj; intros j.
  rew (P x j), aex_frob_r, <-aex_adj; intros i. rew <-(aex_ub _ i).
  rew (aprod_assoc _ _ _); apply aprod_proper_aimpl; [ easy |].
  rew (order_preserving f* (β j) N). now apply transitivity.
Qed.

(** Continuous reflection by neighborhood basis at the codomain.

    To prove [f : X ⇾ Y] continuously reflects neighborhoods, it suffices
    to produce the reflecting neighborhood of [f x] as a basic one [β j]. *)

Lemma refl_by_basis_codom@{u}
  `{@Topology@{u} X NX, @Topology@{u} Y NY}
  {Λ:Type@{u}} {β:Λ → 𝒫 Y}
  {NB:NeighborhoodBasis β}
  (f:X ⇾ Y) :
  (∀ x U, x ⪽ U ⊸ ∐ j, f x ∊ β j ⊠ f* (β j) ⊆ U) → ContinuouslyReflecting f.
Proof. intros P. split; try exact _. intros x U.
  trans (∐ j, f x ∊ β j ⊠ f* (β j) ⊆ U).
  + exact (P x U).
  + rew <-aex_adj; intros j. rew <-(aex_ub _ (β j)).
    now rew (neighborhood_basis_open_iff j (f x)).
Qed.

(** Continuous reflection by neighborhood basis at the domain.

    Dual to [refl_by_basis_codom]: with a basis [β] at the domain [X],
    it suffices to reflect the basic neighborhoods [β i] of [x]. *)

Lemma refl_by_basis_dom@{u}
  `{@Topology@{u} X NX, @Topology@{u} Y NY}
  {Λ:Type@{u}} {β:Λ → 𝒫 X}
  {NB:NeighborhoodBasis β}
  (f:X ⇾ Y) :
  (∀ x i, x ∊ β i ⊸ ∐ V, f x ⪽ V ⊠ f* V ⊆ β i) → ContinuouslyReflecting f.
Proof. intros P. split; try exact _. intros x U.
  rew (NB x U). rew <-aex_adj; intros i.
  rew (P x i), aex_frob_r, <-aex_adj; intros V. rew <-(aex_ub _ V).
  rew (aprod_assoc _ _ _); apply aprod_proper_aimpl; [ easy |].
  now apply transitivity.
Qed.

Lemma refl_by_basis@{u}
  `{@Topology@{u} X NX, @Topology@{u} Y NY}
  {Λ₁:Type@{u}} {α:Λ₁ → 𝒫 X} {NBX:NeighborhoodBasis α}
  {Λ₂:Type@{u}} {β:Λ₂ → 𝒫 Y} {NBY:NeighborhoodBasis β}
  (f:X ⇾ Y) :
  (∀ x i, x ∊ α i ⊸ ∐ j, f x ∊ β j ⊠ f* (β j) ⊆ α i) → ContinuouslyReflecting f.
Proof. intros P. apply refl_by_basis_dom. intros x i.
  rew (P x i). rew <-aex_adj; intros j. rew <-(aex_ub _ (β j)).
  now rew (neighborhood_basis_open_iff j (f x)).
Qed.

(** Both criteria together give initiality: the topology on [X] is exactly
    the one induced by [f], as witnessed basis-to-basis. *)

Lemma initial_by_basis@{u}
  `{@Topology@{u} X NX, @Topology@{u} Y NY}
  {Λ₁:Type@{u}} {α:Λ₁ → 𝒫 X} {NBX:NeighborhoodBasis α}
  {Λ₂:Type@{u}} {β:Λ₂ → 𝒫 Y} {NBY:NeighborhoodBasis β}
  (f:X ⇾ Y) :
  (∀ x j, f x ∊ β j ⊸ ∐ i, x ∊ α i ⊠ α i ⊆ f* (β j))
→ (∀ x i, x ∊ α i ⊸ ∐ j, f x ∊ β j ⊠ f* (β j) ⊆ α i)
→ ContinuouslyInitial f.
Proof. intros P Q. split.
+ exact (cont_by_basis f P).
+ exact (refl_by_basis f Q).
Qed.

(** Density by neighborhood basis: a subset that meets every inhabited
    basic neighborhood is dense. *)

Lemma dense_by_basis@{u}
  `{@Topology@{u} X NX}
  {Λ:Type@{u}} {β:Λ → 𝒫 X}
  {NB:NeighborhoodBasis β}
  (U : 𝒫 X) :
  (∀ x i, x ∊ β i ⊸ ∐ a, a ∊ β i ⊠ a ∊ U) → dense U.
Proof. intros P.
  change (apos (closure U = ⊤)).
  rew <-(le_antisym_iff _ _); split; [exact (below_top _) |].
  change (∏ x:X, 𝐓 ⊸ x ∊ closure U). intros x. simplify.
  change (apos (anot (x ⪽ complement U))).
  rew (NB x (complement U)).
  rew (demorgan_dual _). intros i.
  apply by_contrapositive.
  rew (order_preserving_flip complement _ _).
  change (U ⊆ complement (β i) ⊸ anot (x ∊ β i)).
  rew <-(aimpl_false _).
  rew <-(aprod_adj _ _ _).
  rew (P x i).
  rew aex_frob_l. rew <-aex_adj; intros a.
  change ((∏ p:X, p ∊ U ⊸ p ∊̸ β i) ⊠ (a ∊ β i ⊠ a ∊ U) ⊸ 𝐅).
  rew (all_lb _ a). tautological.
Qed.

Lemma Dense_by_basis@{u}
  {X Y:set@{u}} `{@Topology@{u} Y NY}
  {Λ:Type@{u}} {β:Λ → 𝒫 Y}
  {NB:NeighborhoodBasis β}
  (f : X ⇾ Y) :
  (∀ y i, y ∊ β i ⊸ ∐ x, f x ∊ β i) → Dense f.
Proof. intros P. split; try exact _. apply dense_by_basis.
  intros y i. rew (P y i), <-aex_adj. intros x.
  rew <-(aex_ub _ (f x)). now simplify.
Qed.


(** A basis [β] of subsets of [X] generates a canonical neighborhood relation
    [x ⪽ N := ∐ i, x ∊ β i ⊠ β i ⊆ N], which trivially satisfies [NB] at
    every point. *)

Definition basis_neighborhood@{u} {I:Type@{u}} {X:set@{u}} (β:I → 𝒫 X) : Neighborhood@{u} X
  := set:(λ '(x, N) : X ⊗ 𝒫 X, ∐ i, x ∊ β i ⊠ β i ⊆ N).

Lemma basis_neighborhood_prop@{u} {I:Type@{u}} {X:set@{u}} (β:I → 𝒫 X)
  : NeighborhoodBasis (XN:=basis_neighborhood β) β.
Proof. now intros N. Qed.
#[global] Hint Extern 2 (NeighborhoodBasis (XN:=basis_neighborhood _) _)
  => simple notypeclasses refine (basis_neighborhood_prop _) : typeclass_instances.

Lemma interior_neighborhood_basis@{u} `{@Topology@{u} X NX} : NeighborhoodBasis (XN:=NX) interior.
Proof. intros x N. split.
+ rew <-(aex_ub _ N). now rew (aprod_true_r (interior_subset _)).
+ rew <-aex_adj. intros M.
  rew <-(idempotent_alt interior M) at 1.
  exact (top_isotony x (interior M) N).
Qed.
#[global] Hint Extern 100 (NeighborhoodBasis _) => notypeclasses refine interior_neighborhood_basis : typeclass_instances.

(** Topology from a basis.

    Given a neighborhood relation [⪽] presented by a basis [β : Λ → 𝒫 X]
    satisfying [NB] (the affine equivalence [x ⪽ N ⧟ ∐ i, x ∊ β i ⊠ β i ⊆ N])
    plus the three structural axioms [basis_inhabited], [basis_meet],
    [basis_open], the topology axioms follow.  The reflexivity axiom of
    the topology is automatic because the basis is a basis of subsets
    *containing* the point — no separate [basis_refl] hypothesis. *)

Section topology_by_basis.
  Universes u.
  Context `{XN:Neighborhood@{u} X} {Λ:Type@{u}} {β:Λ → 𝒫 X}
          {NB:NeighborhoodBasis β}.

  Context (Hnull : ∀ x, ∐ i, x ∊ β i)
          (Hbin  : ∀ x i j, x ∊ β i ⊠ x ∊ β j ⊸ ∐ k, x ∊ β k ⊠ β k ⊆ β i ⊓ β j).

  Lemma topology_by_basis: Topology X.
  Proof. split.
  + (* refl: x ⪽ U ⊸ x ∊ U *)
    intros x U. rew (NB x U), <-aex_adj; intros i.
    exact (subset_apply x (β i) U).
  + (* isotony *)
    exact neighborhood_basis_isotony.
  + (* nullary *)
    intros x. pose proof (Hnull x) as [i Hi].
    rew <-(neighborhood_basis_use x (full_subset X) i).
    simplify. exact (below_top _).
  + (* binary *)
    intros x U V. rew (NB x U), aex_frob_r, <-aex_adj; intros i.
    rew (NB x V), aex_frob_l, <-aex_adj; intros j.
    rew (NB x (U ⊓ V)).
    trans ((x ∊ β i ⊠ x ∊ β j) ⊠ (β i ⊆ U ⊠ β j ⊆ V)); [ tautological |].
    rew (Hbin x i j), aex_frob_r, <-aex_adj; intros k.
    rew <-(aex_ub _ k).
    rew (aprod_assoc _ _ _); apply aprod_proper_aimpl; [ easy |].
    rew (order_preserving (⊓) (β i, β j) (U, V) : β i ⊆ U ⊠ β j ⊆ V ⊸ _).
    now apply transitivity.
  + (* trans: x ⪽ U ⊸ x ⪽ {y | y ⪽ U} *)
    intros x U. rew (NB x U), <-aex_adj; intros i.
    rew (NB _ _), <-(aex_ub _ i). apply aprod_proper_aimpl; [ easy |]; clear x.
    change (β i ⊆ U ⊸ ∏ y, y ∊ β i ⊸ y ⪽ U).
    rew <-all_adj; intros y.
    rew (neighborhood_basis_open i y).
    rew <-(neighborhood_basis_isotony y (β i) U); tautological.
  Qed.
End topology_by_basis.

