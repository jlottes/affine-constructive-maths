Require Import interfaces.set abstract_algebra.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.reflection_pair.
Require Import theory.set orders.orders orders.maps orders.subset.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices.
Require Import topology.base topology.interior.
Require Import reflection_pair.base.
Require Import easy rewrite simplify.

Local Open Scope topology_scope.
Local Open Scope subset_scope.

Import set.of_course_set_notation.
Import image_notation.

Section continuity.
  Universes u.
  Context {X Y:set@{u}}.
  
  Lemma continuity_alt f `{@Continuous X Y NX NY f} (U:𝒫 Y) : open U ⊸ open (f* U).
  Proof. change (open U ⊸ interior (f* U) = f* U). rew <-(le_antisym_iff _ _); simplify.
    change (open U ⊸ ∏ x : X, f x ∊ U ⊸ x ⪽ f* U).
    rew <-all_adj; intro x. rew <-(continuity f _ _), <-(open_nbrhood _ _). tautological.
  Qed.
  
  Lemma continuous_preimage_interior_aux `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ U, open U ⊸ open (f* U)) → ∀ U, f* (interior U) ⊆ interior (f* U) .
  Proof. intros Hf U.
    rew <-(aimpl_impl_pos (Hf (interior U)) _ : _ = _).
    rew <-(order_preserving interior _ _).
    now rew <-(order_preserving (preimage f) _ _).
  Qed.
  
  Lemma continuous_preimage_interior f `{@Continuous X Y NX NY f} :
    ∀ U, f* (interior U) ⊆ interior (f* U) .
  Proof. exact (continuous_preimage_interior_aux f (continuity_alt f)). Qed.
  
  Lemma alt_Build_Continuity `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ U, open U ⊸ open (f* U)) → Continuous f.
  Proof. intro Hf. split; try exact _. intros x N.
    exact (continuous_preimage_interior_aux f Hf N x).
  Qed.

  (** The interior-operator inclusion is the pointwise reading of the
      [continuity] field, so this converse is the constructor itself. *)
  Lemma alt_Build_Continuity_preimage_interior `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ U, f* (interior U) ⊆ interior (f* U)) → Continuous f.
  Proof. intros Hf. split; try exact _. intros x N. exact (Hf N x). Qed.

  Lemma continuity_closed f `{@Continuous X Y NX NY f} (U:𝒫 Y) : closed U ⊸ closed (f* U).
  Proof. rew <-(open_complement_closed _). exact (continuity_alt f _). Qed.

  Lemma alt_Build_Continuity_closed `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ U, closed U ⊸ closed (f* U)) → Continuous f.
  Proof. intros Hf. apply alt_Build_Continuity; intros U.
    rew <-(closed_complement_open _). exact (Hf _).
  Qed.
  
  Lemma continuous_preimage_closure f `{@Continuous X Y NX NY f} (U:𝒫 Y) :
    closure (f* U) ⊆  f* (closure U) .
  Proof. change ((interior (f* U) ᗮ) ᗮ ⊆ f* (interior U ᗮ) ᗮ).
    rew <-(order_reflecting_flip complement _ _).
    exact (continuous_preimage_interior f _).
  Qed.

  Lemma alt_Build_Continuity_preimage_closure `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ U, closure (f* U) ⊆ f* (closure U)) → Continuous f.
  Proof. intros Hf. apply alt_Build_Continuity_preimage_interior. intros U.
    rew <-(order_reflecting_flip complement _ _).
    exact (Hf (U ᗮ)).
  Qed.

  Lemma continuous_closure_unit f `{@Continuous X Y NX NY f} (U:𝒫 X)
    : closure U ⊆ f* (closure (f⁎ U)).
  Proof.
    rew <-(continuous_preimage_closure f (f⁎ U)).
    now rew <-(preimage_image_unit f U).
  Qed.

  Lemma continuous_image_closure f `{@Continuous X Y NX NY f} (U:𝒫 X)
    : f⁎ (closure U) ⊆ closure (f⁎ U).
  Proof. rew (image_preimage_adj f _ _). exact (continuous_closure_unit f _). Qed.

  Lemma continuous_closure_counit f `{@Continuous X Y NX NY f} (V:𝒫 Y)
    : f⁎ (closure (f* V)) ⊆ closure V.
  Proof. rew (image_preimage_adj f _ _). exact (continuous_preimage_closure f V). Qed.

  (** The universal-image conjugates: [∀.[f]] against interiors. *)
  Lemma continuous_interior_universal_image f `{@Continuous X Y NX NY f} (U:𝒫 X)
    : interior (∀.[f] U) ⊆ ∀.[f] (interior U).
  Proof. change ((closure (f⁎ (U ᗮ)))ᗮ ⊆ (f⁎ (closure (U ᗮ)))ᗮ).
    rew <-(order_reflecting_flip complement _ _).
    exact (continuous_image_closure f _).
  Qed.

  Lemma continuous_universal_image_unit f `{@Continuous X Y NX NY f} (V:𝒫 Y)
    : interior V ⊆ ∀.[f] (interior (f* V)).
  Proof. change ((closure (V ᗮ))ᗮ ⊆ (f⁎ (closure (f* (V ᗮ))))ᗮ).
    rew <-(order_reflecting_flip complement _ _).
    exact (continuous_closure_counit f _).
  Qed.

  Lemma continuous_universal_image_counit f `{@Continuous X Y NX NY f} (U:𝒫 X)
    : f* (interior (∀.[f] U)) ⊆ interior U.
  Proof. change ((f* (closure (f⁎ (U ᗮ))))ᗮ ⊆ (closure (U ᗮ))ᗮ).
    rew <-(order_reflecting_flip complement _ _).
    exact (continuous_closure_unit f _).
  Qed.

  Lemma alt_Build_Continuity_image_closure `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ U, f⁎ (closure U) ⊆ closure (f⁎ U)) → Continuous f.
  Proof. intros Hf. apply alt_Build_Continuity_closed. intros U.
    enough (closure (f* U) ⊆ f* (closure U)) as HU.
  + change (closed U ⊸ closure (f* U) = f* U). rew <-(le_antisym_iff _ _); simplify.
    rew HU, <-(order_preserving f* _ _). exact (eq_le _ _).
  + rew <-(image_preimage_adj f _ _), (Hf (f* U)).
    now rew (image_preimage_counit f U).
  Qed.
End continuity.


Section reflection.
  Universes u.
  Context {X Y:set@{u}}.

  Lemma reflection_universal_image_unit f `{@ContinuouslyReflecting X Y NX NY f} (A:𝒫 X)
    : interior A ⊆ f* (interior (∀.[f] A)).
  Proof. intros x. exact (cont_reflection f x A). Qed.

  (** The interior-operator inclusion is the pointwise reading of the
      [cont_reflection] field, so this converse is the constructor itself. *)
  Lemma alt_Build_ContinuouslyReflecting_universal_image `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ A:𝒫 X, interior A ⊆ f* (interior (∀.[f] A))) → ContinuouslyReflecting f.
  Proof. intros HA. split; try exact _. intros x A. exact (HA A x). Qed.

  (** The neighborhood-witness form of reflection: [∀.[f] U] is the witness. *)
  Lemma cont_reflection_ex f `{@ContinuousReflection X Y NX NY f} x U
    : x ⪽ U ⊸ ∐ V, f x ⪽ V ⊠ f* V ⊆ U.
  Proof. rew (cont_reflection f x U), <-(aex_ub _ (∀.[f] U)).
    rew (aiff_is_true (universal_image_counit f U)). now simplify.
  Qed.

  Lemma alt_Build_ContinuouslyReflecting_ex `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ x U, x ⪽ U ⊸ ∐ V, f x ⪽ V ⊠ f* V ⊆ U) → ContinuouslyReflecting f.
  Proof. intros P. split; try exact _. intros x U.
    rew (P x U), <-aex_adj; intros V.
    rew (preimage_universal_image_adj f U V). exact (top_isotony _ _ _).
  Qed.

  Lemma reflection_alt f `{@ContinuouslyReflecting X Y NX NY f} (U:𝒫 X)
    : open U ⊸ ∐ V:𝒫 Y, open V ⊠ U = f* V.
  Proof.
    rew <-(aex_ub _ (interior (∀.[f] U))); simplify.
    rew <-(le_antisym_iff _ _); apply aand_intro.
    + rew <-(reflection_universal_image_unit f U).
      change (interior U = U ⊸ U ⊆ interior U). rew <-(le_antisym_iff _ _). exact (aandr _ _).
    + rew (interior_subset (∀.[f] U)), (aiff_is_true (universal_image_counit f U)). now simplify.
  Qed.

  Lemma reflection_interior f `{@ContinuouslyReflecting X Y NX NY f} (U:𝒫 X)
    : ∐ V:𝒫 Y, open V ⊠ interior U = f* V.
  Proof. now rew <-(reflection_alt f _). Qed.

  Lemma alt_Build_ContinuouslyReflecting `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ U:𝒫 X, open U ⊸ ∐ V:𝒫 Y, open V ⊠ U = f* V) → ContinuouslyReflecting f.
  Proof. intros HU. apply alt_Build_ContinuouslyReflecting_universal_image. intros A.
    pose proof aimpl_impl_pos (HU (interior A)) _ as [V [HV HEq]].
    rew HEq, <-(order_preserving f* _ _), <-HV, <-(order_preserving interior _ _).
    rew <-(preimage_universal_image_adj f A V), <-HEq. exact (interior_subset A).
  Qed.

  Lemma reflection_closed f `{@ContinuouslyReflecting X Y NX NY f} (C:𝒫 X)
    : closed C ⊸ ∐ K:𝒫 Y, closed K ⊠ C = f* K.
  Proof. rew <-(open_complement_closed C).
    rew (reflection_alt f (C ᗮ)).
    rew <-aex_adj; intros V. rew <-(aex_ub _ (V ᗮ)).
    rew (closed_complement_open V).
    now rew <-(injective_iff complement C (f* V ᗮ)).
  Qed.

  Lemma reflection_closure f `{@ContinuouslyReflecting X Y NX NY f} (C:𝒫 X)
    : ∐ K:𝒫 Y, closed K ⊠ closure C = f* K.
  Proof. now rew <-(reflection_closed _ _). Qed.

  Lemma alt_Build_ContinuouslyReflecting_closed `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ C:𝒫 X, closed C ⊸ ∐ K:𝒫 Y, closed K ⊠ C = f* K) → ContinuouslyReflecting f.
  Proof. intros HC. apply alt_Build_ContinuouslyReflecting. intros U.
    rew <-(closed_complement_open U), (HC (U ᗮ)).
    rew <-aex_adj; intros K. rew <-(aex_ub _ (K ᗮ)).
    rew (open_complement_closed K).
    now rew <-(injective_iff complement U ((f* K) ᗮ)).
  Qed.

  Lemma reflection_preimage_closure f `{@ContinuouslyReflecting X Y NX NY f} (U:𝒫 X)
    : f* (closure (f⁎ U)) ⊆ closure U.
  Proof.
    pose proof reflection_closure f U as [K [HK HEq]].
    rew HEq.
    rew <-(order_preserving f* _ _).
    rew <-HK.
    rew <-(order_preserving closure _ _).
    rew (image_preimage_adj _ _ _).
    now rew <-HEq.
  Qed.

  Lemma alt_Build_ContinuouslyReflecting_preimage_closure `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ U, f* (closure (f⁎ U)) ⊆ closure U) → ContinuouslyReflecting f.
  Proof. intros Hf. apply alt_Build_ContinuouslyReflecting_closed. intros C.
    rew <-(aex_ub _ (closure (f⁎ C))).
    rew (aiff_is_true (closure_closed _)); simplify.
    enough (C ⊆ f* (closure (f⁎ C))) as H1.
  + rew <-(le_antisym_iff _ _). rew (aiff_is_true H1); simplify.
    rew (Hf C). exact (eq_le _ _).
  + rew <-(image_preimage_adj f _ _). exact (subset_closure _).
  Qed.
End reflection.

(** For a continuously initial map, the topology of [X] is computed in the
    codomain: interiors and closures are pushed forward, computed upstairs,
    and pulled back — the paired continuity/reflection inclusions meet in an
    equality, and each equality characterizes the class.  The open/closed-set
    characterizations pair the continuity form with the reflection form; no
    single internal biconditional is available (the refutation component of
    [(∐ V, open V ⊠ U = f* V) ⊸ open U] would demand refuting [U = f* V]
    against every open [V], which fails already for the identity map). *)
Section initiality.
  Universes u.
  Context {X Y:set@{u}}.

  Lemma alt_Build_ContinuouslyInitial `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ V:𝒫 Y, open V ⊸ open (f* V))
    → (∀ U:𝒫 X, open U ⊸ ∐ V:𝒫 Y, open V ⊠ U = f* V)
    → ContinuouslyInitial f.
  Proof. intros H1 H2. split.
  + now apply alt_Build_Continuity.
  + now apply alt_Build_ContinuouslyReflecting.
  Qed.

  Lemma alt_Build_ContinuouslyInitial_closed `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ K:𝒫 Y, closed K ⊸ closed (f* K))
    → (∀ C:𝒫 X, closed C ⊸ ∐ K:𝒫 Y, closed K ⊠ C = f* K)
    → ContinuouslyInitial f.
  Proof. intros H1 H2. split.
  + now apply alt_Build_Continuity_closed.
  + now apply alt_Build_ContinuouslyReflecting_closed.
  Qed.

  Lemma continuously_initial_interior f `{@ContinuouslyInitial X Y NX NY f} (A:𝒫 X)
    : interior A = f* (interior (∀.[f] A)).
  Proof. apply le_antisym; split.
  + exact (reflection_universal_image_unit f A).
  + exact (continuous_universal_image_counit f A).
  Qed.

  Lemma alt_Build_ContinuouslyInitial_interior `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ A:𝒫 X, interior A = f* (interior (∀.[f] A))) → ContinuouslyInitial f.
  Proof. intros HA. split.
  + apply alt_Build_Continuity_preimage_interior. intros V.
    rew (HA (f* V)).
    rew <-(order_preserving f* _ _).
    rew <-(order_preserving interior _ _).
    exact (universal_image_unit f V).
  + apply alt_Build_ContinuouslyReflecting_universal_image. intros A.
    now rew (HA A).
  Qed.

  Lemma continuously_initial_closure f `{@ContinuouslyInitial X Y NX NY f} (A:𝒫 X)
    : closure A = f* (closure (f⁎ A)).
  Proof. change ((interior (A ᗮ))ᗮ = (f* (interior (∀.[f] (A ᗮ))))ᗮ).
    now rew (continuously_initial_interior f (A ᗮ)).
  Qed.

  Lemma alt_Build_ContinuouslyInitial_closure `{@Topology X XN} `{@Topology Y YN} (f:X ⇾ Y) :
    (∀ A:𝒫 X, closure A = f* (closure (f⁎ A))) → ContinuouslyInitial f.
  Proof. intros HA. apply alt_Build_ContinuouslyInitial_interior.
    intros A. rew (injective_iff complement _ _). exact (HA (A ᗮ)).
  Qed.
End initiality.

Lemma cont_refl_factor@{u} {X Y Z:set@{u}}
  {NX:Neighborhood X} {NY:Neighborhood Y} {NZ:Neighborhood Z} (f: X ⇾ Y) (g: Y ⇾ Z)
  : Continuous g → ContinuouslyReflecting (g ∘ f) → ContinuouslyReflecting f.
Proof. intros Hg Hgf. apply alt_Build_ContinuouslyReflecting_universal_image. intros A.
  rew (reflection_universal_image_unit (g ∘ f) A), (universal_image_compose_alt f g A).
  change ((g ∘ f)* ?W) with (f* (g* W)).
  rew <-(order_preserving f* _ _), (continuous_preimage_interior g _), <-(order_preserving interior _ _).
  exact (universal_image_counit g _).
Qed.

Lemma cont_factor@{u} {X Y Z:set@{u}}
  {NX:Neighborhood X} {NY:Neighborhood Y} {NZ:Neighborhood Z} (f: X ⇾ Y) (g: Y ⇾ Z)
  : ContinuouslyReflecting g → Continuous (g ∘ f) → Continuous f.
Proof. intros Hg Hgf. apply alt_Build_Continuity_preimage_interior. intros N.
  rew (reflection_universal_image_unit g N).
  change (f* (g* ?W)) with ((g ∘ f)* W).
  rew (continuous_preimage_interior (g ∘ f) _), <-(order_preserving interior _ _).
  change ((g ∘ f)* ?W) with (f* (g* W)).
  rew <-(order_preserving f* _ _). exact (universal_image_counit g N).
Qed.


(** Abstract reflection pair instance *)

Inductive 𝐀𝐓𝐨𝐩 :=.

#[global] Hint Extern 0 (Fiber 𝐀𝐓𝐨𝐩) => exact Neighborhood : typeclass_instances.
#[global] Hint Extern 0 (ObjClass 𝐀𝐓𝐨𝐩) => exact @Topology : typeclass_instances.
#[global] Hint Extern 0 (HomClass 𝐀𝐓𝐨𝐩) => exact @Continuous_fun : typeclass_instances.
#[global] Hint Extern 0 (RflClass 𝐀𝐓𝐨𝐩) => exact @ContinuouslyReflecting_fun : typeclass_instances.
#[global] Hint Extern 0 (IniClass 𝐀𝐓𝐨𝐩) => exact @ContinuouslyInitial_fun : typeclass_instances.
#[global] Hint Extern 0 (EmbClass 𝐀𝐓𝐨𝐩) => exact @ContinuouslyEmbedding_fun : typeclass_instances.
#[global] Hint Extern 2 (Fib 𝐀𝐓𝐨𝐩 ?X) => change (Neighborhood X) : typeclass_instances.

Definition atop_classes@{u} : ReflectionPairClasses@{u} 𝐀𝐓𝐨𝐩.  Proof. now esplit. Defined.
#[global] Hint Extern 2 (ReflectionPairClasses 𝐀𝐓𝐨𝐩) => exact atop_classes : typeclass_instances.

Lemma atop_construct: Construct 𝐀𝐓𝐨𝐩.
Proof. split.
+ now change (∀ `{@Topology X NX}, Continuous (id_fun X)).
+ now change (∀ `{@Continuous X Y NX NY f}, Topology X).
+ now change (∀ `{@Continuous X Y NX NY f}, Topology Y).
+ now change (∀ X Y Z NX NY NZ f g, @Continuous X Y NX NY f → @Continuous Y Z NY NZ g
                                  → Continuous (g ∘ f)).
Qed.
#[global] Hint Extern 0 (Construct 𝐀𝐓𝐨𝐩) => exact atop_construct : typeclass_instances.

Lemma atop_rfl_construct: RflConstruct 𝐀𝐓𝐨𝐩.
Proof. split.
+ now change (∀ `{@Topology X NX}, ContinuouslyReflecting (id_fun X)).
+ now change (∀ `{@ContinuouslyReflecting X Y NX NY f}, Topology X).
+ now change (∀ `{@ContinuouslyReflecting X Y NX NY f}, Topology Y).
+ now change (∀ X Y Z NX NY NZ f g, @ContinuouslyReflecting X Y NX NY f → @ContinuouslyReflecting Y Z NY NZ g
                                  → ContinuouslyReflecting (g ∘ f)).
Qed.
#[global] Hint Extern 0 (RflConstruct 𝐀𝐓𝐨𝐩) => exact atop_rfl_construct : typeclass_instances.

Lemma atop_ini_spec : IniClassSpec 𝐀𝐓𝐨𝐩.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (IniClassSpec 𝐀𝐓𝐨𝐩) => exact atop_ini_spec : typeclass_instances.

Lemma atop_emb_spec : EmbClassSpec 𝐀𝐓𝐨𝐩.
Proof. hnf; intros; split; intros [??]; now split. Qed.
#[global] Hint Extern 0 (EmbClassSpec 𝐀𝐓𝐨𝐩) => exact atop_emb_spec : typeclass_instances.

Lemma atop_rfl_pair : ReflectionPair 𝐀𝐓𝐨𝐩.
Proof. esplit; try exact _.
+ change (∀ X Y Z NX NY NZ f g, @ContinuouslyReflecting Y Z NY NZ g → @Continuous X Z NX NZ (g ∘ f)
                            → @Continuous X Y NX NY f).
  intros. now apply (cont_factor f g).
+ change (∀ X Y Z NX NY NZ f g, @Continuous Y Z NY NZ g → @ContinuouslyReflecting X Z NX NZ (g ∘ f)
                            → @ContinuouslyReflecting X Y NX NY f).
  intros. now apply (cont_refl_factor f g).
Qed.
#[global] Hint Extern 0 (ReflectionPair 𝐀𝐓𝐨𝐩) => exact atop_rfl_pair : typeclass_instances.


(** Inverses flip classes *)

Local Open Scope fun_inv_scope.
Lemma invert_continuous `{@Continuous X Y NX NY f} `{!Inverse f, !Bijective f}
  : ContinuouslyReflecting f⁻¹.
Proof. exact (invert_hom (C:=𝐀𝐓𝐨𝐩) (f:=f)). Qed.
#[global] Hint Extern 4 (ContinuouslyReflecting _⁻¹) => simple notypeclasses refine invert_continuous : typeclass_instances.

Lemma invert_reflecting `{@ContinuouslyReflecting X Y NX NY f} `{!Inverse f, !Bijective f}
  : Continuous f⁻¹.
Proof. exact (invert_rfl (C:=𝐀𝐓𝐨𝐩) (f:=f)). Qed.
#[global] Hint Extern 4 (Continuous _⁻¹) => simple notypeclasses refine invert_reflecting : typeclass_instances.

Lemma invert_initial `{@ContinuouslyInitial X Y NX NY f} `{!Inverse f, !Bijective f}
  : ContinuouslyEmbedding (inverse f).
Proof. exact (invert_ini (C:=𝐀𝐓𝐨𝐩) (f:=f)). Qed.
#[global] Hint Extern 4 (ContinuouslyInitial _⁻¹) => simple notypeclasses refine invert_initial : typeclass_instances.
#[global] Hint Extern 4 (ContinuouslyEmbedding _⁻¹) => simple notypeclasses refine invert_initial : typeclass_instances.


(** The image of a dense map meets every neighborhood: the class-level,
    image-free counterpart of [dense_meets]. *)

Lemma Dense_meets `{@Topology Y YN} {X:set} (f:X ⇾ Y) `{!Dense f} (y:Y) (V:𝒫 Y) :
  y ⪽ V ⊸ ∐ x, f x ⪽ V.
Proof.
  rew (top_trans y V).
  rew (dense_meets (range f) _ y dense_range).
  rew <-aex_adj; intros a.
  change ( a ⪽ V ⊠ (∐ x, f x = a) ⊸ ∐ x : X, f x ⪽ V ).
  rew aex_frob_l. rew <-aex_adj; intros x.
  rew <-(aex_ub _ x). simplify.
  rew (symmetry (=) (f x) a).
  rew (aprod_com _ _).
  exact (equal_element {y0 : Y | y0 ⪽ V} a (f x)).
Qed.


(** The image of a dense subset under a continuous map with dense range is dense. *)
Lemma dense_image@{u} {X Y : set@{u}} {NX:Neighborhood X} {NY:Neighborhood Y}
  (f : X ⇾ Y) `{!Continuous f, !Dense f} (U:𝒫 X) : dense U → dense (f⁎ U).
Proof. intros HU.
  apply (above_top _).
  rew <-(idempotent_alt closure (f⁎ U)).
  rew <-(dense_range : closure (range f) = ⊤).
  rew <-(order_preserving closure _ _).
  rew (range_image f).
  rew <-(HU : closure U = ⊤).
  exact (continuous_image_closure f U).
Qed.

Lemma Dense_id `{@Topology X NX} : Dense (id_fun X).
Proof. split; try exact _. change (apos (closure (range (id_fun X)) = ⊤)).
  rew (range_image _), (image_id_alt _). exact closure_space.
Qed.
#[global] Hint Extern 2 (Dense (func_op (id_fun _))) => simple notypeclasses refine Dense_id : typeclass_instances.

(** Not a coercion: the [Topology Y] instance is not part of [WeaklySurjective]. *)
Lemma weakly_surjective_dense@{u} {A:Type@{u}} `{@Topology@{u} Y NY} (f:A → Y)
  `{!WeaklySurjective f} : Dense f.
Proof. split; try exact _. change (apos (closure (range f) = ⊤)).
  rew (weakly_surjective_alt f). exact closure_space.
Qed.

Lemma Dense_compose@{u} {X Y Z : set@{u}} {NY:Neighborhood Y} {NZ:Neighborhood Z}
  (f : X ⇾ Y) (g : Y ⇾ Z) `{!Dense f, !Continuous g, !Dense g} : Dense (g ∘ f).
Proof. split; try exact _.
  change (apos (closure (range (g ∘ f)) = ⊤)).
  rew (range_image _).
  rew <-(above_top _).
  rew <-(dense_range : closure (range g) = ⊤), (range_image _).
  rew <-(idempotent_alt closure ((g ∘ f)⁎ ⌈X⌉)).
  rew <-(order_preserving closure _ _).
  rew (image_compose_alt _ _ _).
  rew (image_preimage_adj _ _ _).
  rew <-(continuous_preimage_closure _ _).
  rew <-(preimage_image_unit _ _).
  rew <-(range_image _).
  now rew (dense_range : closure (range f) = ⊤).
Qed.
#[global] Hint Extern 2 (Dense (func_op (_ ∘ _))) => simple notypeclasses refine (Dense_compose _ _) : typeclass_instances.

Lemma Dense_factor_right@{u} {X Y Z : set@{u}} {NZ:Neighborhood Z}
  (f : X ⇾ Y) (g : Y ⇾ Z) `{!Dense (g ∘ f)} : Dense g.
Proof. split; try exact _.
  change (apos (closure (range g) = ⊤)).
  rew <-(above_top _), (range_image _).
  rew <-(dense_range : closure (range (g ∘ f)) = ⊤).
  rew <-(order_preserving closure _ _).
  rew (range_image _), (image_compose_alt _ _ _).
  rew <-(order_preserving (g⁎) _ _).
  exact (below_top _).
Qed.

Lemma Dense_factor_left@{u} {X Y Z:set@{u}} {NX:Neighborhood X} {NY:Neighborhood Y} {NZ:Neighborhood Z}
  (f: X ⇾ Y) (g: Y ⇾ Z) `{!Dense (g ∘ f)} `{!ContinuouslyReflecting g} : Dense f.
Proof. split; try exact _.
  apply (above_top _).
  rew <-(reflection_preimage_closure g (range f)).
  rew (range_image f), <-(image_compose_alt f g ⊤), <-(range_image (g ∘ f)).
  rew (dense_range : closure (range (g ∘ f)) = ⊤).
  now rew (preserves_top g*).
Qed.


Lemma cont_equal_on_dense `{@Continuous X Y NX NY f} `{@Continuous X Y NX NY g}
  `{!Hausdorff Y} (W:𝒫 X) : dense W → (∏ x, of_course (x ∊ W) ⊸ f x = g x) ⧟ f = g.
Proof. intros HW. split.
+ change (f = g) with (∏ x, f x = g x); rew <-all_adj; intros x.
  rew <-(hausdorff (f x) (g x)). rew <-all_adj; intros N. rew <-all_adj; intros M.
  rew (continuity f x N), (continuity g x M).
  rew (top_binary_additivity x (f* N) (g* M)).
  rew (dense_meets W _ x HW). clear x.
  rew <-(aprod_adj _ _ _), (aprod_com _ _), (aprod_adj _ _ _).
  apply affirmative_aimpl.
  change ((∐ x : X, (f x ∊ N ∧ g x ∊ M) ⊠ x ∊ W) → (∏ x : X, of_course (x ∊ W) ⊸ f x = g x) ⊸ ∐ z : Y, z ∊ N ⊠ z ∊ M).
  intros [x [[elfx elgx] xW]].
  rew [(all_lb _ x) | <-(aex_ub _ (g x))]. simplify.
  rew <-(equal_element N (f x) (g x)). now simplify.
+ change (f = g) with (∏ x, f x = g x); rew <-all_adj; intros x.
  rew (all_lb _ x). tautological.
Qed.
Arguments cont_equal_on_dense {X Y NX NY} f {_} g {_ _} W _.


Lemma cont_dense_epi@{u} `{@Continuous@{u} X Y NX NY f} `{@Continuous@{u} X Y NX NY g}
  `{!Hausdorff Y} {Z:set@{u}} (e:Z ⇾ X) {He:Dense e} : f ∘ e = g ∘ e ⧟ f = g.
Proof. split.
+ rew <-(cont_equal_on_dense f g (range e) dense_range), <-all_adj; intros x.
  rew <-(aprod_adj _ _ _), (aprod_com _ _), (aprod_adj _ _ _).
  apply affirmative_aimpl. intros [z Ez].
  change ((∏ z : Z, f (e z) = g (e z)) ⊸ f x = g x).
  rew (all_lb _ z). now rew Ez.
+ exact (is_fun (∘ e) _ _).
Qed.
Arguments cont_dense_epi {_ _ _ _} f {_} g {_ _ _} e {_}.


