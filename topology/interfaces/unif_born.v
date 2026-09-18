Require Import sprop srelations rewrite orders.filters easy orders.subset.
Require Export topology.interfaces.uniform topology.interfaces.bornology.

(** Uniform spaces carrying a bornology, with no axioms connecting the two
    structures — the fiber product Unif ×_Set PreBorn over the carrier.
    The WCUnif and BUnif flavors refine this chassis with connecting axioms
    (see doc/wcunif.md and the sketches in interfaces/bornology.v). *)

Record UnifBornSpace X {Φ:Uniformity X} {𝒜:Bornology X} : SProp :=
{ #[canonical=no, reversible=no] unif_born_unif    :> UniformSpace X
; #[canonical=no, reversible=no] unif_born_born :> BornologicalSpace X
}.
Existing Class UnifBornSpace.

#[global] Hint Extern 10 (UnifBornSpace _) => simple notypeclasses refine (Build_UnifBornSpace _ _ _) : typeclass_instances.


(** Axioms connecting the uniformity and bornology structures *)
Import thicken_notation.
Import tensor_map_notation.
Import image_notation.
Local Open Scope topology_scope.

(*
(** THESE ARE BUGGED. *)

Class BornologicallyDeterminedUniformity X {Φ:Uniformity X} {𝒜:Bornology X} : SProp :=
  bunif_i (U:𝒫 (X ⊗ X)) : (∀ (M:𝒜), ∐ (V:Φ), powerset_pt V ⊓ (M ⊗ M) ⊆ U) → U ∊ Φ.

Class UniformlyClosedBornology X {Φ:Uniformity X} {𝒜:Bornology X} : SProp :=
  bunif_ii (M:𝒫 X) : (∀ (U:Φ), ∐ (M':𝒜), M ⊆ U.[powerset_pt M']) → M ∊ 𝒜.
*)

Class UniformlyOpenBornology X {Φ:Uniformity X} {𝒜:Bornology X} : SProp :=
  wcunif_thicken (A:𝒜) : ∐ (U:Φ), U.[powerset_pt A] ∊ 𝒜.
Arguments wcunif_thicken X {_ _ _} A.

Record WCUnifSpace  X {Φ:Uniformity X} {𝒜:Bornology X} : SProp :=
{ #[canonical=no, reversible=no] wcunif_unif_born :> UnifBornSpace X
; #[canonical=no, reversible=no] wcunif_unif_open_born :> UniformlyOpenBornology X
}.
Existing Class WCUnifSpace.

(** Regular WCUnif spaces: WCUnif plus the two cover-form decision axioms —
    [UniformRegularity] (inner witness, filter variance) and
    [BornologyRegularity] (outer witness, ideal variance).  Bundled through
    the [Regular*Space] records so all coercion paths come for free. *)
Record RegularWCUnifSpace X {Φ:Uniformity X} {𝒜:Bornology X} : SProp :=
{ #[canonical=no, reversible=no] regular_wcunif_wc           :> WCUnifSpace X
; #[canonical=no, reversible=no] regular_wcunif_regular_unif :> RegularUniformSpace X
; #[canonical=no, reversible=no] regular_wcunif_regular_born :> RegularBornologicalSpace X
}.
Existing Class RegularWCUnifSpace.

(** The well-containment relation (classical [⊂⊂]): bounded, and uniformly
    below.  [K ∊ 𝒜] is the compactness leg (precompactness, at the precompact
    bornology); [K ◁ S] is the uniform-neighborhood leg. *)
Definition well_contained `{Φ:Uniformity X} {𝒜:Bornology X}
  := { '(K, S) : 𝒜 ⊗ 𝒫 X | powerset_pt K ◁ S }.
Notation "K ⋐ S" := (func_op well_contained (K, S)) (at level 70, no associativity) : topology_scope.

(** Product UnifBorn certificates: a uniformity and a bornology on the product
    carrier that jointly realize the canonical product UnifBorn structure.  Each
    bundles the uniform-side and bornology-side product certificates; the Build
    hint splits resolution into the two halves, found by their own _correct
    hints (as UnifBornSpace splits into UniformSpace + BornologicalSpace). *)

Record TensorProductUnifBorn@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}
    (Ξ:Uniformity (X ⊗ Y)) (𝒞:Bornology (X ⊗ Y)) : SProp :=
{ #[canonical=no, reversible=no] tensor_product_unif_born_unif :> TensorProductUniformity Φ Ψ Ξ
; #[canonical=no, reversible=no] tensor_product_unif_born_born :> TensorProductBornology 𝒜 ℬ 𝒞
}.
Existing Class TensorProductUnifBorn.

#[global] Hint Extern 10 (TensorProductUnifBorn _ _) => simple notypeclasses refine (Build_TensorProductUnifBorn _ _ _ _) : typeclass_instances.

Record CartesianProductUnifBorn@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}
    (Ξ:Uniformity (X × Y)) (𝒞:Bornology (X × Y)) : SProp :=
{ #[canonical=no, reversible=no] cartesian_product_unif_born_unif :> CartesianProductUniformity Φ Ψ Ξ
; #[canonical=no, reversible=no] cartesian_product_unif_born_born :> CartesianProductBornology 𝒜 ℬ 𝒞
}.
Existing Class CartesianProductUnifBorn.

#[global] Hint Extern 10 (CartesianProductUnifBorn _ _) => simple notypeclasses refine (Build_CartesianProductUnifBorn _ _ _ _) : typeclass_instances.

(** Morphism flavors. Each leg keeps its own record so that mixed variants
    (e.g. uniformly initial but only forward-bornological, as for open
    immersions) remain expressible; these bundles are the common diagonals. *)

Record UnifBornMorphism@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] unif_born_mor_cont :> UniformlyContinuous f
; #[canonical=no, reversible=no] unif_born_mor_born :> Bornological f
}.
Existing Class UnifBornMorphism.

Record UnifBornReflecting@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] unif_born_refl_ufm  :> UniformlyReflecting f
; #[canonical=no, reversible=no] unif_born_refl_born :> BornologyReflecting f
}.
Existing Class UnifBornReflecting.

Record UnifBornInitial@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] unif_born_init_mor  :> UnifBornMorphism f
; #[canonical=no, reversible=no] unif_born_init_refl :> UnifBornReflecting f
}.
Existing Class UnifBornInitial.

Record UnifBornEmbedding@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] unif_born_emb_initial :> UnifBornInitial f
; #[canonical=no, reversible=no] unif_born_emb_inj     :> Injective f
}.
Existing Class UnifBornEmbedding.


(** Locally uniformly continuous / reflecting. *)

Local Abbreviation π₁ := (tensor_proj1 _ _).

Class LocalUniformContinuity@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} (f:X ⇾ Y) : SProp :=
  local_uniform_continuity (K:𝒜) (W:Ψ) : ∐ U:Φ, π₁* K ⊓ powerset_pt U ⊆ ⟨f,f⟩* W.
Arguments local_uniform_continuity {_ _ _ _ _} f {_} K W.

Class LocalUniformReflection@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
  local_uniform_reflection (L:ℬ) (U:Φ) : ∐ W:Ψ, ⟨f,f⟩* (π₁* L ⊓ powerset_pt W) ⊆ U.
Arguments local_uniform_reflection {_ _ _ _ _} f {_} L U.

Record LocallyUniformlyContinuous@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] locally_uc_X :> UnifBornSpace X
; #[canonical=no] locally_uc_Y : UniformSpace Y
; #[canonical=no, reversible=no] locally_uc_prop :> LocalUniformContinuity f
}.
Existing Class LocallyUniformlyContinuous.

Record LocallyUniformlyReflecting@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] locally_ur_X :> UniformSpace X
; #[canonical=no] locally_ur_Y : UnifBornSpace Y
; #[canonical=no, reversible=no] locally_ur_prop :> LocalUniformReflection f
}.
Existing Class LocallyUniformlyReflecting.

Section locally_unif_born.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y).

  Record LocallyUnifBorn : SProp :=
  { #[canonical=no, reversible=no] locally_ub_uc :> LocallyUniformlyContinuous f
  ; #[canonical=no, reversible=no] locally_ub_born :> Bornological f
  }.
  Existing Class LocallyUnifBorn.

  Record LocallyUnifBornReflecting : SProp :=
  { #[canonical=no, reversible=no] locally_ubr_ur :> LocallyUniformlyReflecting f
  ; #[canonical=no, reversible=no] locally_ubr_born :> BornologyReflecting f
  }.
  Existing Class LocallyUnifBornReflecting.
  
  Record LocallyUnifBornInitial : SProp :=
  { #[canonical=no, reversible=no] locally_ubi_ubc :> LocallyUnifBorn
  ; #[canonical=no, reversible=no] locally_ubi_ubr :> LocallyUnifBornReflecting
  }.
  Existing Class LocallyUnifBornInitial.

  Record LocallyUnifBornEmbedding : SProp :=
  { #[canonical=no, reversible=no] locally_ube_ubi :> LocallyUnifBornInitial
  ; #[canonical=no, reversible=no] locally_ube_inj :> Injective f
  }.
  Existing Class LocallyUnifBornEmbedding.
  
  (** Restriction to WCUnifSpace domains *)
  Record WCUnifMorphism : SProp :=
  { #[canonical=no, reversible=no] wcunif_mor_X :> WCUnifSpace X
  ; wcunif_mor_Y : WCUnifSpace Y
  ; #[canonical=no, reversible=no] wcunif_mor_lub :> LocallyUnifBorn
  }.
  Existing Class WCUnifMorphism.

  Record WCUnifReflecting : SProp :=
  { #[canonical=no, reversible=no] wcunif_rfl_X :> WCUnifSpace X
  ; #[canonical=no] wcunif_rfl_Y : WCUnifSpace Y
  ; #[canonical=no, reversible=no] wcunif_rfl_lubr :> LocallyUnifBornReflecting
  }.
  Existing Class WCUnifReflecting.
  
  Record WCUnifInitial : SProp :=
  { #[canonical=no, reversible=no] wcunif_ini_mor :> WCUnifMorphism
  ; #[canonical=no, reversible=no] wcunif_ini_rfl :> WCUnifReflecting
  }.
  Existing Class WCUnifInitial.

  Record WCUnifEmbedding : SProp :=
  { #[canonical=no, reversible=no] wcunif_emb_ini :> WCUnifInitial
  ; #[canonical=no, reversible=no] wcunif_emb_inj :> Injective f
  }.
  Existing Class WCUnifEmbedding.  
End locally_unif_born.

Lemma locally_ub_Y `{H:@LocallyUnifBorn X Y Φ Ψ 𝒜 ℬ f} : UnifBornSpace Y.
Proof. split; apply H. Qed.

Coercion locally_unif_born_initial_born_initial `{@LocallyUnifBornInitial X Y Φ Ψ 𝒜 ℬ f} : BornologyInitial f.
Proof. now split. Qed.

Coercion wcunif_ini_lub_ini  `{@WCUnifInitial X Y Φ Ψ 𝒜 ℬ f} : LocallyUnifBornInitial f.
Proof. now split. Qed.

Coercion wcunif_emb_lub_emb  `{@WCUnifEmbedding X Y Φ Ψ 𝒜 ℬ f} : LocallyUnifBornEmbedding f.
Proof. now split. Qed.

(** Local completeness *)
Class LocalCompletionReflect@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}
  (ι:X ⇾ Y) := local_completion_reflect_initial `{@WCUnifInitial X Z Φ Ξ 𝒜 𝒵 f, !Dense f} : Z ⇾ Y.
Arguments local_completion_reflect_initial {X Y Φ Ψ 𝒜 ℬ} ι {_ Z Ξ 𝒵} f {_ _}.

Definition LocalCompleteInverse@{u} (X:set@{u}) {Φ:Uniformity X} {𝒜:Bornology X} := LocalCompletionReflect (id_fun X).
Existing Class LocalCompleteInverse.
Identity Coercion LocalCompleteInverse_Reflect : LocalCompleteInverse >-> LocalCompletionReflect.
#[global] Hint Extern 4 (@LocalCompletionReflect ?X _ ?Φ _ ?𝒜 _ (id_fun _)) => change (@LocalCompleteInverse X Φ 𝒜) : typeclass_instances.

Class LocalCompletion@{u} `{@LocalCompletionReflect@{u} X Y Φ Ψ 𝒜 ℬ ι} : SProp :=
{ local_completion_separated : SeparatedUniformSpace Y
; local_completion_initial : WCUnifInitial ι
; local_completion_dense   : Dense ι
; local_completion_reflect_initial_mor `{@WCUnifInitial X Z Φ Ξ 𝒜 𝒵 f, !Dense f}
  : WCUnifMorphism (local_completion_reflect_initial ι f)
; local_completion_reflect_initial_spec `{@WCUnifInitial X Z Φ Ξ 𝒜 𝒵 f, !Dense f}
    : local_completion_reflect_initial ι f ∘ f = ι
}.
Arguments LocalCompletion {X Y Φ Ψ 𝒜 ℬ} ι {_}.
Arguments local_completion_reflect_initial_spec {X Y Φ Ψ 𝒜 ℬ} ι {_ _} {Z Ξ 𝒵} f {_ _}.
Coercion local_completion_separated : LocalCompletion >-> SeparatedUniformSpace.
Coercion local_completion_initial : LocalCompletion >-> WCUnifInitial.
Coercion local_completion_dense : LocalCompletion >-> Dense.
#[global] Hint Extern 2 (WCUnifMorphism             (local_completion_reflect_initial _ _)) => simple notypeclasses refine local_completion_reflect_initial_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (local_completion_reflect_initial _ _)) => simple notypeclasses refine local_completion_reflect_initial_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (local_completion_reflect_initial _ _)) => simple notypeclasses refine local_completion_reflect_initial_mor : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (local_completion_reflect_initial _ _)) => simple notypeclasses refine local_completion_reflect_initial_mor : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (local_completion_reflect_initial _ _)) => simple notypeclasses refine local_completion_reflect_initial_mor : typeclass_instances.

Definition LocallyComplete X `{Li:@LocalCompleteInverse X Φ 𝒜} := LocalCompletion (id_fun X).
Existing Class LocallyComplete.
#[global] Hint Extern 4 (@LocalCompletion ?X _ ?Φ _ ?𝒜 _ (id_fun _) ?i) => change (@LocallyComplete X Φ 𝒜 i) : typeclass_instances.


#[global] Hint Extern 10 (UniformSpace ?Y) =>
  match goal with
  | H : UnifBornMorphism (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UnifBornInitial (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UnifBornEmbedding (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UnifBornReflecting (Y:=Y) _ |- _ => exact (ufm_reflecting_Y _ H)
  | H : LocallyUniformlyContinuous (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : LocallyUniformlyReflecting (Y:=Y) _ |- _ => exact (locally_ur_Y _ H)
  | H : LocallyUnifBorn (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : LocallyUnifBornReflecting (Y:=Y) _ |- _ => exact (locally_ur_Y _ H)
  | H : LocallyUnifBornInitial (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : LocallyUnifBornEmbedding (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : WCUnifMorphism (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : WCUnifReflecting (Y:=Y) _ |- _ => exact (wcunif_rfl_Y _ H)
  | H : WCUnifInitial (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : WCUnifEmbedding (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  end : typeclass_instances.

#[global] Hint Extern 10 (Topology ?Y) =>
  match goal with
  | H : UnifBornMorphism (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UnifBornInitial (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UnifBornEmbedding (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UnifBornReflecting (Y:=Y) _ |- _ => exact (ufm_reflecting_Y _ H)
  | H : LocallyUniformlyContinuous (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : LocallyUniformlyReflecting (Y:=Y) _ |- _ => exact (unif_born_unif _ (locally_ur_Y _ H))
  | H : LocallyUnifBorn (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : LocallyUnifBornReflecting (Y:=Y) _ |- _ => exact (unif_born_unif _ (locally_ur_Y _ H))
  | H : LocallyUnifBornInitial (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : LocallyUnifBornEmbedding (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : WCUnifMorphism (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : WCUnifReflecting (Y:=Y) _ |- _ => exact (unif_born_unif _ (locally_ur_Y _ H))
  | H : WCUnifInitial (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  | H : WCUnifEmbedding (Y:=Y) _ |- _ => exact (locally_uc_Y _ H)
  end : typeclass_instances.

#[global] Hint Extern 10 (BornologicalSpace ?Y) =>
  match goal with
  | H : UnifBornMorphism (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : UnifBornInitial (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : UnifBornEmbedding (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : UnifBornReflecting (Y:=Y) _ |- _ => exact (born_refl_Y _ H)
  | H : LocallyUniformlyReflecting (Y:=Y) _ |- _ => exact (locally_ur_Y _ H)
  | H : LocallyUnifBorn (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : LocallyUnifBornReflecting (Y:=Y) _ |- _ => exact (born_refl_Y _ H)
  | H : LocallyUnifBornInitial (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : LocallyUnifBornEmbedding (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : WCUnifMorphism (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : WCUnifReflecting (Y:=Y) _ |- _ => exact (wcunif_rfl_Y _ H)
  | H : WCUnifInitial (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : WCUnifEmbedding (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  end : typeclass_instances.

#[global] Hint Extern 10 (UnifBornSpace ?Y) =>
  match goal with
  | H : LocallyUnifBorn (Y:=Y) _ |- _ => exact (locally_ub_Y (H:=H))
  | H : LocallyUniformlyReflecting (Y:=Y) _ |- _ => exact (locally_ur_Y _ H)
  | H : LocallyUnifBornReflecting (Y:=Y) _ |- _ => exact (locally_ur_Y _ H)
  | H : LocallyUnifBornInitial (Y:=Y) _ |- _ => exact (locally_ur_Y _ H)
  | H : LocallyUnifBornEmbedding (Y:=Y) _ |- _ => exact (locally_ur_Y _ H)
  | H : WCUnifMorphism (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : WCUnifReflecting (Y:=Y) _ |- _ => exact (wcunif_rfl_Y _ H)
  | H : WCUnifInitial (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : WCUnifEmbedding (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  end : typeclass_instances.

#[global] Hint Extern 10 (WCUnifSpace ?Y) =>
  match goal with
  | H : WCUnifMorphism (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : WCUnifReflecting (Y:=Y) _ |- _ => exact (wcunif_rfl_Y _ H)
  | H : WCUnifInitial (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : WCUnifEmbedding (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  | H : LocalCompletion (Y:=Y) _ |- _ => exact (wcunif_mor_Y _ H)
  end : typeclass_instances.

