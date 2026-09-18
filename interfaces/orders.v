Require Export interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.subset.
Require Import easy rewrite tactics.misc.

Local Notation "X 'ᵒᵖ'" := (order_op X) (at level 1, format "X 'ᵒᵖ'").

Record PreOrder X {Xle:Le X} : SProp :=
{ #[reversible=no] le_refl  :> Reflexive  (A:=X) (≤)
; #[reversible=no] le_trans :> Transitive (A:=X) (≤)
}.
Arguments le_refl {_ _ _} _.
Arguments le_trans {_ _ _} _ _ _.
Existing Class PreOrder.
Global Hint Extern 2 (Reflexive  (≤)) => simple notypeclasses refine le_refl : typeclass_instances.
Global Hint Extern 2 (Transitive (≤)) => simple notypeclasses refine le_trans : typeclass_instances.

Record WeakPoset (X:set) {Xle:Le X} : SProp :=
{ #[reversible=no] partial_order_preorder :> PreOrder X
; #[reversible=no] eq_le_sub :> Subrelation (A:=X∗X) (=) (≤)
; #[reversible=no] le_pseudo_antisym :> PseudoAntisymmetric (A:=X) (≤) (=)
}.
Existing Class WeakPoset.
Arguments eq_le_sub {X _ _} _.
Arguments le_pseudo_antisym {_ _ _} _ _.
Global Hint Extern 2 (Subrelation (=) (≤)) => simple notypeclasses refine eq_le_sub : typeclass_instances.
Global Hint Extern 2 (PseudoAntisymmetric (≤) _) => simple notypeclasses refine le_pseudo_antisym : typeclass_instances.
Global Hint Extern 10 (PseudoAntisymmetric _ (=)) => simple notypeclasses refine le_pseudo_antisym : typeclass_instances.

Lemma le_is_fun `{WeakPoset P} : @IsFun (P ⊗ P) Ω le.
Proof.
  enough (∀ x₁ x₂ y₁ y₂ : P, x₁ = x₂ ⊠ y₁ = y₂ ⊸ x₁ ≤ y₁ ⊸ x₂ ≤ y₂) as Q.
  * intros [x₁ y₁] [x₂ y₂]. change (x₁ = x₂ ⊠ y₁ = y₂ ⊸ x₁ ≤ y₁ ⧟ x₂ ≤ y₂).
    apply aand_intro; [ now apply Q |].
    rew [ (symmetry_iff (=) x₁ x₂) | (symmetry_iff (=) y₁ y₂) ]; now apply Q.
  * intros. rew <-(transitivity (≤) x₂ x₁ y₂), <-(transitivity (≤) x₁ y₁ y₂).
    rew (symmetry_iff (=) x₁ x₂).
    rew (subrelation (=) _).
    tautological.
Qed.
Canonical Structure le_fun `{WeakPoset P} : _ ⇾ _ := @func_make _ _ _ le_is_fun.

Lemma lt_is_fun `{WeakPoset P} : @IsFun (P ⊗ P) Ω lt.
Proof. exact (anot_fun ∘ le_fun ∘ tensor_swap _ _). Qed.
Canonical Structure lt_fun `{WeakPoset P} : _ ⇾ _ := @func_make _ _ _ lt_is_fun.


Record Poset (X:set) {Xle:Le X} : SProp :=
{ #[reversible=no] poset_weak_poset :> WeakPoset X
; #[reversible=no] le_antisym :> Antisymmetric (A:=X) (≤) (=)
}.
Existing Class Poset.
Arguments le_antisym {_ _ _} _ _.
Global Hint Extern 2 (Antisymmetric (≤) _) => simple notypeclasses refine le_antisym : typeclass_instances.
Global Hint Extern 10 (Antisymmetric _ (=)) => simple notypeclasses refine le_antisym : typeclass_instances.

SubClass StrongLe X {Xle:Le X} := @StronglyTransitive X (@le X Xle).
SubClass DecidableLe X {Xle:Le X} := @DecidableRelation (X∗X) (@le X Xle).
SubClass AffirmativeLe X {Xle:Le X}:= @AffirmativeRelation (X∗X) (@le X Xle).
SubClass RefutativeLe X {Xle:Le X} := @RefutativeRelation (X∗X) (@le X Xle).
Existing Class StrongLe.
Existing Class DecidableLe.
Existing Class AffirmativeLe.
Existing Class RefutativeLe.
Global Hint Extern 2 (StronglyTransitive (A:=?X) (≤)) => change (StrongLe X) : typeclass_instances.
Global Hint Extern 2 (DecidableRelation (A:=?X ∗ _) (≤)) => change (DecidableLe X) : typeclass_instances.
Global Hint Extern 2 (AffirmativeRelation (A:=?X ∗ _) (≤)) => change (AffirmativeLe X) : typeclass_instances.
Global Hint Extern 2 (RefutativeRelation (A:=?X ∗ _) (≤)) => change (RefutativeLe X) : typeclass_instances.

SubClass IsDecLe X {Xle:Le X} {d:@Dec (X∗X) (≤)} := @IsDec (X∗X) (≤) d.
Existing Class IsDecLe.
Global Hint Extern 2 (@IsDec (?X ∗ _) (@le _ ?Xle) ?d) => change (@IsDecLe X Xle d) : typeclass_instances.

Record StrongPoset (X:set) {Xle: Le X} : SProp :=
{ #[reversible=no] StrongPoset_poset :> Poset X
; #[reversible=no] StrongPoset_prop :> StrongLe X
}.
Record DecidableOrder (X:set) {Xle: Le X} : SProp :=
{ #[reversible=no] DecidableOrder_poset :> Poset X
; #[reversible=no] DecidableOrder_prop :> DecidableLe X
}.
Record AffirmativeOrder (X:set) {Xle: Le X} : SProp :=
{ #[reversible=no] AffirmativeOrder_poset :> Poset X
; #[reversible=no] AffirmativeOrder_prop :> AffirmativeLe X
}.
Record RefutativeOrder (X:set) {Xle: Le X} : SProp :=
{ #[reversible=no] RefutativeOrder_poset :> Poset X
; #[reversible=no] RefutativeOrder_prop :> RefutativeLe X
}.
Record TotalOrder (X:set) {Xle: Le X} : SProp :=
{ #[reversible=no] TotalOrder_poset :> Poset X
; #[reversible=no] TotalOrder_prop :> @TotalRelation  X (≤)
}.
Record LinearOrder (X:set) {Xle: Le X} : SProp :=
{ #[reversible=no] LinearOrder_poset :> Poset X
; #[reversible=no] LinearOrder_prop :> @PseudoTotalRelation  X (≤)
}.
Existing Class StrongPoset.
Existing Class DecidableOrder.
Existing Class AffirmativeOrder.
Existing Class RefutativeOrder.
Existing Class TotalOrder.
Existing Class LinearOrder.
Arguments StrongPoset_prop {_ _ _}.
Arguments DecidableOrder_prop {_ _ _}.
Arguments AffirmativeOrder_prop {_ _ _}.
Arguments RefutativeOrder_prop {_ _ _}.
Arguments TotalOrder_prop {_ _ _}.
Arguments LinearOrder_prop {_ _ _}.
(*
Global Hint Extern 2 (StronglyTransitive  (≤)) => simple notypeclasses refine StrongPoset_prop      : typeclass_instances.
Global Hint Extern 2 (DecidableRelation   (≤)) => simple notypeclasses refine DecidableOrder_prop   : typeclass_instances.
Global Hint Extern 2 (AffirmativeRelation (≤)) => simple notypeclasses refine AffirmativeOrder_prop : typeclass_instances.
Global Hint Extern 2 (RefutativeRelation  (≤)) => simple notypeclasses refine RefutativeOrder_prop  : typeclass_instances.
*)
Global Hint Extern 2 (TotalRelation       (≤)) => simple notypeclasses refine TotalOrder_prop       : typeclass_instances.
Global Hint Extern 2 (PseudoTotalRelation (≤)) => simple notypeclasses refine LinearOrder_prop      : typeclass_instances.


Inductive trich_t : Set := is_lt | is_eq | is_gt.
Class Trich (X:set) {R:Le X} := trich : X ∗ X → trich_t.
Record IsTrich (X:set) {R:Le X} {t:Trich X} : SProp :=
{ #[reversible=no] trich_linear :> LinearOrder X
;  trich_spec x y : match (trich (x, y)) with
  | is_lt => x < y
  | is_eq => x = y
  | is_gt => y < x
  end
}.
Existing Class IsTrich.
Arguments trich_spec {X _ _ _} _ _.



Section morphisms.
  Universes u.
  Record OrderMorphism (X:set@{u}) (Y:set@{u}) {Xle:Le X} {Yle:Le Y} : SProp :=
  { #[reversible=no] order_mor_X :> WeakPoset X
  ; order_mor_Y :  WeakPoset Y
  }.
  Existing Class OrderMorphism.

  Context {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} (f : X ⇾ Y).

  Record OrderPreserving : SProp :=
  { #[reversible=no] order_preserving_mor_X :> OrderMorphism X Y
  ; order_preserving (x y : X) : x ≤ y ⊸ f x ≤ f y
  }.
  Record OrderReflecting : SProp :=
  { #[reversible=no] order_reflecting_mor :> OrderMorphism X Y
  ; order_reflecting (x y : X) : f x ≤ f y ⊸ x ≤ y
  }.
  Record OrderEmbedding : SProp :=
  { #[reversible=no] order_embedding_preserving :> OrderPreserving
  ; #[reversible=no] order_embedding_reflecting :> OrderReflecting
  }.
  Existing Class OrderPreserving.
  Existing Class OrderReflecting.
  Existing Class OrderEmbedding.
  Global Arguments order_preserving {_} _ _.
  Global Arguments order_reflecting {_} _ _.
  Definition order_embedding `{!OrderEmbedding} (x y : X) : x ≤ y ⧟ f x ≤ f y
    := sprop.conj (order_preserving x y) (order_reflecting x y).
End morphisms.

Section morphisms_flip.
  Universes u.
  Context {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} (f : X ⇾ Y).

  Definition OrderPreservingFlip : SProp := @OrderPreserving X (Y ᵒᵖ) _ _ f.
  Definition OrderReflectingFlip : SProp := @OrderReflecting X (Y ᵒᵖ) _ _ f.
  Definition OrderEmbeddingFlip : SProp := @OrderEmbedding X (Y ᵒᵖ) _ _ f.
  Existing Class OrderPreservingFlip.
  Existing Class OrderReflectingFlip.
  Existing Class OrderEmbeddingFlip.

  Definition order_embedding_preserving_flip : OrderEmbeddingFlip → OrderPreservingFlip := @order_embedding_preserving X (Y ᵒᵖ) _ _ f.
  Definition order_embedding_reflecting_flip : OrderEmbeddingFlip → OrderReflectingFlip := @order_embedding_reflecting X (Y ᵒᵖ) _ _ f.
  Coercion order_embedding_preserving_flip : OrderEmbeddingFlip >-> OrderPreservingFlip.
  Coercion order_embedding_reflecting_flip : OrderEmbeddingFlip >-> OrderReflectingFlip.

  Definition order_preserving_flip {H:OrderPreservingFlip} : ∀ x y, x ≤ y ⊸ f y ≤ f x := @order_preserving _ _ _ _ _ H.
  Definition order_reflecting_flip {H:OrderReflectingFlip} : ∀ x y, f y ≤ f x ⊸ x ≤ y := @order_reflecting _ _ _ _ _ H.
  Definition order_embedding_flip  {H:OrderEmbeddingFlip}  : ∀ x y, x ≤ y ⧟ f y ≤ f x := @order_embedding _ _ _ _ _ H.
End morphisms_flip.


(** Lattices *)

Record UpDirected X {Xle:Le X} : SProp :=
{ #[reversible=no] UpDirected_preorder :> PreOrder X
; #[reversible=no] up_directed_inhabited :> Inhabited X
; up_directed (x y : X) : ∐ z, x ≤ z ⊠ y ≤ z
}.
Existing Class UpDirected.
Arguments up_directed_inhabited X {_ _}.
Arguments up_directed {_ _ _} _ _.

Definition DownDirected X `{Le X} : SProp := UpDirected (X ᵒᵖ).
Existing Class DownDirected.
Coercion down_directed_inhabited `{H:DownDirected X} : Inhabited X := up_directed_inhabited (X ᵒᵖ).
Definition down_directed `{H:DownDirected X} (x y : X) : ∐ z, z ≤ x ⊠ z ≤ y := up_directed (X:=X ᵒᵖ) x y.


Record MeetSemiLatticeOrder (L:set) `{Le L} `{Meet L} : SProp :=
{ #[reversible=no] meet_sl_poset :> WeakPoset L
; meet_lb_l (x y : L) : x ⊓ y ≤ x
; meet_lb_r (x y : L) : x ⊓ y ≤ y
; meet_glb (x y z : L) : z ≤ x ⊠ z ≤ y ⊸ z ≤ x ⊓ y
}.
Existing Class MeetSemiLatticeOrder.
Arguments meet_lb_l {L _ _ _} _ _.
Arguments meet_lb_r {L _ _ _} _ _.
Arguments meet_glb {L _ _ _} _ _ _.

Definition JoinSemiLatticeOrder (L:set) `{Le L} `{Join L} : SProp := MeetSemiLatticeOrder (L ᵒᵖ).
Existing Class JoinSemiLatticeOrder.
Definition join_ub_l `{H:JoinSemiLatticeOrder L} (x y : L) : x ≤ x ⊔ y := meet_lb_l (m:=H) x y.
Definition join_ub_r `{H:JoinSemiLatticeOrder L} (x y : L) : y ≤ x ⊔ y := meet_lb_r (m:=H) x y.
Definition join_lub `{H:JoinSemiLatticeOrder L} (x y z : L) : x ≤ z ⊠ y ≤ z ⊸ x ⊔ y ≤ z:= meet_glb (m:=H) x y z.

Record LatticeOrder (L:set) `{Le L} `{Meet L} `{Join L} : SProp :=
{ #[reversible=no] lattice_order_meet :> MeetSemiLatticeOrder L
; #[reversible=no] lattice_order_join :> JoinSemiLatticeOrder L
}.
Existing Class LatticeOrder.

Record BoundedMeetSemiLatticeOrder (L:set) `{Le L} `{Meet L} `{Top L} : SProp :=
{ #[reversible=no] bounded_meet_sl_order_meet :> MeetSemiLatticeOrder L
; below_top (x : L) : x ≤ ⊤
}.
Existing Class BoundedMeetSemiLatticeOrder.
Arguments below_top {L _ _ _ _} _.

Definition BoundedJoinSemiLatticeOrder (L:set) `{Le L} `{Join L} `{Bottom L} : SProp := BoundedMeetSemiLatticeOrder (L ᵒᵖ).
Existing Class BoundedJoinSemiLatticeOrder.
Definition above_bottom `{H:BoundedJoinSemiLatticeOrder L} (x : L) : ⊥ ≤ x := below_top (L:=L ᵒᵖ) x.

Record BoundedLatticeOrder (L:set) `{Le L} `{Meet L} `{Join L} `{Top L} `{Bottom L} : SProp :=
{ #[reversible=no] bounded_lattice_order_meet :> BoundedMeetSemiLatticeOrder L
; #[reversible=no] bounded_lattice_order_join :> BoundedJoinSemiLatticeOrder L
}.
Existing Class BoundedLatticeOrder.

#[global] Hint Extern 2 (apos (_ ≤ ⊤)) => simple notypeclasses refine (below_top _) : typeclass_instances.
#[global] Hint Extern 2 (apos (⊥ ≤ _)) => simple notypeclasses refine (above_bottom _) : typeclass_instances.

(** Subsets *)

Global Hint Extern 2 (Le AProp) => exact aimpl : typeclass_instances.
Global Hint Extern 2 (Le (set_T AProp_set)) => exact aimpl : typeclass_instances.

Definition UpSet {X:set} {Xle:Le X} (U : 𝒫 X) := OrderPreserving U.
Existing Class UpSet.
Definition up_closed {X Xle} U {H:@UpSet X Xle U} : ∀ x y, x ≤ y ⊸ x ∊ U ⊸ y ∊ U := order_preserving U.
Identity Coercion UpSet_OrderPreserving : UpSet >-> OrderPreserving.

Definition DownSet {X:set} {Xle:Le X} (U : 𝒫 X) : SProp := UpSet (X:=X ᵒᵖ) U.
Existing Class DownSet.
Definition down_closed {X Xle} U {H:@DownSet X Xle U} x y : x ≤ y ⊸ y ∊ U ⊸ x ∊ U := up_closed U (H:=H) y x.


Record LeastUpSet {X:set} {Xle:Le X} (U : 𝒫 X) : SProp :=
{ #[canonical=no, reversible=no] LeastUpSet_WeakPoset :> WeakPoset X
; least_upset x : x ∊ U ⧟ ∐ a:U, subset_pt a ≤ x
}.
Existing Class LeastUpSet.
Arguments least_upset {X Xle} U {_} x.

Definition LeastDownSet {X:set} {Xle:Le X} (U : 𝒫 X) : SProp := LeastUpSet (X:=X ᵒᵖ) U.
Existing Class LeastDownSet.
Definition least_downset {X Xle} U {H:@LeastDownSet X Xle U} x : x ∊ U ⧟ ∐ a:U, x ≤ subset_pt a := @least_upset _ _ _ H x.


(** Induced order on subsets when viewed as sets. *)
Global Hint Extern 2 (Le (set_T (subset_to_set (X:=?X) _))) => let t := get_instance (Le X) in refine (λ '(x, y), t (subset_pt x, subset_pt y)) : typeclass_instances.
Global Hint Extern 2 (Le (@subset_el ?X _)) => let t := get_instance (Le X) in refine (λ '(x, y), t (subset_pt x, subset_pt y)) : typeclass_instances.
Global Hint Extern 2 (Le (@powerset_el ?X _)) => let t := get_instance (Le (𝒫 X)) in refine (λ '(x, y), t (powerset_pt x, powerset_pt y)) : typeclass_instances.

(*
Record Filter {X:set} {Xle:Le X} (U : 𝒫 X) : SProp :=
{ #[reversible=no] Filter_UpSet :> LeastUpSet U
; #[reversible=no] Filter_directed :> DownDirected U
}.
Existing Class Filter.

Definition Ideal {X:set} {Xle:Le X} (U : 𝒫 X) : SProp := Filter (X:=X ᵒᵖ) U.
Existing Class Ideal.
Coercion Ideal_DownSet `{H:@Ideal X Xle U} : LeastDownSet U := Filter_UpSet (X:=X ᵒᵖ) U _.
Coercion Ideal_directed `{H:@Ideal X Xle U} : UpDirected U.  Proof. apply H. Defined.
*)

(** Directed subsets with full affine membership content *)

Record UpDirectedSubset {X:set} {Xle:Le X} (U : 𝒫 X) : SProp :=
{ #[reversible=no] UpDirectedSubset_preorder :> PreOrder X
; up_directed_subset_inhabited : ∐ x : X, x ∊ U
; up_directed_subset (x y : X) : x ∊ U ⊠ y ∊ U ⊸ ∐ z : X, z ∊ U ⊠ x ≤ z ⊠ y ≤ z
}.
Existing Class UpDirectedSubset.
Arguments up_directed_subset_inhabited {_ _} U {_}.
Arguments up_directed_subset {_ _} U {_} _ _.

Definition DownDirectedSubset {X:set} {Xle:Le X} (U : 𝒫 X) : SProp := UpDirectedSubset (X:=X ᵒᵖ) U.
Existing Class DownDirectedSubset.
Definition down_directed_subset_inhabited `{H:DownDirectedSubset (X:=X) U} : ∐ x : X, x ∊ U := up_directed_subset_inhabited U (u:=H).
Definition down_directed_subset `{H:DownDirectedSubset (X:=X) U} (x y : X) : x ∊ U ⊠ y ∊ U ⊸ ∐ z : X, z ∊ U ⊠ z ≤ x ⊠ z ≤ y := up_directed_subset U (u:=H) x y.

Record Filter {X:set} {Xle:Le X} (U : 𝒫 X) : SProp :=
{ #[reversible=no] Filter_UpSet :> UpSet U
; #[reversible=no] Filter_directed :> DownDirectedSubset U
}.
Existing Class Filter.

Definition Ideal {X:set} {Xle:Le X} (U : 𝒫 X) : SProp := Filter (X:=X ᵒᵖ) U.
Existing Class Ideal.
Coercion Ideal_DownSet `{H:@Ideal X Xle U} : DownSet U := Filter_UpSet (X:=X ᵒᵖ) U _.
Coercion Ideal_directed `{H:@Ideal X Xle U} : UpDirectedSubset U := Filter_directed (X:=X ᵒᵖ) U _.

Record FilterPresentation@{u} {X:set@{u}} {Xle:Le X} (U : 𝒫 X) {Λ:Type@{u}} (β:Λ → X) : SProp :=
{ #[canonical=no, reversible=no] filter_presentation_poset :> WeakPoset X
;  filter_presentation x : x ∊ U ⧟ ∐ i, β i ≤ x
}.
Existing Class FilterPresentation.
Arguments filter_presentation {_ _} U {_} β {_} x.

Class FilterBasis@{u} {X:set@{u}} {Xle:Le X} {Λ:Type@{u}} (β:Λ → X) : SProp :=
  filter_basis (x:X) : ∐ i, β i ≤ x.
Arguments filter_basis {_ _ _} β {_} x.

Definition IdealPresentation@{u} {X:set@{u}} {Xle:Le X} (U : 𝒫 X) {Λ:Type@{u}} (β:Λ → X) : SProp :=
  @FilterPresentation (X ᵒᵖ) _ U Λ β.
Definition IdealBasis@{u} {X:set@{u}} {Xle:Le X} {Λ:Type@{u}} (β:Λ → X) : SProp :=
  @FilterBasis (X ᵒᵖ) _ Λ β.
Existing Class IdealPresentation.
Existing Class IdealBasis.

Definition ideal_presentation `{H:@IdealPresentation X Xle U Λ β}
  : ∀ x, x ∊ U ⧟ ∐ i, x ≤ β i := @filter_presentation _ _ _ _ _ H.
Definition ideal_basis `{H:@IdealBasis X Xle Λ β}
  : ∀ x:X, ∐ i, x ≤ β i := H.
Arguments ideal_presentation {_ _} U {_} β {_} x.
Arguments ideal_basis {_ _ _} β {_} x.


