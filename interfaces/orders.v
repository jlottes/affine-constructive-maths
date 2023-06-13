Require Export interfaces.set algebra_notation.
Require Import logic.aprop relations.

Local Notation "X 'ᵒᵖ'" := (order_op X) (at level 1, format "X 'ᵒᵖ'").
Global Hint Extern 2 (Le (set_T (?X ᵒᵖ))) => simple notypeclasses refine (flip (@le X _)) : typeclass_instances.

Record PreOrder X {Xle:Le X} : SProp :=
{ le_refl  :> Reflexive  (A:=X) (≤)
; le_trans :> Transitive (A:=X) (≤)
}.
Arguments le_refl {_ _ _} _.
Arguments le_trans {_ _ _} _ _ _.
Existing Class PreOrder.
Global Hint Extern 2 (Reflexive  (≤)) => simple notypeclasses refine le_refl : typeclass_instances.
Global Hint Extern 2 (Transitive (≤)) => simple notypeclasses refine le_trans : typeclass_instances.

Record WeakPoset (X:set) {Xle:Le X} : SProp :=
{ partial_order_preorder :> PreOrder X
; eq_le :> Subrelation (A:=X) (=) (≤)
; le_pseudo_antisym :> PseudoAntisymmetric (A:=X) (≤) (=)
}.
Existing Class WeakPoset.
Arguments eq_le {X _ _} _ _.
Arguments le_pseudo_antisym {_ _ _} _ _.
Global Hint Extern 2 (Subrelation (=) (≤)) => simple notypeclasses refine eq_le : typeclass_instances.
Global Hint Extern 2 (PseudoAntisymmetric (≤) _) => simple notypeclasses refine le_pseudo_antisym : typeclass_instances.
Global Hint Extern 10 (PseudoAntisymmetric _ (=)) => simple notypeclasses refine le_pseudo_antisym : typeclass_instances.

Record Poset (X:set) {Xle:Le X} : SProp :=
{ poset_weak_poset :> WeakPoset X
; le_antisym :> Antisymmetric (A:=X) (≤) (=)
}.
Existing Class Poset.
Arguments le_antisym {_ _ _} _ _.
Global Hint Extern 2 (Antisymmetric (≤) _) => simple notypeclasses refine le_antisym : typeclass_instances.
Global Hint Extern 10 (Antisymmetric _ (=)) => simple notypeclasses refine le_antisym : typeclass_instances.

Record StrongPoset (X:set) {Xle: Le X} : SProp :=
{ StrongPoset_poset :> Poset X
; StrongPoset_prop :> @StronglyTransitive  X (≤)
}.
Record DecidableOrder (X:set) {Xle: Le X} : SProp :=
{ DecidableOrder_poset :> Poset X
; DecidableOrder_prop :> @DecidableRelation  X (≤)
}.
Record AffirmativeOrder (X:set) {Xle: Le X} : SProp :=
{ AffirmativeOrder_poset :> Poset X
; AffirmativeOrder_prop :> @AffirmativeRelation  X (≤)
}.
Record RefutativeOrder (X:set) {Xle: Le X} : SProp :=
{ RefutativeOrder_poset :> Poset X
; RefutativeOrder_prop :> @RefutativeRelation  X (≤)
}.
Record TotalOrder (X:set) {Xle: Le X} : SProp :=
{ TotalOrder_poset :> Poset X
; TotalOrder_prop :> @TotalRelation  X (≤)
}.
Record LinearOrder (X:set) {Xle: Le X} : SProp :=
{ LinearOrder_poset :> Poset X
; LinearOrder_prop :> @PseudoTotalRelation  X (≤)
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
Global Hint Extern 2 (StronglyTransitive  (≤)) => simple notypeclasses refine StrongPoset_prop      : typeclass_instances.
Global Hint Extern 2 (DecidableRelation   (≤)) => simple notypeclasses refine DecidableOrder_prop   : typeclass_instances.
Global Hint Extern 2 (AffirmativeRelation (≤)) => simple notypeclasses refine AffirmativeOrder_prop : typeclass_instances.
Global Hint Extern 2 (RefutativeRelation  (≤)) => simple notypeclasses refine RefutativeOrder_prop  : typeclass_instances.
Global Hint Extern 2 (TotalRelation       (≤)) => simple notypeclasses refine TotalOrder_prop       : typeclass_instances.
Global Hint Extern 2 (PseudoTotalRelation (≤)) => simple notypeclasses refine LinearOrder_prop      : typeclass_instances.


Section morphisms.
  Universes i.
  Record OrderMorphism (X:set@{i}) (Y:set@{i}) {Xle:Le X} {Yle:Le Y} : SProp :=
  { order_mor_X :> WeakPoset X
  ; order_mor_Y :  WeakPoset Y
  }.
  Existing Class OrderMorphism.

  Context {X Y:set@{i}} {Xle:Le X} {Yle:Le Y} (f : X ⇾ Y).

  Record OrderPreserving : SProp :=
  { order_preserving_mor_X :> OrderMorphism X Y
  ; order_preserving (x y : X) : x ≤ y ⊸ f x ≤ f y
  }.
  Record OrderReflecting : SProp :=
  { order_reflecting_mor :> OrderMorphism X Y
  ; order_reflecting (x y : X) : f x ≤ f y ⊸ x ≤ y
  }.
  Record OrderEmbedding : SProp :=
  { order_embedding_preserving :> OrderPreserving
  ; order_embedding_reflecting :> OrderReflecting
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
  Universes i.
  Context {X Y:set@{i}} {Xle:Le X} {Yle:Le Y} (f : X ⇾ Y).

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


Record MeetSemiLatticeOrder (L:set) `{Le L} `{Meet L} : SProp :=
{ meet_sl_poset :> Poset L
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
{ lattice_order_meet :> MeetSemiLatticeOrder L
; lattice_order_join :> JoinSemiLatticeOrder L
}.
Existing Class LatticeOrder.
