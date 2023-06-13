Require Export interfaces.abstract_algebra interfaces.orders interfaces.subset.
Require Import orders.orders.
Require Import set_lambda.

Section cones.
  Universes i.
  Context (P:set@{i}) {Ple:Le P} {z:Zero P} `{!WeakPoset P}.

  Definition NonZero := { x : P | x ≠ 0 }.
  Definition NonNeg  := { x : P | 0 ≤ x }.
  Definition NonPos  := { x : P | x ≤ 0 }.
  Definition Pos     := { x : P | 0 < x }.
  Definition Neg     := { x : P | x < 0 }.
End cones.

Module cone_notation.
  Notation "R ⁺" := (NonNeg R) (at level 7, no associativity, format "R ⁺") : set_scope.
  Notation "R ₊" := (Pos R)    (at level 7, no associativity, format "R ₊") : set_scope.
  Notation "R ⁻" := (NonPos R) (at level 7, no associativity, format "R ⁻") : set_scope.
  Notation "R ₋" := (Neg R)    (at level 7, no associativity, format "R ₋") : set_scope.
End cone_notation.
Import cone_notation.

Record AdditiveMonoidOrder (M:set) {Mp:Plus M} {Mz:Zero M} {Mle:Le M} : SProp :=
{ AdditiveMonoidOrder_AdditiveMonoid :> AdditiveMonoid M
; AdditiveMonoidOrder_Order :> Poset M
; plus_l_order_embedding (z:M) : OrderEmbedding (z+)
}.
Existing Class AdditiveMonoidOrder.
Arguments plus_l_order_embedding {M Mp Mz Mle _ z}.
Global Hint Extern 2 (OrderEmbedding (_+)) => simple notypeclasses refine plus_l_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (_+)) => simple notypeclasses refine plus_l_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (_+)) => simple notypeclasses refine plus_l_order_embedding : typeclass_instances.

Record SubtractionMonoidOrder (M:set) {p:Plus M} {z:Zero M} {Mle:Le M} : SProp :=
{ SubtractionMonoidOrder_add_mon_order :> AdditiveMonoidOrder M
; sub_mon_order_partial_minus : ∏ x y : M, ∐ z : M, x ≤ y ⊸ y = x + z
}.
Existing Class SubtractionMonoidOrder.

(*
Local Open Scope mult_scope.

Record RgOrder (R:set) {p:Plus R} {m:Mult R} {z:Zero R} {Rle:Le R} : SProp :=
{ RgOrder_rg :> Rg R
; RgOrder_sub_mon_order :> SubtractionMonoidOrder R
; RgOrder_mult_nonneg (x y : R) : 0 ≤ x ⊠ 0 ≤ y ⊸ 0 ≤ x · y
}.
Existing Class RgOrder.

Require Import logic.aprop.


Section blah.
Context `{Rg R} `{Le R} `{!RgOrder R}.
Context (x y : R).
Goal atrue.
Check contrapositive (RgOrder_mult_nonneg R _ x y).

*)
