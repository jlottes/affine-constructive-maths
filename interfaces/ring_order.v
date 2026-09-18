Require Export interfaces.abstract_algebra interfaces.orders interfaces.subset.
Require Import orders.orders.
Require Import set_lambda.

Section cones.
  Context (P:set) {Ple:Le P} {z:Zero P} `{!WeakPoset P}.

  Definition NonZero := { x : P | x ≠ 0 }.
  Definition NonNeg  := { x : P | 0 ≤ x }.
  Definition NonPos  := { x : P | x ≤ 0 }.
  Definition Pos     := { x : P | 0 < x }.
  Definition Neg     := { x : P | x < 0 }.
End cones.

Module cone_notation.
  Notation "R ⁺" := (NonNeg R) (at level 1, no associativity, format "R ⁺") : set_scope.
  Notation "R ₊" := (Pos R)    (at level 1, no associativity, format "R ₊") : set_scope.
  Notation "R ⁻" := (NonPos R) (at level 1, no associativity, format "R ⁻") : set_scope.
  Notation "R ₋" := (Neg R)    (at level 1, no associativity, format "R ₋") : set_scope.
End cone_notation.
Import cone_notation.

Record AdditiveMonoidOrder (M:set) {Mp:Plus M} {Mz:Zero M} {Mle:Le M} : SProp :=
{ #[reversible=no] AdditiveMonoidOrder_AdditiveMonoid :> AdditiveMonoid M
; #[reversible=no] AdditiveMonoidOrder_Order :> Poset M
; plus_l_order_embedding (z:M) : OrderEmbedding (z+)
}.
Existing Class AdditiveMonoidOrder.
Arguments plus_l_order_embedding {M Mp Mz Mle _ z}.
Global Hint Extern 2 (OrderEmbedding (_+)) => simple notypeclasses refine plus_l_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (_+)) => simple notypeclasses refine plus_l_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (_+)) => simple notypeclasses refine plus_l_order_embedding : typeclass_instances.


Record AdditiveGroupOrder (G:set) {Gp:Plus G} {Gz:Zero G} {Gn:Negate G} {Gle:Le G} : SProp :=
{ #[reversible=no] AdditiveGroupOrder_AdditiveGroup :> AdditiveGroup G
; #[reversible=no] AdditiveGroupOrder_Order :> Poset G
; add_group_plus_order_preserving (z:G) : OrderPreserving (z+)
}.
Existing Class AdditiveGroupOrder.


Local Open Scope mult_scope.

Record StrongLinearRefutativeRigOrder (R:set) {Rp:Plus R} {Rm:Mult R} {Rz:Zero R} {Ro:One R} {Rle:Le R} : SProp :=
{ #[reversible=no] slr_rig_order_rig :> Rig R
; #[reversible=no] slr_rig_order_strong :> StrongPoset R
; #[reversible=no] slr_rig_order_linear :> LinearOrder R
; #[reversible=no] slr_rig_order_refutative :> RefutativeOrder R
; #[reversible=no] slr_rig_order_mon_order :> AdditiveMonoidOrder R
; mult_lt_compat_full (b a d c : R)
  : b < a ⊠ d < c ⊸ a · d + b · c < a · c + b · d
}.
Existing Class StrongLinearRefutativeRigOrder.
Arguments mult_lt_compat_full {R _ _ _ _ _ _} b a d c.


Record StrongLinearRefutativeRingOrder (R:set) {Rp:Plus R} {Rm:Mult R} {Rz:Zero R} {Rn:Negate R} {Ro:One R} {Rle:Le R} : SProp :=
{ #[reversible=no] slr_ring_order_ring :> Ring R
; #[reversible=no] slr_ring_order_strong :> StrongPoset R
; #[reversible=no] slr_ring_order_linear :> LinearOrder R
; #[reversible=no] slr_ring_order_refutative :> RefutativeOrder R
; #[reversible=no] slr_ring_order_grp_order :> AdditiveGroupOrder R
; slr_ring_order_pos_mult (x y : R) : 0 < x ⊠ 0 < y ⊸ 0 < x · y
}.
Existing Class StrongLinearRefutativeRingOrder.
Arguments slr_ring_order_pos_mult {R _ _ _ _ _ _ _} x y.


