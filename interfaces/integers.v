Require Import
 abstract_algebra interfaces.bundled_algebra strip_coercions interfaces.ring_order.



Class IntegersToGroup@{u} (Z:set@{u})
  := integers_to_group: ∀ (G:set@{u}) {pG:Plus G} {zG:Zero G} {nG:Negate G} {oG:One G} {H:AdditiveNonComGroup G}, Z ⇾ G.
Arguments integers_to_group Z {_} G {_ _ _ _ _}.

Class Integers@{u} (Z:set@{u}) {zZ:Zero Z} {oZ:One Z} {pZ:Plus Z} {nZ:Negate Z} {mZ:Mult Z} {U:IntegersToGroup Z} : SProp :=
{ integers_ring : Ring Z
; integers_to_group_mor   {G:set@{u}} `{AdditiveNonComGroup G} {oG:One G} : AdditiveMonoid_Morphism (integers_to_group Z G)
; integers_to_group_pointed {G:set@{u}} `{AdditiveNonComGroup G} {oG:One G} : One_Pointed_Morphism (integers_to_group Z G)
; integers_initial {G:set@{u}} `{AdditiveNonComGroup G} {oG:One G}
    (h:Z ⇾ G) `{!AdditiveMonoid_Morphism h, !One_Pointed_Morphism h} : h = integers_to_group Z G
}.
Coercion integers_ring : Integers >-> Ring.
Global Hint Extern 2 (AdditiveMonoid_Morphism (integers_to_group _ _)) => simple notypeclasses refine integers_to_group_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (integers_to_group _ _)) => simple notypeclasses refine integers_to_group_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (integers_to_group _ _)) => simple notypeclasses refine integers_to_group_mor : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (integers_to_group _ _)) => simple notypeclasses refine integers_to_group_pointed : typeclass_instances.


Record integers :=
{ ints_ring :> ring
; #[canonical=no, reversible=no] ints_to_grp :> IntegersToGroup ints_ring
; #[canonical=no, reversible=no] ints_integers :> Integers ints_ring
}.
Global Hint Extern 2 (StripCoercions (ints_ring ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (IntegersToGroup ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (Integers ?X) => exact_strip_coercions X : typeclass_instances.


(** Order *)

Record OrderedIntegers Z {zZ:Zero Z} {oZ:One Z} {pZ:Plus Z} {nZ:Negate Z} {mZ:Mult Z} {leZ:Le Z} {U:IntegersToGroup Z} : SProp :=
{ #[reversible=no] ord_int_int :> Integers Z
; #[reversible=no] ord_int_ord :> StrongLinearRefutativeRingOrder Z
}.
Existing Class OrderedIntegers.


