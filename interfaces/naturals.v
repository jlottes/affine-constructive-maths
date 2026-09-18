Require Import
 abstract_algebra interfaces.bundled_algebra strip_coercions.
Require Import interfaces.orders interfaces.ring_order.
Require Import projected_set.

(** Characterization as an NNO *)
Class Successor (X:set) := suc : X ⇾ X.
Global Hint Extern 20 (Successor _) => refine (1 +) : typeclass_instances.

Class MaybeAlgebra_Morphism `(f:X ⇾ Y) {zX:Zero X} {sX:Successor X} {zY:Zero Y} {sY:Successor Y} : SProp :=
{ maybe_alg_preserves_zero  : Zero_Pointed_Morphism f
; preserves_suc x : f (suc x) = suc (f x)
}.
Coercion maybe_alg_preserves_zero : MaybeAlgebra_Morphism >-> Zero_Pointed_Morphism.
Arguments maybe_alg_preserves_zero {_ _} f {_ _ _ _ _}.
Arguments preserves_suc {_ _} f {_ _ _ _ _} x.

Section NNO.
  Universes u.
  Context (N:set@{u}).

  Class FromNNO := nno_to_set : ∀ (X:set@{u}) {z:Zero X} {s:Successor X}, N ⇾ X.

  Class NaturalNumbersObject {H:FromNNO} {zN:Zero N} {sN:Successor N} : SProp :=
  { nno_to_set_mor {X:set@{u}} {z:Zero X} {s:Successor X} : MaybeAlgebra_Morphism (nno_to_set X)
  ; nno_initial {X:set@{u}} {z:Zero X} {s:Successor X} (f:N ⇾ X) `{!MaybeAlgebra_Morphism f} : f = nno_to_set X
  }.
End NNO.
Arguments nno_to_set_mor {N _ _ _ _ _ _ _}.
Arguments nno_initial {N _ _ _ _ _ _ _} f {_}.
Global Hint Extern 2 (MaybeAlgebra_Morphism (nno_to_set _ _)) => simple notypeclasses refine nno_to_set_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (nno_to_set _ _)) => simple notypeclasses refine nno_to_set_mor : typeclass_instances.

(** Characterization as the near-rig initial in the category of pointed additive non-commutative monoids. *)

Class NaturalsToMon@{u} (N:set@{u})
  := naturals_to_mon: ∀ (M:set@{u}) {pM:Plus M} {zM:Zero M} {oM:One M}, N ⇾ M.
Arguments naturals_to_mon N {_} M {_ _ _}.

Class Naturals@{u} (N:set@{u}) {zN:Zero N} {oN:One N} {pN:Plus N} {mN:Mult N} {U:NaturalsToMon N} : SProp :=
{ naturals_near_rig : NearRig N
; naturals_to_mon_mor     {M:set@{u}} `{AdditiveNonComMonoid M} {oM:One M} : AdditiveMonoid_Morphism (naturals_to_mon N M)
; naturals_to_mon_pointed {M:set@{u}} `{AdditiveNonComMonoid M} {oM:One M} : One_Pointed_Morphism (naturals_to_mon N M)
; naturals_initial {M:set@{u}} `{AdditiveNonComMonoid M} {oM:One M}
    (h:N ⇾ M) `{!AdditiveMonoid_Morphism h, !One_Pointed_Morphism h} : h = naturals_to_mon N M
}.
Coercion naturals_near_rig : Naturals >-> NearRig.
Global Hint Extern 2 (AdditiveMonoid_Morphism (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_mon_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_mon_mor : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_mon_pointed : typeclass_instances.

Record naturals :=
{ nats_near_rig :> near_rig
; #[canonical=no, reversible=no] nats_to_mon :> NaturalsToMon nats_near_rig
; #[canonical=no, reversible=no] nats_naturals :> Naturals nats_near_rig
}.
Global Hint Extern 2 (StripCoercions (nats_near_rig ?X)) => strip_coercions_chain X : strip_coercions.
Global Hint Extern 4 (NaturalsToMon ?X) => exact_strip_coercions X : typeclass_instances.
Global Hint Extern 4 (Naturals ?X) => exact_strip_coercions X : typeclass_instances.

(** Subtraction *)

Module natsubtract.
  Inductive t (N:set) := is_lt_by : N → t N | is_eq | is_gt_by : N → t N.
  Arguments is_lt_by {N} _.
  Arguments is_eq {N}.
  Arguments is_gt_by {N} _.

  Definition T (N:set) := @projected_set (t N) (sum_set 𝟏 (sum_set N N))
    (λ r, match r with | is_lt_by z => inr (inl z) | is_eq => inl the | is_gt_by z => inr (inr z) end).
End natsubtract.
Canonical natsubtract.T.
Global Hint Extern 1 (IsProjectedSet (set_T (natsubtract.T _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.

Class NatSubtract (N:set) := nat_subtract : N ⊗ N ⇾ natsubtract.T N.

Class NatSubtractSpec (N:set) `{Zero N} `{Plus N} `{!NatSubtract N} : SProp
  := nat_subtract_spec : ∀ x y : N,
  match nat_subtract (x, y) with
  | natsubtract.is_lt_by z => x + z = y ⊠ z ≠ 0
  | natsubtract.is_eq => x = y
  | natsubtract.is_gt_by z => x = y + z ⊠ z ≠ 0
  end.

(** Order *)

Record OrderedNaturals N {zN:Zero N} {oN:One N} {pN:Plus N} {mN:Mult N} {leN:Le N} {U:NaturalsToMon N} : SProp :=
{ #[reversible=no] ord_nat_nat :> Naturals N
; #[reversible=no] ord_nat_ord :> StrongLinearRefutativeRigOrder N
}.
Existing Class OrderedNaturals.

