Require Export interfaces.subset.
Require Import abstract_algebra theory.lattices.
Require Import interfaces.orders orders.orders orders.lattices.
Require Import logic.aprop.
Require Import easy rewrite.

Local Ltac unfold_subset :=
  try change (?U ⊆ ?W) with (∏ x, x ∊ U ⊸ x ∊ W);
  try change (?U = ?W) with (∏ x, x ∊ U ⧟ x ∊ W).

Lemma subset_poset {X} : Poset (𝒫 X).
Proof. split; [ split | .. ].
+ tautological.
+ tautological.
+ tautological.
+ hnf; intros U V; unfold_subset. rew <-all_adj. intros x. now rew [ (all_lb _ x) | (all_lb _ x) ].
Qed.

Global Hint Extern 2 (Poset (subset_set _)) => simple notypeclasses refine subset_poset : typeclass_instances.
Global Hint Extern 2 (PreOrder (subset _)) => simple notypeclasses refine subset_poset : typeclass_instances.
Global Hint Extern 2 (PreOrder (set_T (subset_set _))) => simple notypeclasses refine subset_poset : typeclass_instances.

Lemma subset_lattice_order {X} : LatticeOrder (𝒫 X).
Proof. split.
+ split; [ exact _ | tautological.. ].
+ apply Build_JoinSemiLatticeOrder; tautological.
Qed.

Global Hint Extern 2 (LatticeOrder (subset_set _)) => simple notypeclasses refine subset_lattice_order : typeclass_instances.
Global Hint Extern 2 (MeetSemiLatticeOrder (subset_set _)) => simple notypeclasses refine subset_lattice_order : typeclass_instances.
Global Hint Extern 2 (JoinSemiLatticeOrder (subset_set _)) => simple notypeclasses refine subset_lattice_order : typeclass_instances.
Global Hint Extern 2 (Lattice (subset_set _)) => simple notypeclasses refine subset_lattice_order : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice (subset_set _)) => simple notypeclasses refine subset_lattice_order : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice (subset_set _)) => simple notypeclasses refine subset_lattice_order : typeclass_instances.

Lemma subset_distr_lattice {X} : DistributiveLattice (𝒫 X).
Proof. apply Build_DistributiveLatticeOrder. tautological. Qed.
Global Hint Extern 2 (DistributiveLattice (subset_set _)) => simple notypeclasses refine subset_distr_lattice : typeclass_instances.

Lemma subset_bounded_meet_sl {X} : BoundedMeetSemiLattice (𝒫 X).
Proof. apply alt_Build_BoundedMeetSemiLattice; try exact _. tautological. Qed.
Global Hint Extern 2 (BoundedMeetSemiLattice (subset_set _)) => simple notypeclasses refine subset_bounded_meet_sl : typeclass_instances.

Lemma subset_bounded_join_sl {X} : BoundedJoinSemiLattice (𝒫 X).
Proof. apply alt_Build_BoundedJoinSemiLattice; try exact _. tautological. Qed.
Global Hint Extern 2 (BoundedJoinSemiLattice (subset_set _)) => simple notypeclasses refine subset_bounded_join_sl : typeclass_instances.

Lemma nonempty_alt {X} {U : 𝒫 X} : U ≠ ∅ ⧟ ∐ x, x ∊ U.
Proof. tautological. Qed.

(** Image and preimage *)

Lemma preimage_lattice_mor `{f:X ⇾ Y} : Lattice_Morphism (preimage f).
Proof. split; try exact _.
+ apply Build_MeetSemiLattice_Morphism. tautological.
+ apply Build_JoinSemiLattice_Morphism. tautological.
Qed.
Global Hint Extern 2 (Lattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_lattice_mor : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_lattice_mor : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_lattice_mor : typeclass_instances.

Definition preimage_order_preserving `{f:X ⇾ Y} : OrderPreserving (preimage f).
Proof join_sl_mor_preserving _.
Global Hint Extern 2 (OrderPreserving (func_op preimage _)) => simple notypeclasses refine preimage_order_preserving : typeclass_instances.

Lemma image_join_sl_mor `{f:X ⇾ Y} : BoundedJoinSemiLattice_Morphism (image f).
Proof. apply alt_Build_BoundedJoinSemiLattice_Morphism; [| tautological ].
  intros U V y.
  change ((∐ x, (x ∊ U ∨ x ∊ V) ⊠ f x = y) ⧟ (∐ x, x ∊ U ⊠ f x = y) ∨ (∐ x, x ∊ V ⊠ f x = y)). split.
+ rew <-aex_adj. intros x. rew (aprod_adj _ _ _). apply aor_elim.
  * now rew <-(aorl _ _), <-(aex_ub _ x), <-(aprod_adj _ _ _).
  * now rew <-(aorr _ _), <-(aex_ub _ x), <-(aprod_adj _ _ _).
+ apply aor_elim; rew <-aex_adj; intros x; rew <-(aex_ub _ x).
  * now rew <-(aorl _ _).
  * now rew <-(aorr _ _).
Qed.
Global Hint Extern 2 (BoundedJoinSemiLattice_Morphism (func_op image _)) => simple notypeclasses refine image_join_sl_mor : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Morphism (func_op image _)) => simple notypeclasses refine image_join_sl_mor : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (func_op image _)) => simple notypeclasses refine image_join_sl_mor : typeclass_instances.

Definition image_order_preserving `{f:X ⇾ Y} : OrderPreserving (image f).
Proof join_sl_mor_preserving _.
Global Hint Extern 2 (OrderPreserving (func_op image _)) => simple notypeclasses refine image_order_preserving : typeclass_instances.
