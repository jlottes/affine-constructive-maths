Require Export interfaces.orders interfaces.ring_order.
Require Export orders.orders orders.maps orders.groups.
Require Import theory.rings theory.subrings.
Require Import logic.aprop relations logic.refutative.
Require Import easy rewrite replc simplify.
Require Import tactics.algebra.com_monoids.

Local Open Scope mult_scope.
Import cone_notation.

Global Hint Extern 1 (Le (set_T (ring_op ?R))) => change (Le (set_T R)) : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoidOrder (ring_op ?R)) => change (AdditiveMonoidOrder R) : typeclass_instances.

Section opposite_ring.
  Ltac go := split; try exact _; change (@mult (ring_op _) ?f) with f; unfold ring_op; try exact _.

  Instance StrongLinearRefutativeRigOrder_op `{StrongLinearRefutativeRigOrder (R:=R)}
    : StrongLinearRefutativeRigOrder (ring_op R).
  Proof. go. intros b a d c. change (b < a ⊠ d < c ⊸ d · a + c · b < c · a + d · b).
    rew (aprod_com _ _).
    rew (mult_lt_compat_full _ _ _ _). now rew (commutativity (+) (c · b) _).
  Qed.

  Instance StrongLinearRefutativeRingOrder_op `{StrongLinearRefutativeRingOrder (R:=R)}
    : StrongLinearRefutativeRingOrder (ring_op R).
  Proof. go. intros x y; simplify. rew (aprod_com _ _). apply H. Qed.
End opposite_ring.
Global Hint Extern 2 (StrongLinearRefutativeRigOrder (ring_op ?R)) => simple notypeclasses refine StrongLinearRefutativeRigOrder_op : typeclass_instances.
Global Hint Extern 2 (StrongLinearRefutativeRingOrder (ring_op ?R)) => simple notypeclasses refine StrongLinearRefutativeRingOrder_op : typeclass_instances.


Lemma mult_le_compat_full `{StrongLinearRefutativeRigOrder (R:=R)} (b a d c : R)
: b ≤ a ⊠ d ≤ c ⊸ a · d + b · c ≤ a · c + b · d.
Proof.
  rew (le_iff_lt_par_eq _ (a · c + b · d)).
  rew (apar_adj_dual _ _ _).
  rew exact:(contrapositive (mult_lt_compat_full b a d c)).
  rew (apar_aprod_distr_l _ _ _ _).
  rew [(le_pseudo_antisym b a)|(le_pseudo_antisym d c)].
  rew (refutativity (a · d + b · c = a · c + b · d)), <-(apar_why_not _).
  rew (commutativity (+) _ _) at 1.
  rew <-exact:(is_fun (strong_op (+)) (_, _) (_,_) : _ = _ ∧ _ = _ ⊸ b · c + a · d = a · c + b · d).
  rew <-exact:(is_fun (strong_op (+)) (_, _) (_,_) : _ = _ ∧ _ = _ ⊸ a · d + b · c = a · c + b · d).
  rew [<-exact:(is_fun (·c) _ _ : b = a ⊸ b · c = a · c)
      |<-exact:(is_fun (·d) _ _ : a = b ⊸ a · d = b · d)
      |<-exact:(is_fun (a·) _ _ : d = c ⊸ a · d = a · c)
      |<-exact:(is_fun (b·) _ _ : c = d ⊸ b · c = b · d)
      ].
  rew [(symmetry_iff (=) a b) | (symmetry_iff (=) c d)].
  now simplify.
Qed.


Lemma strong_linear_refutative_rig_order_from_partial_minus
  `{Rig (R:=R)} {Rle : Le R}
  `{!StrongPoset R, !LinearOrder R, !RefutativeOrder R}
  `{!AdditiveMonoidOrder R}
  : (∀ x y : R, x < y ⊸ ∐ z : R, 0 < z ⊠ y = x + z)
  → (∀ x y : R, 0 < x ⊠ 0 < y ⊸ 0 < x · y)
  → StrongLinearRefutativeRigOrder R.
Proof. intros Pminus Pmult. split; try exact _.
  intros b a d c. apply affirmative_aimpl.
  intros [E1 E2].
  pose proof aimpl_impl_pos (Pminus _ _) E1 as [x [Px Ex]].
  pose proof aimpl_impl_pos (Pminus _ _) E2 as [y [Py Ey]].
  rew [Ex | Ey]. clear Ex Ey E1 E2 a c.
  rew (plus_mult_distr_r b x (d+y)).
  replc (b · (d + y) + x · (d + y) + b · d) with (x · (d + y) + b · d + b · (d + y)) by add_mon.
  apply (strictly_order_preserving (+ b·(d+y))).
  rew [(plus_mult_distr_r b x d) | (plus_mult_distr_l x d y)].
  replc (x · d + x · y + b · d) with (x·y + (b · d + x · d)) by add_mon.
  apply (strictly_order_preserving_simp (+ (b · d + x · d) ) 0 (x · y)).
  now apply Pmult.
Qed.


Coercion StrongLinearRefutativeRingOrder_StrongLinearRefutativeRigOrder
  `{H:StrongLinearRefutativeRingOrder R} : StrongLinearRefutativeRigOrder R.
Proof. apply strong_linear_refutative_rig_order_from_partial_minus; [| exact slr_ring_order_pos_mult ].
  intros x y. apply affirmative_aimpl. intros E. exists (y - x). split.
  * now apply (strictly_order_reflecting_simp (+x) 0 (y - x)).
  * now simplify.
Qed.


Coercion StrongLinearRefutativeRigOrder_NoZeroDivisors
  `{H:StrongLinearRefutativeRigOrder R} : NoZeroDivisors R.
Proof. intros x y. rew <-?(le_antisym_iff _ _). apply by_contrapositive.
  apply affirmative_aimpl; intros [[Ex|Ex] [Ey|Ey]];
  generalize (aimpl_impl_pos (mult_lt_compat_full _ _ _ _) (sprop.conj Ex Ey));
  apply aimpl_impl_pos; now simplify.
Qed.


Lemma nonneg_mult_order_preserving_l `{StrongLinearRefutativeRigOrder (R:=R)} {z:R} `{0 ≤ z} : OrderPreserving (z·).
Proof. apply alt_Build_OrderPreserving; intros x y; simplify. exact (simplify_thm (mult_le_compat_full 0 z x y)). Qed.
Global Hint Extern 2 (OrderPreserving (_·)) => simple notypeclasses refine nonneg_mult_order_preserving_l : typeclass_instances.

Lemma nonneg_mult_order_preserving_r `{StrongLinearRefutativeRigOrder (R:=R)} {z:R} `{0 ≤ z} : OrderPreserving (·z).
Proof. exact (nonneg_mult_order_preserving_l (R:=ring_op R)). Qed.
Global Hint Extern 2 (OrderPreserving (·_)) => simple notypeclasses refine nonneg_mult_order_preserving_r : typeclass_instances.

Lemma nonpos_mult_order_preserving_flip_l `{StrongLinearRefutativeRigOrder (R:=R)} {z:R} `{z ≤ 0} : OrderPreservingFlip (z·).
Proof. apply alt_Build_OrderPreservingFlip; intros x y; simplify. exact (simplify_thm (mult_le_compat_full z 0 x y)). Qed.
Global Hint Extern 2 (OrderPreservingFlip (_·)) => simple notypeclasses refine nonpos_mult_order_preserving_flip_l : typeclass_instances.

Lemma nonpos_mult_order_preserving_flip_r `{StrongLinearRefutativeRigOrder (R:=R)} {z:R} `{z ≤ 0} : OrderPreservingFlip (·z).
Proof. exact (nonpos_mult_order_preserving_flip_l (R:=ring_op R)). Qed.
Global Hint Extern 2 (OrderPreservingFlip (·_)) => simple notypeclasses refine nonpos_mult_order_preserving_flip_r : typeclass_instances.



Lemma pos_mult_order_embedding_l `{StrongLinearRefutativeRigOrder (R:=R)} {z:R} `{0 < z} : OrderEmbedding (z·).
Proof. split; [ exact _ |]. apply alt_Build_OrderReflecting. intros x y; simplify.
  apply by_contrapositive. exact (simplify_thm (mult_lt_compat_full 0 z y x)).
Qed.
Global Hint Extern 2 (OrderEmbedding (_·)) => simple notypeclasses refine pos_mult_order_embedding_l : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (_·)) => simple notypeclasses refine pos_mult_order_embedding_l : typeclass_instances.

Lemma pos_mult_order_embedding_r `{StrongLinearRefutativeRigOrder (R:=R)} {z:R} `{0 < z} : OrderEmbedding (·z).
Proof. exact (pos_mult_order_embedding_l (R:=ring_op R)). Qed.
Global Hint Extern 2 (OrderEmbedding (·_)) => simple notypeclasses refine pos_mult_order_embedding_r : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (·_)) => simple notypeclasses refine pos_mult_order_embedding_r : typeclass_instances.


Lemma neg_mult_order_embedding_flip_l `{StrongLinearRefutativeRigOrder (R:=R)} {z:R} `{z < 0} : OrderEmbeddingFlip (z·).
Proof. apply Build_OrderEmbeddingFlip; [ exact _ |]. apply alt_Build_OrderReflectingFlip. intros x y; simplify.
  apply by_contrapositive. exact (simplify_thm (mult_lt_compat_full z 0 y x)).
Qed.
Global Hint Extern 2 (OrderEmbeddingFlip (_·)) => simple notypeclasses refine neg_mult_order_embedding_flip_l : typeclass_instances.
Global Hint Extern 2 (OrderReflectingFlip (_·)) => simple notypeclasses refine neg_mult_order_embedding_flip_l : typeclass_instances.

Lemma neg_mult_order_embedding_flip_r `{StrongLinearRefutativeRigOrder (R:=R)} {z:R} `{z < 0} : OrderEmbeddingFlip (z·).
Proof. exact (neg_mult_order_embedding_flip_l (R:=ring_op R)). Qed.
Global Hint Extern 2 (OrderEmbeddingFlip (·_)) => simple notypeclasses refine neg_mult_order_embedding_flip_r : typeclass_instances.
Global Hint Extern 2 (OrderReflectingFlip (·_)) => simple notypeclasses refine neg_mult_order_embedding_flip_r : typeclass_instances.


Lemma rig_order_mult_cancel_left `{StrongLinearRefutativeRigOrder (R:=R)} (z:R) {E:z ≠ 0} : Injective (z·).
Proof.
  intros x y; simplify. rew <-(le_antisym_iff (z·x) _).
  rew (ne_iff_lt _ _) in E. destruct E as [E|E].
+ rew [exact:(order_reflecting_flip_simp (z·) x y) | exact:(order_reflecting_flip_simp (z·) y x)].
  rew (le_antisym_iff _ _). now apply symmetry.
+ rew [exact:(order_reflecting_simp (z·) x y) | exact:(order_reflecting_simp (z·) y x)].
  now apply antisymmetry.
Qed.

Lemma rig_order_mult_cancel_right `{StrongLinearRefutativeRigOrder (R:=R)} (z:R) {E:z ≠ 0} : Injective (·z).
Proof. exact (rig_order_mult_cancel_left (R:=ring_op R) _). Qed.

Coercion rig_order_mult_cancel `{StrongLinearRefutativeRigOrder (R:=R)} : NonZeroMultiplicativeCancellation R.
Proof. split; [ exact rig_order_mult_cancel_left | exact rig_order_mult_cancel_right ]. Qed.


Section squares.
  Context `{StrongLinearRefutativeRigOrder (R:=R)}.

  Lemma square_pos (z:R) {E:z ≠ 0} : 0 < z · z.
  Proof. rew (ne_iff_lt _ _) in E. destruct E as [E|E].
  + now rew <-(strictly_order_embedding_flip_simp (z·) z 0).
  + now rew <-(strictly_order_embedding_simp (z·) 0 z).
  Qed.

  Lemma square_nonneg (z:R) : 0 ≤ z · z.
  Proof. apply (refutative_by_aff_cases (0 ≤ z)); intros [E|E].
  + now apply (order_preserving_simp (z·) 0 z).
  + apply lt_le. exact (square_pos _).
  Qed.

  Lemma le_0_1: 0 ≤ 1 :> R.   Proof. exact (simplify_thm (square_nonneg 1)). Qed.
  Lemma le_0_2: 0 ≤ 2 :> R.   Proof. rew <-le_0_1; now simplify. Qed.

  Context `{!OneNonZero R}.
  Local Instance lt_0_1: 0 < 1 :> R.  Proof. exact (simplify_thm (square_pos 1)). Qed.
  Local Instance lt_0_2: 0 < 2 :> R.  Proof. rew <-le_0_1 at 1. now simplify. Qed.

  Lemma ne_2_0: anot (2 = 0 :> R).  Proof. now apply lt_ne_flip. Qed.
End squares.

Global Hint Extern 8 (apos (0 < ?x · ?x)) => simple notypeclasses refine square_pos : typeclass_instances.
Global Hint Extern 8 (apos (0 ≤ ?x · ?x)) => simple notypeclasses refine square_nonneg : typeclass_instances.
Global Hint Extern 4 (apos (0 < 1)) => simple notypeclasses refine lt_0_1 : typeclass_instances.
Global Hint Extern 4 (apos (0 ≤ 1)) => simple notypeclasses refine le_0_1 : typeclass_instances.
Global Hint Extern 4 (apos (0 < 2)) => simple notypeclasses refine lt_0_2 : typeclass_instances.
Global Hint Extern 4 (apos (0 ≤ 2)) => simple notypeclasses refine le_0_2 : typeclass_instances.
Global Hint Extern 4 (apos (2 ≠ 0)) => simple notypeclasses refine ne_2_0 : typeclass_instances.

Section misc.
  Context `{StrongLinearRefutativeRingOrder (R:=R)}.
  Lemma minus_le_swap (a b c d : R) : a - b ≤ c - d ⧟ a + d ≤ c + b.
    rew (order_embedding_simp (+ b + d) _ _) at 1.
    replc (a - b + (b + d)) with (a + d + (b - b)) by add_mon
      and (c - d + (b + d)) with (c + b + (d - d)) by add_mon.
    now simplify.
  Qed.

  Lemma minus_lt_swap (a b c d : R) : a - b < c - d ⧟ a + d < c + b.
  Proof. exact (contrapositive_iff (minus_le_swap c d a b)). Qed.
End misc.


Lemma slr_rig_order_nonneg_sub_rig `{StrongLinearRefutativeRigOrder R} : SubNearRig R⁺.
Proof. split; try exact _.
  apply alt_Build_MultiplicativeSubMonoid.
+ intros x y. change (0 ≤ x ⊠ 0 ≤ y ⊸ 0 ≤ x · y).
  exact ( simplify_thm (mult_le_compat_full 0 x 0 y) ).
+ now change (0 ≤ 1 :> R).
Qed.
Global Hint Extern 2 (SubNearRig _⁺) => simple notypeclasses refine slr_rig_order_nonneg_sub_rig : typeclass_instances.
Global Hint Extern 2 (SubNearRg _⁺) => simple notypeclasses refine slr_rig_order_nonneg_sub_rig : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubMonoid _⁺) => simple notypeclasses refine slr_rig_order_nonneg_sub_rig : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubSemiGroup _⁺) => simple notypeclasses refine slr_rig_order_nonneg_sub_rig : typeclass_instances.


Lemma slr_rig_order_nonneg_order `{StrongLinearRefutativeRigOrder R} : StrongLinearRefutativeRigOrder R⁺.
Proof. split; try exact _. intros a b c d. exact (mult_lt_compat_full (R:=R) a b c d). Qed.
Global Hint Extern 2 (StrongLinearRefutativeRigOrder (subset_to_set _⁺)) => simple notypeclasses refine slr_rig_order_nonneg_order : typeclass_instances.
