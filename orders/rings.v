Require Export interfaces.orders interfaces.ring_order.
Require Export orders.orders orders.maps orders.groups.
Require Import theory.rings.
Require Import logic.aprop relations logic.refutative.
Require Import easy rewrite replc.

Local Open Scope mult_scope.
Import cone_notation.

Global Hint Extern 1 (Le (set_T (ring_op ?R))) => change (Le (set_T R)) : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoidOrder (ring_op ?R)) => change (AdditiveMonoidOrder R) : typeclass_instances.
Global Hint Extern 2 (SubtractionMonoidOrder (ring_op ?R)) => change (SubtractionMonoidOrder R) : typeclass_instances.

Lemma RigOrder_op `{RigOrder R} : RigOrder (ring_op R).
Proof. split; try exact _.
+ change (∀ x y : R, 0 ≤ x ⊠ 0 ≤ y ⊸ 0 ≤ y · x); intros x y.
  rew (aprod_com _ _). now apply mult_nonneg.
+ change (∀ x y : R, 0 < x ⊠ 0 < y ⊸ 0 < y · x); intros x y.
  rew (aprod_com _ _). now apply mult_pos.
Qed.
Global Hint Extern 2 (RigOrder (ring_op ?R)) => simple notypeclasses refine RigOrder_op : typeclass_instances.


(** Multiplication by nonnegative / positive elements is order preserving / reflecting. *)

Lemma nonneg_mult_l `{RigOrder R} `{z ∊ R⁺} : OrderPreserving (z ·).
Proof.
  apply alt_Build_OrderPreserving.
  intros x y; change ((z·) ?x) with (z·x).
  pose proof decompose_le x y as [a Ha]. rew Ha.
  rew <-(transitivity (≤) (z·x) (z·(x+a)) (z·y)).
  apply aprod_proper_aimpl.
  * rew [ <-(plus_0_r (z·x)) | (plus_mult_distr_l _ _ _) ].
    rew <-exact:(order_preserving (z·x +) _ _ : _ ⊸ z · x + 0 ≤ z · x + z · a).
    rew <-(mult_nonneg _ _).
    now rew (aprod_true_l (_: 0 ≤ z)).
  * rew <-(eq_le_flip _ _). exact (is_fun (z ·) _ _).
Qed.

Lemma pos_mult_l `{RigOrder R} `{z ∊ R₊} : OrderReflecting (z ·).
Proof.
  apply alt_Build_OrderReflecting.
  intros x y; change ((z·) ?x) with (z·x).
  apply by_contrapositive.
  pose proof decompose_lt y x as [a Ha].
  rew [ Ha | <-(lt_le_trans (z·y) (z·(y+a)) (z·x)) ].
  apply aprod_proper_aimpl.
  * rew [ <-(plus_0_r (z·y)) | (plus_mult_distr_l _ _ _) ].
    rew <-exact:(strictly_order_preserving (z·y +) _ _ : _ ⊸ z · y + 0 < z · y + z · a).
    rew <-(mult_pos _ _).
    now rew (aprod_true_l (_: 0 < z)).
  * rew <-(eq_le_flip _ _). exact (is_fun (z ·) _ _).
Qed.

Lemma nonneg_mult_r `{RigOrder R} `{z ∊ R⁺} : OrderPreserving (· z).
Proof nonneg_mult_l (R:=ring_op R).

Lemma pos_mult_r `{RigOrder R} `{z ∊ R₊} : OrderReflecting (· z).
Proof pos_mult_l (R:=ring_op R).


(** Multiplication by nonpositive / negative elements is (contravariantly) order preserving / reflecting. *)


Lemma nonpos_mult_l `{RigOrder R} `{z ∊ R⁻} : OrderPreservingFlip (z ·).
Proof.
  apply alt_Build_OrderPreservingFlip.
  intros x y; change ((z·) ?x) with (z·x).
  pose proof decompose_le x y as [a Ha]. rew Ha; clear Ha.
  rew [ (aprod_com _ _) | <-(transitivity (≤) (z·y) (z·(x+a)) (z·x)) ].
  apply aprod_proper_aimpl.
  * rew <-(eq_le _ _). exact (is_fun (z ·) _ _).
  * rew [ (plus_mult_distr_l _ _ _) | <-(plus_0_r (z·x)) ].
    rew <-exact:(order_preserving (z·x +) _ _ : _ ⊸ z · x + z · a ≤ z · x + 0).
    pose proof decompose_le z 0 as [b [Hb _]]; specialize (Hb _); destruct Hb as [? E].
    rew <-exact:(order_reflecting (+ b·a) (z·a) 0 : z · a + b · a ≤ 0 + b · a ⊸ _).
    rew [ <-(plus_mult_distr_r _ _ _) | (plus_0_l _) ].
    rew <-E, (mult_0_l _).
    rew <-(mult_nonneg _ _).
    now rew (aprod_true_l (_: 0 ≤ b)).
Qed.

Lemma neg_mult_l `{RigOrder R} `{z ∊ R₋} : OrderReflectingFlip (z ·).
Proof.
  apply alt_Build_OrderReflectingFlip.
  intros x y; change ((z·) ?x) with (z·x).
  apply by_contrapositive.
  pose proof decompose_lt y x as [a Ha].
  rew Ha.
  rew [ (aprod_com _ _) | <-(le_lt_trans (z·x) (z·(y+a)) (z·y)) ].
  apply aprod_proper_aimpl.
  * rew <-(eq_le _ _). exact (is_fun (z ·) _ _).
  * rew [ <-(plus_0_r (z·y)) | (plus_mult_distr_l _ _ _) ].
    rew <-exact:(strictly_order_preserving (z·y +) _ _ : _ ⊸ z · y + z · a < z · y + 0).
    pose proof decompose_lt z 0 as [b [Hb _]]; specialize (Hb _); destruct Hb as [? E].
    rew <-exact:(strictly_order_reflecting (+ b·a) (z·a) 0 : z · a + b · a < 0 + b · a ⊸ _).
    rew [ <-(plus_mult_distr_r _ _ _) | (plus_0_l _) ].
    rew <-E, (mult_0_l _).
    rew <-(mult_pos _ _).
    now rew (aprod_true_l (_: 0 < b)).
Qed.

Lemma nonpos_mult_r `{RigOrder R} `{z ∊ R⁻} : OrderPreservingFlip (· z).
Proof nonpos_mult_l (R:=ring_op R).

Lemma neg_mult_r `{RigOrder R} `{z ∊ R₋} : OrderReflectingFlip (· z).
Proof neg_mult_l (R:=ring_op R).


(** In a totally ordered rig with no zero divisors,
    we can derive that multiplication preserves positivity from
    the fact that it preserves nonnegativity. *)

Lemma total_rig_order `{Rig (R:=R)} {Rle:Le R}
  `{!SubtractionMonoidOrder R}
  `{!TotalOrder R}
  `{!NoZeroDivisors R}
:  (∀ x y : R, 0 ≤ x ⊠ 0 ≤ y ⊸ 0 ≤ x · y)
  → RigOrder R.
Proof. intros mult_nonneg. unshelve esplit; try exact _.
  intros x y.
  apply by_contrapositive.
  pose proof total (≤) x 0 as [Ex|Ex]; [ now rew (apar_is_true_l Ex) |].
  pose proof total (≤) y 0 as [Ey|Ey]; [ now rew (apar_is_true_r Ey) |].
  rew <-(aand_true_r (P:=x ≤ 0) Ex), (le_antisym_iff _ _).
  rew <-(aand_true_r (P:=y ≤ 0) Ey), (le_antisym_iff _ _).
  assert (0 ≤ x · y) as E by (apply mult_nonneg; now split).
  rew <-(aand_true_r (P:=x · y ≤ 0) E), (le_antisym_iff _ _).
  now apply no_zero_divisors.
Qed.

Lemma total_rig_order2 `{Rig (R:=R)} {Rle:Le R}
  `{!AdditiveMonoidOrder R}
  `{!TotalOrder R}
  `{!NoZeroDivisors R}
: (∀ x y : R, ∐ z, x ≤ y ⊸ 0 ≤ z ⊠ y = x + z)
  → (∀ x y : R, 0 ≤ x ⊠ 0 ≤ y ⊸ 0 ≤ x · y)
  → RigOrder R.
Proof. intros. simple refine (total_rig_order _).
  now apply total_subtraction_monoid_order.
Qed.

Lemma total_ring_order `{Ring (R:=R)} {Rle:Le R}
  `{!TotalOrder R}
  `{!NoZeroDivisors R}
: (∀ z : R, OrderPreserving (z+))
  → (∀ x y : R, 0 ≤ x ⊠ 0 ≤ y ⊸ 0 ≤ x · y)
  → RigOrder R.
Proof. intros ??.
  assert (SubtractionMonoidOrder R) by now apply alt_Build_AdditiveGroupOrder.
  now apply total_rig_order.
Qed.


(** In a rig with a linear refutative order,
    we can derive that multiplication preserves nonnegativity from
    the fact that it preserves positivity. *)

Lemma linear_refutative_rig_order `{Rig (R:=R)} {Rle:Le R}
  `{!SubtractionMonoidOrder R}
  `{!RefutativeOrder R}
: (∀ x y : R, 0 < x ⊠ 0 < y ⊸ 0 < x · y)
  → RigOrder R.
Proof. intros mult_pos. unshelve esplit; try exact _.
  intros x y. apply by_contrapositive.
  apply affirmative_aimpl. intros E.
  assert (x · y ≠ 0) as E2 by now rew <-(lt_ne _ _).
  rew (nonzero_product _ _) in E2. destruct E2 as [Ex Ey].
  rew [ (lt_iff_le_prod_ne _ _) | (lt_iff_le_prod_ne _ _) ].
  rew [ (aprod_true_r Ex) | (aprod_true_r Ey) ].
  rew <-(contrapositive (mult_pos x y)).
  now apply lt_le.
Qed.


Lemma linear_refutative_rig_order2 `{Rig (R:=R)} {Rle:Le R}
  `{!AdditiveMonoidOrder R}
  `{!LinearOrder R}
  `{!RefutativeOrder R}
: (∀ x y : R, ∐ z, x ≤ y ⊸ 0 ≤ z ⊠ y = x + z)
  → (∀ x y : R, 0 < x ⊠ 0 < y ⊸ 0 < x · y)
  → RigOrder R.
Proof. intros partial_minus mult_pos.
  pose proof refutative_subtraction_monoid_order partial_minus.
  now apply linear_refutative_rig_order.
Qed.


Lemma linear_refutative_ring_order `{Ring (R:=R)} {Rle:Le R}
  `{!LinearOrder R} `{!RefutativeOrder R}
: (∀ z:R, OrderPreserving (z+))
  → (∀ x y : R, 0 < x ⊠ 0 < y ⊸ 0 < x · y)
  → RigOrder R.
Proof. intros ? mult_pos.
  assert (SubtractionMonoidOrder R) by now apply alt_Build_AdditiveGroupOrder.
  now apply linear_refutative_rig_order.
Qed.




