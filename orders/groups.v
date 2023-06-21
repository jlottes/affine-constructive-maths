Require Export interfaces.orders interfaces.ring_order.
Require Export orders.orders orders.maps.
Require Import theory.additive_groups.
Require Import logic.aprop relations.
Require Import easy rewrite.

(** Ordered Monoids *)

Import cone_notation.
Lemma nonneg_dual `{WeakPoset P} {z:Zero P} {x:P} : DeMorganDual (x ∊ P⁺) (x ∊ P₋).  Proof _ : DeMorganDual (0 ≤ x) _.
Lemma nonpos_dual `{WeakPoset P} {z:Zero P} {x:P} : DeMorganDual (x ∊ P⁻) (x ∊ P₊).  Proof _ : DeMorganDual (x ≤ 0) _.
Lemma pos_dual    `{WeakPoset P} {z:Zero P} {x:P} : DeMorganDual (x ∊ P₊) (x ∊ P⁻).  Proof _ : DeMorganDual (0 < x) _.
Lemma neg_dual    `{WeakPoset P} {z:Zero P} {x:P} : DeMorganDual (x ∊ P₋) (x ∊ P⁺).  Proof _ : DeMorganDual (x < 0) _.
Global Hint Extern 2 (DeMorganDual (_ ∊ _⁺) _) => notypeclasses refine nonneg_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ ∊ _⁻) _) => notypeclasses refine nonpos_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ ∊ _₊) _) => notypeclasses refine pos_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ ∊ _₋) _) => notypeclasses refine neg_dual : typeclass_instances.

Lemma plus_r_order_embedding `{AdditiveMonoidOrder M} : ∀ {z:M}, OrderEmbedding (+z).
Proof right_order_embedding_from_left (@plus_l_order_embedding _ _ _ _ _).
Global Hint Extern 2 (OrderEmbedding (+_)) => simple notypeclasses refine plus_r_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (+_)) => simple notypeclasses refine plus_r_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (+_)) => simple notypeclasses refine plus_r_order_embedding : typeclass_instances.

Lemma plus_order_preserving `{AdditiveMonoidOrder M} : OrderPreserving (Y:=M) (+).
Proof. apply alt_Build_OrderPreserving.
  intros [x₁ y₁][x₂ y₂]. unfold_pair_le.
  rew ( order_preserving (+ y₁) x₁ x₂ : _ ⊸ x₁ + y₁ ≤ x₂ + y₁).
  rew ( order_preserving (x₂ +) y₁ y₂ : _ ⊸ x₂ + y₁ ≤ x₂ + y₂).
  now apply transitivity.
Qed.
Global Hint Extern 2 (OrderPreserving (+)) => simple notypeclasses refine plus_order_preserving : typeclass_instances.

Lemma compose_le `{AdditiveMonoidOrder M} (x y z : M) : 0 ≤ z ⊠ y = x + z ⊸ x ≤ y.
Proof. rew <-(transitivity (≤) x (x + z) y). apply aprod_proper_aimpl.
+ rew <-(plus_0_r x) at 1. exact (order_preserving (x+) _ _).
+ apply eq_le_flip.
Qed.

Lemma compose_lt `{AdditiveMonoidOrder M} (x y z : M) : 0 < z ⊠ y = x + z ⊸ x < y.
Proof. rew <-(lt_le_trans x (x+z) y). apply aprod_proper_aimpl.
+ rew <-(plus_0_r x) at 1. exact (strictly_order_preserving (x+) _ _).
+ apply eq_le_flip.
Qed.

Coercion add_mon_order_plus_cancel `{AdditiveMonoidOrder M} : AdditiveCancellation M.
Proof. apply alt_Build_AdditiveCancellation. intros z x y. change (z + x = z + y ⊸ x = y).
  rew <-(antisymmetry (≤) x y). apply aand_intro.
  * rew <-(order_reflecting (z+) x y). now apply subrelation.
  * rew [ (symmetry_iff (=) (z+x) (z+y)) | <-(order_reflecting (z+) y x)]. now apply subrelation.
Qed.


Section lt_le.
  Context `{AdditiveMonoidOrder (M:=R)}.

  Lemma plus_lt_le_compat x₁ `{x₁ ∊ R} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R} y₂ `{y₂ ∊ R}
    : x₁ < y₁ ⊠ x₂ ≤ y₂ ⊸ x₁ + x₂ < y₁ + y₂.
  Proof.
    rew [ ( strictly_order_preserving (+x₂) x₁ y₁ ) |( order_preserving (y₁+) x₂ y₂ ) ].
    change ((+ ?a) ?b) with (b + a). change ((?a +) ?b) with (a + b).
    apply lt_le_trans.
  Qed.

  Lemma plus_le_lt_compat x₁ `{x₁ ∊ R} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R} y₂ `{y₂ ∊ R}
    : x₁ ≤ y₁ ⊠ x₂ < y₂ ⊸ x₁ + x₂ < y₁ + y₂.
  Proof.
    rew [ ( order_preserving (+x₂) x₁ y₁ ) |( strictly_order_preserving (y₁+) x₂ y₂ ) ].
    change ((+ ?a) ?b) with (b + a). change ((?a +) ?b) with (a + b).
    apply le_lt_trans.
  Qed.
End lt_le.



Section preserves_sign.
  Context `{AdditiveMonoidOrder (M:=M)} `{AdditiveMonoidOrder (M:=N)}.
  Context (f:M ⇾ N) `{!AdditiveMonoid_Morphism f}.

  Lemma preserves_nonneg `{!OrderPreserving f} x : x ∊ M⁺ ⊸ f x ∊ N⁺.
  Proof. change (0 ≤ x ⊸ 0 ≤ f x). rew <-(preserves_0 f). exact (order_preserving f _ _). Qed.

  Lemma preserves_nonpos `{!OrderPreserving f} x : x ∊ M⁻ ⊸ f x ∊ N⁻.
  Proof. change (x ≤ 0 ⊸ f x ≤ 0). rew <-(preserves_0 f). exact (order_preserving f _ _). Qed.

  Lemma reflects_nonneg `{!OrderReflecting f} x : f x ∊ N⁺ ⊸ x ∊ M⁺.
  Proof. change (0 ≤ f x ⊸ 0 ≤ x). rew <-(preserves_0 f). exact (order_reflecting f _ _). Qed.

  Lemma reflects_nonpos `{!OrderReflecting f} x : f x ∊ N⁻ ⊸ x ∊ M⁻.
  Proof. change (f x ≤ 0 ⊸ x ≤ 0). rew <-(preserves_0 f). exact (order_reflecting f _ _). Qed.

  Lemma embeds_nonneg `{!OrderEmbedding f} x : x ∊ M⁺ ⧟ f x ∊ N⁺.
  Proof. split; [ exact (preserves_nonneg _) | exact (reflects_nonneg _) ]. Qed.

  Lemma embeds_nonpos `{!OrderEmbedding f} x : x ∊ M⁻ ⧟ f x ∊ N⁻.
  Proof. split; [ exact (preserves_nonpos _) | exact (reflects_nonpos _) ]. Qed.

  Lemma reflects_pos `{!OrderPreserving f} x : f x ∊ N₊ ⊸ x ∊ M₊.
  Proof contrapositive (preserves_nonpos x).

  Lemma reflects_neg `{!OrderPreserving f} x : f x ∊ N₋ ⊸ x ∊ M₋.
  Proof contrapositive (preserves_nonneg x).

  Lemma preserves_pos `{!OrderReflecting f} x : x ∊ M₊ ⊸ f x ∊ N₊.
  Proof contrapositive (reflects_nonpos x).

  Lemma preserves_neg `{!OrderReflecting f} x : x ∊ M₋ ⊸ f x ∊ N₋.
  Proof contrapositive (reflects_nonneg x).

  Lemma embeds_pos `{!OrderEmbedding f} x : x ∊ M₊ ⧟ f x ∊ N₊.
  Proof contrapositive_iff (embeds_nonpos x).

  Lemma embeds_neg `{!OrderEmbedding f} x : x ∊ M₋ ⧟ f x ∊ N₋.
  Proof contrapositive_iff (embeds_nonneg x).
End preserves_sign.


Lemma negate_order_embedding_flip `{AdditiveGroup (R:=R)} {Rle:Le R} `{!AdditiveMonoidOrder R}
  : OrderEmbeddingFlip (X:=R) (-).
Proof. apply alt_Build_OrderEmbeddingFlip.
  enough (∀ a b : R, a ≤ b ⊸ -b ≤ -a) as P; intros x y.
+ split; [ apply P |].
  rew <-(negate_involutive x) at 2.
  rew <-(negate_involutive y) at 2.
  apply P.
+ rew (order_preserving (-x-y+) x y : _ ⊸ -x-y+x ≤ -x-y+y).
  rew (commutativity (+) (-x) (-y)) at 1.
  rew <-!2(associativity (+) _ _ _).
  rew [ (plus_negate_l x) | (plus_negate_l y) ].
  now rew [ (plus_0_r _) | (plus_0_r _) ].
Qed.

Global Hint Extern 2 (OrderEmbeddingFlip (-)) => simple notypeclasses refine negate_order_embedding_flip : typeclass_instances.
Global Hint Extern 2 (OrderPreservingFlip (-)) => simple notypeclasses refine negate_order_embedding_flip : typeclass_instances.
Global Hint Extern 2 (OrderReflectingFlip (-)) => simple notypeclasses refine negate_order_embedding_flip : typeclass_instances.


(** The notion of [SubtractionMonoidOrder] includes linearly ordered additive groups. *)

Lemma alt_Build_AdditiveGroupOrder `{AdditiveGroup (R:=G)} {Gle:Le G} `{!LinearOrder G}
  : (∀ z:G, OrderPreserving (z+)) → SubtractionMonoidOrder G.
Proof. intro.
  assert (∀ z:G, OrderEmbedding (z+)). {
    intros z. apply alt_Build_OrderEmbedding. change ((?a +) ?b) with (a + b).
    intros x y. split; [ exact (order_preserving (z+) _ _) |].
    rew (order_preserving (-z +) (z+x) (z+y)); change ((?a +) ?b) with (a + b).
    rew ?(associativity (+) _ _ _). rew (plus_negate_l z).
    now rew ?(plus_0_l _).
  }
  split; [ now split .. | |].
  all: intros x y; exists (-x + y).
  all: rew (associativity (+) _ _ _), (plus_negate_r x), (plus_0_l _).
  all: rew (aprod_true_r (_ : y = y)).
  all: rew <-(plus_negate_l x).
  + exact (order_preserving (-x +) _ _).
  + exact (strictly_order_preserving (H:=_:OrderEmbedding (-x+)) (-x +) _ _).
Qed.

(** For both totally ordered and linear refutative ordered additive monoids,
    [decompose_lt] is derivable from [decompose_le]. *)

Lemma total_subtraction_monoid_order
  `{AdditiveMonoidOrder M}
  `{!TotalOrder M}
: (∀ x y : M, ∐ z, x ≤ y ⊸ 0 ≤ z ⊠ y = x + z)
  → SubtractionMonoidOrder M.
Proof. intros partial_minus. split; try exact _.
  intros x y.
  pose proof partial_minus x y as [z [Hz _]]; exists z.
  pose proof total (≤) x y as [E|E]; [| now apply aimpl_by_contradiction].
  specialize (Hz E). destruct Hz as [? Ey].
  rew (aprod_true_r Ey), Ey.
  rew <-(plus_0_r x) at 1.
  exact (strictly_order_reflecting (x+) _ _).
Qed.

Lemma refutative_subtraction_monoid_order
  `{AdditiveMonoidOrder M}
  `{!LinearOrder M}
  `{!RefutativeOrder M}
: (∀ x y : M, ∐ z, x ≤ y ⊸ 0 ≤ z ⊠ y = x + z)
  → SubtractionMonoidOrder M.
Proof. intros partial_minus. split; try exact _.
  intros x y.
  pose proof partial_minus x y as [z [Hz _]]; exists z.
  apply affirmative_aimpl. intros E.
  specialize (Hz (sprop.andl (lt_le _ _) E)). destruct Hz as [? Ey].
  split; trivial.
  apply (strictly_order_reflecting (x+) _ _).
  change (x + 0 < x + z). now rew [ (plus_0_r x) | <-Ey ].
Qed.



