Require Export interfaces.orders interfaces.ring_order.
Require Export orders.orders orders.maps.
Require Import theory.additive_groups.
Require Import logic.aprop relations.
Require Import easy rewrite.

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

Coercion add_mon_order_plus_cancel `{AdditiveMonoidOrder M} : AdditiveCancellation M.
Proof. apply alt_Build_AdditiveCancellation. intros z x y. change (z + x = z + y ⊸ x = y).
  rew <-(antisymmetry (≤) x y). apply aand_intro.
  * rew <-(order_reflecting (z+) x y). now apply subrelation.
  * rew [ (symmetry_iff (=) (z+x) (z+y)) | <-(order_reflecting (z+) y x)]. now apply subrelation.
Qed.

Lemma alt_Build_AdditiveGroupOrder `{AdditiveGroup (R:=G)} {Gle:Le G} `{!Poset G}
  : (∀ z:G, OrderPreserving (z+)) → SubtractionMonoidOrder G.
Proof. intro. split; [ split; try exact _ |].
+ intros z. apply alt_Build_OrderEmbedding. change ((?a +) ?b) with (a + b).
  intros x y. split; [ exact (order_preserving (z+) _ _) |].
  rew (order_preserving (-z +) (z+x) (z+y)); change ((?a +) ?b) with (a + b).
  rew ?(associativity (+) _ _ _). rew (plus_negate_l z).
  now rew ?(plus_0_l _).
+ intros x y. exists (-x + y).
  rew (associativity (+) _ _ _), (plus_negate_r x), (plus_0_l _).
  now rew (aiff_is_true (_ : y = y)).
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


