Require Export interfaces.orders interfaces.ring_order.
Require Export orders.orders orders.maps orders.suborders.
Require Import theory.additive_groups theory.subrings.
Require Import logic.aprop relations.
Require Import easy rewrite simplify tactics.misc.

(** Ordered Monoids *)

Import cone_notation.
Lemma nonneg_dual `{WeakPoset P} {z:Zero P} {x:P} : DeMorganDual (x ∊ P⁺) (x ∊ P₋).  Proof. exact (_ : DeMorganDual (0 ≤ x) _). Qed.
Lemma nonpos_dual `{WeakPoset P} {z:Zero P} {x:P} : DeMorganDual (x ∊ P⁻) (x ∊ P₊).  Proof. exact (_ : DeMorganDual (x ≤ 0) _). Qed.
Lemma pos_dual    `{WeakPoset P} {z:Zero P} {x:P} : DeMorganDual (x ∊ P₊) (x ∊ P⁻).  Proof. exact (_ : DeMorganDual (0 < x) _). Qed.
Lemma neg_dual    `{WeakPoset P} {z:Zero P} {x:P} : DeMorganDual (x ∊ P₋) (x ∊ P⁺).  Proof. exact (_ : DeMorganDual (x < 0) _). Qed.
Global Hint Extern 2 (DeMorganDual (_ ∊ _⁺) _) => notypeclasses refine nonneg_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ ∊ _⁻) _) => notypeclasses refine nonpos_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ ∊ _₊) _) => notypeclasses refine pos_dual : typeclass_instances.
Global Hint Extern 2 (DeMorganDual (_ ∊ _₋) _) => notypeclasses refine neg_dual : typeclass_instances.

Lemma plus_r_order_embedding `{AdditiveMonoidOrder M} : ∀ {z:M}, OrderEmbedding (+z).
Proof. exact (right_order_embedding_from_left (@plus_l_order_embedding _ _ _ _ _)). Qed.
Global Hint Extern 2 (OrderEmbedding (+_)) => simple notypeclasses refine plus_r_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (+_)) => simple notypeclasses refine plus_r_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (+_)) => simple notypeclasses refine plus_r_order_embedding : typeclass_instances.

Lemma plus_order_preserving `{AdditiveMonoidOrder M} : OrderPreserving (Y:=M) (+).
Proof. apply alt_Build_OrderPreserving.
  intros [x₁ y₁][x₂ y₂]. unfold_pair_le.
  rew ( order_preserving_simp (+ y₁) x₁ x₂).
  rew ( order_preserving_simp (x₂ +) y₁ y₂).
  now apply transitivity.
Qed.
Global Hint Extern 2 (OrderPreserving (+)) => simple notypeclasses refine plus_order_preserving : typeclass_instances.

Lemma compose_le `{AdditiveMonoidOrder M} (x y z : M) : 0 ≤ z ⊠ y = x + z ⊸ x ≤ y.
Proof. rew <-(transitivity (≤) x (x + z) y). apply aprod_proper_aimpl.
+ exact (order_preserving_simp (x+) _ _).
+ apply eq_le_flip.
Qed.

Lemma compose_lt `{AdditiveMonoidOrder M} (x y z : M) : 0 < z ⊠ y = x + z ⊸ x < y.
Proof. rew <-(lt_le_trans x (x+z) y). apply aprod_proper_aimpl.
+ exact (strictly_order_preserving_simp (x+) _ _).
+ apply eq_le_flip.
Qed.

Coercion add_mon_order_plus_cancel `{AdditiveMonoidOrder M} : AdditiveCancellation M.
Proof. apply alt_Build_AdditiveCancellation. intros z x y; simplify.
  rew <-(antisymmetry (≤) x y). apply aand_intro.
  * rew <-(order_reflecting_simp (z+) x y). now apply subrelation.
  * rew [ (symmetry_iff (=) (z+x) (z+y)) | <-(order_reflecting_simp (z+) y x)]. now apply subrelation.
Qed.


Lemma add_mon_order_nonneg_sub_mon `{AdditiveMonoidOrder M} : AdditiveSubMonoid M⁺.
Proof. apply alt_Build_AdditiveSubMonoid.
+ intros x y. change (0 ≤ x ⊠ 0 ≤ y ⊸ 0 ≤ x + y).
  rew (order_embedding_simp (x+) 0 y). now apply transitivity.
+ now change (0 ≤ 0 :> M).
Qed.
Global Hint Extern 2 (AdditiveSubMonoid _⁺) => simple notypeclasses refine add_mon_order_nonneg_sub_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveSubSemiGroup _⁺) => simple notypeclasses refine add_mon_order_nonneg_sub_mon : typeclass_instances.


Lemma add_mon_order_nonneg_order `{AdditiveMonoidOrder M} : AdditiveMonoidOrder M⁺.
Proof. split; try exact _.
  intros z. apply alt_Build_OrderEmbedding. intros x y.
  exact (order_embedding (subset_pt z +) (subset_pt _) (subset_pt _)).
Qed.
Global Hint Extern 2 (AdditiveMonoidOrder (subset_to_set _⁺)) => simple notypeclasses refine add_mon_order_nonneg_order : typeclass_instances.
Global Hint Extern 4 (AdditiveCancellation (subset_to_set _⁺)) => simple notypeclasses refine add_mon_order_nonneg_order : typeclass_instances.


Section lt_le.
  Context `{AdditiveMonoidOrder (M:=R)}.

  Lemma plus_lt_le_compat (x₁ y₁ x₂ y₂ : R) : x₁ < y₁ ⊠ x₂ ≤ y₂ ⊸ x₁ + x₂ < y₁ + y₂.
  Proof.
    rew [ ( strictly_order_preserving_simp (+x₂) x₁ y₁ ) |( order_preserving_simp (y₁+) x₂ y₂ ) ].
    apply lt_le_trans.
  Qed.

  Lemma plus_le_lt_compat (x₁ y₁ x₂ y₂ : R) : x₁ ≤ y₁ ⊠ x₂ < y₂ ⊸ x₁ + x₂ < y₁ + y₂.
  Proof.
    rew [ ( order_preserving_simp (+x₂) x₁ y₁ ) |( strictly_order_preserving_simp (y₁+) x₂ y₂ ) ].
    apply le_lt_trans.
  Qed.
End lt_le.


(*
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
*)

Section preserves_sign.
  Universes u.
  Context `{AdditiveMonoidOrder@{u} (M:=M)} `{AdditiveMonoidOrder@{u} (M:=N)}.
  Context (f:M ⇾ N) `{!AdditiveMonoid_Morphism f}.

  Lemma preserves_nonneg `{!OrderPreserving f} x : 0 ≤ x ⊸ 0 ≤ f x.
  Proof. rew <-(preserves_0 f). exact (order_preserving f _ _). Qed.

  Lemma preserves_nonpos `{!OrderPreserving f} x : x ≤ 0 ⊸ f x ≤ 0.
  Proof. rew <-(preserves_0 f). exact (order_preserving f _ _). Qed.

  Lemma reflects_nonneg `{!OrderReflecting f} x : 0 ≤ f x ⊸ 0 ≤ x.
  Proof. rew <-(preserves_0 f). exact (order_reflecting f _ _). Qed.

  Lemma reflects_nonpos `{!OrderReflecting f} x : f x ≤ 0 ⊸ x ≤ 0.
  Proof. rew <-(preserves_0 f). exact (order_reflecting f _ _). Qed.

  Lemma embeds_nonneg `{!OrderEmbedding f} x : 0 ≤ x ⧟ 0 ≤ f x.
  Proof. split; [ exact (preserves_nonneg _) | exact (reflects_nonneg _) ]. Qed.

  Lemma embeds_nonpos `{!OrderEmbedding f} x : x ≤ 0 ⧟ f x ≤ 0.
  Proof. split; [ exact (preserves_nonpos _) | exact (reflects_nonpos _) ]. Qed.

  Lemma reflects_pos `{!OrderPreserving f} x : 0 < f x ⊸ 0 < x.
  Proof. exact (contrapositive (preserves_nonpos x)). Qed.

  Lemma reflects_neg `{!OrderPreserving f} x : f x < 0 ⊸ x < 0.
  Proof. exact (contrapositive (preserves_nonneg x)). Qed.

  Lemma preserves_pos `{!OrderReflecting f} x : 0 < x ⊸ 0 < f x.
  Proof. exact (contrapositive (reflects_nonpos x)). Qed.

  Lemma preserves_neg `{!OrderReflecting f} x : x < 0 ⊸ f x < 0.
  Proof. exact (contrapositive (reflects_nonneg x)). Qed.

  Lemma embeds_pos `{!OrderEmbedding f} x : 0 < x ⧟ 0 < f x.
  Proof. exact (contrapositive_iff (embeds_nonpos x)). Qed.

  Lemma embeds_neg `{!OrderEmbedding f} x : x < 0 ⧟ f x < 0.
  Proof. exact (contrapositive_iff (embeds_nonneg x)). Qed.
End preserves_sign.

Section preserves_sign_flip.
  Universes u.
  Context `{AdditiveMonoidOrder@{u} (M:=M)} `{AdditiveMonoidOrder@{u} (M:=N)}.
  Context (f:M ⇾ N) `{!AdditiveMonoid_Morphism f}.

  Lemma preserves_nonneg_flip `{!OrderPreservingFlip f} x : 0 ≤ x ⊸ f x ≤ 0.
  Proof. rew <-(preserves_0 f). exact (order_preserving_flip f _ _). Qed.

  Lemma preserves_nonpos_flip `{!OrderPreservingFlip f} x : x ≤ 0 ⊸ 0 ≤ f x.
  Proof. rew <-(preserves_0 f). exact (order_preserving_flip f _ _). Qed.

  Lemma reflects_nonneg_flip `{!OrderReflectingFlip f} x : 0 ≤ f x ⊸ x ≤ 0.
  Proof. rew <-(preserves_0 f). exact (order_reflecting_flip f _ _). Qed.

  Lemma reflects_nonpos_flip `{!OrderReflectingFlip f} x : f x ≤ 0 ⊸ 0 ≤ x.
  Proof. rew <-(preserves_0 f). exact (order_reflecting_flip f _ _). Qed.

  Lemma embeds_nonneg_flip `{!OrderEmbeddingFlip f} x : 0 ≤ x ⧟ f x ≤ 0.
  Proof. split; [ exact (preserves_nonneg_flip _) | exact (reflects_nonpos_flip _) ]. Qed.

  Lemma embeds_nonpos_flip `{!OrderEmbeddingFlip f} x : x ≤ 0 ⧟ 0 ≤ f x.
  Proof. split; [ exact (preserves_nonpos_flip _) | exact (reflects_nonneg_flip _) ]. Qed.

  Lemma reflects_pos_flip `{!OrderPreservingFlip f} x : 0 < f x ⊸ x < 0.
  Proof. exact (contrapositive (preserves_nonneg_flip x)). Qed.

  Lemma reflects_neg_flip `{!OrderPreservingFlip f} x : f x < 0 ⊸ 0 < x.
  Proof. exact (contrapositive (preserves_nonpos_flip x)). Qed.

  Lemma preserves_pos_flip `{!OrderReflectingFlip f} x : 0 < x ⊸ f x < 0.
  Proof. exact (contrapositive (reflects_nonneg_flip x)). Qed.

  Lemma preserves_neg_flip `{!OrderReflectingFlip f} x : x < 0 ⊸ 0 < f x.
  Proof. exact (contrapositive (reflects_nonpos_flip x)). Qed.

  Lemma embeds_pos_flip `{!OrderEmbeddingFlip f} x : 0 < x ⧟ f x < 0.
  Proof. exact (contrapositive_iff (embeds_nonpos_flip x)). Qed.

  Lemma embeds_neg_flip `{!OrderEmbeddingFlip f} x : x < 0 ⧟ 0 < f x.
  Proof. exact (contrapositive_iff (embeds_nonneg_flip x)). Qed.
End preserves_sign_flip.


(** Ordered Groups *)

Coercion AdditiveGroupOrder_AdditiveMonoidOrder `{AdditiveGroupOrder (G:=G)} : AdditiveMonoidOrder G.
Proof. split; [ exact _ ..|]. intros z. apply alt_Build_OrderEmbedding. intros x y; simplify; split.
+ apply (add_group_plus_order_preserving G _).
+ pose proof add_group_plus_order_preserving G _ (-z).
  now rew (order_preserving_simp (-z +) (z+x) (z+y)).
Qed.

Lemma negate_order_embedding_flip `{AdditiveGroupOrder (G:=G)} : OrderEmbeddingFlip (X:=G) (-).
Proof. apply (involutive_order_embedding_flip _). apply alt_Build_OrderPreservingFlip.
  intros x y. now rew (order_preserving_simp (-x-y+) x y).
Qed.

Global Hint Extern 2 (OrderEmbeddingFlip (-)) => simple notypeclasses refine negate_order_embedding_flip : typeclass_instances.
Global Hint Extern 2 (OrderPreservingFlip (-)) => simple notypeclasses refine negate_order_embedding_flip : typeclass_instances.
Global Hint Extern 2 (OrderReflectingFlip (-)) => simple notypeclasses refine negate_order_embedding_flip : typeclass_instances.


Lemma nonneg_between `{AdditiveGroupOrder (G:=G)} `{!StrongPoset G} (x:G) : 0 ≤ x ⊸ -x ≤ x.
Proof.
  rew <-(strong_transitivity (≤) (-x) 0 x).
  rew <-(preserves_nonneg_flip (-) x).
  now simplify.
Qed.

Lemma nonpos_between `{AdditiveGroupOrder (G:=G)} `{!StrongPoset G} (x:G) : x ≤ 0 ⊸ x ≤ -x.
Proof.
  rew <-(strong_transitivity (≤) x 0 (-x)).
  rew <-(preserves_nonpos_flip (-) x).
  now simplify.
Qed.

Lemma between_neg `{AdditiveGroupOrder (G:=G)} `{!StrongPoset G} (x:G) : x < -x ⊸ x < 0.
Proof. exact (contrapositive (nonneg_between x)). Qed.

Lemma between_pos `{AdditiveGroupOrder (G:=G)} `{!StrongPoset G} (x:G) : -x < x ⊸ 0 < x.
Proof. exact (contrapositive (nonpos_between x)). Qed.


Lemma pos_between `{AdditiveGroupOrder (G:=G)} `{!LinearOrder G, !RefutativeOrder G} (x:G) : 0 < x ⊸ -x < x.
Proof.
  apply affirmative_aimpl; intro.
  rew <-(transitivity (<) (-x) 0 x).
  now rew <-(preserves_pos_flip (-) x).
Qed.

Lemma neg_between `{AdditiveGroupOrder (G:=G)} `{!LinearOrder G, !RefutativeOrder G} (x:G) : x < 0 ⊸ x < -x.
Proof.
  apply affirmative_aimpl; intro.
  rew <-(transitivity (<) x 0 (-x)).
  now rew <-(preserves_neg_flip (-) x).
Qed.

Lemma between_nonneg `{AdditiveGroupOrder (G:=G)} `{!LinearOrder G, !RefutativeOrder G} (x:G) : -x ≤ x ⊸ 0 ≤ x.
Proof. exact (contrapositive (neg_between x)). Qed.

Lemma between_nonpos `{AdditiveGroupOrder (G:=G)} `{!LinearOrder G, !RefutativeOrder G} (x:G) : x ≤ -x ⊸ x ≤ 0.
Proof. exact (contrapositive (pos_between x)). Qed.

