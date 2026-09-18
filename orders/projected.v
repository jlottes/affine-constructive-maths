Require Import orders.orders orders.maps theory.set theory.projected_set.
Require Import logic.aprop relations easy rewrite tactics.misc.

Record IsProjectedOrder@{u} (A:Type@{u}) {Ae:Equiv A} {Ale:Le A} {Y:set@{u}} {Yle:Le Y} (f:A → Y) : SProp :=
{ #[canonical=no, reversible=no] projected_order_set :> IsProjectedSet A (f:=f)
; is_projected_order : ∀ x y, x ≤ y ⧟ f x ≤ f y
}.
Existing Class IsProjectedOrder.
Arguments is_projected_order {A _ _ _ _} f {_} x y.

Section projected_order.
  Universes u.
  Context {X:set@{u}} {Xle:Le X} {Y:set@{u}} {Yle:Le Y} (f:X → Y) `{!IsProjectedOrder X f}.
  
  Local Instance projected_preorder `{!PreOrder Y} : PreOrder X.
  Proof. split; hnf; intros; rew (is_projected_order f _ _).
  + refl.
  + now apply transitivity.
  Qed.
  
  Local Instance projected_weak_poset `{!WeakPoset Y} : WeakPoset X.
  Proof. split; try exact _.
  + intros [x y]. rew [(is_projected_set (f:=f) _ _)|(is_projected_order f _ _)]. exact (eq_le _ _).
  + intros x y. rew [(is_projected_set (f:=f) _ _)|(is_projected_order f _ _)]. now apply pseudo_antisymmetry.
  Qed.
  
  Lemma projected_order_embedding `{!WeakPoset Y} : OrderEmbedding (projected_set_project X (f:=f)).
  Proof. apply alt_Build_OrderEmbedding. exact (is_projected_order f). Qed.

  Local Instance projected_poset `{!Poset Y} : Poset X.
  Proof. split; try exact _.
    intros x y. rew [(is_projected_set (f:=f) _ _)|(is_projected_order f _ _)]. now apply antisymmetry.
  Qed.

  Local Instance projected_strong_le `{!StrongLe Y} : StrongLe X.
  Proof. intros x y z. rew (is_projected_order f _ _). now apply strong_transitivity. Qed.

  Local Instance projected_decidable_le `{!DecidableLe Y} : DecidableLe X.
  Proof. intros [x y]. now rew (is_projected_order f _ _). Qed.

  Local Instance projected_affirmative_le `{!AffirmativeLe Y} : AffirmativeLe X.
  Proof. intros [x y]. now rew (is_projected_order f _ _). Qed.

  Local Instance projected_refutative_le `{!RefutativeLe Y} : RefutativeLe X.
  Proof. intros [x y]. now rew (is_projected_order f _ _). Qed.
  
  Local Instance projected_strong_poset      `{!StrongPoset      Y} : StrongPoset      X.   Proof. now split. Qed.
  Local Instance projected_decidable_order   `{!DecidableOrder   Y} : DecidableOrder   X.   Proof. now split. Qed.
  Local Instance projected_affirmative_order `{!AffirmativeOrder Y} : AffirmativeOrder X.   Proof. now split. Qed.
  Local Instance projected_refutative_order  `{!RefutativeOrder  Y} : RefutativeOrder  X.   Proof. now split. Qed.

  Local Instance projected_total_order `{!TotalOrder Y} : TotalOrder X.
  Proof. split; try exact _.
    intros x y. rew (is_projected_order f _ _). now apply total.
  Qed.

  Local Instance projected_linear_order `{!LinearOrder Y} : LinearOrder X.
  Proof. split; try exact _.
    intros x y. rew (is_projected_order f _ _). now apply pseudo_total.
  Qed.
End projected_order.


