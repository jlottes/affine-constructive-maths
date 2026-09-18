Require Import interfaces.abstract_algebra interfaces.orders interfaces.ring_order.
Require Import implementations.nat theory.nno theory.naturals orders.naturals.
Require Import implementations.grothendieck_group theory.integers theory.group_completion.
Require Import theory.groups theory.rings theory.subrings.
Require Import orders.orders orders.suborders orders.groups orders.rings.
Require Import rewrite replc easy tactics.misc rewrite_preserves simplify.
Require Import logic.aprop logic.relations.
Require Import tactics.algebra.com_monoids.

Local Open Scope mult_scope.

Section int_to_ring.
  Universes u.
  Context `{OrderedIntegers@{u} Z}.

  Abbreviation ϕ₁ := (naturals_to_mon Nat Z).

  Lemma integers_le_plus_1 (x y : Z) : x ≤ y ⧟ x < 1 + y.
  Proof.
    pose proof group_completion_decompose ϕ₁ x as [a[b Ex]]; rew Ex; clear Ex x.
    pose proof group_completion_decompose ϕ₁ y as [c[d Ey]]; rew Ey; clear Ey y.
    rew (associativity (+) _ _ _).
    rew [(minus_le_swap _ _ _ _) | (minus_lt_swap _ _ _ _)].
    rew <-(preserves_1 ϕ₁). rew <-?(preserves_plus ϕ₁ _ _).
    rew [<-(order_embedding ϕ₁ _ _) | <-(strictly_order_embedding ϕ₁ _ _) ].
    rew <-(associativity (+) _ _ _).
    exact (naturals_le_plus_1 _ _).
  Qed.

  Lemma integers_lt_plus_1 (x y : Z) : x < y ⧟ 1 + x ≤ y.
  Proof. exact (contrapositive_iff (integers_le_plus_1 y x)). Qed.

  Context `{StrongLinearRefutativeRingOrder@{u} R} `{!OneNonZero R}.
  Context (f:Z ⇾ R) `{!Rig_Morphism f}.

  Abbreviation ϕ₂ := (naturals_to_mon Nat R).

  Lemma integers_to_ring_ord_embedding: OrderEmbedding f.
  Proof.
    apply alt_Build_OrderEmbedding.
    intros x y.
    pose proof group_completion_decompose ϕ₁ x as [a[b Ex]]; rew Ex; clear Ex x.
    pose proof group_completion_decompose ϕ₁ y as [c[d Ey]]; rew Ey; clear Ey y.
    rewrite_preserves f. rew [(minus_le_swap (ϕ₁ a) _ _ _) | (minus_le_swap (f (ϕ₁ a)) _ _ _)].
    change (func_op f (func_op ϕ₁ ?z)) with ((f ∘ ϕ₁) z); rew (naturals_initial  (f ∘ ϕ₁)).
    rew [<-(preserves_plus ϕ₁ _ _) | <-(preserves_plus ϕ₂ _ _)].
    now rew [<-(order_embedding ϕ₁ _ _) | <-(order_embedding ϕ₂ _ _)].
  Qed.
End int_to_ring.
Global Hint Extern 2 (OrderEmbedding (integers_to_group _ _)) => simple notypeclasses refine (integers_to_ring_ord_embedding _) : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (integers_to_group _ _)) => simple notypeclasses refine (integers_to_ring_ord_embedding _) : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (integers_to_group _ _)) => simple notypeclasses refine (integers_to_ring_ord_embedding _) : typeclass_instances.


Section integers_le_plus_aux.
  Universes u.
  Context `{Integers@{u} Z}.
  Context `{Naturals@{u} N}.

  Abbreviation ϕ := (naturals_to_mon N Z).

  Let inst : Injective ϕ.  Proof. exact naturals_to_integers_inj. Qed.

  Lemma integers_le_plus_aux {x y a b c d} : x = ϕ a - ϕ b → y = ϕ c - ϕ d →
    a + d ≤ c + b ⧟ (∐ z : N, y = x + ϕ z) .
  Proof. intros Ex Ey.
    rew (naturals_le_plus _ _). apply aex_aiff. intros z.
    rew [Ex|Ey]; clear x y Ex Ey.
    replc (ϕ a - ϕ b + ϕ z) with (ϕ a + ϕ z - ϕ b) by add_mon.
    rew (injective_iff_simp (+ (ϕ b + ϕ d)) (ϕ c - ϕ d) (ϕ a + ϕ z - ϕ b)).
    rew <-(associativity (+) (ϕ c) _ _), <-(associativity (+) (ϕ a + ϕ z) _ _); simplify.
    replc (ϕ a + ϕ z + ϕ d) with (ϕ a + ϕ d + ϕ z) by add_mon.
    rew <-?(preserves_plus ϕ _ _).
    exact (injective_iff ϕ _ _).
  Qed.
End integers_le_plus_aux.


(** Characterization of the order on the integers as x ≤ y ⧟ ∐ z:ℕ, y = x + z *)
Section integers_le_plus.
  Universes u.
  Context `{OrderedIntegers@{u} Z}.
  Context `{Naturals@{u} N}.

  Abbreviation ϕ := (naturals_to_mon N Z).

  Lemma integers_le_plus_nat : ∀ x y : Z, x ≤ y ⧟ ∐ z, y = x + ϕ z.
  Proof. intros x y.
    pose proof group_completion_decompose ϕ x as [a [b Ex]].
    pose proof group_completion_decompose ϕ y as [c [d Ey]].
    rew (group_completion_order_le ϕ Ex Ey).
    exact (integers_le_plus_aux Ex Ey).
  Qed.

  Context (f:N ⇾ Z) `{!Rig_Morphism f}.

  Lemma integers_le_plus_nat_alt : ∀ x y : Z, x ≤ y ⧟ ∐ z, y = x + f z.
  Proof. rew (naturals_initial f). exact integers_le_plus_nat. Qed.
End integers_le_plus.


(** In the other direction, x ≤ y ⧟ ∐ z:ℕ, y = x + z  gives a ring order on ℤ. *)
Section props2.
  Universes u.
  Context `{Integers@{u} Z} {Zle: Le Z}.

  Abbreviation ℕ := Nat.
  Abbreviation ϕ := (naturals_to_mon ℕ Z).

  Context (le_plus : ∀ x y : Z, x ≤ y ⧟ ∐ z, y = x + ϕ z).

  Let le_correct : ∀ x y a b c d, x = ϕ a - ϕ b → y = ϕ c - ϕ d → x ≤ y ⧟ a + d ≤ c + b.
  Proof. intros x y a b c d Ex Ey. rew (le_plus _ _). sym. exact (integers_le_plus_aux Ex Ey). Qed.

  Local Instance: AdditiveGroupOrder Z.
  Proof. exact (group_completion_add_grp_order ϕ le_correct). Qed.

  Local Instance: OrderEmbedding ϕ.
  Proof. exact (to_group_completion_order_embedding ϕ le_correct). Qed.

  Lemma alt_Build_OrderedIntegers : OrderedIntegers Z.
  Proof. split; try exact _. exact (group_completion_ring_order (i:=ϕ)). Qed.
End props2.


(** More properties that follow from being the group completion of ℕ. *)
Section props3.
  Universes u.
  Context `{OrderedIntegers@{u} Z}.

  Abbreviation ℕ := Nat.
  Abbreviation ϕ := (naturals_to_mon ℕ Z).

  Definition integers_strong_poset : StrongPoset Z  := group_completion_strong_poset ϕ.
  Definition integers_total_order : TotalOrder Z  := group_completion_total_order ϕ.
  Definition integers_decidable_order : DecidableOrder Z  := group_completion_decidable_order ϕ.
End props3.

Coercion integers_strong_poset    : OrderedIntegers >-> StrongPoset.
Coercion integers_total_order     : OrderedIntegers >-> TotalOrder.
Coercion integers_decidable_order : OrderedIntegers >-> DecidableOrder.


(** Default construction of the order. *)
Definition integers_le (Z:set) {p:Plus Z} {z:Zero Z} {o:One Z} : Le Z := λ '(x, y), ∐ z:Nat, y = x + naturals_to_mon Nat Z z.

Global Hint Extern 2 (Le (set_T (ring_car (ints_ring ?Z)))) => simple refine (integers_le Z) : typeclass_instances.
Global Hint Extern 50 (Le (set_T ?Z)) => let t := get_instance constr:(IntegersToGroup Z) in simple refine (integers_le Z) : typeclass_instances.

Lemma integers_le_correct {Z:set} {p:Plus Z} {z:Zero Z} {o:One Z} : ∀ x y : Z, @le Z (integers_le Z) (x, y) ⧟ ∐ z, y = x + naturals_to_mon Nat Z z.
Proof. now intros x y. Qed.

Definition integers_le_order `{Integers Z} : OrderedIntegers Z (leZ:=integers_le Z) := alt_Build_OrderedIntegers integers_le_correct.


Global Hint Extern 2 (OrderedIntegers _ (leZ:=integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@TotalOrder _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@LinearOrder _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@DecidableOrder _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@AffirmativeLe _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@AffirmativeOrder _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@DecidableLe _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@Poset _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@PreOrder _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@RefutativeLe _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@StrongLe _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@StrongPoset _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (@WeakPoset _ (integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoidOrder _ (Mle:=integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (AdditiveGroupOrder _ (Gle:=integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (StrongLinearRefutativeRigOrder _ (Rle:=integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.
Global Hint Extern 2 (StrongLinearRefutativeRingOrder _ (Rle:=integers_le _)) => simple notypeclasses refine integers_le_order : typeclass_instances.


(** We always have, in principle, a function ℤ ⇾ ℕ taking x to |x|. *)
Section integers_abs_slow.
  Universes u.
  Context `{OrderedIntegers@{u} Z}.

  Local Abbreviation ϕ := (naturals_to_mon Nat Z).

  Definition integers_abs_slow_op : Z → Nat := λ x,
  match nat_subtract (group_completion_split ϕ x) with
  | natsubtract.is_lt_by z => z
  | natsubtract.is_eq => 0
  | natsubtract.is_gt_by z => z
  end.

  Lemma integers_abs_slow_op_nonneg x {Px:0 ≤ x} : ϕ (integers_abs_slow_op x) = x .
  Proof. unfold integers_abs_slow_op.
    generalize (group_completion_split_spec ϕ x);
      destruct (group_completion_split ϕ x) as [a b]; simplify; intros Ex; rew Ex; rew Ex in Px.
    generalize (nat_subtract_spec a b); destruct (nat_subtract (a, b)) as [m| |m].
    + intros [Eb _]; rew <-Eb; rewrite_preserves ϕ; rew (negate_plus_distr _ _); simplify.
      sym. rew (to_ring_zero_sum_alt ϕ _ _). enough (m = 0) by now split.
      apply le_antisym. split; [| apply naturals_nonneg ].
      revert Px. rew <-Eb; rewrite_preserves ϕ; rew (negate_plus_distr _ _); simplify.
      rew (order_embedding_simp (+ ϕ m) _ _). intro. now rew <-(reflects_nonpos ϕ _).
    + intro E; rew E; simplify; exact (preserves_0 _).
    + intros [Ea _]; rew Ea; rewrite_preserves ϕ; now simplify.
  Qed.

  Lemma integers_abs_slow_op_nonpos x {Px:x ≤ 0} : ϕ (integers_abs_slow_op x) = -x .
  Proof. unfold integers_abs_slow_op.
    generalize (group_completion_split_spec ϕ x);
      destruct (group_completion_split ϕ x) as [a b]; simplify; intros Ex; rew Ex; rew Ex in Px.
    generalize (nat_subtract_spec a b); destruct (nat_subtract (a, b)) as [m| |m].
    + intros [Eb _]; rew <-Eb; rewrite_preserves ϕ; rew (negate_plus_distr _ _); now simplify.
    + intro E; rew E; simplify; exact (preserves_0 _).
    + intros [Ea _]; rew Ea; rewrite_preserves ϕ; simplify.
      sym. rew (to_ring_zero_sum_alt ϕ _ _). enough (m = 0) by now split.
      apply le_antisym. split; [| apply naturals_nonneg ].
      revert Px. rew Ea; rewrite_preserves ϕ; simplify.
      intro. now rew <-(reflects_nonpos ϕ _).
  Qed.

  Lemma integers_abs_slow_is_fun : IsFun integers_abs_slow_op.
  Proof. intros x y. apply affirmative_aimpl. intros E. apply (injective ϕ).
    destruct ( total (≤) 0 x ) as [Ex|Ex].
  + assert (0 ≤ y) by now rew <-E. now rew (integers_abs_slow_op_nonneg _).
  + assert (y ≤ 0) by now rew <-E. rew (integers_abs_slow_op_nonpos _). now rew E.
  Qed.

  Definition integers_abs_slow : Z ⇾ Nat := @func_make _ _ _ integers_abs_slow_is_fun.

  Lemma integers_abs_slow_nonneg x {Px:0 ≤ x} : ϕ (integers_abs_slow x) = x .
  Proof. exact (integers_abs_slow_op_nonneg x). Qed.

  Lemma integers_abs_slow_nonpos x {Px:x ≤ 0} : ϕ (integers_abs_slow x) = -x .
  Proof. exact (integers_abs_slow_op_nonpos x). Qed.
End integers_abs_slow.
Arguments integers_abs_slow Z {_ _ _ _ _ _ _ _}.


(** The nonnegative integers are the naturals. *)
Import cone_notation.
Section nonneg_is_naturals.
  Universes u.
  Context `{OrderedIntegers@{u} Z}.

  Local Abbreviation ϕ₁ := (naturals_to_mon Nat Z).
  Local Abbreviation ϕ₂ := (naturals_to_mon Nat (subset_to_set Z⁺)).

  Definition nonneg_to_nat : Z⁺ ⇾ Nat := integers_abs_slow _ ∘ (from_subset _).

  Local Hint Extern 2 (Inverse ϕ₂) => refine nonneg_to_nat : typeclass_instances.

  Local Instance nat_to_nonneg_surj : Surjective ϕ₂.
  Proof. red. apply (injective_compose_cancel (from_subset Z⁺) _ _).
    change ((from_subset _ ∘ ϕ₂) ∘ integers_abs_slow _ ∘ from_subset Z⁺ = from_subset _).
    rew (naturals_initial (from_subset _ ∘ ϕ₂)).
    intros [x elx]. exact (integers_abs_slow_nonneg x).
  Qed.
  Local Instance nat_to_nonneg_bij : Bijective ϕ₂.  Proof. now split. Qed.

  Local Instance nonneg_int_to_mon : NaturalsToMon Z⁺ := retract_is_nat_to_mon ϕ₂.
  Lemma nonneg_int_naturals : Naturals Z⁺.   Proof. exact (retract_is_nat ϕ₂). Qed.
End nonneg_is_naturals.
Global Hint Extern 2 (NaturalsToMon (subset_to_set _⁺)) => refine nonneg_int_to_mon : typeclass_instances.
Global Hint Extern 2 (Naturals (subset_to_set _⁺)) => refine nonneg_int_naturals : typeclass_instances.


