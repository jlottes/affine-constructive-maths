Require Import implementations.nat theory.naturals.
Require Import interfaces.orders interfaces.ring_order.
Require Import theory.groups theory.rings.
Require Import orders.orders orders.groups orders.rings.
Require Import rewrite easy tactics.misc simplify rewrite_preserves.
Require Import logic.aprop logic.relations.

Local Open Scope mult_scope.


(** Characterization of the order on the naturals as x ≤ y ⧟ ∐ z, y = x + z *)
Section naturals_le_plus.
  Context `{OrderedNaturals (N:=N)}.

  Local Instance naturals_nonneg : ∀ (x:N), 0 ≤ x.
  Proof. naturals_induction.
  + refl.
  + intros n E. rew <-E. now simplify.
  Qed.

  Lemma naturals_le_plus_1 (x y : N) : x ≤ y ⧟ x < 1 + y.
  Proof. pose proof naturals_distance x y as [z [Ez|Ez]].
  + rew <-Ez, <-(order_embedding_simp (x+) 0 z).
    pose proof (naturals_nonneg z) as Pz; simplify; rew <-Pz; simplify.
    now rew <-(strictly_order_embedding_simp (+x) 0 1).
  + rew Ez. apply by_contrapositive_iff.
    rew <-(strictly_order_embedding_simp (y+) 0 z).
    rew (commutativity (+) 1 y).
    rew <-(order_embedding_simp (y+) 1 z).
    destruct (nno_zero_or_suc z) as [E|[b E]].
    * rew  E. apply by_contrapositive_iff; now simplify.
    * change (suc b) with (1 + b) in E; rew E.
      match goal with |- apos (?P ⧟ ?Q) => enough (P ∧ Q) as [H1 H2] by now simplify end; split;
      rew <-(naturals_nonneg b); now simplify.
  Qed.

  Lemma naturals_lt_plus_1 (x y : N) : x < y ⧟ 1 + x ≤ y.
  Proof. exact (contrapositive_iff (naturals_le_plus_1 y x)). Qed.

  Lemma naturals_le_plus : ∀ x y : N, x ≤ y ⧟ ∐ z, y = x + z .
  Proof. naturals_induction.
  + intros y. pose proof _ : 0 ≤ y. simplify. exists y. now simplify.
  + intros x P y. destruct (nno_zero_or_suc y) as [E|[b E]].
    * rew E. apply by_contrapositive_iff.
      rew <-(naturals_le_plus_1 _ _); pose proof (naturals_nonneg x); simplify.
      intros z. rew (symmetry_iff (=) _ _), <-(associativity (+) _ _ _). exact (nno_suc_nonzero (x + z)).
    * change (apos (y = 1 + b)) in E. rew E.
      rew <-exact:(order_embedding_simp (1+) x b).
      rew (P b). apply aex_aiff. intros w. rew <-(associativity (+) _ _ _).
      exact (injective_iff (1+) b (x+w)).
  Qed.

  Context `{StrongLinearRefutativeRigOrder R} `{!OneNonZero R}.
  Context  (f:N ⇾ R) `{!Rig_Morphism f}.
  Lemma naturals_to_rig_ord_embedding: OrderEmbedding f.
  Proof.
    apply alt_Build_OrderEmbedding.
    intros x y.
    pose proof naturals_distance x y as [z[E|E]].
  + rew <-E. rewrite_preserves f.
    rew <-(order_embedding_simp (x+) 0 z), <-(order_embedding_simp (f x +) 0 (f z)).
    clear E x y. pose proof (naturals_nonneg z) as P; simplify; clear P.
    revert z. naturals_induction.
    * now rewrite_preserves f.
    * intros n E. rewrite_preserves f. rew <-E. now simplify.
  + apply by_contrapositive_iff. rew E. rewrite_preserves f.
    rew <-(strictly_order_embedding_simp (y+) 0 z), <-(strictly_order_embedding_simp (f y +) 0 (f z)).
    clear E x y. pose proof nno_zero_or_suc z as [Ez|[n Ez]].
    * rew Ez. rewrite_preserves f. apply by_contrapositive_iff. now simplify.
    * change (apos (z = 1 + n)) in Ez. rew Ez. clear Ez z. rewrite_preserves f.
      assert (0 < 1 + n) as P by (rew <-(naturals_nonneg n); now simplify); simplify; clear P.
      revert n. naturals_induction.
      - rewrite_preserves f. now simplify.
      - intros n E. rewrite_preserves f. rew <-E. now simplify.
  Qed.
End naturals_le_plus.
Global Hint Extern 2 (OrderEmbedding (naturals_to_mon _ _)) => simple notypeclasses refine (naturals_to_rig_ord_embedding _) : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (naturals_to_mon _ _)) => simple notypeclasses refine (naturals_to_rig_ord_embedding _) : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (naturals_to_mon _ _)) => simple notypeclasses refine (naturals_to_rig_ord_embedding _) : typeclass_instances.


(** In the other direction, x ≤ y ⧟ ∐ z, y = x + z  gives a rig order on ℕ. *)
Section props2.
  Context `{Naturals (N:=N)} {Nle:Le N}.

  Lemma naturals_plus_zero (x y : N) : x = x + y ⊸ y = 0.
  Proof. rew <-exact:(injective_iff_simp (x+) 0 y). now apply symmetry. Qed.

  Lemma naturals_plus_zero_sum (x y z : N) : x = x + y + z ⊸ y = 0 ⊠ z = 0 .
  Proof. rew [<-(zero_sum _ _)|<-(associativity (+) _ _ _)]. apply naturals_plus_zero. Qed.

  Context (le_plus : ∀ x y : N, x ≤ y ⧟ ∐ z, y = x + z ).

  Local Instance: AffirmativeLe N.
  Proof. intros [x y]. now rew (le_plus _ _). Qed.

  Local Instance: DecidableLe N.
  Proof. intros [x y]. pose proof naturals_distance x y as [z [E|E]].
  + left. rew (le_plus _ _). now exists z.
  + destruct (_ : Decidable (z = 0)) as [P | P].
    * left. rew (le_plus _ _). exists 0. rew E, P. now simplify.
    * right. rew (le_plus _ _). intros w. change (y ≠ x + w). rew E.
      revert P. apply aimpl_impl_pos, by_contrapositive.
      now rew (naturals_plus_zero_sum _ _ _).
  Qed.

  Lemma naturals_le_ne_lt_aux (x y : N) : x ≤ y → x ≠ y → x < y.
  Proof. change (x < y) with (anot (y ≤ x)).
    rew [(le_plus x y) | (le_plus y x)].
    intros [a Ea] E z. change (x ≠ y + z).
    revert E. apply aimpl_impl_pos, by_contrapositive.
    rew Ea, (naturals_plus_zero_sum _ _ _).
    apply affirmative_aimpl. intros [E _].
    rew E. now simplify.
  Qed.

  Lemma naturals_dec_order_aux : DecidableOrder N.
  Proof. split; try exact _. apply alt_Build_Poset.
  + intros x. rew (le_plus _ _). exists 0. now simplify.
  + intros x y z. apply affirmative_aimpl.
    rew ?(le_plus _ _). intros [[a Ea][b Eb]]. exists (a + b).
    rew Eb, Ea. now rew (associativity (+) _ _ _).
  + intros [x y]. apply affirmative_aimpl. intros E. rew (le_plus _ _). exists 0. now simplify.
  + intros x y. apply refutative_aimpl_dual. intros E.
    destruct (_ : Decidable (y ≤ x)) as [P | P].
    * left. apply naturals_le_ne_lt_aux. assumption. now apply symmetry.
    * now right.
  Qed.
  Let inst3 : DecidableOrder N.  Proof. exact naturals_dec_order_aux. Qed.

  Lemma naturals_total_order_aux : TotalOrder N.
  Proof. split; try exact _. intros x y.
    pose proof naturals_distance x y as [z[E|E]]; [ left | right ]; rew (le_plus _ _); now exists z.
  Qed.
  Let inst4 : TotalOrder N.  Proof. exact naturals_total_order_aux. Qed.

  Local Instance: AdditiveMonoidOrder N.
  Proof. split; try exact _. intros z. apply alt_Build_OrderEmbedding. intros x y; simplify.
    rew ?(le_plus _ _). apply aex_aiff. intros w. rew <-(associativity (+) _ _ _).
    exact (injective_iff (z+) _ _).
  Qed.

  Lemma alt_Build_OrderedNaturals : OrderedNaturals N.
  Proof. split; try exact _. apply strong_linear_refutative_rig_order_from_partial_minus.
  + intros x y. apply affirmative_aimpl. intros E.
    pose proof aimpl_impl_pos (lt_le _ _) E as P.
    rew (le_plus _ _) in P. destruct P as [z P]. exists z. split; trivial.
    now rew <-exact:(strictly_order_reflecting_simp (x+) 0 z), <-P.
  + intros x y. apply by_contrapositive, affirmative_aimpl. intros E.
    apply aor_apar. rew <-?(eq_le _ _). apply strong_no_zero_divisors.
    apply le_antisym; split; trivial.
    rew (le_plus _ _). exists (x · y). now simplify.
  Qed.
End props2.

Coercion naturals_dec_order   `{OrderedNaturals (N:=N)} : DecidableOrder N := naturals_dec_order_aux   naturals_le_plus.
Coercion naturals_total_order `{OrderedNaturals (N:=N)} : TotalOrder     N := naturals_total_order_aux naturals_le_plus.

(** Default construction of the order. *)
Definition naturals_le (N:set) {p:Plus N} : Le N := λ '(x, y), ∐ z, y = x + z.

Global Hint Extern 2 (Le nat) => simple refine (naturals_le Nat) : typeclass_instances.
Global Hint Extern 2 (Le (set_T Nat)) => simple refine (naturals_le Nat) : typeclass_instances.
Global Hint Extern 2 (Le (set_T (near_rig_car (nats_near_rig ?N)))) => simple refine (naturals_le N) : typeclass_instances.

Global Hint Extern 50 (Le (set_T ?N)) => let t := get_instance constr:(NaturalsToMon N) in simple refine (naturals_le N) : typeclass_instances.

Lemma naturals_le_correct {N:set} {p:Plus N} : ∀ x y : N, @le N (naturals_le N) (x, y) ⧟ ∐ z, y = x + z.
Proof. now intros x y. Qed.

Definition naturals_le_order `{Naturals (N:=N)} : OrderedNaturals N (leN:=naturals_le N) := alt_Build_OrderedNaturals naturals_le_correct.

Global Hint Extern 2 (OrderedNaturals _ (leN:=naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@TotalOrder _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@LinearOrder _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@DecidableOrder _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@AffirmativeLe _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@AffirmativeOrder _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@DecidableLe _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@Poset _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@PreOrder _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@RefutativeLe _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@StrongLe _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@StrongPoset _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (@WeakPoset _ (naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoidOrder _ (Mle:=naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.
Global Hint Extern 2 (StrongLinearRefutativeRigOrder _ (Rle:=naturals_le _)) => simple notypeclasses refine naturals_le_order : typeclass_instances.

Coercion naturals_mult_cancel `{Naturals N} : NonZeroMultiplicativeCancellation N := naturals_le_order.


Section trich.
  Context `{OrderedNaturals (N:=N)} `{NatSubtract N} `{!NatSubtractSpec N}.
 
  Local Instance naturals_trich : Trich N :=
    λ '(x, y), match nat_subtract (x, y) with
    | natsubtract.is_lt_by _ => is_lt
    | natsubtract.is_eq => is_eq
    | natsubtract.is_gt_by _ => is_gt
    end.

  Lemma naturals_trich_correct : IsTrich N.
  Proof. split; try exact _. intros x y. unfold trich, naturals_trich.
    generalize (nat_subtract_spec x y); destruct (nat_subtract (x, y)) as [z| |z]; try easy; intros [E Ez].
    + rew (lt_iff_le_prod_ne _ _); split; [ apply naturals_le_plus; now exists z |].
      revert Ez. apply aimpl_impl_pos, by_contrapositive. rew <-E. apply naturals_plus_zero.
    + rew (lt_iff_le_prod_ne _ _); split; [ apply naturals_le_plus; now exists z |].
      revert Ez. apply aimpl_impl_pos, by_contrapositive. rew E. apply naturals_plus_zero.
  Qed.
End trich.

Global Hint Extern 2 (Trich Nat) => simple refine naturals_trich : typeclass_instances.
Global Hint Extern 2 (Trich (near_rig_car (nats_near_rig ?N))) => simple refine naturals_trich : typeclass_instances.
Global Hint Extern 2 (IsTrich _ (t:=naturals_trich)) => simple notypeclasses refine naturals_trich_correct : typeclass_instances.

Global Hint Extern 50 (Trich ?N) => let t := get_instance constr:(NaturalsToMon N) in simple refine naturals_trich : typeclass_instances.

