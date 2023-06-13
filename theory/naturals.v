Require Import abstract_algebra.
Require Export interfaces.naturals interfaces.bundled_algebra.
Require Import interfaces.sprop logic.aprop logic.relations theory.rings.
Require Import implementations.nat.
Require Export theory.nno.
Require Import easy rewrite rewrite_preserves tactics.misc change_quantifiers.
Require Import strip_coercions.

Lemma naturals_initial_alt `{Naturals N} `{AdditiveNonComMonoid M} {oM:One M}
  (f g : N ⇾ M) `{!AdditiveMonoid_Morphism f} `{!AdditiveMonoid_Morphism g}
  `{!One_Pointed_Morphism f} `{!One_Pointed_Morphism g}
  : f = g.
Proof. now rew [ (naturals_initial f) | (naturals_initial g) ]. Qed.

Local Open Scope fun_inv_scope.

Global Hint Extern 5 (Inverse (naturals_to_mon ?N₁ ?N₂)) => refine (naturals_to_mon N₂ N₁) : typeclass_instances.
Lemma naturals_to_naturals_bijective `{Naturals N₁} `{Naturals N₂}
  : Bijective (naturals_to_mon N₁ N₂).
Proof. apply alt_Build_Bijective; unfold inverse; now apply naturals_initial_alt. Qed.
Global Hint Extern 5 (Bijective (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_naturals_bijective : typeclass_instances.
Global Hint Extern 10 (Injective (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_naturals_bijective : typeclass_instances.
Global Hint Extern 5 (Surjective (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_naturals_bijective : typeclass_instances.

Section retract_is_nat.
  Local Open Scope fun_inv_scope.
  Context `{Naturals N} `{NearRig R} (f:N ⇾ R).
  Context `{!Surjective f (inv:=f_inv)}.
  Context `{!AdditiveMonoid_Morphism f} `{!AdditiveMonoid_Morphism f⁻¹}.
  Context `{!One_Pointed_Morphism f} `{!One_Pointed_Morphism f⁻¹}.

  Instance retract_is_nat_to_mon : NaturalsToMon R
    := λ M pM zM oM, naturals_to_mon N M ∘ f⁻¹.
  Lemma retract_is_nat : Naturals R.
  Proof. split; [ exact _ | intros M; intros; unfold naturals_to_mon, retract_is_nat_to_mon .. ]; try exact _.
    rew <-(surjective_compose_cancel f _ _).
    exact (naturals_initial_alt _ _).
  Qed.
End retract_is_nat.

Section is_nno.
  Universes i.
  Context `{Naturals@{i} N}.
  Local Notation ψ := (naturals_to_mon N Nat).
  Instance naturals_to_nno : FromNNO N := λ X _ _, nno_to_set Nat X ∘ ψ.

  Instance: MaybeAlgebra_Morphism ψ.
  Proof. split; [ exact _ |].
    intro n. change (suc ?x) with (1+x).
    now rewrite_preserves constr:(ψ).
  Qed.

  Lemma naturals_nno : NaturalNumbersObject N.
  Proof. split; unfold nno_to_set at 1, naturals_to_nno; intros X ??.
  + exact _.
  + intros f ?.
    apply (surjective_compose_cancel ψ⁻¹ _ _).
    change (?f ∘ ?g ∘ ?h) with (f ∘ (g ∘ h)).
    rew (surjective ψ).
    change (?f ∘ id_fun _) with f.
    exact (nno_initial _).
  Qed.

  Lemma naturals_add_mon : AdditiveMonoid N.
  Proof. apply alt_Build_AdditiveMonoid; try exact _.
    intros x y. quote_injective constr:(ψ). now apply commutativity.
  Qed.

  Lemma naturals_distance `{Naturals N} (x y : N) : ∐ z, x + z = y ∨ x = y + z.
  Proof. generalize ( nat_subtract_spec (ψ x) (ψ y) ).
    destruct (nat_subtract (ψ x, ψ y)) as [ z' | z' ]; intros E;
    exists (naturals_to_mon Nat N z'); [ left | right ]; quote_injective constr:(ψ);
    change (ψ (?f z')) with ((ψ ∘ f) z');
    now rew (naturals_initial_alt (ψ ∘ naturals_to_mon Nat N) id).
  Qed.
End is_nno.
Coercion naturals_nno : Naturals >-> NaturalNumbersObject.
Coercion naturals_add_mon : Naturals >-> AdditiveMonoid.
Global Hint Extern 10 (FromNNO _) => notypeclasses refine naturals_to_nno : typeclass_instances.
Global Hint Extern 10 (NaturalNumbersObject _) => notypeclasses refine naturals_nno : typeclass_instances.

Local Open Scope mult_scope.

Section preserves_mult.
  Universes i.
  Context `{Naturals@{i} N}.
  Context `{NearRig@{i} R}.

  Notation ϕ := (naturals_to_mon N R).

  Lemma naturals_to_mon_rig_mor : Rig_Morphism ϕ.
  Proof. split; try exact _. apply alt_Build_MultiplicativeMonoid_Morphism; [| exact (preserves_1 ϕ) ].
    nno_induction.
  + intros y. now rew (mult_0_l _), (preserves_0 ϕ), (mult_0_l _).
  + intros n IHn y. change (suc ?n) with (1+n).
    rew (plus_mult_distr_r _ _ _), (mult_1_l _).
    rewrite_preserves constr:(ϕ).
    now rew (IHn y), (plus_mult_distr_r _ _ _), (mult_1_l _).
  Qed.
End preserves_mult.
Global Hint Extern 2 (Rig_Morphism (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_mon_rig_mor : typeclass_instances.
Global Hint Extern 2 (Rg_Morphism (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_mon_rig_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_mon_rig_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (naturals_to_mon _ _)) => simple notypeclasses refine naturals_to_mon_rig_mor : typeclass_instances.

Lemma naturals_is_com_rig `{Naturals N} : CommutativeRig N.
Proof. enough (Commutative (X:=N) (·)).
+ apply alt_Build_CommutativeRig2; try exact _.
  apply left_distr_from_right.
+ intros x y. quote_injective (naturals_to_mon N Nat). refine (commutativity _ _ _).
Qed.
Coercion naturals_is_com_rig : Naturals >-> CommutativeRig.


Coercion naturals_as_com_rig (N:naturals) := make_commutative_rig N.
Global Hint Extern 2 (StripCoercions (naturals_as_com_rig ?X)) => strip_coercions_chain X : strip_coercions.

Coercion naturals_as_strong_rig (N:naturals) := make_strong_rig N.
Global Hint Extern 2 (StripCoercions (naturals_as_strong_rig ?X)) => strip_coercions_chain X : strip_coercions.


Definition naturals_ind `{Naturals N} (P:N ⇾ Ω) :
    (∏ n, P n ⊸ P (1 + n)) → (P 0 ⊸ all P)
  := nno_ind P.

Definition naturals_ind_alt `{Naturals N} (P:N → Ω) : (∀ n m, n = m → P n → P m)
    → P 0 → (∀ n, P n → P (1 + n)) → all P
  := nno_ind_alt P.

Ltac naturals_induction :=
    hnf; try change_quantifiers;
    apply naturals_ind_alt; [
      intros ??; let E := fresh "E" in intro E; now rew E
    |..].

Lemma naturals_add_cancel `{Naturals N} : AdditiveCancellation N.
Proof. apply alt_Build_AdditiveCancellation.
  change (∏ z x y : N, z + x = z + y ⊸ x = y).
  naturals_induction.
  + intros x y. now rew !2(plus_0_l _).
  + intros n IHn x y.
    rew <-!2(associativity (+) _ _ _).
    rew <-(IHn x y).
    exact (injective (X:=N) suc _ _).
Qed.
Coercion naturals_add_cancel : Naturals >-> AdditiveCancellation.


Lemma zero_sum `{Naturals N} : ∀ (x y : N), x + y = 0 ⧟ x = 0 ⊠ y = 0.
Proof. intros x y; split.
* revert x y. naturals_induction.
  + intros n. rew (plus_0_l n). now rew (aprod_true_l (_ : 0 = 0)).
  + intros n _ m. apply aimpl_by_contradiction.
    rew <-(associativity (+) _ _ _).
    exact (nno_suc_nonzero _).
* apply affirmative_aimpl. intros [Ex Ey]. rew [Ex | Ey]. exact (plus_0_r _).
Qed.

Section with_a_near_ring.
  Universes i.
  Context `{Naturals@{i} N}.
  Context `{NearRing@{i} R}.

  Notation ϕ := (naturals_to_mon N R).

  Lemma naturals_to_near_ring_negate_mult_r : ∀ n, -(ϕ n) = ϕ n · (-1).
  Proof. enough (∀ n, -(ϕ n) = ϕ n · (-1) ∧ ϕ n · -1 - 1 = -1 + ϕ n · -1 : Ω) as P by (intro; now apply P).
    naturals_induction; [| intros n [IH1 IH2]]; rewrite_preserves constr:(ϕ).
  + rew (mult_0_l _). rew [ (plus_0_l _) | (plus_0_r _) ]. split; [ exact negate_0 | refl ].
  + split.
    * rew (negate_plus_distr_alt _ _), IH1.
      now rew (plus_mult_distr_r 1 (ϕ n) _), (mult_1_l _).
    * rew (plus_mult_distr_r 1 (ϕ n) _), <-(associativity (+) _ _ _), (mult_1_l _).
      now apply (is_fun (-1 +) _ _).
  Qed.
End with_a_near_ring.


Section with_a_ring.
  Universes i.
  Context `{Naturals@{i} N} `{Ring@{i} R} (f:N ⇾ R) `{!Rig_Morphism f} `{!Injective f}.

  Lemma to_ring_zero_sum x y : -(f x) = f y ⧟ x = 0 ⊠ y = 0.
  Proof.
    rew <-(zero_sum x y), (injective_iff f _ _).
    rewrite_preserves f.
    rew (left_cancellation (+) (f x) (-f x) _).
    rew (plus_negate_r _).
    now apply symmetry_iff.
  Qed.

  Lemma to_ring_zero_sum_alt x y : -(f x) = f y ⧟ x = 0 ∧ y = 0.
  Proof. rew (to_ring_zero_sum _ _). sym. exact (aand_aprod_dec_l _ _). Qed.

  Lemma negate_to_ring x y : -(f x) = f y ⊸ f x = f y.
  Proof. rew (to_ring_zero_sum _ _). apply decidable_aimpl.
    intros [E1 E2]. now rew [E1|E2].
  Qed.
End with_a_ring.

