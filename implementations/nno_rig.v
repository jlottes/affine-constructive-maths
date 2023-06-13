Require Import abstract_algebra interfaces.naturals.
Require Import theory.set interfaces.sprop logic.aprop.
Require Import theory.nno theory.rings.
Require Import easy rewrite.
Require Import set_lambda.

Import projection_notation.
Local Open Scope mult_scope.

Section ops.
  Universes i.
  Context `{NaturalNumbersObject@{i} ℕ}.
  Instance nno_one : One ℕ := suc 0.
  Instance nno_plus : Plus ℕ := uncurry set:(λ x y, nno_rec ℕ suc (y, x)).
  Instance nno_mult : Mult ℕ := uncurry set:(λ x y : ℕ, nno_rec ℕ (y +) (0, x)).
End ops.

Local Ltac unfold_plus := repeat change (?a + ?b) with (nno_rec _ suc (b, a)).
Local Ltac unfold_mult := repeat change (?a · ?b) with (nno_rec _ (b +) (0, a)).

Section plus.
  Universes i.
  Context `{NaturalNumbersObject@{i} ℕ}.
  Existing Instance nno_plus.

  Local Instance plus_base : LeftIdentity (X:=ℕ) (+) 0 := λ x, nno_rec_base (ℕ:=ℕ).
  Local Definition plus_step (x y:ℕ) : (suc x) + y = suc (x + y) := nno_rec_step _.

  Instance: RightIdentity (X:=ℕ) (+) 0.
  Proof. nno_induction.
  + exact (plus_base 0).
  + intros n E. now rew (plus_step _ _), E.
  Qed.

  Instance: Associative (X:=ℕ) (+).
  Proof. nno_induction.
  + intros y z. now rew [ (left_identity (+) (y+z)) | (left_identity (+) y) ].
  + intros x IHx y z. rew ?(plus_step _ _). now rew (IHx y z).
  Qed.

  Lemma nno_plus_suc_swap : ∀ (x y:ℕ), suc x + y = x + suc y.
  Proof. nno_induction.
  + intros y. rew (plus_step _ _). now rew ?(left_identity (+) _).
  + intros x IHx y. rew ?(plus_step _ _). rew <-(IHx y). now rew ?(plus_step _ _).
  Qed.

  Instance: Commutative (X:=ℕ) (+).
  Proof. nno_induction.
  + intros y. now rew [ (left_identity (+) y) | (right_identity (+) y) ].
  + intros x IHx y. rew <-(nno_plus_suc_swap _ _). rew ?(plus_step _ _). now rew (IHx y).
  Qed.

  Instance nno_add_mon : AdditiveMonoid ℕ.
  Proof. now apply alt_Build_AdditiveMonoid. Qed.
End plus.

Section mult.
  Universes i.
  Context `{NaturalNumbersObject@{i} ℕ}.

  Existing Instance nno_one.
  Existing Instance nno_plus.
  Existing Instance nno_mult.
  Let inst := nno_add_mon.

  Local Instance mult_base: LeftAbsorb (X:=ℕ) (·) 0 := λ x, nno_rec_base (ℕ:=ℕ).
  Local Definition mult_step (x y:ℕ) : suc x · y = y + (x · y) := nno_rec_step _.

  Instance: LeftIdentity  (X:=ℕ) (·) 1.
  Proof. intros x. change 1 with (suc 0).
    now rew (mult_step _ _), (mult_base _), (plus_0_r _).
  Qed.

  Instance: LeftDistribute (X:=ℕ) (·) (+).
  Proof. nno_induction.
  + intros y z. rew ?(mult_base _). now rew (plus_0_l _).
  + intros n IHn y z. rew ?(mult_step _ _). rew (IHn y z).
    rew ?(associativity (+) _ _ _).
    now rew <-(associativity (+) _ z (n·y)), (commutativity (+) z _), (associativity (+) _ _ _).
  Qed.

  Instance: RightAbsorb (X:=ℕ) (·) 0.
  Proof. nno_induction.
  + exact (mult_base _).
  + intros n IHn. now rew (mult_step _ _), IHn, (plus_0_l _).
  Qed.

  Local Lemma mult_step_r : ∀ x y:ℕ, x · suc y = x + (x · y).
  Proof. nno_induction.
  + intros y. rew ?(mult_base _). now rew (plus_0_l _).
  + intros n IHn y. rew ?(mult_step _ _). rew (IHn y).
    rew !2(associativity (+) _ _ _).
    now rew (nno_plus_suc_swap y _), (commutativity (+) y _).
  Qed.

  Instance: Commutative (X:=ℕ) (·).
  Proof. nno_induction.
  + intros y. rew (mult_base _). sym. exact (right_absorb _ _).
  + intros n IHn y. rew [(mult_step _ _) | (mult_step_r _ _)]. now rew (IHn y).
  Qed.

  Instance: RightDistribute (X:=ℕ) (·) (+) := right_distr_from_left.

  Instance: Associative (X:=ℕ) (·).
  Proof. nno_induction.
  + intros y z. now rew ?(mult_base _).
  + intros n IHn y z. rew ?(mult_step _ _). rew (IHn y z).
    sym. now apply distribute_r.
  Qed.

  Instance nno_com_rig: CommutativeRig ℕ.
  Proof. now apply alt_Build_CommutativeRig2. Qed.
End mult.

