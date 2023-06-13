Require Import abstract_algebra interfaces.naturals interfaces.integers
  interfaces.bundled_algebra interfaces.group_completion
  logic.aprop logic.relations logic.dec theory.set theory.projected_set theory.rings
  theory.group_completion
  theory.naturals.
Require Import grothendieck_group theory.integers.
Require Import implementations.bool.
Require Import easy replc.

Local Open Scope mult_scope.

Module signed_naturals.

  Section with_naturals.
    Universes u.
    Context (ℕ:naturals@{u}).

    Notation ℤ := (GrothendieckPairs (near_rig_car (nats_near_rig ℕ))).
    Notation i := (to_grothendieck_group (near_rig_car (nats_near_rig ℕ))).

    Let inst : Integers ℤ := _.
    Let inst2 : Rig_Morphism i := _.
    Let inst3 : Injective i.
    Proof naturals_to_integers_inj_alt (N:=ℕ) (Z:=ℤ) i.

    (** Note: zero has (at least) two representations *)
    Inductive t := pos : ℕ → t | neg : ℕ → t.

    Definition to_ℤ_op (x:t) : ℤ :=
    match x with
    | pos x' => i x'
    | neg x' => -(i x')
    end.

    Definition Z := projected_set@{u} to_ℤ_op.
    Local Hint Extern 5 => progress unfold Z : typeclass_instances.
    Definition to_ℤ : Z ⇾ ℤ := projected_set_project _.
    Instance to_ℤ_inj : Injective to_ℤ := projected_set_project_injective Z.

    Definition of_ℕ := @make_fun ℕ Z pos (is_fun i).

    Local Open Scope bool_scope.
    Instance eq_dec {d:Dec (A:=ℕ) (=)} : Dec (A:=Z) (=) := λ x y,
    match x with
    | pos x' =>
      match y with
      | pos y' => dec (=) x' y'
      | neg y' => dec (=) x' 0 && dec (=) y' 0
      end
    | neg x' =>
      match y with
      | pos y' => dec (=) x' 0 && dec (=) y' 0
      | neg y' => dec (=) x' y'
      end
    end.

    Lemma pos_eq (x y : ℕ) : x = y ⧟ pos x = pos y :> Z.
    Proof injective_iff i _ _.

    Lemma neg_eq (x y : ℕ) : x = y ⧟ neg x = neg y :> Z.
    Proof injective_iff ((-) ∘ i) _ _.

    Lemma neg_pos_eq (x y : ℕ) : x = 0 ∧ y = 0 ⧟ neg x = pos y :> Z.
    Proof. change (neg x = pos y) with (-i x = i y).
      sym. exact (naturals.to_ring_zero_sum_alt (N:=ℕ) i _ _).
    Qed.
    Lemma pos_neg_eq (x y : ℕ) : x = 0 ∧ y = 0 ⧟ pos x = neg y :> Z.
    Proof. rew [ (aand_com _ _) | (symmetry_iff (A:=Z) (=) (pos x) _) ].
      exact (neg_pos_eq _ _).
    Qed.

    Lemma eq_is_dec `{!IsDecEq ℕ (d:=d)} : IsDecEq Z (d:=eq_dec).
    Proof. intros [p₁|n₁] [p₂|n₂]; unfold dec, eq_dec.
    + apply dec_spec_by_iff. exact (pos_eq _ _).
    + generalize (dec_spec_andb p₁ 0 n₂ 0); destruct (andb (dec (=) p₁ 0, dec (=) n₂ 0));
      now rew <-(pos_neg_eq _ _).
    + generalize (dec_spec_andb n₁ 0 p₂ 0); destruct (andb (dec (=) n₁ 0, dec (=) p₂ 0));
      now rew <-(neg_pos_eq _ _).
    + apply dec_spec_by_iff. exact (neg_eq _ _).
    Qed.

    Lemma from_Z_is_fun `{X:set@{u}} (f:Z → X) :
      (∀ n m : ℕ, n = m → f (pos n) = f (pos m)) →
      (∀ n m : ℕ, n = m → f (neg n) = f (neg m)) →
      (∀ n m : ℕ, n = 0 ∧ m = 0 → f (pos n) = f (neg m)) →
      IsFun f.
    Proof. intros Pp Pn P0. intros [n|n] [m|m].
    + rew <-(pos_eq _ _). apply affirmative_aimpl, Pp.
    + rew <-(pos_neg_eq _ _). apply decidable_aimpl, P0.
    + rew <-(neg_pos_eq _ _), (aand_com _ _), (symmetry_iff (=) (f (neg n)) _).
      apply decidable_aimpl, P0.
    + rew <-(neg_eq _ _). apply affirmative_aimpl, Pn.
    Qed.

    Instance z : Zero Z := pos 0.
    Instance o : One Z := pos 1.

    Definition negate_op (x:Z) : Z := match x with
    | pos x' => neg x'
    | neg x' => pos x'
    end.

    Definition mult_op (x:Z) (y:Z) : Z :=
    match x with
    | pos x' =>
      match y with
      | pos y' => pos (x' · y')
      | neg y' => neg (x' · y')
      end
    | neg x' =>
      match y with
      | pos y' => neg (x' · y')
      | neg y' => pos (x' · y')
      end
    end.

    Context {sub:NatSubtract ℕ} `{!NatSubtractSpec ℕ}.

    Definition plus_op (x:Z) (y:Z) : Z :=
    match x with
    | pos x' =>
      match y with
      | pos y' => pos (x' + y')
      | neg y' => match nat_subtract (x', y') with
        | inl z => neg z
        | inr z => pos z
        end
      end
    | neg x' =>
      match y with
      | pos y' => match nat_subtract (x', y') with
        | inl z => pos z
        | inr z => neg z
        end
      | neg y' => neg (x' + y')
      end
    end.

    Import projection_notation.
    Local Ltac smpl := unfold tuncurry; change (func_op to_ℤ ?x) with (to_ℤ_op x);
      cbn [π₁ π₂ negate_op mult_op plus_op to_ℤ_op].

    Lemma negate_op_correct : ∀ x:Z, to_ℤ (negate_op x) = - to_ℤ x.
    Proof. intros [p|n]; smpl.
    + refl.
    + sym. exact (negate_involutive _).
    Qed.

    Instance ngt : Negate Z
      := @make_fun _ _ _ (projected_is_fun negate_op (-) negate_op_correct).
    Definition negate_correct : ∀ x:Z, to_ℤ (-x) = -(to_ℤ x) := negate_op_correct.

    Lemma mult_op_correct : ∀ p : Z ⊗ Z,
        to_ℤ (tuncurry mult_op p) = to_ℤ (π₁ p) · to_ℤ (π₂ p).
    Proof. intros [[p₁|n₁] [p₂|n₂]]; smpl; rew (preserves_mult i _ _).
    + refl.
    + apply negate_mult_distr_r.
    + apply negate_mult_distr_l.
    + sym. apply negate_mult_negate.
    Qed.

    Instance mlt : Mult Z
      := @make_fun _ _ _ (projected_is_fun (X:=Z ⊗ Z) (tuncurry mult_op) (·) mult_op_correct).
    Definition mult_correct x y : to_ℤ (x · y) = to_ℤ x · to_ℤ y := mult_op_correct (x,y).

    Lemma plus_op_correct : ∀ p : Z ⊗ Z,
        to_ℤ (tuncurry plus_op p) = to_ℤ (π₁ p) + to_ℤ (π₂ p).
    Proof. intros [[p₁|n₁] [p₂|n₂]]; smpl.
    + exact (preserves_plus i _ _).
    + generalize (nat_subtract_spec p₁ n₂); destruct (nat_subtract (p₁, n₂)) as [z | z]; smpl; intro E.
      * rew <-E, (preserves_plus i _ _), (negate_plus_distr _ _), (associativity (+) _ _ _).
        now rew (plus_negate_r _), (plus_0_l _).
      * rew E, (commutativity (+) n₂ z), (preserves_plus i _ _), <-(associativity (+) _ _ _).
        now rew (plus_negate_r _), (plus_0_r _).
    + generalize (nat_subtract_spec n₁ p₂); destruct (nat_subtract (n₁, p₂)) as [z | z]; smpl; intro E.
      * rew <-E, (preserves_plus i _ _), (associativity (+) _ _ _).
        now rew (plus_negate_l _), (plus_0_l _).
      * rew E, (commutativity (+) p₂ z), (preserves_plus i _ _), (negate_plus_distr _ _).
        now rew <-(associativity (+) _ _ _), (plus_negate_l _), (plus_0_r _).
    + now rew (preserves_plus i _ _), (negate_plus_distr _ _).
    Qed.

    Instance pls : Plus Z
      := @make_fun _ _ _ (projected_is_fun (X:=Z ⊗ Z) (tuncurry plus_op) (+) plus_op_correct).
    Definition plus_correct x y : to_ℤ (x + y) = to_ℤ x + to_ℤ y := plus_op_correct (x,y).

    Lemma zero_correct : to_ℤ 0 = 0.  Proof. refl. Qed.
    Lemma one_correct  : to_ℤ 1 = 1.  Proof. refl. Qed.

    Instance is_com_ring : CommutativeRing Z
      := projected_commutative_ring to_ℤ
           plus_correct mult_correct zero_correct one_correct negate_correct.
    Let inst4 := is_com_ring.

    Instance to_ℤ_mor : Rig_Morphism to_ℤ.
    Proof. apply alt_Build_Rig_Morphism.
    + exact plus_correct.
    + exact mult_correct.
    + exact zero_correct.
    + exact one_correct.
    Qed.

    Instance of_ℕ_mor : Rig_Morphism of_ℕ.
    Proof. now apply alt_Build_Rig_Morphism. Qed.
    Let inst5 := of_ℕ_mor.

    Definition of_ℤ : ℤ ⇾ Z := from_group_completion2 i of_ℕ.
    Instance of_ℤ_mor : Rig_Morphism of_ℤ.  Proof. now unfold of_ℤ. Qed.

    Lemma of_ℤ_spec : of_ℤ ∘ i = of_ℕ.
    Proof from_group_completion2_spec.
  End with_naturals.

  #[global] Hint Extern 1 (Dec (A:=t ?ℕ) (=)) => refine (eq_dec ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Dec (A:=set_T (Z ?ℕ)) (=)) => refine (eq_dec ℕ) : typeclass_instances.
  #[global] Hint Extern 2 (IsDecEq _ (d:=eq_dec ?ℕ)) => simple notypeclasses refine (eq_is_dec ℕ) : typeclass_instances.

  #[global] Hint Extern 1 (Zero   (Z ?ℕ)) => refine (z ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (One    (Z ?ℕ)) => refine (o ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Negate (Z ?ℕ)) => refine (ngt ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Plus   (Z ?ℕ)) => refine (pls ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Mult   (Z ?ℕ)) => refine (mlt ℕ) : typeclass_instances.

  #[global] Hint Extern 1 (CommutativeRing         (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveCancellation    (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveGroup           (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveMonoid          (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveNonComGroup     (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveNonComMonoid    (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveNonComSemiGroup (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveSemiGroup       (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (CommutativeRig          (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRg              (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRig             (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRing            (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRng             (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeComMonoid (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeMonoid    (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeSemiGroup (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (NearRg                  (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (NearRig                 (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (NearRing                (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (NearRng                 (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rg                      (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rig                     (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Ring                    (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rng                     (Z ?ℕ)) => refine (is_com_ring ℕ) : typeclass_instances.

  #[global] Hint Extern 1 (Rig_Morphism                     (to_ℤ ?ℕ)) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rg_Morphism                      (to_ℤ ?ℕ)) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveMonoid_Morphism          (to_ℤ ?ℕ)) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveSemiGroup_Morphism       (to_ℤ ?ℕ)) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeSemiGroup_Morphism (to_ℤ ?ℕ)) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeMonoid_Morphism    (to_ℤ ?ℕ)) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (One_Pointed_Morphism             (to_ℤ ?ℕ)) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Zero_Pointed_Morphism            (to_ℤ ?ℕ)) => refine (to_ℤ_mor ℕ) : typeclass_instances.

  #[global] Hint Extern 1 (Rig_Morphism                     (of_ℤ ?ℕ)) => refine (of_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rg_Morphism                      (of_ℤ ?ℕ)) => refine (of_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveMonoid_Morphism          (of_ℤ ?ℕ)) => refine (of_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveSemiGroup_Morphism       (of_ℤ ?ℕ)) => refine (of_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeSemiGroup_Morphism (of_ℤ ?ℕ)) => refine (of_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeMonoid_Morphism    (of_ℤ ?ℕ)) => refine (of_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (One_Pointed_Morphism             (of_ℤ ?ℕ)) => refine (of_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Zero_Pointed_Morphism            (of_ℤ ?ℕ)) => refine (of_ℤ_mor ℕ) : typeclass_instances.

  #[global] Hint Extern 1 (Rig_Morphism                     (of_ℕ ?ℕ)) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rg_Morphism                      (of_ℕ ?ℕ)) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveMonoid_Morphism          (of_ℕ ?ℕ)) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveSemiGroup_Morphism       (of_ℕ ?ℕ)) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeSemiGroup_Morphism (of_ℕ ?ℕ)) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeMonoid_Morphism    (of_ℕ ?ℕ)) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (One_Pointed_Morphism             (of_ℕ ?ℕ)) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Zero_Pointed_Morphism            (of_ℕ ?ℕ)) => refine (of_ℕ_mor ℕ) : typeclass_instances.

  #[global] Hint Extern 1 (Inverse (of_ℤ ?ℕ)) => refine (to_ℤ ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rig_Morphism                     (inverse (of_ℤ ?ℕ))) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rg_Morphism                      (inverse (of_ℤ ?ℕ))) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveMonoid_Morphism          (inverse (of_ℤ ?ℕ))) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveSemiGroup_Morphism       (inverse (of_ℤ ?ℕ))) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeSemiGroup_Morphism (inverse (of_ℤ ?ℕ))) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeMonoid_Morphism    (inverse (of_ℤ ?ℕ))) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (One_Pointed_Morphism             (inverse (of_ℤ ?ℕ))) => refine (to_ℤ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Zero_Pointed_Morphism            (inverse (of_ℤ ?ℕ))) => refine (to_ℤ_mor ℕ) : typeclass_instances.

  Section is_integers.
    Universes u.
    Context (ℕ:naturals@{u}).
    Context {sub:NatSubtract ℕ} `{!NatSubtractSpec ℕ}.

    Notation ℤ := (GrothendieckPairs (near_rig_car (nats_near_rig ℕ))).
    Notation i := (to_grothendieck_group (near_rig_car (nats_near_rig ℕ))).

    Let inst : Integers ℤ := _.
    Let inst2 : Rig_Morphism i := _.
    Let inst3 : Injective i.
    Proof naturals_to_integers_inj_alt (N:=ℕ) (Z:=ℤ) i.

    Local Notation Z' := (Z ℕ).

    Instance of_ℤ_surj : Surjective (of_ℤ ℕ).
    Proof. intros [p|n].
    + change (of_ℤ ℕ (i p) = of_ℕ ℕ p). exact (of_ℤ_spec ℕ _).
    + change (of_ℤ ℕ (-i n) = -(of_ℕ ℕ n)).
      rew (preserves_negate (of_ℤ ℕ) _), <-(is_fun (-) _ _).
      exact (of_ℤ_spec ℕ _).
    Qed.

    Instance to_group : IntegersToGroup Z' := retract_is_int_to_group (Z:=ℤ) (of_ℤ ℕ).
    Instance is_integers : Integers Z' := retract_is_int _.
  End is_integers.

  #[global] Hint Extern 1 (IntegersToGroup (Z ?ℕ)) => refine (to_group ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Integers (Z ?ℕ)) => refine (is_integers ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (DecidableEquality   (Z ?ℕ)) => refine (is_integers ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AffirmativeEquality (Z ?ℕ)) => refine (is_integers ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (RefutativeEquality  (Z ?ℕ)) => refine (is_integers ℕ) : typeclass_instances.

  Definition ints (ℕ:naturals) {sub:NatSubtract ℕ} `{!NatSubtractSpec ℕ} : integers.
  Proof. unshelve esplit.
  + exact (make_ring (Z ℕ)).
  + exact (to_group ℕ).
  + exact (is_integers ℕ).
  Defined.

  #[global] Hint Extern 1 (Dec (A:=set_T (ring_car (ints_ring (ints ?N)))) (=)) => simple notypeclasses refine (eq_dec N) : typeclass_instances.

  #[global] Hint Extern 2 (Cast (near_rig_car (nats_near_rig _)) (ring_car (ints_ring (ints _)))) => refine (of_ℕ _) : typeclass_instances.
  #[global] Hint Extern 1 (Rig_Morphism                     (cast (near_rig_car (nats_near_rig ?ℕ)) (ring_car (ints_ring (ints ?ℕ))))) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Rg_Morphism                      (cast (near_rig_car (nats_near_rig ?ℕ)) (ring_car (ints_ring (ints ?ℕ))))) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveMonoid_Morphism          (cast (near_rig_car (nats_near_rig ?ℕ)) (ring_car (ints_ring (ints ?ℕ))))) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveSemiGroup_Morphism       (cast (near_rig_car (nats_near_rig ?ℕ)) (ring_car (ints_ring (ints ?ℕ))))) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeSemiGroup_Morphism (cast (near_rig_car (nats_near_rig ?ℕ)) (ring_car (ints_ring (ints ?ℕ))))) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeMonoid_Morphism    (cast (near_rig_car (nats_near_rig ?ℕ)) (ring_car (ints_ring (ints ?ℕ))))) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (Zero_Pointed_Morphism            (cast (near_rig_car (nats_near_rig ?ℕ)) (ring_car (ints_ring (ints ?ℕ))))) => refine (of_ℕ_mor ℕ) : typeclass_instances.
  #[global] Hint Extern 1 (One_Pointed_Morphism             (cast (near_rig_car (nats_near_rig ?ℕ)) (ring_car (ints_ring (ints ?ℕ))))) => refine (of_ℕ_mor ℕ) : typeclass_instances.
End signed_naturals.


Require Import nat.

Definition SignedNat := signed_naturals.ints Nat_naturals.
Definition SignedNat_eq_dec : Dec (A:=SignedNat) (=) := signed_naturals.eq_dec _.
Global Hint Extern 1 (Dec (A:=set_T (ring_car (ints_ring SignedNat))) (=)) => refine SignedNat_eq_dec : typeclass_instances.

Definition SignedNat_eq_is_dec : IsDecEq SignedNat := signed_naturals.eq_is_dec _.
Global Hint Extern 1 (IsDecEq _ (d:=SignedNat_eq_dec)) => refine SignedNat_eq_is_dec : typeclass_instances.


