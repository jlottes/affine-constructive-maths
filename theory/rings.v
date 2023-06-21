Require Export theory.additive_groups theory.multiplicative_groups.
Require Import interfaces.sprop abstract_algebra.
Require Import logic.aprop.
Require Import easy rewrite.

Local Notation "X 'ᵒᵖ'" := (ring_op X) (at level 1, format "X 'ᵒᵖ'").
Local Open Scope mult_scope.

(** Alternative axiomatizations *)

Section alt_build.
  Universes i.
  Context {R:set@{i}} {Rplus: Plus R} {Rmult: Mult R} {Rzero: Zero R} {Rone: One R} {Rnegate: Negate R}.

  Lemma alt_Build_NearRg :
      Associative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → RightIdentity (X:=R) (+) 0
    → Associative (X:=R) (·)
    → RightDistribute (X:=R) (·) (+)
    → LeftAbsorb  (X:=R) (·) 0
    → NearRg R.
  Proof. intros. split; trivial. now apply alt_Build_AdditiveNonComMonoid. Qed.

  Lemma alt_Build_LeftNearRg :
      Associative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → RightIdentity (X:=R) (+) 0
    → Associative (X:=R) (·)
    → LeftDistribute  (X:=R) (·) (+)
    → RightAbsorb (X:=R) (·) 0
    → LeftNearRg R.
  Proof. intros. split; trivial. now apply alt_Build_AdditiveNonComMonoid. Qed.

  Lemma alt_Build_Rg :
      Associative (X:=R) (+)
    → Commutative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → Associative (X:=R) (·)
    → LeftDistribute  (X:=R) (·) (+)
    → RightDistribute (X:=R) (·) (+)
    → LeftAbsorb  (X:=R) (·) 0
    → RightAbsorb (X:=R) (·) 0
    → Rg R.
  Proof. intros. assert (AdditiveMonoid R) by now apply alt_Build_AdditiveMonoid. split; trivial.
  + now apply alt_Build_NearRg.
  + now apply alt_Build_LeftNearRg.
  Qed.

  Lemma alt_Build_NearRig :
      AdditiveNonComMonoid R
    → MultiplicativeMonoid R
    → RightDistribute (X:=R) (·) (+)
    → LeftAbsorb  (X:=R) (·) 0
    → NearRig R.
  Proof. intros. repeat (split; try exact _). Qed.

  Lemma alt_Build_LeftNearRig :
      AdditiveNonComMonoid R
    → MultiplicativeMonoid R
    → LeftDistribute  (X:=R) (·) (+)
    → RightAbsorb (X:=R) (·) 0
    → LeftNearRig R.
  Proof. intros. repeat (split; try exact _). Qed.

  Lemma alt_Build_Rig :
      AdditiveMonoid R
    → MultiplicativeMonoid R
    → LeftDistribute  (X:=R) (·) (+)
    → RightDistribute (X:=R) (·) (+)
    → LeftAbsorb  (X:=R) (·) 0
    → RightAbsorb (X:=R) (·) 0
    → Rig R.
  Proof. intros. repeat (split; try exact _). Qed.

  Lemma alt_Build_NearRig2 :
      Associative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → RightIdentity (X:=R) (+) 0
    → Associative (X:=R) (·)
    → LeftIdentity  (X:=R) (·) 1
    → RightIdentity (X:=R) (·) 1
    → RightDistribute (X:=R) (·) (+)
    → LeftAbsorb  (X:=R) (·) 0
    → NearRig R.
  Proof. intros. apply alt_Build_NearRig; trivial.
  + now apply alt_Build_AdditiveNonComMonoid.
  + now apply alt_Build_MultiplicativeMonoid.
  Qed.

  Lemma alt_Build_LeftNearRig2 :
      Associative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → RightIdentity (X:=R) (+) 0
    → Associative (X:=R) (·)
    → LeftIdentity  (X:=R) (·) 1
    → RightIdentity (X:=R) (·) 1
    → LeftDistribute  (X:=R) (·) (+)
    → RightAbsorb (X:=R) (·) 0
    → LeftNearRig R.
  Proof. intros. apply alt_Build_LeftNearRig; trivial.
  + now apply alt_Build_AdditiveNonComMonoid.
  + now apply alt_Build_MultiplicativeMonoid.
  Qed.

  Lemma alt_Build_Rig2 :
      Associative (X:=R) (+)
    → Commutative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → Associative (X:=R) (·)
    → LeftIdentity  (X:=R) (·) 1
    → RightIdentity (X:=R) (·) 1
    → LeftDistribute  (X:=R) (·) (+)
    → RightDistribute (X:=R) (·) (+)
    → LeftAbsorb  (X:=R) (·) 0
    → RightAbsorb (X:=R) (·) 0
    → Rig R.
  Proof. intros. apply alt_Build_Rig; trivial.
  + now apply alt_Build_AdditiveMonoid.
  + now apply alt_Build_MultiplicativeMonoid.
  Qed.

  Lemma comrig_from_rig :
      Rig R
    → Commutative (X:=R) (·)
    → CommutativeRig R.
  Proof. intros. split; trivial. now apply alt_Build_MultiplicativeComMonoid. Qed.

  Lemma alt_Build_CommutativeRig :
      AdditiveMonoid R
    → MultiplicativeComMonoid R
    → LeftDistribute  (X:=R) (·) (+)
    → LeftAbsorb  (X:=R) (·) 0
    → CommutativeRig R.
  Proof. intros. split;trivial.
    apply alt_Build_Rig; try exact _.
    exact right_distr_from_left.
    exact right_absorb_from_left.
  Qed.

  Lemma alt_Build_CommutativeRig2 :
      Associative (X:=R) (+)
    → Commutative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → Associative (X:=R) (·)
    → Commutative (X:=R) (·)
    → LeftIdentity  (X:=R) (·) 1
    → LeftDistribute  (X:=R) (·) (+)
    → LeftAbsorb  (X:=R) (·) 0
    → CommutativeRig R.
  Proof. intros. apply alt_Build_CommutativeRig; trivial.
  + now apply alt_Build_AdditiveMonoid.
  + now apply alt_Build_MultiplicativeComMonoid.
  Qed.

  Lemma alt_Build_NearRng :
      AdditiveNonComGroup R
    → MultiplicativeSemiGroup R
    → RightDistribute (X:=R) (·) (+)
    → NearRng R.
  Proof. intros. split; trivial. apply alt_Build_NearRg; try exact _.
    intros y. apply (right_cancellation (+) (0 · y) _ _).
    now rew <-(distribute_r (·) (+) 0 0 y), (plus_0_r _), (plus_0_l (0 · y)).
  Qed.

  Lemma alt_Build_LeftNearRng :
      AdditiveNonComGroup R
    → MultiplicativeSemiGroup R
    → LeftDistribute (X:=R) (·) (+)
    → LeftNearRng R.
  Proof. intros. split; trivial. apply alt_Build_LeftNearRg; try exact _.
    intros y. apply (left_cancellation (+) (y · 0) _ _).
    now rew <-(distribute_l (·) (+) y 0 0), (plus_0_l _), (plus_0_r (y · 0)).
  Qed.

  Lemma alt_Build_Rng :
      AdditiveGroup R
    → MultiplicativeSemiGroup R
    → LeftDistribute  (X:=R) (·) (+)
    → RightDistribute (X:=R) (·) (+)
    → Rng R.
  Proof. intros.
    assert (NearRng R) by now apply alt_Build_NearRng.
    assert (LeftNearRng R) by now apply alt_Build_LeftNearRng.
    split; trivial; now split.
  Qed.

  Lemma alt_Build_NearRng2 :
      Associative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → RightIdentity (X:=R) (+) 0
    → LeftInverse (X:=R) (+) (-) 0
    → RightInverse (X:=R) (+) (-) 0
    → Associative (X:=R) (·)
    → RightDistribute (X:=R) (·) (+)
    → NearRng R.
  Proof. intros. apply alt_Build_NearRng; try exact _.
    now apply alt_Build_AdditiveNonComGroup.
  Qed.

  Lemma alt_Build_LeftNearRng2 :
      Associative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → RightIdentity (X:=R) (+) 0
    → LeftInverse (X:=R) (+) (-) 0
    → RightInverse (X:=R) (+) (-) 0
    → Associative (X:=R) (·)
    → LeftDistribute (X:=R) (·) (+)
    → LeftNearRng R.
  Proof. intros. apply alt_Build_LeftNearRng; try exact _.
    now apply alt_Build_AdditiveNonComGroup.
  Qed.

  Lemma alt_Build_Rng2 :
      Associative (X:=R) (+)
    → Commutative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → LeftInverse (X:=R) (+) (-) 0
    → Associative (X:=R) (·)
    → LeftDistribute  (X:=R) (·) (+)
    → RightDistribute (X:=R) (·) (+)
    → Rng R.
  Proof. intros. apply alt_Build_Rng; try exact _.
    now apply alt_Build_AdditiveGroup.
  Qed.

  Lemma alt_Build_NearRing :
      AdditiveNonComGroup R
    → MultiplicativeMonoid R
    → RightDistribute (X:=R) (·) (+)
    → NearRing R.
  Proof. intros. assert (NearRng R) by now apply alt_Build_NearRng.
    split; trivial. now apply alt_Build_NearRig.
  Qed.

  Lemma alt_Build_LeftNearRing :
      AdditiveNonComGroup R
    → MultiplicativeMonoid R
    → LeftDistribute (X:=R) (·) (+)
    → LeftNearRing R.
  Proof. intros. assert (LeftNearRng R) by now apply alt_Build_LeftNearRng.
    split; trivial. now apply alt_Build_LeftNearRig.
  Qed.

  Lemma alt_Build_Ring :
      AdditiveGroup R
    → MultiplicativeMonoid R
    → LeftDistribute  (X:=R) (·) (+)
    → RightDistribute (X:=R) (·) (+)
    → Ring R.
  Proof. intros. assert (Rng R) by now apply alt_Build_Rng.
    split; trivial. now apply alt_Build_Rig.
  Qed.

  Lemma alt_Build_NearRing2 :
      Associative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → RightIdentity (X:=R) (+) 0
    → LeftInverse (X:=R) (+) (-) 0
    → RightInverse (X:=R) (+) (-) 0
    → Associative (X:=R) (·)
    → LeftIdentity  (X:=R) (·) 1
    → RightIdentity  (X:=R) (·) 1
    → RightDistribute (X:=R) (·) (+)
    → NearRing R.
  Proof. intros. apply alt_Build_NearRing; trivial.
  + now apply alt_Build_AdditiveNonComGroup.
  + now apply alt_Build_MultiplicativeMonoid.
  Qed.

  Lemma alt_Build_LeftNearRing2 :
      Associative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → RightIdentity (X:=R) (+) 0
    → LeftInverse (X:=R) (+) (-) 0
    → RightInverse (X:=R) (+) (-) 0
    → Associative (X:=R) (·)
    → LeftIdentity  (X:=R) (·) 1
    → RightIdentity  (X:=R) (·) 1
    → LeftDistribute (X:=R) (·) (+)
    → LeftNearRing R.
  Proof. intros. apply alt_Build_LeftNearRing; trivial.
  + now apply alt_Build_AdditiveNonComGroup.
  + now apply alt_Build_MultiplicativeMonoid.
  Qed.

  Lemma alt_Build_Ring2 :
      Associative (X:=R) (+)
    → Commutative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → LeftInverse (X:=R) (+) (-) 0
    → Associative (X:=R) (·)
    → LeftIdentity  (X:=R) (·) 1
    → RightIdentity  (X:=R) (·) 1
    → LeftDistribute  (X:=R) (·) (+)
    → RightDistribute (X:=R) (·) (+)
    → Ring R.
  Proof. intros. apply alt_Build_Ring; trivial.
  + now apply alt_Build_AdditiveGroup.
  + now apply alt_Build_MultiplicativeMonoid.
  Qed.

  Lemma comring_from_ring :
      Ring R
    → Commutative (X:=R) (·)
    → CommutativeRing R.
  Proof. intros. split; trivial. now apply comrig_from_rig. Qed.

  Lemma alt_Build_CommutativeRing :
      AdditiveGroup R
    → MultiplicativeComMonoid R
    → LeftDistribute  (X:=R) (·) (+)
    → CommutativeRing R.
  Proof. intros. apply comring_from_ring; [|exact _].
    apply alt_Build_Ring; try exact _.
    exact right_distr_from_left.
  Qed.

  Lemma alt_Build_CommutativeRing2 :
      Associative (X:=R) (+)
    → Commutative (X:=R) (+)
    → LeftIdentity (X:=R) (+) 0
    → LeftInverse (X:=R) (+) (-) 0
    → Associative (X:=R) (·)
    → Commutative (X:=R) (·)
    → LeftIdentity  (X:=R) (·) 1
    → LeftDistribute  (X:=R) (·) (+)
    → CommutativeRing R.
  Proof. intros. apply alt_Build_CommutativeRing; trivial.
  + now apply alt_Build_AdditiveGroup.
  + now apply alt_Build_MultiplicativeComMonoid.
  Qed.
End alt_build.

Coercion Rig_NearRig     `{H:Rig R} : NearRig     R.  Proof. now apply alt_Build_NearRig. Qed.
Coercion Rig_LeftNearRig `{H:Rig R} : LeftNearRig R.  Proof. now apply alt_Build_LeftNearRig. Qed.
Coercion Rng_NearRng     `{H:Rng R} : NearRng     R.  Proof. now apply alt_Build_NearRng. Qed.
Coercion Rng_LeftNearRng `{H:Rng R} : LeftNearRng R.  Proof. now apply alt_Build_LeftNearRng. Qed.
Coercion Ring_NearRing     `{H:Ring R} : NearRing     R.  Proof. now apply alt_Build_NearRing. Qed.
Coercion Ring_LeftNearRing `{H:Ring R} : LeftNearRing R.  Proof. now apply alt_Build_LeftNearRing. Qed.

(** Opposite ring structures: multiplication order reversed *)

Section opposite.
  Instance NoZeroDivisors_op `{NoZeroDivisors R} : NoZeroDivisors (R ᵒᵖ).
  Proof. change (∀ x y : R, y · x = 0 ⊸ x = 0 ⊞ y = 0). intros x y; now rew (apar_com _ _). Qed.
  Instance ZeroProduct_op `{ZeroProduct R} : ZeroProduct (R ᵒᵖ).
  Proof. change (∀ x y : R, y · x = 0 ⊸ x = 0 ∨ y = 0). intros x y; now rew (aor_com _ _). Qed.

  Ltac go := split; try exact _; change (@mult (ring_op _) ?f) with f; unfold ring_op; exact _.
  Instance NearRg_op          `{NearRg R}          : LeftNearRg (R ᵒᵖ).      Proof. go. Defined.
  Instance LeftNearRg_op      `{LeftNearRg R}      : NearRg (R ᵒᵖ).          Proof. go. Defined.
  Instance Rg_op              `{Rg R}              : Rg (R ᵒᵖ).              Proof. go. Defined.
  Instance NearRig_op         `{NearRig R}         : LeftNearRig (R ᵒᵖ).     Proof. go. Defined.
  Instance LeftNearRig_op     `{LeftNearRig R}     : NearRig (R ᵒᵖ).         Proof. go. Defined.
  Instance Rig_op             `{Rig R}             : Rig (R ᵒᵖ).             Proof. go. Defined.
  Instance CommutativeRig_op  `{CommutativeRig R}  : CommutativeRig (R ᵒᵖ).  Proof. go. Defined.
  Instance NearRng_op         `{NearRng R}         : LeftNearRng (R ᵒᵖ).     Proof. go. Defined.
  Instance LeftNearRng_op     `{LeftNearRng R}     : NearRng (R ᵒᵖ).         Proof. go. Defined.
  Instance Rng_op             `{Rng R}             : Rng (R ᵒᵖ).             Proof. go. Defined.
  Instance NearRing_op        `{NearRing R}        : LeftNearRing (R ᵒᵖ).    Proof. go. Defined.
  Instance LeftNearRing_op    `{LeftNearRing R}    : NearRing (R ᵒᵖ).        Proof. go. Defined.
  Instance Ring_op            `{Ring R}            : Ring (R ᵒᵖ).            Proof. go. Defined.
  Instance CommutativeRing_op `{CommutativeRing R} : CommutativeRing (R ᵒᵖ). Proof. go. Defined.
End opposite.
Global Hint Extern 2 (NoZeroDivisors  (_ ᵒᵖ)) => simple notypeclasses refine NoZeroDivisors_op  : typeclass_instances.
Global Hint Extern 2 (ZeroProduct     (_ ᵒᵖ)) => simple notypeclasses refine ZeroProduct_op     : typeclass_instances.
Global Hint Extern 2 (LeftNearRg      (_ ᵒᵖ)) => simple notypeclasses refine NearRg_op          : typeclass_instances.
Global Hint Extern 2 (NearRg          (_ ᵒᵖ)) => simple notypeclasses refine LeftNearRg_op      : typeclass_instances.
Global Hint Extern 2 (Rg              (_ ᵒᵖ)) => simple notypeclasses refine Rg_op              : typeclass_instances.
Global Hint Extern 2 (LeftNearRig     (_ ᵒᵖ)) => simple notypeclasses refine NearRig_op         : typeclass_instances.
Global Hint Extern 2 (NearRig         (_ ᵒᵖ)) => simple notypeclasses refine LeftNearRig_op     : typeclass_instances.
Global Hint Extern 2 (Rig             (_ ᵒᵖ)) => simple notypeclasses refine Rig_op             : typeclass_instances.
Global Hint Extern 2 (CommutativeRig  (_ ᵒᵖ)) => simple notypeclasses refine CommutativeRig_op  : typeclass_instances.
Global Hint Extern 2 (LeftNearRng     (_ ᵒᵖ)) => simple notypeclasses refine NearRng_op         : typeclass_instances.
Global Hint Extern 2 (NearRng         (_ ᵒᵖ)) => simple notypeclasses refine LeftNearRng_op     : typeclass_instances.
Global Hint Extern 2 (Rng             (_ ᵒᵖ)) => simple notypeclasses refine Rng_op             : typeclass_instances.
Global Hint Extern 2 (LeftNearRing    (_ ᵒᵖ)) => simple notypeclasses refine NearRing_op        : typeclass_instances.
Global Hint Extern 2 (NearRing        (_ ᵒᵖ)) => simple notypeclasses refine LeftNearRing_op    : typeclass_instances.
Global Hint Extern 2 (Ring            (_ ᵒᵖ)) => simple notypeclasses refine Ring_op            : typeclass_instances.
Global Hint Extern 2 (CommutativeRing (_ ᵒᵖ)) => simple notypeclasses refine CommutativeRing_op : typeclass_instances.

Coercion zero_product_no_zero_divisors `{H:ZeroProduct R} : NoZeroDivisors R.
Proof. red; intros x y. rew <-(aor_apar _ _). apply H. Qed.

(** Miscellaneous Rg properties *)
(* Lemma zero_product `{Rg R} : ∀ x y : R, x = 0 ∨ y = 0 ⊸ x · y = 0.
Proof left_or_right_absorb _. *)

Lemma nonzero_product `{Rg R} : ∀ x y : R, x · y ≠ 0 ⊸ x ≠ 0 ∧ y ≠ 0.
Proof absorb_ne_left_and_right _.

(*Lemma zero_product_par `{Rg R} `{!RefutativeEquality R} : ∀ x y : R, x = 0 ⊞ y = 0 ⊸ x · y = 0.
Proof left_par_right_absorb _.*)

Lemma nonzero_product_prod `{Rg R} `{!RefutativeEquality R} : ∀ x y : R, x · y ≠ 0 ⊸ x ≠ 0 ⊠ y ≠ 0.
Proof absorb_ne_left_prod_right _.

(** Miscellaneous Rig properties *)

Lemma mult_2_plus_l `{NearRig R} (x:R) : 2 · x = x + x.
Proof. now rew (plus_mult_distr_r _ _ _), (mult_1_l _). Qed.

Lemma mult_2_plus_r `{LeftNearRig R} : ∀ x:R, x · 2 = x + x.
Proof mult_2_plus_l (R:=R ᵒᵖ).

Lemma mult_2_2 `{Rig R} : 2 · 2 = 4 :> R.
Proof. rew (mult_2_plus_l _). exact plus_2_2. Qed.

Lemma mult_2_comm `{Rig R} (x:R) : 2 · x = x · 2.
Proof. now rew [(mult_2_plus_l _) | (mult_2_plus_r _)]. Qed.

(** Miscellaneous Rng properties *)

Lemma negate_mult_distr_l `{NearRng R} (x y : R) : -(x · y) = -x · y.
Proof. apply (left_cancellation (+) (x · y) _ _).
  rew [(plus_negate_r _) | <-(plus_mult_distr_r _ _ _)].
  now rew (plus_negate_r _), (mult_0_l _).
Qed.

Lemma negate_mult_distr_r `{LeftNearRng R} (x y : R) : -(x · y) = x · -y.
Proof negate_mult_distr_l (R:=R ᵒᵖ) _ _.

Lemma negate_mult_negate `{Rng R} (x y : R) : -x · -y = x · y.
Proof. rew <-(negate_mult_distr_l _ _), <-(negate_mult_distr_r _ _).
  exact (negate_involutive _).
Qed.

Lemma mult_minus_distr_l `{LeftNearRng R} (x y z : R) : x · (y - z) = x · y - x · z.
Proof. rew (negate_mult_distr_r _ _). exact (plus_mult_distr_l _ _ _). Qed.

Lemma mult_minus_distr_r `{NearRng R} (x y z : R) : (x - y) · z = x · z - y · z.
Proof mult_minus_distr_l (R:=R ᵒᵖ) _ _ _.

Lemma negate_zero_prod_l `{NearRng R} (x y : R) : -x · y = 0 ⧟ x · y = 0.
Proof.
  rew (injective_iff (-) (x · y) _), (negate_mult_distr_l _ _).
  now let E := constr:(negate_0) in rew E.
Qed.

Lemma negate_zero_prod_r `{LeftNearRng R} (x y : R) : x · -y = 0 ⧟ x · y = 0.
Proof negate_zero_prod_l (R:=R ᵒᵖ) _ _.

Lemma negate_mult `{NearRing R} (x:R) : -x = -1 · x.
Proof. now rew <-(negate_mult_distr_l _ _), (mult_1_l _). Qed.

Lemma negate_mult_r `{LeftNearRing R} (x:R) : -x = x · -1.
Proof negate_mult (R:=R ᵒᵖ) _.

(** Morphisms *)

Lemma Rg_Morphism_proper_impl {X Y pX pY mX mY zX zY} (f g : X ⇾ Y)
  : f = g → impl (@Rg_Morphism X Y pX pY mX mY zX zY f) (Rg_Morphism g).
Proof. intros E H; split; now rew <-E. Qed.
Canonical Structure Rg_Morphism_fun {X Y pX pY mX mY zX zY} :=
  make_weak_spred (@Rg_Morphism X Y pX pY mX mY zX zY) Rg_Morphism_proper_impl.

Lemma Rig_Morphism_proper_impl {X Y pX pY mX mY zX zY oX oY} (f g : X ⇾ Y)
  : f = g → impl (@Rig_Morphism X Y pX pY mX mY zX zY oX oY f) (Rig_Morphism g).
Proof. intros E H; split; now rew <-E. Qed.
Canonical Structure Rig_Morphism_fun {X Y pX pY mX mY zX zY oX oY} :=
  make_weak_spred (@Rig_Morphism X Y pX pY mX mY zX zY oX oY) Rig_Morphism_proper_impl.


Lemma rig_mor_rg_mor `{Rig_Morphism (f:=f)} : Rg_Morphism f.  Proof. now split. Qed.
Coercion rig_mor_rg_mor : Rig_Morphism >-> Rg_Morphism.

Lemma alt_Build_Rg_Morphism
  `{AdditiveNonComMonoid X} {mX : Mult X} `{!MultiplicativeSemiGroup X}
  `{AdditiveNonComMonoid Y} {mY : Mult Y} `{!MultiplicativeSemiGroup Y}
  {f : X ⇾ Y} :
  (∀ x y : X, f (x + y) = f x + f y)
 → (∀ x y : X, f (x · y) = f x · f y)
 → f 0 = 0
 → Rg_Morphism f.
Proof. intros. split; try exact _.
+ now apply alt_Build_AdditiveMonoid_Morphism.
+ now apply Build_MultiplicativeSemiGroup_Morphism.
Qed.

Lemma alt_Build_Rig_Morphism
  `{AdditiveNonComMonoid X} {mX : Mult X} {oX : One X} `{!MultiplicativeMonoid X}
  `{AdditiveNonComMonoid Y} {mY : Mult Y} {oY : One Y} `{!MultiplicativeMonoid Y}
  {f : X ⇾ Y} :
  (∀ x y : X, f (x + y) = f x + f y)
 → (∀ x y : X, f (x · y) = f x · f y)
 → f 0 = 0
 → f 1 = 1
 → Rig_Morphism f.
Proof. intros. split; try exact _.
+ now apply alt_Build_AdditiveMonoid_Morphism.
+ now apply alt_Build_MultiplicativeMonoid_Morphism.
Qed.

Lemma Build_Rng_Morphism `{NearRng X} `{NearRng Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x + y) = f x + f y)
 → (∀ x y : X, f (x · y) = f x · f y)
 → Rg_Morphism f.
Proof. intros. split; try exact _.
+ now apply Build_AdditiveGroup_Morphism.
+ now apply Build_MultiplicativeSemiGroup_Morphism.
Qed.

Lemma Build_Ring_Morphism `{NearRing X} `{NearRing Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x + y) = f x + f y)
 → (∀ x y : X, f (x · y) = f x · f y)
 → f 1 = 1
 → Rig_Morphism f.
Proof. intros. split; try exact _.
+ now apply Build_AdditiveGroup_Morphism.
+ now apply alt_Build_MultiplicativeMonoid_Morphism.
Qed.

Lemma id_rg_mor  `{AdditiveNonComMonoid R} `{Mult R} `{!MultiplicativeSemiGroup R} : Rg_Morphism  (id_fun R).  Proof. now split. Qed.
Lemma id_rig_mor `{AdditiveNonComMonoid R} `{Mult R} `{One R} `{!MultiplicativeMonoid R} : Rig_Morphism (id_fun R).  Proof. now split. Qed.

Lemma compose_rg_mor {X Y Z} {p₁ m₁ z₁} {p₂ m₂ z₂} {p₃ m₃ z₃} {g f} :
  @Rg_Morphism X Y p₁ p₂ m₁ m₂ z₁ z₂ f
→ @Rg_Morphism Y Z p₂ p₃ m₂ m₃ z₂ z₃ g
→ Rg_Morphism (g ∘ f).
Proof. now split. Qed.

Lemma compose_rig_mor {X Y Z} {p₁ m₁ z₁ o₁} {p₂ m₂ z₂ o₂} {p₃ m₃ z₃ o₃} {g f} :
  @Rig_Morphism X Y p₁ p₂ m₁ m₂ z₁ z₂ o₁ o₂ f
→ @Rig_Morphism Y Z p₂ p₃ m₂ m₃ z₂ z₃ o₂ o₃ g
→ Rig_Morphism (g ∘ f).
Proof. now split. Qed.

Local Open Scope fun_inv_scope.
Lemma invert_rg_mor `{Rg_Morphism (f:=f)} `{!Inverse f} `{!Bijective f}
  : Rg_Morphism f⁻¹.
Proof. now split. Qed.

Lemma invert_rig_mor `{Rig_Morphism (f:=f)} `{!Inverse f} `{!Bijective f}
  : Rig_Morphism f⁻¹.
Proof. now split. Qed.


Global Hint Extern 2 (Rg_Morphism  (id_fun _) ) => simple notypeclasses refine id_rg_mor  : typeclass_instances.
Global Hint Extern 2 (Rig_Morphism (id_fun _) ) => simple notypeclasses refine id_rig_mor : typeclass_instances.
Global Hint Extern 2 (Rg_Morphism  (_ ∘ _)    ) => simple notypeclasses refine (compose_rg_mor  _ _) : typeclass_instances.
Global Hint Extern 2 (Rig_Morphism (_ ∘ _)    ) => simple notypeclasses refine (compose_rig_mor _ _) : typeclass_instances.
Global Hint Extern 2 (Rg_Morphism  (_⁻¹)      ) => simple notypeclasses refine invert_rg_mor  : typeclass_instances.
Global Hint Extern 2 (Rig_Morphism (_⁻¹)      ) => simple notypeclasses refine invert_rig_mor : typeclass_instances.

Lemma projected_near_rg
  `{NearRg R} `(f:X ⇾ R) `{!Injective f} `{Plus X} `{Mult X} `{Zero X} :
   (∀ x y, f (x + y) = f x + f y)
 → (∀ x y, f (x · y) = f x · f y)
 → f 0 = 0
 → NearRg X.
Proof. intros plus_correct mult_correct zero_correct.
  pose proof projected_additive_non_com_monoid f plus_correct zero_correct.
  pose proof projected_multiplicative_semigroup f mult_correct.
  split; trivial; hnf; intros;
  rew (injective_iff f _ _); rew ?(mult_correct _ _); rew ?(plus_correct _ _);
  rew ?(mult_correct _ _); try rew zero_correct.
  + now apply distribute_r.
  + now apply left_absorb.
Qed.

Lemma projected_left_near_rg
  `{LeftNearRg R} `(f:X ⇾ R) `{!Injective f} `{Plus X} `{Mult X} `{Zero X} :
   (∀ x y, f (x + y) = f x + f y)
 → (∀ x y, f (x · y) = f x · f y)
 → f 0 = 0
 → LeftNearRg X.
Proof. intros plus_correct mult_correct zero_correct.
  enough (NearRg (X ᵒᵖ)) by now change (LeftNearRg (X ᵒᵖ)ᵒᵖ).
  apply (projected_near_rg (R:=R ᵒᵖ) f); trivial.
  intros. apply mult_correct.
Qed.

Lemma projected_rg
  `{Rg R} `(f:X ⇾ R) `{!Injective f} `{Plus X} `{Mult X} `{Zero X} :
   (∀ x y, f (x + y) = f x + f y)
 → (∀ x y, f (x · y) = f x · f y)
 → f 0 = 0
 → Rg X.
Proof. intros plus_correct mult_correct zero_correct.
  pose proof projected_near_rg f plus_correct mult_correct zero_correct.
  pose proof projected_left_near_rg f plus_correct mult_correct zero_correct.
  pose proof projected_additive_monoid f plus_correct zero_correct.
  now split.
Qed.

Lemma projected_rig
  `{Rig R} `(f:X ⇾ R) `{!Injective f} `{Plus X} `{Mult X} `{Zero X} `{One X} :
   (∀ x y, f (x + y) = f x + f y)
 → (∀ x y, f (x · y) = f x · f y)
 → f 0 = 0
 → f 1 = 1
 → Rig X.
Proof. intros plus_correct mult_correct zero_correct one_correct.
  pose proof projected_rg f plus_correct mult_correct zero_correct.
  pose proof projected_multiplicative_monoid f mult_correct one_correct.
  now split.
Qed.

Lemma projected_commutative_rig
  `{CommutativeRig R} `(f:X ⇾ R) `{!Injective f} `{Plus X} `{Mult X} `{Zero X} `{One X} :
   (∀ x y, f (x + y) = f x + f y)
 → (∀ x y, f (x · y) = f x · f y)
 → f 0 = 0
 → f 1 = 1
 → CommutativeRig X.
Proof. intros plus_correct mult_correct zero_correct one_correct.
  pose proof projected_rig f plus_correct mult_correct zero_correct.
  pose proof projected_multiplicative_com_monoid f mult_correct one_correct.
  now split.
Qed.

Lemma projected_rng
  `{Rng R} `(f:X ⇾ R) `{!Injective f} `{Plus X} `{Mult X} `{Zero X} `{Negate X} :
   (∀ x y, f (x + y) = f x + f y)
 → (∀ x y, f (x · y) = f x · f y)
 → f 0 = 0
 → (∀ x, f (-x) = -(f x))
 → Rng X.
Proof. intros plus_correct mult_correct zero_correct negate_correct.
  pose proof projected_rg f plus_correct mult_correct zero_correct.
  pose proof projected_additive_group f plus_correct zero_correct negate_correct.
  now split.
Qed.

Lemma projected_ring
  `{Ring R} `(f:X ⇾ R) `{!Injective f} `{Plus X} `{Mult X} `{Zero X} `{One X} `{Negate X} :
   (∀ x y, f (x + y) = f x + f y)
 → (∀ x y, f (x · y) = f x · f y)
 → f 0 = 0
 → f 1 = 1
 → (∀ x, f (-x) = -(f x))
 → Ring X.
Proof. intros plus_correct mult_correct zero_correct one_correct negate_correct.
  pose proof projected_rng f plus_correct mult_correct zero_correct negate_correct.
  pose proof projected_rig f plus_correct mult_correct zero_correct one_correct.
  now split.
Qed.

Lemma projected_commutative_ring
  `{CommutativeRing R} `(f:X ⇾ R) `{!Injective f} `{Plus X} `{Mult X} `{Zero X} `{One X} `{Negate X} :
   (∀ x y, f (x + y) = f x + f y)
 → (∀ x y, f (x · y) = f x · f y)
 → f 0 = 0
 → f 1 = 1
 → (∀ x, f (-x) = -(f x))
 → CommutativeRing X.
Proof. intros plus_correct mult_correct zero_correct one_correct negate_correct.
  pose proof projected_ring f plus_correct mult_correct zero_correct one_correct negate_correct.
  pose proof projected_commutative_rig f plus_correct mult_correct zero_correct one_correct.
  now split.
Qed.

