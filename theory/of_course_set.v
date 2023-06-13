Require Import interfaces.common_props.
Require Import abstract_algebra.
Require Import easy.

Import of_course_set_notation.

Local Ltac doit := let H := fresh "H" in intro H; hnf; intros; apply H.


Lemma of_course_set_associative       {X     f    } : @Associative      X     f     → @Associative      !X       (of_course_op  f).  Proof. doit. Qed.
Lemma of_course_set_commutative       {X Y   f    } : @Commutative      X Y   f     → @Commutative      !X !Y    (of_course_op  f).  Proof. doit. Qed.
Lemma of_course_set_binary_idempotent {X     f    } : @BinaryIdempotent X     f     → @BinaryIdempotent !X       (of_course_op  f).  Proof. doit. Qed.
Lemma of_course_set_involutive        {X     f    } : @Involutive       X     f     → @Involutive       !X       (of_course_map f).  Proof. doit. Qed.
Lemma of_course_set_absorption        {X Y Z f g  } : @Absorption       X Y Z f g   → @Absorption       !X !Y !Z (of_course_op  f) (of_course_op g).  Proof. doit. Qed.
Lemma of_course_set_left_distribute   {X     f g  } : @LeftDistribute   X     f g   → @LeftDistribute   !X       (of_course_op  f) (of_course_op g).  Proof. doit. Qed.
Lemma of_course_set_right_distribute  {X     f g  } : @RightDistribute  X     f g   → @RightDistribute  !X       (of_course_op  f) (of_course_op g).  Proof. doit. Qed.

Lemma of_course_set_left_identity     {X Y   f x  } : @LeftIdentity     X Y   f x   → @LeftIdentity     !X !Y    (of_course_op  f) x.  Proof. doit. Qed.
Lemma of_course_set_right_identity    {X Y   f y  } : @RightIdentity    X Y   f y   → @RightIdentity    !X !Y    (of_course_op  f) y.  Proof. doit. Qed.
Lemma of_course_set_left_absorb       {X Y   f x  } : @LeftAbsorb       X Y   f x   → @LeftAbsorb       !X !Y    (of_course_op  f) x.  Proof. doit. Qed.
Lemma of_course_set_right_absorb      {X Y   f y  } : @RightAbsorb      X Y   f y   → @RightAbsorb      !X !Y    (of_course_op  f) y.  Proof. doit. Qed.

Lemma of_course_set_left_inverse      {X Y Z f g x} : @LeftInverse      X Y Z f g x → @LeftInverse      !X !Y !Z (of_course_op  f) (of_course_map g) x.  Proof. doit. Qed.
Lemma of_course_set_right_inverse     {X Y Z f g x} : @RightInverse     X Y Z f g x → @RightInverse     !X !Y !Z (of_course_op  f) (of_course_map g) x.  Proof. doit. Qed.

Global Hint Extern 2 (Associative (of_course_op _)) => simple notypeclasses refine (of_course_set_associative _) : typeclass_instances.
Global Hint Extern 2 (Commutative (of_course_op _)) => simple notypeclasses refine (of_course_set_commutative _) : typeclass_instances.
Global Hint Extern 2 (BinaryIdempotent (of_course_op _)) => simple notypeclasses refine (of_course_set_binary_idempotent _) : typeclass_instances.
Global Hint Extern 2 (Involutive (of_course_map _)) => simple notypeclasses refine (of_course_set_involutive _) : typeclass_instances.
Global Hint Extern 2 (Absorption (of_course_op _) _) => simple notypeclasses refine (of_course_set_absorption _) : typeclass_instances.
Global Hint Extern 2 (LeftDistribute (of_course_op _) _) => simple notypeclasses refine (of_course_set_left_distribute _) : typeclass_instances.
Global Hint Extern 2 (RightDistribute (of_course_op _) _) => simple notypeclasses refine (of_course_set_right_distribute _) : typeclass_instances.

Global Hint Extern 2 (LeftIdentity (of_course_op _) _) => simple notypeclasses refine (of_course_set_left_identity _) : typeclass_instances.
Global Hint Extern 2 (RightIdentity (of_course_op _) _) => simple notypeclasses refine (of_course_set_right_identity _) : typeclass_instances.
Global Hint Extern 2 (LeftAbsorb (of_course_op _) _) => simple notypeclasses refine (of_course_set_left_absorb _) : typeclass_instances.
Global Hint Extern 2 (RightAbsorb (of_course_op _) _) => simple notypeclasses refine (of_course_set_right_absorb _) : typeclass_instances.

Global Hint Extern 2 (LeftInverse (of_course_op _) _ _) => simple notypeclasses refine (of_course_set_left_inverse _) : typeclass_instances.
Global Hint Extern 2 (RightInverse (of_course_op _) _ _) => simple notypeclasses refine (of_course_set_right_inverse _) : typeclass_instances.


Global Hint Extern 6 (MonUnit (! ?X)) => change (MonUnit X) : typeclass_instances.
Global Hint Extern 6 (Zero    (! ?X)) => change (Zero    X) : typeclass_instances.
Global Hint Extern 6 (One     (! ?X)) => change (One     X) : typeclass_instances.
Global Hint Extern 6 (Top     (! ?X)) => change (Top     X) : typeclass_instances.
Global Hint Extern 6 (Bottom  (! ?X)) => change (Bottom  X) : typeclass_instances.

Global Hint Extern 6 (SgOp   (! _)) => refine (of_course_op sg_op) : typeclass_instances.
Global Hint Extern 6 (Inv    (! _)) => refine (of_course_map inv ) : typeclass_instances.
Global Hint Extern 6 (Plus   (! _)) => refine (of_course_op (+)  ) : typeclass_instances.
Global Hint Extern 6 (Mult   (! _)) => refine (of_course_op mult ) : typeclass_instances.
Global Hint Extern 6 (Negate (! _)) => refine (of_course_map (-) ) : typeclass_instances.
Global Hint Extern 6 (Meet   (! _)) => refine (of_course_op meet ) : typeclass_instances.
Global Hint Extern 6 (Join   (! _)) => refine (of_course_op join ) : typeclass_instances.


Local Ltac doit2 :=
  try exact _;
  try change (_ _ (of_course_op ?f)) with (of_course_op f);
  try change (_ _ (of_course_map ?f)) with (of_course_map f);
  try exact _.

Local Ltac doit3 := intro; first [ split | red ]; doit2.

Local Instance of_course_set_semigroup      `{SgOp X}                       : SemiGroup            X → SemiGroup            !X.  Proof. doit3. Qed.
Local Instance of_course_set_com_semigroup  `{SgOp X}                       : CommutativeSemiGroup X → CommutativeSemiGroup !X.  Proof. doit3. Qed.
Local Instance of_course_set_semilattice    `{SgOp X}                       : SemiLattice          X → SemiLattice          !X.  Proof. doit3. Qed.
Local Instance of_course_set_monoid         `{SgOp X} `{MonUnit X}          : Monoid               X → Monoid               !X.  Proof. doit3. Qed.
Local Instance of_course_set_com_monoid     `{SgOp X} `{MonUnit X}          : CommutativeMonoid    X → CommutativeMonoid    !X.  Proof. doit3. Qed.
Local Instance of_course_set_bounded_sl     `{SgOp X} `{MonUnit X}          : BoundedSemiLattice   X → BoundedSemiLattice   !X.  Proof. doit3. Qed.
Local Instance of_course_set_group          `{SgOp X} `{MonUnit X} `{Inv X} : Group                X → Group                !X.  Proof. doit3. Qed.
Local Instance of_course_set_abgroup        `{SgOp X} `{MonUnit X} `{Inv X} : AbGroup              X → AbGroup              !X.  Proof. doit3. Qed.

Global Hint Extern 4 (SemiGroup !_) => simple notypeclasses refine (of_course_set_semigroup _) : typeclass_instances.
Global Hint Extern 4 (CommutativeSemiGroup !_) => simple notypeclasses refine (of_course_set_com_semigroup _) : typeclass_instances.
Global Hint Extern 4 (SemiLattice !_) => simple notypeclasses refine (of_course_set_semilattice _) : typeclass_instances.
Global Hint Extern 4 (Monoid !_) => simple notypeclasses refine (of_course_set_monoid _) : typeclass_instances.
Global Hint Extern 4 (CommutativeMonoid !_) => simple notypeclasses refine (of_course_set_com_monoid _) : typeclass_instances.
Global Hint Extern 4 (BoundedSemiLattice !_) => simple notypeclasses refine (of_course_set_bounded_sl _) : typeclass_instances.
Global Hint Extern 4 (Group !_) => simple notypeclasses refine (of_course_set_group _) : typeclass_instances.
Global Hint Extern 4 (AbGroup !_) => simple notypeclasses refine (of_course_set_abgroup _) : typeclass_instances.


Local Instance of_course_set_meet_sl         `{Meet X}             : MeetSemiLattice        X → MeetSemiLattice        !X.  Proof of_course_set_semilattice.
Local Instance of_course_set_bounded_meet_sl `{Meet X} `{Top X}    : BoundedMeetSemiLattice X → BoundedMeetSemiLattice !X.  Proof of_course_set_bounded_sl.
Local Instance of_course_set_join_sl         `{Join X}             : JoinSemiLattice        X → JoinSemiLattice        !X.  Proof of_course_set_semilattice.
Local Instance of_course_set_bounded_join_sl `{Join X} `{Bottom X} : BoundedJoinSemiLattice X → BoundedJoinSemiLattice !X.  Proof of_course_set_bounded_sl.

Local Instance of_course_set_lattice       `{Meet X} `{Join X} : Lattice             X → Lattice             !X.  Proof. doit3. Qed.
Local Instance of_course_set_distr_lattice `{Meet X} `{Join X} : DistributiveLattice X → DistributiveLattice !X.  Proof. doit3. Qed.

Global Hint Extern 4 (MeetSemiLattice !_) => simple notypeclasses refine (of_course_set_meet_sl _) : typeclass_instances.
Global Hint Extern 4 (BoundedMeetSemiLattice !_) => simple notypeclasses refine (of_course_set_bounded_meet_sl _) : typeclass_instances.
Global Hint Extern 4 (JoinSemiLattice !_) => simple notypeclasses refine (of_course_set_join_sl _) : typeclass_instances.
Global Hint Extern 4 (BoundedJoinSemiLattice !_) => simple notypeclasses refine (of_course_set_bounded_join_sl _) : typeclass_instances.
Global Hint Extern 4 (Lattice !_) => simple notypeclasses refine (of_course_set_lattice _) : typeclass_instances.
Global Hint Extern 4 (DistributiveLattice !_) => simple notypeclasses refine (of_course_set_distr_lattice _) : typeclass_instances.



Local Instance of_course_set_add_nc_sg  `{Plus X}                       : AdditiveNonComSemiGroup X → AdditiveNonComSemiGroup !X.  Proof of_course_set_semigroup.
Local Instance of_course_set_add_sg     `{Plus X}                       : AdditiveSemiGroup       X → AdditiveSemiGroup       !X.  Proof of_course_set_com_semigroup.
Local Instance of_course_set_add_nc_mon `{Plus X} `{Zero X}             : AdditiveNonComMonoid    X → AdditiveNonComMonoid    !X.  Proof of_course_set_monoid.
Local Instance of_course_set_add_mon    `{Plus X} `{Zero X}             : AdditiveMonoid          X → AdditiveMonoid          !X.  Proof of_course_set_com_monoid.
Local Instance of_course_set_add_nc_grp `{Plus X} `{Zero X} `{Negate X} : AdditiveNonComGroup     X → AdditiveNonComGroup     !X.  Proof of_course_set_group.
Local Instance of_course_set_add_grp    `{Plus X} `{Zero X} `{Negate X} : AdditiveGroup           X → AdditiveGroup           !X.  Proof of_course_set_abgroup.

Local Instance of_course_set_mult_sg      `{Mult X}          : MultiplicativeSemiGroup X → MultiplicativeSemiGroup !X.  Proof of_course_set_semigroup.
Local Instance of_course_set_mult_mon     `{Mult X} `{One X} : MultiplicativeMonoid    X → MultiplicativeMonoid    !X.  Proof of_course_set_monoid.
Local Instance of_course_set_mult_com_mon `{Mult X} `{One X} : MultiplicativeComMonoid X → MultiplicativeComMonoid !X.  Proof of_course_set_com_monoid.

Global Hint Extern 4 (AdditiveNonComSemiGroup !_) => simple notypeclasses refine (of_course_set_add_nc_sg _) : typeclass_instances.
Global Hint Extern 4 (AdditiveSemiGroup !_) => simple notypeclasses refine (of_course_set_add_sg _) : typeclass_instances.
Global Hint Extern 4 (AdditiveNonComMonoid !_) => simple notypeclasses refine (of_course_set_add_nc_mon _) : typeclass_instances.
Global Hint Extern 4 (AdditiveMonoid !_) => simple notypeclasses refine (of_course_set_add_mon _) : typeclass_instances.
Global Hint Extern 4 (AdditiveNonComGroup !_) => simple notypeclasses refine (of_course_set_add_nc_grp _) : typeclass_instances.
Global Hint Extern 4 (AdditiveGroup !_) => simple notypeclasses refine (of_course_set_add_grp _) : typeclass_instances.
Global Hint Extern 4 (MultiplicativeSemiGroup !_) => simple notypeclasses refine (of_course_set_mult_sg _) : typeclass_instances.
Global Hint Extern 4 (MultiplicativeMonoid !_) => simple notypeclasses refine (of_course_set_mult_mon _) : typeclass_instances.
Global Hint Extern 4 (MultiplicativeComMonoid !_) => simple notypeclasses refine (of_course_set_mult_com_mon _) : typeclass_instances.


Local Instance of_course_set_near_rg        `{Plus X} `{Mult X} `{Zero X}                      : NearRg          X → NearRg          !X.  Proof. doit3. Qed.
Local Instance of_course_set_left_near_rg   `{Plus X} `{Mult X} `{Zero X}                      : LeftNearRg      X → LeftNearRg      !X.  Proof. doit3. Qed.
Local Instance of_course_set_rg             `{Plus X} `{Mult X} `{Zero X}                      : Rg              X → Rg              !X.  Proof. doit3. Qed.
Local Instance of_course_set_near_rig       `{Plus X} `{Mult X} `{Zero X} `{One X}             : NearRig         X → NearRig         !X.  Proof. doit3. Qed.
Local Instance of_course_set_left_near_rig  `{Plus X} `{Mult X} `{Zero X} `{One X}             : LeftNearRig     X → LeftNearRig     !X.  Proof. doit3. Qed.
Local Instance of_course_set_rig            `{Plus X} `{Mult X} `{Zero X} `{One X}             : Rig             X → Rig             !X.  Proof. doit3. Qed.
Local Instance of_course_set_near_rng       `{Plus X} `{Mult X} `{Zero X}          `{Negate X} : NearRng         X → NearRng         !X.  Proof. doit3. Qed.
Local Instance of_course_set_left_near_rng  `{Plus X} `{Mult X} `{Zero X}          `{Negate X} : LeftNearRng     X → LeftNearRng     !X.  Proof. doit3. Qed.
Local Instance of_course_set_rng            `{Plus X} `{Mult X} `{Zero X}          `{Negate X} : Rng             X → Rng             !X.  Proof. doit3. Qed.
Local Instance of_course_set_near_ring      `{Plus X} `{Mult X} `{Zero X} `{One X} `{Negate X} : NearRing        X → NearRing        !X.  Proof. doit3. Qed.
Local Instance of_course_set_left_near_ring `{Plus X} `{Mult X} `{Zero X} `{One X} `{Negate X} : LeftNearRing    X → LeftNearRing    !X.  Proof. doit3. Qed.
Local Instance of_course_set_ring           `{Plus X} `{Mult X} `{Zero X} `{One X} `{Negate X} : Ring            X → Ring            !X.  Proof. doit3. Qed.

Local Instance of_course_set_com_rig        `{Plus X} `{Mult X} `{Zero X} `{One X}             : CommutativeRig  X → CommutativeRig  !X.  Proof. doit3. Qed.
Local Instance of_course_set_com_ring       `{Plus X} `{Mult X} `{Zero X} `{One X} `{Negate X} : CommutativeRing X → CommutativeRing !X.  Proof. doit3. Qed.

Global Hint Extern 4 (NearRg !_) => simple notypeclasses refine (of_course_set_near_rg _) : typeclass_instances.
Global Hint Extern 4 (LeftNearRg !_) => simple notypeclasses refine (of_course_set_left_near_rg _) : typeclass_instances.
Global Hint Extern 4 (Rg !_) => simple notypeclasses refine (of_course_set_rg _) : typeclass_instances.

Global Hint Extern 4 (NearRig !_) => simple notypeclasses refine (of_course_set_near_rig _) : typeclass_instances.
Global Hint Extern 4 (LeftNearRig !_) => simple notypeclasses refine (of_course_set_left_near_rig _) : typeclass_instances.
Global Hint Extern 4 (Rig !_) => simple notypeclasses refine (of_course_set_rig _) : typeclass_instances.

Global Hint Extern 4 (NearRng !_) => simple notypeclasses refine (of_course_set_near_rg _) : typeclass_instances.
Global Hint Extern 4 (LeftNearRng !_) => simple notypeclasses refine (of_course_set_left_near_rg _) : typeclass_instances.
Global Hint Extern 4 (Rng !_) => simple notypeclasses refine (of_course_set_rg _) : typeclass_instances.

Global Hint Extern 4 (NearRing !_) => simple notypeclasses refine (of_course_set_near_ring _) : typeclass_instances.
Global Hint Extern 4 (LeftNearRing !_) => simple notypeclasses refine (of_course_set_left_near_ring _) : typeclass_instances.
Global Hint Extern 4 (Ring !_) => simple notypeclasses refine (of_course_set_ring _) : typeclass_instances.

Global Hint Extern 4 (CommutativeRig !_) => simple notypeclasses refine (of_course_set_com_rig _) : typeclass_instances.
Global Hint Extern 4 (CommutativeRing !_) => simple notypeclasses refine (of_course_set_com_ring _) : typeclass_instances.

Local Notation ε := of_course_counit.

Local Instance of_course_counit_pointed {X:set} {x:X} : @Pointed_Morphism !X X x x (ε X).  Proof. now change (x = x). Qed.
Local Instance of_course_counit_unit_pointed   `{MonUnit X} : MonUnit_Pointed_Morphism (ε X).  Proof of_course_counit_pointed.
Local Instance of_course_counit_top_pointed    `{Top     X} : Top_Pointed_Morphism     (ε X).  Proof of_course_counit_pointed.
Local Instance of_course_counit_bottom_pointed `{Bottom  X} : Bottom_Pointed_Morphism  (ε X).  Proof of_course_counit_pointed.
Local Instance of_course_counit_zero_pointed   `{Zero    X} : Zero_Pointed_Morphism    (ε X).  Proof of_course_counit_pointed.
Local Instance of_course_counit_one_pointed    `{One     X} : One_Pointed_Morphism     (ε X).  Proof of_course_counit_pointed.

Local Instance of_course_counit_sg_mor `{SemiGroup X} : SemiGroup_Morphism (ε X).  Proof. split; try exact _. now intros. Qed.
Local Instance of_course_counit_mon_mor `{Monoid X} : Monoid_Morphism (ε X).  Proof. now split. Qed.

Local Instance of_course_counit_add_sg_mor `{AdditiveNonComSemiGroup X} : AdditiveSemiGroup_Morphism (ε X).  Proof of_course_counit_sg_mor.
Local Instance of_course_counit_add_mon_mor `{AdditiveNonComMonoid X} : AdditiveMonoid_Morphism (ε X).  Proof of_course_counit_mon_mor.

Local Instance of_course_counit_mul_sg_mor `{MultiplicativeSemiGroup X} : MultiplicativeSemiGroup_Morphism (ε X).  Proof of_course_counit_sg_mor.
Local Instance of_course_counit_mul_mon_mor `{MultiplicativeMonoid X} : MultiplicativeMonoid_Morphism (ε X).  Proof of_course_counit_mon_mor.

Local Instance of_course_counit_rg_mor `{AdditiveNonComMonoid X} `{MultiplicativeSemiGroup X} : Rg_Morphism (ε X).  Proof. now split. Qed.
Local Instance of_course_counit_rig_mor `{AdditiveNonComMonoid X} `{MultiplicativeMonoid X} : Rig_Morphism (ε X).  Proof. now split. Qed.

Global Hint Extern 2 (Pointed_Morphism _ _ (ε _)) => simple notypeclasses refine of_course_counit_pointed : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (ε _)) => simple notypeclasses refine of_course_counit_unit_pointed : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism (ε _)) => simple notypeclasses refine of_course_counit_top_pointed : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (ε _)) => simple notypeclasses refine of_course_counit_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (ε _)) => simple notypeclasses refine of_course_counit_zero_pointed : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (ε _)) => simple notypeclasses refine of_course_counit_one_pointed : typeclass_instances.

Global Hint Extern 2 (SemiGroup_Morphism (ε _)) => simple notypeclasses refine of_course_counit_sg_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (ε _)) => simple notypeclasses refine of_course_counit_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (ε _)) => simple notypeclasses refine of_course_counit_add_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (ε _)) => simple notypeclasses refine of_course_counit_add_mon_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (ε _)) => simple notypeclasses refine of_course_counit_mul_sg_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (ε _)) => simple notypeclasses refine of_course_counit_mul_mon_mor : typeclass_instances.
Global Hint Extern 2 (Rg_Morphism (ε _)) => simple notypeclasses refine of_course_counit_rg_mor : typeclass_instances.
Global Hint Extern 2 (Rig_Morphism (ε _)) => simple notypeclasses refine of_course_counit_rig_mor : typeclass_instances.


