Require Export interfaces.pointwise.
Require Import interfaces.common_props.
Require Import abstract_algebra.

Local Ltac doit := let H := fresh "H" in
  intro H; hnf; intros; intro; (* repeat change (pointwise_op ?f ?D (?x, ?y) ?p) with (f (x p, y p)); *) apply H.

Lemma pointwise_associative       {X     f     D} {Hf:PointwiseOp f D}                      : @Associative      X     f     → Associative      (pointwise_op   f D).  Proof. doit. Qed.
Lemma pointwise_commutative       {X Y   f     D} {Hf:PointwiseOp f D}                      : @Commutative      X Y   f     → Commutative      (pointwise_op   f D).  Proof. doit. Qed.
Lemma pointwise_binary_idempotent {X     f     D} {Hf:PointwiseOp f D}                      : @BinaryIdempotent X     f     → BinaryIdempotent (pointwise_op   f D).  Proof. doit. Qed.
Lemma pointwise_involutive        {X     f     D}                                           : @Involutive       X     f     → Involutive       (pointwise_func f D).  Proof. doit. Qed.
Lemma pointwise_absorption        {X Y Z f g   D} {Hf:PointwiseOp f D} {Hg:PointwiseOp g D} : @Absorption       X Y Z f g   → Absorption       (pointwise_op   f D) (pointwise_op g D).  Proof. doit. Qed.
Lemma pointwise_left_distribute   {X     f g   D} {Hf:PointwiseOp f D} {Hg:PointwiseOp g D} : @LeftDistribute   X     f g   → LeftDistribute   (pointwise_op   f D) (pointwise_op g D).  Proof. doit. Qed.
Lemma pointwise_right_distribute  {X     f g   D} {Hf:PointwiseOp f D} {Hg:PointwiseOp g D} : @RightDistribute  X     f g   → RightDistribute  (pointwise_op   f D) (pointwise_op g D).  Proof. doit. Qed.

Lemma pointwise_left_identity     {X Y   f x   D} {Hf:PointwiseOp f D}                      : @LeftIdentity     X Y   f x   → LeftIdentity     (pointwise_op   f D) (const x).  Proof. doit. Qed.
Lemma pointwise_right_identity    {X Y   f y   D} {Hf:PointwiseOp f D}                      : @RightIdentity    X Y   f y   → RightIdentity    (pointwise_op   f D) (const y).  Proof. doit. Qed.
Lemma pointwise_left_absorb       {X Y   f x   D} {Hf:PointwiseOp f D}                      : @LeftAbsorb       X Y   f x   → LeftAbsorb       (pointwise_op   f D) (const x).  Proof. doit. Qed.
Lemma pointwise_right_absorb      {X Y   f y   D} {Hf:PointwiseOp f D}                      : @RightAbsorb      X Y   f y   → RightAbsorb      (pointwise_op   f D) (const y).  Proof. doit. Qed.

Lemma pointwise_left_inverse      {X Y Z f g x D} {Hf:PointwiseOp f D}                      : @LeftInverse      X Y Z f g x → LeftInverse      (pointwise_op   f D) (pointwise_func g D) (const x).  Proof. doit. Qed.
Lemma pointwise_right_inverse     {X Y Z f g x D} {Hf:PointwiseOp f D}                      : @RightInverse     X Y Z f g x → RightInverse     (pointwise_op   f D) (pointwise_func g D) (const x).  Proof. doit. Qed.

Global Hint Extern 2 (Associative (pointwise_op _ _)) => simple notypeclasses refine (pointwise_associative _) : typeclass_instances.
Global Hint Extern 2 (Commutative (pointwise_op _ _)) => simple notypeclasses refine (pointwise_commutative _) : typeclass_instances.
Global Hint Extern 2 (BinaryIdempotent (pointwise_op _ _)) => simple notypeclasses refine (pointwise_binary_idempotent _) : typeclass_instances.
Global Hint Extern 2 (Involutive (pointwise_func _ _)) => simple notypeclasses refine (pointwise_involutive _) : typeclass_instances.
Global Hint Extern 2 (Absorption (pointwise_op _ _) _) => simple notypeclasses refine (pointwise_absorption _) : typeclass_instances.
Global Hint Extern 2 (LeftDistribute (pointwise_op _ _) _) => simple notypeclasses refine (pointwise_left_distribute _) : typeclass_instances.
Global Hint Extern 2 (RightDistribute (pointwise_op _ _) _) => simple notypeclasses refine (pointwise_right_distribute _) : typeclass_instances.

Global Hint Extern 2 (LeftIdentity (pointwise_op _ _) _) => simple notypeclasses refine (pointwise_left_identity _) : typeclass_instances.
Global Hint Extern 2 (RightIdentity (pointwise_op _ _) _) => simple notypeclasses refine (pointwise_right_identity _) : typeclass_instances.
Global Hint Extern 2 (LeftAbsorb (pointwise_op _ _) _) => simple notypeclasses refine (pointwise_left_absorb _) : typeclass_instances.
Global Hint Extern 2 (RightAbsorb (pointwise_op _ _) _) => simple notypeclasses refine (pointwise_right_absorb _) : typeclass_instances.

Global Hint Extern 2 (LeftInverse (pointwise_op _ _) _ _) => simple notypeclasses refine (pointwise_left_inverse _) : typeclass_instances.
Global Hint Extern 2 (RightInverse (pointwise_op _ _) _ _) => simple notypeclasses refine (pointwise_right_inverse _) : typeclass_instances.


Local Hint Extern 2 (MonUnit (_ ⇾ _)) => refine (const mon_unit) : typeclass_instances.
Local Hint Extern 2 (Zero    (_ ⇾ _)) => refine (const zero    ) : typeclass_instances.
Local Hint Extern 2 (One     (_ ⇾ _)) => refine (const one     ) : typeclass_instances.
Local Hint Extern 2 (Top     (_ ⇾ _)) => refine (const top     ) : typeclass_instances.
Local Hint Extern 2 (Bottom  (_ ⇾ _)) => refine (const bottom  ) : typeclass_instances.

Local Hint Extern 2 (SgOp   (?D ⇾ _)) => refine (pointwise_op sg_op D) : typeclass_instances.
Local Hint Extern 2 (Inv    (?D ⇾ _)) => refine (pointwise_func inv D) : typeclass_instances.
Local Hint Extern 2 (Plus   (?D ⇾ _)) => refine (pointwise_op (+)   D) : typeclass_instances.
Local Hint Extern 2 (Mult   (?D ⇾ _)) => refine (pointwise_op mult  D) : typeclass_instances.
Local Hint Extern 2 (Negate (?D ⇾ _)) => refine (pointwise_func (-) D) : typeclass_instances.
Local Hint Extern 2 (Meet   (?D ⇾ _)) => refine (pointwise_op meet  D) : typeclass_instances.
Local Hint Extern 2 (Join   (?D ⇾ _)) => refine (pointwise_op join  D) : typeclass_instances.

Local Ltac doit2 :=
  try exact _;
  try change (_ _ (pointwise_op ?f ?D)) with (pointwise_op f D);
  try change (_ _ (pointwise_func ?f ?D)) with (pointwise_func f D);
  try change (_ _ (const ?x)) with (const x);
  try exact _.

Local Ltac doit3 := intro; first [ split | red ]; doit2.

Local Instance pointwise_semigroup      `{SgOp X} `{!PointwiseOp (X:=X) sg_op D}                       : SemiGroup            X → SemiGroup            (D ⇾ X).  Proof. doit3. Qed.
Local Instance pointwise_com_semigroup  `{SgOp X} `{!PointwiseOp (X:=X) sg_op D}                       : CommutativeSemiGroup X → CommutativeSemiGroup (D ⇾ X).  Proof. doit3. Qed.
Local Instance pointwise_semilattice    `{SgOp X} `{!PointwiseOp (X:=X) sg_op D}                       : SemiLattice          X → SemiLattice          (D ⇾ X).  Proof. doit3. Qed.
Local Instance pointwise_monoid         `{SgOp X} `{!PointwiseOp (X:=X) sg_op D} `{MonUnit X}          : Monoid               X → Monoid               (D ⇾ X).  Proof. doit3. Qed.
Local Instance pointwise_com_monoid     `{SgOp X} `{!PointwiseOp (X:=X) sg_op D} `{MonUnit X}          : CommutativeMonoid    X → CommutativeMonoid    (D ⇾ X).  Proof. doit3. Qed.
Local Instance pointwise_bounded_sl     `{SgOp X} `{!PointwiseOp (X:=X) sg_op D} `{MonUnit X}          : BoundedSemiLattice   X → BoundedSemiLattice   (D ⇾ X).  Proof. doit3. Qed.
Local Instance pointwise_group          `{SgOp X} `{!PointwiseOp (X:=X) sg_op D} `{MonUnit X} `{Inv X} : Group                X → Group                (D ⇾ X).  Proof. doit3. Qed.
Local Instance pointwise_abgroup        `{SgOp X} `{!PointwiseOp (X:=X) sg_op D} `{MonUnit X} `{Inv X} : AbGroup              X → AbGroup              (D ⇾ X).  Proof. doit3. Qed.

Local Instance pointwise_meet_sl         `{Meet X} `{!PointwiseOp (X:=X) meet D}             : MeetSemiLattice        X → MeetSemiLattice        (D ⇾ X).  Proof pointwise_semilattice.
Local Instance pointwise_bounded_meet_sl `{Meet X} `{!PointwiseOp (X:=X) meet D} `{Top X}    : BoundedMeetSemiLattice X → BoundedMeetSemiLattice (D ⇾ X).  Proof pointwise_bounded_sl.
Local Instance pointwise_join_sl         `{Join X} `{!PointwiseOp (X:=X) join D}             : JoinSemiLattice        X → JoinSemiLattice        (D ⇾ X).  Proof pointwise_semilattice.
Local Instance pointwise_bounded_join_sl `{Join X} `{!PointwiseOp (X:=X) join D} `{Bottom X} : BoundedJoinSemiLattice X → BoundedJoinSemiLattice (D ⇾ X).  Proof pointwise_bounded_sl.

Local Instance pointwise_lattice       `{Meet X} `{Join X} `{!PointwiseOp (X:=X) meet D} `{!PointwiseOp (X:=X) join D} : Lattice             X → Lattice             (D ⇾ X).  Proof. doit3. Qed.
Local Instance pointwise_distr_lattice `{Meet X} `{Join X} `{!PointwiseOp (X:=X) meet D} `{!PointwiseOp (X:=X) join D} : DistributiveLattice X → DistributiveLattice (D ⇾ X).  Proof. doit3. Qed.


Local Instance pointwise_add_nc_mon `{Plus X} `{!PointwiseOp (X:=X) plus D} `{Zero X}             : AdditiveNonComMonoid X → AdditiveNonComMonoid (D ⇾ X).  Proof pointwise_monoid.
Local Instance pointwise_add_mon    `{Plus X} `{!PointwiseOp (X:=X) plus D} `{Zero X}             : AdditiveMonoid       X → AdditiveMonoid       (D ⇾ X).  Proof pointwise_com_monoid.
Local Instance pointwise_add_nc_grp `{Plus X} `{!PointwiseOp (X:=X) plus D} `{Zero X} `{Negate X} : AdditiveNonComGroup  X → AdditiveNonComGroup  (D ⇾ X).  Proof pointwise_group.
Local Instance pointwise_add_grp    `{Plus X} `{!PointwiseOp (X:=X) plus D} `{Zero X} `{Negate X} : AdditiveGroup        X → AdditiveGroup        (D ⇾ X).  Proof pointwise_abgroup.

Local Instance pointwise_mult_sg      `{Mult X} `{!PointwiseOp (X:=X) mult D}          : MultiplicativeSemiGroup X → MultiplicativeSemiGroup (D ⇾ X).  Proof pointwise_semigroup.
Local Instance pointwise_mult_mon     `{Mult X} `{!PointwiseOp (X:=X) mult D} `{One X} : MultiplicativeMonoid    X → MultiplicativeMonoid    (D ⇾ X).  Proof pointwise_monoid.
Local Instance pointwise_mult_com_mon `{Mult X} `{!PointwiseOp (X:=X) mult D} `{One X} : MultiplicativeComMonoid X → MultiplicativeComMonoid (D ⇾ X).  Proof pointwise_com_monoid.


