Require Import interfaces.common_props.
Require Import abstract_algebra.
Require Import theory.groups.
Require Import easy.
Require Import set_lambda.
Require Import rewrite.

Section tensor.
  Universes u.
  Context {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : set@{u}}.

  Local Ltac doit := let H1 := fresh "H" in let H2 := fresh "H" in
    intros H1 H2; hnf; repeat intros [??]; split; [apply H1 | apply H2].
  (*    repeat change (tensor_map2 (?f, ?g) ((?a, ?b), (?c, ?d))) with (f (a, c), g (b, d)); split; [apply H1 | apply H2].  *)


  Lemma tensor_map2_associative       {f₁      } {f₂      } : @Associative      X₁       f₁       → @Associative      X₂       f₂       → Associative (tensor_map2 (f₁, f₂)).  Proof. doit. Qed.
  Lemma tensor_map2_commutative       {f₁      } {f₂      } : @Commutative      X₁ Y₁    f₁       → @Commutative      X₂ Y₂    f₂       → Commutative (tensor_map2 (f₁, f₂)).  Proof. doit. Qed.
  Lemma tensor_map2_binary_idempotent {f₁      } {f₂      } : @BinaryIdempotent X₁       f₁       → @BinaryIdempotent X₂       f₂       → BinaryIdempotent (tensor_map2 (f₁, f₂)).  Proof. doit. Qed.
  (*Lemma tensor_map2_involutive        {f₁      } {f₂      } : @Involutive       X₁       f₁       → @Involutive       X₂       f₂       → Involutive (tensor_map f₁ f₂).  Proof. doit. Qed.*)
  Lemma tensor_map2_absorption        {f₁ g₁   } {f₂ g₂   } : @Absorption       X₁ Y₁ Z₁ f₁ g₁    → @Absorption       X₂ Y₂ Z₂ f₂ g₂    → Absorption (tensor_map2 (f₁, f₂)) (tensor_map2 (g₁, g₂)).  Proof. doit. Qed.
  Lemma tensor_map2_left_distribute   {f₁ g₁   } {f₂ g₂   } : @LeftDistribute   X₁       f₁ g₁    → @LeftDistribute   X₂       f₂ g₂    → LeftDistribute (tensor_map2 (f₁, f₂)) (tensor_map2 (g₁, g₂)).  Proof. doit. Qed.
  Lemma tensor_map2_right_distribute  {f₁ g₁   } {f₂ g₂   } : @RightDistribute  X₁       f₁ g₁    → @RightDistribute  X₂       f₂ g₂    → RightDistribute (tensor_map2 (f₁, f₂)) (tensor_map2 (g₁, g₂)).  Proof. doit. Qed.

  Lemma tensor_map2_left_identity     {f₁ x₁   } {f₂ x₂   } : @LeftIdentity     X₁ Y₁    f₁ x₁    → @LeftIdentity     X₂ Y₂    f₂ x₂    → LeftIdentity (tensor_map2 (f₁, f₂)) (x₁, x₂).  Proof. doit. Qed.
  Lemma tensor_map2_right_identity    {f₁ y₁   } {f₂ y₂   } : @RightIdentity    X₁ Y₁    f₁ y₁    → @RightIdentity    X₂ Y₂    f₂ y₂    → RightIdentity (tensor_map2 (f₁, f₂)) (y₁, y₂).  Proof. doit. Qed.
  Lemma tensor_map2_left_absorb       {f₁ x₁   } {f₂ x₂   } : @LeftAbsorb       X₁ Y₁    f₁ x₁    → @LeftAbsorb       X₂ Y₂    f₂ x₂    → LeftAbsorb (tensor_map2 (f₁, f₂)) (x₁, x₂).  Proof. doit. Qed.
  Lemma tensor_map2_right_absorb      {f₁ y₁   } {f₂ y₂   } : @RightAbsorb      X₁ Y₁    f₁ y₁    → @RightAbsorb      X₂ Y₂    f₂ y₂    → RightAbsorb (tensor_map2 (f₁, f₂)) (y₁, y₂).  Proof. doit. Qed.

  Lemma tensor_map2_left_inverse      {f₁ g₁ x₁} {f₂ g₂ x₂} : @LeftInverse      X₁ Y₁ Z₁ f₁ g₁ x₁ → @LeftInverse      X₂ Y₂ Z₂ f₂ g₂ x₂ → LeftInverse (tensor_map2 (f₁, f₂)) (tensor_map g₁ g₂) (x₁, x₂).  Proof. doit. Qed.
  Lemma tensor_map2_right_inverse     {f₁ g₁ x₁} {f₂ g₂ x₂} : @RightInverse     X₁ Y₁ Z₁ f₁ g₁ x₁ → @RightInverse     X₂ Y₂ Z₂ f₂ g₂ x₂ → RightInverse (tensor_map2 (f₁, f₂)) (tensor_map g₁ g₂) (x₁, x₂).  Proof. doit. Qed.
End tensor.

Global Hint Extern 2 (Associative (func_op tensor_map2 _)) => simple notypeclasses refine (tensor_map2_associative _ _) : typeclass_instances.
Global Hint Extern 2 (Commutative (func_op tensor_map2 _)) => simple notypeclasses refine (tensor_map2_commutative _ _) : typeclass_instances.
Global Hint Extern 2 (BinaryIdempotent (func_op tensor_map2 _)) => simple notypeclasses refine (tensor_map2_binary_idempotent _ _) : typeclass_instances.
(*Global Hint Extern 2 (Involutive (tensor_map _ _)) => simple notypeclasses refine (tensor_map2_involutive _ _) : typeclass_instances.*)
Global Hint Extern 2 (Absorption (func_op tensor_map2 _) _) => simple notypeclasses refine (tensor_map2_absorption _ _) : typeclass_instances.
Global Hint Extern 2 (LeftDistribute (func_op tensor_map2 _) _) => simple notypeclasses refine (tensor_map2_left_distribute _ _) : typeclass_instances.
Global Hint Extern 2 (RightDistribute (func_op tensor_map2 _) _) => simple notypeclasses refine (tensor_map2_right_distribute _ _) : typeclass_instances.

Global Hint Extern 2 (LeftIdentity (func_op tensor_map2 _) _) => simple notypeclasses refine (tensor_map2_left_identity _ _) : typeclass_instances.
Global Hint Extern 2 (RightIdentity (func_op tensor_map2 _) _) => simple notypeclasses refine (tensor_map2_right_identity _ _) : typeclass_instances.
Global Hint Extern 2 (LeftAbsorb (func_op tensor_map2 _) _) => simple notypeclasses refine (tensor_map2_left_absorb _ _) : typeclass_instances.
Global Hint Extern 2 (RightAbsorb (func_op tensor_map2 _) _) => simple notypeclasses refine (tensor_map2_right_absorb _ _) : typeclass_instances.

Global Hint Extern 2 (LeftInverse (func_op tensor_map2 _) _ _) => simple notypeclasses refine (tensor_map2_left_inverse _ _) : typeclass_instances.
Global Hint Extern 2 (RightInverse (func_op tensor_map2 _) _ _) => simple notypeclasses refine (tensor_map2_right_inverse _ _) : typeclass_instances.


Global Hint Extern 2 (MonUnit (_ ⊗ _)) => refine (mon_unit, mon_unit) : typeclass_instances.
Global Hint Extern 2 (Zero    (_ ⊗ _)) => refine (zero, zero    ) : typeclass_instances.
Global Hint Extern 2 (One     (_ ⊗ _)) => refine (one, one     ) : typeclass_instances.
Global Hint Extern 2 (Top     (_ ⊗ _)) => refine (top, top     ) : typeclass_instances.
Global Hint Extern 2 (Bottom  (_ ⊗ _)) => refine (bottom, bottom  ) : typeclass_instances.

Global Hint Extern 2 (SgOp   (_ ⊗ _)) => refine (tensor_map2 (sg_op, sg_op)) : typeclass_instances.
Global Hint Extern 2 (Inv    (_ ⊗ _)) => refine (tensor_map  inv inv) : typeclass_instances.
Global Hint Extern 2 (Plus   (_ ⊗ _)) => refine (tensor_map2 (plus, plus)) : typeclass_instances.
Global Hint Extern 2 (Mult   (_ ⊗ _)) => refine (tensor_map2 (mult, mult)) : typeclass_instances.
Global Hint Extern 2 (Negate (_ ⊗ _)) => refine (tensor_map negate negate) : typeclass_instances.
Global Hint Extern 2 (Meet   (_ ⊗ _)) => refine (tensor_map2 (meet, meet)) : typeclass_instances.
Global Hint Extern 2 (Join   (_ ⊗ _)) => refine (tensor_map2 (join, join)) : typeclass_instances.

Section tensor.
  Universes u.
  Context {X Y : set@{u}}.

  Local Ltac doit2 :=
    try exact _;
    try change (_ _ (tensor_map2 ?p)) with (tensor_map2 p);
    try change (_ _ (tensor_map ?f ?g)) with (tensor_map f g);
    try exact _.

  Local Instance tensor_semigroup     `{SemiGroup            (X:=X)} `{SemiGroup            (X:=Y)} : SemiGroup            (X ⊗ Y).  Proof. red. doit2. Qed.
  Local Instance tensor_com_semigroup `{CommutativeSemiGroup (X:=X)} `{CommutativeSemiGroup (X:=Y)} : CommutativeSemiGroup (X ⊗ Y).  Proof. split; doit2. Qed.
  Local Instance tensor_semilattice   `{SemiLattice          (X:=X)} `{SemiLattice          (X:=Y)} : SemiLattice          (X ⊗ Y).  Proof. split; doit2. Qed.
  Local Instance tensor_monoid        `{Monoid               (X:=X)} `{Monoid               (X:=Y)} : Monoid               (X ⊗ Y).  Proof. split; doit2. Qed.
  Local Instance tensor_com_monoid    `{CommutativeMonoid    (X:=X)} `{CommutativeMonoid    (X:=Y)} : CommutativeMonoid    (X ⊗ Y).  Proof. split; doit2. Qed.
  Local Instance tensor_bounded_sl    `{BoundedSemiLattice   (X:=X)} `{BoundedSemiLattice   (X:=Y)} : BoundedSemiLattice   (X ⊗ Y).  Proof. split; doit2. Qed.
  Local Instance tensor_group         `{Group                (X:=X)} `{Group                (X:=Y)} : Group                (X ⊗ Y).  Proof. split; doit2. Qed.
  Local Instance tensor_abgroup       `{AbGroup              (X:=X)} `{AbGroup              (X:=Y)} : AbGroup              (X ⊗ Y).  Proof. split; doit2. Qed.

  Local Instance tensor_meet_sl `{MeetSemiLattice (L:=X)} `{MeetSemiLattice (L:=Y)} : MeetSemiLattice (X ⊗ Y).  Proof. exact tensor_semilattice. Qed.
  Local Instance tensor_join_sl `{JoinSemiLattice (L:=X)} `{JoinSemiLattice (L:=Y)} : JoinSemiLattice (X ⊗ Y).  Proof. exact tensor_semilattice. Qed.
  Local Instance tensor_bounded_meet_sl `{BoundedMeetSemiLattice (L:=X)} `{BoundedMeetSemiLattice (L:=Y)} : BoundedMeetSemiLattice (X ⊗ Y).  Proof. exact tensor_bounded_sl. Qed.
  Local Instance tensor_bounded_join_sl `{BoundedJoinSemiLattice (L:=X)} `{BoundedJoinSemiLattice (L:=Y)} : BoundedJoinSemiLattice (X ⊗ Y).  Proof. exact tensor_bounded_sl. Qed.
  Local Instance tensor_lattice `{Lattice (L:=X)} `{Lattice (L:=Y)} : Lattice (X ⊗ Y).  Proof. split; doit2. Qed.
  Local Instance tensor_distr_lattice `{DistributiveLattice (L:=X)} `{DistributiveLattice (L:=Y)} : DistributiveLattice (X ⊗ Y).  Proof. split; doit2. Qed.

  Local Instance tensor_add_nc_sg  `{AdditiveNonComSemiGroup (R:=X)} `{AdditiveNonComSemiGroup (R:=Y)} : AdditiveNonComSemiGroup (X ⊗ Y).  Proof. exact tensor_semigroup. Qed.
  Local Instance tensor_add_nc_mon `{AdditiveNonComMonoid    (R:=X)} `{AdditiveNonComMonoid    (R:=Y)} : AdditiveNonComMonoid    (X ⊗ Y).  Proof. exact tensor_monoid. Qed.
  Local Instance tensor_add_mon    `{AdditiveMonoid          (R:=X)} `{AdditiveMonoid          (R:=Y)} : AdditiveMonoid          (X ⊗ Y).  Proof. exact tensor_com_monoid. Qed.
  Local Instance tensor_add_nc_grp `{AdditiveNonComGroup     (R:=X)} `{AdditiveNonComGroup     (R:=Y)} : AdditiveNonComGroup     (X ⊗ Y).  Proof. exact tensor_group. Qed.
  Local Instance tensor_add_grp    `{AdditiveGroup           (R:=X)} `{AdditiveGroup           (R:=Y)} : AdditiveGroup           (X ⊗ Y).  Proof. exact tensor_abgroup. Qed.

  Local Instance tensor_mult_sg      `{MultiplicativeSemiGroup (R:=X)} `{MultiplicativeSemiGroup (R:=Y)} : MultiplicativeSemiGroup (X ⊗ Y).  Proof. exact tensor_semigroup. Qed.
  Local Instance tensor_mult_mon     `{MultiplicativeMonoid    (R:=X)} `{MultiplicativeMonoid    (R:=Y)} : MultiplicativeMonoid    (X ⊗ Y).  Proof. exact tensor_monoid. Qed.
  Local Instance tensor_mult_com_mon `{MultiplicativeComMonoid (R:=X)} `{MultiplicativeComMonoid (R:=Y)} : MultiplicativeComMonoid (X ⊗ Y).  Proof. exact tensor_com_monoid. Qed.
End tensor.

Global Hint Extern 2 (SemiGroup (_ ⊗ _)) => simple notypeclasses refine tensor_semigroup : typeclass_instances.
Global Hint Extern 2 (CommutativeSemiGroup (_ ⊗ _)) => simple notypeclasses refine tensor_com_semigroup : typeclass_instances.
Global Hint Extern 2 (SemiLattice (_ ⊗ _)) => simple notypeclasses refine tensor_semilattice : typeclass_instances.
Global Hint Extern 2 (Monoid (_ ⊗ _)) => simple notypeclasses refine tensor_monoid : typeclass_instances.
Global Hint Extern 2 (CommutativeMonoid (_ ⊗ _)) => simple notypeclasses refine tensor_com_monoid : typeclass_instances.
Global Hint Extern 2 (BoundedSemiLattice (_ ⊗ _)) => simple notypeclasses refine tensor_bounded_sl : typeclass_instances.
Global Hint Extern 2 (Group (_ ⊗ _)) => simple notypeclasses refine tensor_group : typeclass_instances.
Global Hint Extern 2 (AbGroup (_ ⊗ _)) => simple notypeclasses refine tensor_abgroup : typeclass_instances.

Global Hint Extern 2 (MeetSemiLattice (_ ⊗ _)) => simple notypeclasses refine tensor_meet_sl : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice (_ ⊗ _)) => simple notypeclasses refine tensor_join_sl : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice (_ ⊗ _)) => simple notypeclasses refine tensor_bounded_meet_sl : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice (_ ⊗ _)) => simple notypeclasses refine tensor_bounded_join_sl : typeclass_instances.
Global Hint Extern 2 (Lattice (_ ⊗ _)) => simple notypeclasses refine tensor_lattice : typeclass_instances.
Global Hint Extern 2 (DistributiveLattice (_ ⊗ _)) => simple notypeclasses refine tensor_distr_lattice : typeclass_instances.

Global Hint Extern 2 (AdditiveNonComSemiGroup (_ ⊗ _)) => simple notypeclasses refine tensor_add_nc_sg : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComMonoid (_ ⊗ _)) => simple notypeclasses refine tensor_add_nc_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid (_ ⊗ _)) => simple notypeclasses refine tensor_add_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComGroup (_ ⊗ _)) => simple notypeclasses refine tensor_add_nc_grp : typeclass_instances.
Global Hint Extern 2 (AdditiveGroup (_ ⊗ _)) => simple notypeclasses refine tensor_add_grp : typeclass_instances.

Global Hint Extern 2 (MultiplicativeSemiGroup (_ ⊗ _)) => simple notypeclasses refine tensor_mult_sg : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid (_ ⊗ _)) => simple notypeclasses refine tensor_mult_mon : typeclass_instances.
Global Hint Extern 2 (MultiplicativeComMonoid (_ ⊗ _)) => simple notypeclasses refine tensor_mult_com_mon : typeclass_instances.


Section prod.
  Universes u.
  Context {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : set@{u}}.

  Local Ltac doit := let H1 := fresh "H" in let H2 := fresh "H" in
    intros H1 H2; hnf; repeat intros [??]; split; [apply H1 | apply H2].
  (*    repeat change (tensor_map2 (?f, ?g) ((?a, ?b), (?c, ?d))) with (f (a, c), g (b, d)); split; [apply H1 | apply H2].  *)


  Lemma prod_map2_associative       {f₁      } {f₂      } : @Associative      X₁       f₁       → @Associative      X₂       f₂       → Associative (prod_map2 (f₁, f₂)).  Proof. doit. Qed.
  Lemma prod_map2_commutative       {f₁      } {f₂      } : @Commutative      X₁ Y₁    f₁       → @Commutative      X₂ Y₂    f₂       → Commutative (prod_map2 (f₁, f₂)).  Proof. doit. Qed.
  Lemma prod_map2_binary_idempotent {f₁      } {f₂      } : @BinaryIdempotent X₁       f₁       → @BinaryIdempotent X₂       f₂       → BinaryIdempotent (prod_map2 (f₁, f₂)).  Proof. doit. Qed.
  (*Lemma prod_map2_involutive        {f₁      } {f₂      } : @Involutive       X₁       f₁       → @Involutive       X₂       f₂       → Involutive (prod_map (f₁, f₂)).  Proof. doit. Qed.*)
  Lemma prod_map2_absorption        {f₁ g₁   } {f₂ g₂   } : @Absorption       X₁ Y₁ Z₁ f₁ g₁    → @Absorption       X₂ Y₂ Z₂ f₂ g₂    → Absorption (prod_map2 (f₁, f₂)) (prod_map2 (g₁, g₂)).  Proof. doit. Qed.
  Lemma prod_map2_left_distribute   {f₁ g₁   } {f₂ g₂   } : @LeftDistribute   X₁       f₁ g₁    → @LeftDistribute   X₂       f₂ g₂    → LeftDistribute (prod_map2 (f₁, f₂)) (prod_map2 (g₁, g₂)).  Proof. doit. Qed.
  Lemma prod_map2_right_distribute  {f₁ g₁   } {f₂ g₂   } : @RightDistribute  X₁       f₁ g₁    → @RightDistribute  X₂       f₂ g₂    → RightDistribute (prod_map2 (f₁, f₂)) (prod_map2 (g₁, g₂)).  Proof. doit. Qed.

  Lemma prod_map2_left_identity     {f₁ x₁   } {f₂ x₂   } : @LeftIdentity     X₁ Y₁    f₁ x₁    → @LeftIdentity     X₂ Y₂    f₂ x₂    → LeftIdentity (prod_map2 (f₁, f₂)) (x₁, x₂).  Proof. doit. Qed.
  Lemma prod_map2_right_identity    {f₁ y₁   } {f₂ y₂   } : @RightIdentity    X₁ Y₁    f₁ y₁    → @RightIdentity    X₂ Y₂    f₂ y₂    → RightIdentity (prod_map2 (f₁, f₂)) (y₁, y₂).  Proof. doit. Qed.
  Lemma prod_map2_left_absorb       {f₁ x₁   } {f₂ x₂   } : @LeftAbsorb       X₁ Y₁    f₁ x₁    → @LeftAbsorb       X₂ Y₂    f₂ x₂    → LeftAbsorb (prod_map2 (f₁, f₂)) (x₁, x₂).  Proof. doit. Qed.
  Lemma prod_map2_right_absorb      {f₁ y₁   } {f₂ y₂   } : @RightAbsorb      X₁ Y₁    f₁ y₁    → @RightAbsorb      X₂ Y₂    f₂ y₂    → RightAbsorb (prod_map2 (f₁, f₂)) (y₁, y₂).  Proof. doit. Qed.

  Lemma prod_map2_left_inverse      {f₁ g₁ x₁} {f₂ g₂ x₂} : @LeftInverse      X₁ Y₁ Z₁ f₁ g₁ x₁ → @LeftInverse      X₂ Y₂ Z₂ f₂ g₂ x₂ → LeftInverse (prod_map2 (f₁, f₂)) (prod_map (g₁, g₂)) (x₁, x₂).  Proof. doit. Qed.
  Lemma prod_map2_right_inverse     {f₁ g₁ x₁} {f₂ g₂ x₂} : @RightInverse     X₁ Y₁ Z₁ f₁ g₁ x₁ → @RightInverse     X₂ Y₂ Z₂ f₂ g₂ x₂ → RightInverse (prod_map2 (f₁, f₂)) (prod_map (g₁, g₂)) (x₁, x₂).  Proof. doit. Qed.
End prod.

Global Hint Extern 2 (Associative (func_op prod_map2 _)) => simple notypeclasses refine (prod_map2_associative _ _) : typeclass_instances.
Global Hint Extern 2 (Commutative (func_op prod_map2 _)) => simple notypeclasses refine (prod_map2_commutative _ _) : typeclass_instances.
Global Hint Extern 2 (BinaryIdempotent (func_op prod_map2 _)) => simple notypeclasses refine (prod_map2_binary_idempotent _ _) : typeclass_instances.
(*Global Hint Extern 2 (Involutive (prod_map _)) => simple notypeclasses refine (prod_map2_involutive _ _) : typeclass_instances.*)
Global Hint Extern 2 (Absorption (func_op prod_map2 _) _) => simple notypeclasses refine (prod_map2_absorption _ _) : typeclass_instances.
Global Hint Extern 2 (LeftDistribute (func_op prod_map2 _) _) => simple notypeclasses refine (prod_map2_left_distribute _ _) : typeclass_instances.
Global Hint Extern 2 (RightDistribute (func_op prod_map2 _) _) => simple notypeclasses refine (prod_map2_right_distribute _ _) : typeclass_instances.

Global Hint Extern 2 (LeftIdentity (func_op prod_map2 _) _) => simple notypeclasses refine (prod_map2_left_identity _ _) : typeclass_instances.
Global Hint Extern 2 (RightIdentity (func_op prod_map2 _) _) => simple notypeclasses refine (prod_map2_right_identity _ _) : typeclass_instances.
Global Hint Extern 2 (LeftAbsorb (func_op prod_map2 _) _) => simple notypeclasses refine (prod_map2_left_absorb _ _) : typeclass_instances.
Global Hint Extern 2 (RightAbsorb (func_op prod_map2 _) _) => simple notypeclasses refine (prod_map2_right_absorb _ _) : typeclass_instances.

Global Hint Extern 2 (LeftInverse (func_op prod_map2 _) _ _) => simple notypeclasses refine (prod_map2_left_inverse _ _) : typeclass_instances.
Global Hint Extern 2 (RightInverse (func_op prod_map2 _) _ _) => simple notypeclasses refine (prod_map2_right_inverse _ _) : typeclass_instances.


Global Hint Extern 2 (MonUnit (_ × _)) => refine (mon_unit, mon_unit) : typeclass_instances.
Global Hint Extern 2 (Zero    (_ × _)) => refine (zero, zero    ) : typeclass_instances.
Global Hint Extern 2 (One     (_ × _)) => refine (one, one     ) : typeclass_instances.
Global Hint Extern 2 (Top     (_ × _)) => refine (top, top     ) : typeclass_instances.
Global Hint Extern 2 (Bottom  (_ × _)) => refine (bottom, bottom  ) : typeclass_instances.

Global Hint Extern 2 (SgOp   (_ × _)) => refine (prod_map2 (sg_op, sg_op)) : typeclass_instances.
Global Hint Extern 2 (Inv    (_ × _)) => refine (prod_map  (inv, inv)) : typeclass_instances.
Global Hint Extern 2 (Plus   (_ × _)) => refine (prod_map2 (plus, plus)) : typeclass_instances.
Global Hint Extern 2 (Mult   (_ × _)) => refine (prod_map2 (mult, mult)) : typeclass_instances.
Global Hint Extern 2 (Negate (_ × _)) => refine (prod_map (negate, negate)) : typeclass_instances.
Global Hint Extern 2 (Meet   (_ × _)) => refine (prod_map2 (meet, meet)) : typeclass_instances.
Global Hint Extern 2 (Join   (_ × _)) => refine (prod_map2 (join, join)) : typeclass_instances.

Section prod.
  Universes u.
  Context {X Y : set@{u}}.

  Local Ltac doit2 :=
    try exact _;
    try change (_ _ (prod_map2 ?p)) with (prod_map2 p);
    try change (_ _ (prod_map ?p)) with (prod_map p);
    try exact _.

  Local Instance prod_semigroup     `{SemiGroup            (X:=X)} `{SemiGroup            (X:=Y)} : SemiGroup            (X × Y).  Proof. red. doit2. Qed.
  Local Instance prod_com_semigroup `{CommutativeSemiGroup (X:=X)} `{CommutativeSemiGroup (X:=Y)} : CommutativeSemiGroup (X × Y).  Proof. split; doit2. Qed.
  Local Instance prod_semilattice   `{SemiLattice          (X:=X)} `{SemiLattice          (X:=Y)} : SemiLattice          (X × Y).  Proof. split; doit2. Qed.
  Local Instance prod_monoid        `{Monoid               (X:=X)} `{Monoid               (X:=Y)} : Monoid               (X × Y).  Proof. split; doit2. Qed.
  Local Instance prod_com_monoid    `{CommutativeMonoid    (X:=X)} `{CommutativeMonoid    (X:=Y)} : CommutativeMonoid    (X × Y).  Proof. split; doit2. Qed.
  Local Instance prod_bounded_sl    `{BoundedSemiLattice   (X:=X)} `{BoundedSemiLattice   (X:=Y)} : BoundedSemiLattice   (X × Y).  Proof. split; doit2. Qed.
  Local Instance prod_group         `{Group                (X:=X)} `{Group                (X:=Y)} : Group                (X × Y).  Proof. split; doit2. Qed.
  Local Instance prod_abgroup       `{AbGroup              (X:=X)} `{AbGroup              (X:=Y)} : AbGroup              (X × Y).  Proof. split; doit2. Qed.

  Local Instance prod_meet_sl `{MeetSemiLattice (L:=X)} `{MeetSemiLattice (L:=Y)} : MeetSemiLattice (X × Y).  Proof. exact prod_semilattice. Qed.
  Local Instance prod_join_sl `{JoinSemiLattice (L:=X)} `{JoinSemiLattice (L:=Y)} : JoinSemiLattice (X × Y).  Proof. exact prod_semilattice. Qed.
  Local Instance prod_bounded_meet_sl `{BoundedMeetSemiLattice (L:=X)} `{BoundedMeetSemiLattice (L:=Y)} : BoundedMeetSemiLattice (X × Y).  Proof. exact prod_bounded_sl. Qed.
  Local Instance prod_bounded_join_sl `{BoundedJoinSemiLattice (L:=X)} `{BoundedJoinSemiLattice (L:=Y)} : BoundedJoinSemiLattice (X × Y).  Proof. exact prod_bounded_sl. Qed.
  Local Instance prod_lattice `{Lattice (L:=X)} `{Lattice (L:=Y)} : Lattice (X × Y).  Proof. split; doit2. Qed.
  Local Instance prod_distr_lattice `{DistributiveLattice (L:=X)} `{DistributiveLattice (L:=Y)} : DistributiveLattice (X × Y).  Proof. split; doit2. Qed.

  Local Instance prod_add_nc_mon `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveNonComMonoid (X × Y).  Proof. exact prod_monoid. Qed.
  Local Instance prod_add_mon    `{AdditiveMonoid       (R:=X)} `{AdditiveMonoid       (R:=Y)} : AdditiveMonoid       (X × Y).  Proof. exact prod_com_monoid. Qed.
  Local Instance prod_add_nc_grp `{AdditiveNonComGroup  (R:=X)} `{AdditiveNonComGroup  (R:=Y)} : AdditiveNonComGroup  (X × Y).  Proof. exact prod_group. Qed.
  Local Instance prod_add_grp    `{AdditiveGroup        (R:=X)} `{AdditiveGroup        (R:=Y)} : AdditiveGroup        (X × Y).  Proof. exact prod_abgroup. Qed.

  Local Instance prod_mult_sg      `{MultiplicativeSemiGroup (R:=X)} `{MultiplicativeSemiGroup (R:=Y)} : MultiplicativeSemiGroup (X × Y).  Proof. exact prod_semigroup. Qed.
  Local Instance prod_mult_mon     `{MultiplicativeMonoid    (R:=X)} `{MultiplicativeMonoid    (R:=Y)} : MultiplicativeMonoid    (X × Y).  Proof. exact prod_monoid. Qed.
  Local Instance prod_mult_com_mon `{MultiplicativeComMonoid (R:=X)} `{MultiplicativeComMonoid (R:=Y)} : MultiplicativeComMonoid (X × Y).  Proof. exact prod_com_monoid. Qed.
End prod.

Global Hint Extern 2 (SemiGroup (_ × _)) => simple notypeclasses refine prod_semigroup : typeclass_instances.
Global Hint Extern 2 (CommutativeSemiGroup (_ × _)) => simple notypeclasses refine prod_com_semigroup : typeclass_instances.
Global Hint Extern 2 (SemiLattice (_ × _)) => simple notypeclasses refine prod_semilattice : typeclass_instances.
Global Hint Extern 2 (Monoid (_ × _)) => simple notypeclasses refine prod_monoid : typeclass_instances.
Global Hint Extern 2 (CommutativeMonoid (_ × _)) => simple notypeclasses refine prod_com_monoid : typeclass_instances.
Global Hint Extern 2 (BoundedSemiLattice (_ × _)) => simple notypeclasses refine prod_bounded_sl : typeclass_instances.
Global Hint Extern 2 (Group (_ × _)) => simple notypeclasses refine prod_group : typeclass_instances.
Global Hint Extern 2 (AbGroup (_ × _)) => simple notypeclasses refine prod_abgroup : typeclass_instances.

Global Hint Extern 2 (MeetSemiLattice (_ × _)) => simple notypeclasses refine prod_meet_sl : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice (_ × _)) => simple notypeclasses refine prod_join_sl : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice (_ × _)) => simple notypeclasses refine prod_bounded_meet_sl : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice (_ × _)) => simple notypeclasses refine prod_bounded_join_sl : typeclass_instances.
Global Hint Extern 2 (Lattice (_ × _)) => simple notypeclasses refine prod_lattice : typeclass_instances.
Global Hint Extern 2 (DistributiveLattice (_ × _)) => simple notypeclasses refine prod_distr_lattice : typeclass_instances.

Global Hint Extern 2 (AdditiveNonComMonoid (_ × _)) => simple notypeclasses refine prod_add_nc_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid (_ × _)) => simple notypeclasses refine prod_add_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComGroup (_ × _)) => simple notypeclasses refine prod_add_nc_grp : typeclass_instances.
Global Hint Extern 2 (AdditiveGroup (_ × _)) => simple notypeclasses refine prod_add_grp : typeclass_instances.

Global Hint Extern 2 (MultiplicativeSemiGroup (_ × _)) => simple notypeclasses refine prod_mult_sg : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid (_ × _)) => simple notypeclasses refine prod_mult_mon : typeclass_instances.
Global Hint Extern 2 (MultiplicativeComMonoid (_ × _)) => simple notypeclasses refine prod_mult_com_mon : typeclass_instances.


(** [X ⊗ Y ⇾ X × Y] *)

Section tensor_to_prod.
  Universes u.
  Context {X Y : set@{u}}.

  Definition tensor_to_prod_pointed {x y} : @Pointed_Morphism (X ⊗ Y) (X × Y) (x, y) (x, y) (tensor_to_prod X Y) := reflexivity (=) _.

  Definition tensor_to_prod_mon_unit_pointed `{MonUnit X} `{MonUnit Y} : MonUnit_Pointed_Morphism (tensor_to_prod X Y) := tensor_to_prod_pointed.
  Definition tensor_to_prod_top_pointed `{Top X} `{Top Y} : Top_Pointed_Morphism (tensor_to_prod X Y) := tensor_to_prod_pointed.
  Definition tensor_to_prod_bottom_pointed `{Bottom X} `{Bottom Y} : Bottom_Pointed_Morphism (tensor_to_prod X Y) := tensor_to_prod_pointed.
  Definition tensor_to_prod_zero_pointed `{Zero X} `{Zero Y} : Zero_Pointed_Morphism (tensor_to_prod X Y) := tensor_to_prod_pointed.
  Definition tensor_to_prod_one_pointed `{One X} `{One Y} : One_Pointed_Morphism (tensor_to_prod X Y) := tensor_to_prod_pointed.

  Lemma tensor_to_prod_sg_mor `{SemiGroup (X:=X)} `{SemiGroup (X:=Y)} : SemiGroup_Morphism (tensor_to_prod X Y).
  Proof. split; try exact _. now intros x y. Qed.

  Lemma tensor_to_prod_mon_mor `{Monoid (X:=X)} `{Monoid (X:=Y)} : Monoid_Morphism (tensor_to_prod X Y).
  Proof. now split. Qed.

  Definition tensor_to_prod_add_sg_mor `{AdditiveNonComSemiGroup (R:=X)} `{AdditiveNonComSemiGroup (R:=Y)} : AdditiveSemiGroup_Morphism (tensor_to_prod X Y) := tensor_to_prod_sg_mor.
  Definition tensor_to_prod_add_mon_mor `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveMonoid_Morphism (tensor_to_prod X Y) := tensor_to_prod_mon_mor.
End tensor_to_prod.

Global Hint Extern 2 (Pointed_Morphism _ _ (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_pointed : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_mon_unit_pointed : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_top_pointed : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_zero_pointed : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_one_pointed : typeclass_instances.
Global Hint Extern 2 (SemiGroup_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_sg_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_add_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_add_mon_mor : typeclass_instances.

(** Tensor map *)

Section tensor_map.
  Universes u.
  Context {X₁ Y₁ X₂ Y₂ : set@{u}}.

  Local Instance tensor_map_pointed `{H1:@Pointed_Morphism X₁ Y₁ x₁ y₁ f₁} `{H2:@Pointed_Morphism X₂ Y₂ x₂ y₂ f₂} : Pointed_Morphism (x₁, x₂) (y₁, y₂) (tensor_map f₁ f₂).
  Proof. split; [ apply H1 | apply H2 ]. Qed.

  Context {f : X₁ ⇾ Y₁} {g : X₂ ⇾ Y₂}.

  Local Instance tensor_map_mon_unit_pointed `{MonUnit_Pointed_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{MonUnit_Pointed_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : MonUnit_Pointed_Morphism (tensor_map f g) := tensor_map_pointed.
  Local Instance tensor_map_top_pointed `{Top_Pointed_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{Top_Pointed_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : Top_Pointed_Morphism (tensor_map f g) := tensor_map_pointed.
  Local Instance tensor_map_bottom_pointed `{Bottom_Pointed_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{Bottom_Pointed_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : Bottom_Pointed_Morphism (tensor_map f g) := tensor_map_pointed.
  Local Instance tensor_map_zero_pointed `{Zero_Pointed_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{Zero_Pointed_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : Zero_Pointed_Morphism (tensor_map f g) := tensor_map_pointed.
  Local Instance tensor_map_one_pointed `{One_Pointed_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{One_Pointed_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : One_Pointed_Morphism (tensor_map f g) := tensor_map_pointed.

  Local Instance tensor_map_sg_mor `{H1:SemiGroup_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{H2:SemiGroup_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : SemiGroup_Morphism (tensor_map f g).
  Proof. split; try exact _. intros [a b][c d]. split; [ apply H1 | apply H2 ]. Qed.

  Local Instance tensor_map_mon_mor `{H1:Monoid_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{H2:Monoid_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : Monoid_Morphism (tensor_map f g).
  Proof. now split. Qed.

  Local Instance tensor_map_add_sg_mor `{H1:AdditiveSemiGroup_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{H2:AdditiveSemiGroup_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : AdditiveSemiGroup_Morphism (tensor_map f g) := tensor_map_sg_mor.
  Local Instance tensor_map_add_mon_mor `{H1:AdditiveMonoid_Morphism (X:=X₁) (Y:=Y₁) (f:=f)} `{H2:AdditiveMonoid_Morphism (X:=X₂) (Y:=Y₂) (f:=g)} : AdditiveMonoid_Morphism (tensor_map f g) := tensor_map_mon_mor.
End tensor_map.

Global Hint Extern 2 (Pointed_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_pointed : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_mon_unit_pointed : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_top_pointed : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_zero_pointed : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_one_pointed : typeclass_instances.
Global Hint Extern 2 (SemiGroup_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_sg_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_add_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (tensor_map _ _)) => simple notypeclasses refine tensor_map_add_mon_mor : typeclass_instances.


(** Projections *)

Section prod_proj.
  Universes u.
  Context {X Y : set@{u}}.

  Local Instance prod_proj1_pointed {x y} : @Pointed_Morphism (X × Y) _ (x, y) x (prod_proj1 X Y) := reflexivity (=) x.
  Local Instance prod_proj2_pointed {x y} : @Pointed_Morphism (X × Y) _ (x, y) y (prod_proj2 X Y) := reflexivity (=) y.

  Local Instance prod_proj1_mon_unit_pointed `{MonUnit X} `{MonUnit Y} : MonUnit_Pointed_Morphism (prod_proj1 X Y) := prod_proj1_pointed.
  Local Instance prod_proj1_top_pointed `{Top X} `{Top Y} : Top_Pointed_Morphism (prod_proj1 X Y) := prod_proj1_pointed.
  Local Instance prod_proj1_bottom_pointed `{Bottom X} `{Bottom Y} : Bottom_Pointed_Morphism (prod_proj1 X Y) := prod_proj1_pointed.
  Local Instance prod_proj1_zero_pointed `{Zero X} `{Zero Y} : Zero_Pointed_Morphism (prod_proj1 X Y) := prod_proj1_pointed.
  Local Instance prod_proj1_one_pointed `{One X} `{One Y} : One_Pointed_Morphism (prod_proj1 X Y) := prod_proj1_pointed.
  Local Instance prod_proj2_mon_unit_pointed `{MonUnit X} `{MonUnit Y} : MonUnit_Pointed_Morphism (prod_proj2 X Y) := prod_proj2_pointed.
  Local Instance prod_proj2_top_pointed `{Top X} `{Top Y} : Top_Pointed_Morphism (prod_proj2 X Y) := prod_proj2_pointed.
  Local Instance prod_proj2_bottom_pointed `{Bottom X} `{Bottom Y} : Bottom_Pointed_Morphism (prod_proj2 X Y) := prod_proj2_pointed.
  Local Instance prod_proj2_zero_pointed `{Zero X} `{Zero Y} : Zero_Pointed_Morphism (prod_proj2 X Y) := prod_proj2_pointed.
  Local Instance prod_proj2_one_pointed `{One X} `{One Y} : One_Pointed_Morphism (prod_proj2 X Y) := prod_proj2_pointed.

  Local Instance prod_proj1_sg_mor `{SemiGroup (X:=X)} `{SemiGroup (X:=Y)} : SemiGroup_Morphism (prod_proj1 X Y).
  Proof. split; try exact _. now intros x y. Qed.

  Local Instance prod_proj2_sg_mor `{SemiGroup (X:=X)} `{SemiGroup (X:=Y)} : SemiGroup_Morphism (prod_proj2 X Y).
  Proof. split; try exact _. now intros x y. Qed.

  Local Instance prod_proj1_mon_mor `{Monoid (X:=X)} `{Monoid (X:=Y)} : Monoid_Morphism (prod_proj1 X Y).
  Proof. now split. Qed.

  Local Instance prod_proj2_mon_mor `{Monoid (X:=X)} `{Monoid (X:=Y)} : Monoid_Morphism (prod_proj2 X Y).
  Proof. now split. Qed.

  Local Instance prod_proj1_add_sg_mor `{AdditiveNonComSemiGroup (R:=X)} `{AdditiveNonComSemiGroup (R:=Y)} : AdditiveSemiGroup_Morphism (prod_proj1 X Y) := prod_proj1_sg_mor.
  Local Instance prod_proj2_add_sg_mor `{AdditiveNonComSemiGroup (R:=X)} `{AdditiveNonComSemiGroup (R:=Y)} : AdditiveSemiGroup_Morphism (prod_proj2 X Y) := prod_proj2_sg_mor.
  Local Instance prod_proj1_add_mon_mor `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveMonoid_Morphism (prod_proj1 X Y) := prod_proj1_mon_mor.
  Local Instance prod_proj2_add_mon_mor `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveMonoid_Morphism (prod_proj2 X Y) := prod_proj2_mon_mor.
End prod_proj.

Global Hint Extern 2 (Pointed_Morphism _ _ (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_pointed : typeclass_instances.
Global Hint Extern 2 (Pointed_Morphism _ _ (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_pointed : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_mon_unit_pointed : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_top_pointed : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_zero_pointed : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_one_pointed : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_mon_unit_pointed : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_top_pointed : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_zero_pointed : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_one_pointed : typeclass_instances.
Global Hint Extern 2 (SemiGroup_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_sg_mor : typeclass_instances.
Global Hint Extern 2 (SemiGroup_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_sg_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_mon_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_add_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_add_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (prod_proj1 _ _)) => simple notypeclasses refine prod_proj1_add_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (prod_proj2 _ _)) => simple notypeclasses refine prod_proj2_add_mon_mor : typeclass_instances.


(** Projections *)

Section tensor_proj.
  Universes u.
  Context {X Y : set@{u}}.

  Local Instance tensor_proj1_pointed {x y} : Pointed_Morphism (x, y) x (tensor_proj1 X Y) := reflexivity (=) x.
  Local Instance tensor_proj2_pointed {x y} : Pointed_Morphism (x, y) y (tensor_proj2 X Y) := reflexivity (=) y.

  Local Instance tensor_proj1_mon_unit_pointed `{MonUnit X} `{MonUnit Y} : MonUnit_Pointed_Morphism (tensor_proj1 X Y) := tensor_proj1_pointed.
  Local Instance tensor_proj1_top_pointed `{Top X} `{Top Y} : Top_Pointed_Morphism (tensor_proj1 X Y) := tensor_proj1_pointed.
  Local Instance tensor_proj1_bottom_pointed `{Bottom X} `{Bottom Y} : Bottom_Pointed_Morphism (tensor_proj1 X Y) := tensor_proj1_pointed.
  Local Instance tensor_proj1_zero_pointed `{Zero X} `{Zero Y} : Zero_Pointed_Morphism (tensor_proj1 X Y) := tensor_proj1_pointed.
  Local Instance tensor_proj1_one_pointed `{One X} `{One Y} : One_Pointed_Morphism (tensor_proj1 X Y) := tensor_proj1_pointed.
  Local Instance tensor_proj2_mon_unit_pointed `{MonUnit X} `{MonUnit Y} : MonUnit_Pointed_Morphism (tensor_proj2 X Y) := tensor_proj2_pointed.
  Local Instance tensor_proj2_top_pointed `{Top X} `{Top Y} : Top_Pointed_Morphism (tensor_proj2 X Y) := tensor_proj2_pointed.
  Local Instance tensor_proj2_bottom_pointed `{Bottom X} `{Bottom Y} : Bottom_Pointed_Morphism (tensor_proj2 X Y) := tensor_proj2_pointed.
  Local Instance tensor_proj2_zero_pointed `{Zero X} `{Zero Y} : Zero_Pointed_Morphism (tensor_proj2 X Y) := tensor_proj2_pointed.
  Local Instance tensor_proj2_one_pointed `{One X} `{One Y} : One_Pointed_Morphism (tensor_proj2 X Y) := tensor_proj2_pointed.

  Local Instance tensor_proj1_sg_mor `{SemiGroup (X:=X)} `{SemiGroup (X:=Y)} : SemiGroup_Morphism (tensor_proj1 X Y).
  Proof. now change (tensor_proj1 X Y) with (prod_proj1 X Y ∘ tensor_to_prod X Y). Qed.

  Local Instance tensor_proj2_sg_mor `{SemiGroup (X:=X)} `{SemiGroup (X:=Y)} : SemiGroup_Morphism (tensor_proj2 X Y).
  Proof. now change (tensor_proj1 X Y) with (prod_proj1 X Y ∘ tensor_to_prod X Y). Qed.

  Local Instance tensor_proj1_mon_mor `{Monoid (X:=X)} `{Monoid (X:=Y)} : Monoid_Morphism (tensor_proj1 X Y).
  Proof. now change (tensor_proj1 X Y) with (prod_proj1 X Y ∘ tensor_to_prod X Y). Qed.

  Local Instance tensor_proj2_mon_mor `{Monoid (X:=X)} `{Monoid (X:=Y)} : Monoid_Morphism (tensor_proj2 X Y).
  Proof. now change (tensor_proj1 X Y) with (prod_proj1 X Y ∘ tensor_to_prod X Y). Qed.

  Local Instance tensor_proj1_add_sg_mor `{AdditiveNonComSemiGroup (R:=X)} `{AdditiveNonComSemiGroup (R:=Y)} : AdditiveSemiGroup_Morphism (tensor_proj1 X Y) := tensor_proj1_sg_mor.
  Local Instance tensor_proj2_add_sg_mor `{AdditiveNonComSemiGroup (R:=X)} `{AdditiveNonComSemiGroup (R:=Y)} : AdditiveSemiGroup_Morphism (tensor_proj2 X Y) := tensor_proj2_sg_mor.
  Local Instance tensor_proj1_add_mon_mor `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveMonoid_Morphism (tensor_proj1 X Y) := tensor_proj1_mon_mor.
  Local Instance tensor_proj2_add_mon_mor `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveMonoid_Morphism (tensor_proj2 X Y) := tensor_proj2_mon_mor.
End tensor_proj.

Global Hint Extern 2 (Pointed_Morphism _ _ (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_pointed : typeclass_instances.
Global Hint Extern 2 (Pointed_Morphism _ _ (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_pointed : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_mon_unit_pointed : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_top_pointed : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_zero_pointed : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_one_pointed : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_mon_unit_pointed : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_top_pointed : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_zero_pointed : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_one_pointed : typeclass_instances.
Global Hint Extern 2 (SemiGroup_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_sg_mor : typeclass_instances.
Global Hint Extern 2 (SemiGroup_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_sg_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_mon_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_add_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_add_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (tensor_proj1 _ _)) => simple notypeclasses refine tensor_proj1_add_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (tensor_proj2 _ _)) => simple notypeclasses refine tensor_proj2_add_mon_mor : typeclass_instances.


(** Injections *)

Section monoid_injections.
  Universes i.
  Context (X Y : set@{i}) `{MonUnit X} `{MonUnit Y}.

  Definition mon_inl := set:(λ x:X, (x, @mon_unit Y _)).
  Definition mon_inr := set:(λ y:Y, (@mon_unit X _, y)).

  Definition mon_inl_pointed : MonUnit_Pointed_Morphism mon_inl := reflexivity (=) _.
  Definition mon_inr_pointed : MonUnit_Pointed_Morphism mon_inr := reflexivity (=) _.
End monoid_injections.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (mon_inl _ _)) => simple notypeclasses refine (mon_inl_pointed _ _) : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (mon_inr _ _)) => simple notypeclasses refine (mon_inr_pointed _ _) : typeclass_instances.

Section mon_injection_morphisms.
  Universes u.
  Context {X Y : set@{u}}.

  Local Instance mon_inl_sg_mor `{SemiGroup (X:=X)} `{Monoid (X:=Y)} : SemiGroup_Morphism (mon_inl X Y).
  Proof. split; try exact _. intros x y.
    change (sg_op (x, y) = sg_op (x, y) ⊠ @mon_unit Y _ = sg_op (@mon_unit Y _, @mon_unit Y _)).
    split; [ easy | now rew (left_identity sg_op _) ].
  Qed.

  Local Instance mon_inr_sg_mor `{Monoid (X:=X)} `{SemiGroup (X:=Y)} : SemiGroup_Morphism (mon_inr X Y).
  Proof. split; try exact _. intros x y.
    change (@mon_unit X _ = sg_op (@mon_unit X _, @mon_unit X _) ⊠ sg_op (x, y) = sg_op (x, y)).
    split; [ now rew (left_identity sg_op _) | easy ].
  Qed.

  Local Instance mon_inl_mon_mor `{Monoid (X:=X)} `{Monoid (X:=Y)} : Monoid_Morphism (mon_inl X Y).
  Proof. now split. Qed.

  Local Instance mon_inr_mon_mor `{Monoid (X:=X)} `{Monoid (X:=Y)} : Monoid_Morphism (mon_inr X Y).
  Proof. now split. Qed.
End mon_injection_morphisms.

Global Hint Extern 2 (SemiGroup_Morphism (mon_inl _ _)) => simple notypeclasses refine mon_inl_sg_mor : typeclass_instances.
Global Hint Extern 2 (SemiGroup_Morphism (mon_inr _ _)) => simple notypeclasses refine mon_inr_sg_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (mon_inl _ _)) => simple notypeclasses refine mon_inl_mon_mor : typeclass_instances.
Global Hint Extern 2 (Monoid_Morphism (mon_inr _ _)) => simple notypeclasses refine mon_inr_mon_mor : typeclass_instances.


Section add_mon_injections.
  Universes i.
  Context (X Y : set@{i}) `{Zero X} `{Zero Y}.

  Definition add_mon_inl := set:(λ x:X, (x, @zero Y _)).
  Definition add_mon_inr := set:(λ y:Y, (@zero X _, y)).
End add_mon_injections.

Section add_mon_injection_morphisms.
  Universes u.
  Context {X Y : set@{u}}.

  Local Instance add_mon_inl_pointed `{Zero X} `{Zero Y} : Zero_Pointed_Morphism (add_mon_inl X Y) := mon_inl_pointed _ _.
  Local Instance add_mon_inr_pointed `{Zero X} `{Zero Y} : Zero_Pointed_Morphism (add_mon_inr X Y) := mon_inr_pointed _ _.
  Local Instance add_mon_inl_sg_mor `{AdditiveNonComSemiGroup (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveSemiGroup_Morphism (add_mon_inl X Y) := mon_inl_sg_mor.
  Local Instance add_mon_inr_sg_mor `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComSemiGroup (R:=Y)} : AdditiveSemiGroup_Morphism (add_mon_inr X Y) := mon_inr_sg_mor.
  Local Instance add_mon_inl_mon_mor `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveMonoid_Morphism (add_mon_inl X Y) := mon_inl_mon_mor.
  Local Instance add_mon_inr_mon_mor `{AdditiveNonComMonoid (R:=X)} `{AdditiveNonComMonoid (R:=Y)} : AdditiveMonoid_Morphism (add_mon_inr X Y) := mon_inr_mon_mor.
End add_mon_injection_morphisms.

Global Hint Extern 2 (Zero_Pointed_Morphism (add_mon_inl _ _)) => simple notypeclasses refine add_mon_inl_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (add_mon_inr _ _)) => simple notypeclasses refine add_mon_inr_pointed : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (add_mon_inl _ _)) => simple notypeclasses refine add_mon_inl_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (add_mon_inr _ _)) => simple notypeclasses refine add_mon_inr_sg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (add_mon_inl _ _)) => simple notypeclasses refine add_mon_inl_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (add_mon_inr _ _)) => simple notypeclasses refine add_mon_inr_mon_mor : typeclass_instances.
