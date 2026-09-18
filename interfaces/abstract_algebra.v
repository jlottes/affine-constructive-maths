Require Export theory.set interfaces.common_props algebra_notation.
Require Import set_lambda.

Section groups.
  Local Open Scope sg_op_scope.
  Local Abbreviation e := mon_unit.

  Context (X:set) {op:SgOp X} {unit:MonUnit X} {inv:Inv X}.

  SubClass SemiGroup := @Associative X (∙).
  Existing Class SemiGroup.

  Record CommutativeSemiGroup : SProp :=
  { #[reversible=no] comsg_sg :> SemiGroup
  ; #[reversible=no] comsg_com :> Commutative (X:=X) (∙)
  }.
  Existing Class CommutativeSemiGroup.

  Record SemiLattice : SProp :=
  { #[reversible=no] semilattice_sg :> CommutativeSemiGroup
  ; #[reversible=no] semilattice_idempotent :> @BinaryIdempotent X (∙)
  }.
  Existing Class SemiLattice.

  Record Monoid : SProp :=
  { #[reversible=no] monoid_semigroup   :> SemiGroup
  ; #[reversible=no] monoid_left_id     :> LeftIdentity  (X:=X) (∙) e
  ; #[reversible=no] monoid_right_id    :> RightIdentity (X:=X) (∙) e
  }.
  Existing Class Monoid.

  Record CommutativeMonoid : SProp :=
  { #[reversible=no] commonoid_monoid  :> Monoid
  ; #[reversible=no] commonoid_com :> Commutative (X:=X) (∙)
  }.
  Existing Class CommutativeMonoid.

  Record BoundedSemiLattice : SProp :=
  { #[reversible=no] bounded_semilattice_sl :> SemiLattice
  ; #[reversible=no] bounded_semilattice_common :> CommutativeMonoid
  }.
  Existing Class BoundedSemiLattice.

  Record StarSemiGroup : SProp :=
  { #[reversible=no] star_sg_sg :> SemiGroup
  ; #[reversible=no] inv_involutive :> Involutive (X:=X) inv
  ; #[reversible=no] inv_anti_distr :> AntiDistribute inv (∙)
  }.
  Existing Class StarSemiGroup.
  
  Record StarMonoid : SProp :=
  { #[reversible=no] star_mon_star_sg :> StarSemiGroup
  ; #[reversible=no] star_mon_mon :> Monoid
  }.
  Existing Class StarMonoid.

  Local Open Scope grp_scope.
  Record Group : SProp :=
  { #[reversible=no] group_monoid :> Monoid
  ; #[reversible=no] inverse_l :> LeftInverse  (X:=X) (∙) (⁻¹) e
  ; #[reversible=no] inverse_r :> RightInverse (X:=X) (∙) (⁻¹) e
  }.
  Existing Class Group.

  Record AbGroup : SProp :=
  { #[reversible=no] abgroup_group :> Group
  ; #[reversible=no] abgroup_com :> Commutative (X:=X) (∙)
  }.
  Existing Class AbGroup.
End groups.
Arguments monoid_left_id {X _ _ _} _.
Arguments monoid_right_id {X _ _ _} _.
Arguments inv_involutive {X _ _ _} _.
Arguments inv_anti_distr {X _ _ _} _ _.
Arguments inverse_l {X _ _ _ _} _.
Arguments inverse_r {X _ _ _ _} _.
Global Hint Extern 2 (Associative (X:=?X) sg_op) => change (SemiGroup X) : typeclass_instances.
Global Hint Extern 2 (LeftIdentity sg_op _) => simple notypeclasses refine monoid_left_id : typeclass_instances.
Global Hint Extern 2 (RightIdentity sg_op _) => simple notypeclasses refine monoid_right_id : typeclass_instances.
Global Hint Extern 2 (Involutive inv) => simple notypeclasses refine inv_involutive : typeclass_instances.
Global Hint Extern 2 (AntiDistribute inv sg_op) => simple notypeclasses refine inv_anti_distr : typeclass_instances.

Section strong_groups.
  Local Open Scope sg_op_scope.
  Context (X:set) {op:SgOp X} {unit:MonUnit X} {inv:Inv X}.

  Record StrongOpSemiGroup : SProp :=
  { #[reversible=no] strong_op_sg_sg :> SemiGroup X
  ; #[reversible=no] strong_sg_op :> StrongOp (X:=X) (∙)
  }.
  Existing Class StrongOpSemiGroup.

  Record StrongOpMonoid : SProp :=
  { #[reversible=no] strong_op_mon_mon :> Monoid X
  ; #[reversible=no] strong_op_mon_str :> StrongOp (X:=X) (∙)
  }.
  Existing Class StrongOpMonoid.
End strong_groups.
Arguments strong_sg_op {X _ _}.
Global Hint Extern 2 (StrongOp sg_op) => simple notypeclasses refine strong_sg_op : typeclass_instances.

Section lattices.
  Context (L:set) `{Meet L} `{Join L} `{Top L} `{Bottom L}.
  Definition MeetSemiLattice := SemiLattice (MeetSemigroupOps L).
  Definition BoundedMeetSemiLattice := BoundedSemiLattice (MeetSemigroupOps L).
  Definition JoinSemiLattice := SemiLattice (JoinSemigroupOps L).
  Definition BoundedJoinSemiLattice := BoundedSemiLattice (JoinSemigroupOps L).
  Existing Class MeetSemiLattice.
  Existing Class JoinSemiLattice.
  Existing Class BoundedMeetSemiLattice.
  Existing Class BoundedJoinSemiLattice.

  Record Lattice : SProp := 
  { #[reversible=no] lattice_join :> JoinSemiLattice
  ; #[reversible=no] lattice_meet :> MeetSemiLattice
  ; join_meet_absorption : Absorption (X:=L) (⊔) (⊓)
  ; meet_join_absorption : Absorption (X:=L) (⊓) (⊔)
  }.
  Existing Class Lattice.

  Record DistributiveLattice : SProp :=
  { #[reversible=no] distr_lattice_lattice :> Lattice
  ; join_meet_distr_l : LeftDistribute (X:=L) (⊔) (⊓)
  ; meet_join_distr_l : LeftDistribute (X:=L) (⊓) (⊔)
  }.
  Existing Class DistributiveLattice.

  Record BoundedLattice : SProp :=
  { #[reversible=no] bounded_lattice_lattice :> Lattice
  ; #[reversible=no] bounded_lattice_meet :> BoundedMeetSemiLattice
  ; #[reversible=no] bounded_lattice_join :> BoundedJoinSemiLattice
  }.
  Existing Class BoundedLattice.

  Record BoundedDistributiveLattice : SProp :=
  { #[reversible=no] bounded_distr_lattice_distr :> DistributiveLattice
  ; #[reversible=no] bounded_distr_lattice_bounded :> BoundedLattice
  }.
  Existing Class BoundedDistributiveLattice.
End lattices.
Arguments meet_join_absorption {L _ _ _} _ _.
Arguments join_meet_absorption {L _ _ _} _ _.
Arguments join_meet_distr_l {L _ _ _} _ _ _.
Arguments meet_join_distr_l {L _ _ _} _ _ _.
Global Hint Extern 2 (Absorption (⊔) (⊓)) => simple notypeclasses refine join_meet_absorption : typeclass_instances.
Global Hint Extern 2 (Absorption (⊓) (⊔)) => simple notypeclasses refine meet_join_absorption : typeclass_instances.
Global Hint Extern 2 (LeftDistribute (⊔) (⊓)) => simple notypeclasses refine join_meet_distr_l : typeclass_instances.
Global Hint Extern 2 (LeftDistribute (⊓) (⊔)) => simple notypeclasses refine meet_join_distr_l : typeclass_instances.

Section rings.
  Local Open Scope mult_scope.
  Context (R:set) {Rplus: Plus R} {Rmult: Mult R} {Rzero: Zero R} {Rone: One R} {Rnegate: Negate R}.

  Definition AdditiveNonComSemiGroup := SemiGroup            (AdditiveGroupOps R).
  Definition AdditiveNonComMonoid    := Monoid               (AdditiveGroupOps R).
  Definition AdditiveNonComGroup     := Group                (AdditiveGroupOps R).
  Definition AdditiveSemiGroup       := CommutativeSemiGroup (AdditiveGroupOps R).
  Definition AdditiveMonoid          := CommutativeMonoid    (AdditiveGroupOps R).
  Definition AdditiveGroup           := AbGroup              (AdditiveGroupOps R).

  Definition MultiplicativeSemiGroup := SemiGroup         (MultiplicativeGroupOps R).
  Definition MultiplicativeMonoid    := Monoid            (MultiplicativeGroupOps R).
  Definition MultiplicativeComMonoid := CommutativeMonoid (MultiplicativeGroupOps R).

  Existing Class AdditiveNonComSemiGroup.
  Existing Class AdditiveNonComMonoid.
  Existing Class AdditiveNonComGroup.
  Existing Class AdditiveSemiGroup.
  Existing Class AdditiveMonoid.
  Existing Class AdditiveGroup.

  Existing Class MultiplicativeSemiGroup.
  Existing Class MultiplicativeMonoid.
  Existing Class MultiplicativeComMonoid.

  Class AdditiveCancellation : SProp :=
  { add_cancel_l (z:R) : Injective (z +)
  ; add_cancel_r (z:R) : Injective (+ z)
  }.

  Class NonZeroMultiplicativeCancellation : SProp :=
  { mult_cancel_l (z:R) {H: z ≠ 0} : Injective (z ·)
  ; mult_cancel_r (z:R) {H: z ≠ 0} : Injective (· z)
  }.

  Record NearRg : SProp :=
  { #[reversible=no] near_rg_plus_monoid    :> AdditiveNonComMonoid
  ; #[reversible=no] near_rg_mult_semigroup :> MultiplicativeSemiGroup
  ; plus_mult_distr_r : RightDistribute (X:=R) (·) (+)
  ; mult_0_l : LeftAbsorb  (X:=R) (·) 0
  }.
  Existing Class NearRg.

  Record LeftNearRg : SProp :=
  { #[reversible=no] lnear_rg_plus_monoid    :> AdditiveNonComMonoid
  ; #[reversible=no] lnear_rg_mult_semigroup :> MultiplicativeSemiGroup
  ; plus_mult_distr_l : LeftDistribute (X:=R) (·) (+)
  ; mult_0_r : RightAbsorb  (X:=R) (·) 0
  }.
  Existing Class LeftNearRg.

  Record Rg : SProp :=
  { #[reversible=no] rg_near_rg :> NearRg
  ; #[reversible=no] rg_lnear_rg :> LeftNearRg
  ; #[reversible=no] rg_plus_monoid    :> AdditiveMonoid
  }.
  Existing Class Rg.

  Record NearRig : SProp :=
  { #[reversible=no] near_rig_near_rg :> NearRg
  ; #[reversible=no] near_rig_multmon :> MultiplicativeMonoid
  }.
  Existing Class NearRig.

  Record LeftNearRig : SProp :=
  { #[reversible=no] lnear_rig_lnear_rg :> LeftNearRg
  ; #[reversible=no] lnear_rig_multmon :> MultiplicativeMonoid
  }.
  Existing Class LeftNearRig.

  Record Rig : SProp :=
  { #[reversible=no] rig_rg :> Rg
  ; #[reversible=no] rig_multmon :> MultiplicativeMonoid
  }.
  Existing Class Rig.

  Record CommutativeRig : SProp :=
  { #[reversible=no] comrig_rig :> Rig
  ; #[reversible=no] comrig_multcommon :> MultiplicativeComMonoid
  }.
  Existing Class CommutativeRig.

  Record NearRng : SProp :=
  { #[reversible=no] near_rng_near_rg :> NearRg
  ; #[reversible=no] near_rngplus_group :> AdditiveNonComGroup
  }.
  Existing Class NearRng.

  Record LeftNearRng : SProp :=
  { #[reversible=no] lnear_rng_lnear_rg :> LeftNearRg
  ; #[reversible=no] lnear_rngplus_group :> AdditiveNonComGroup
  }.
  Existing Class LeftNearRng.

  Record Rng : SProp :=
  { #[reversible=no] rng_rg :> Rg
  ; #[reversible=no] rngplus_abgroup :> AdditiveGroup
  }.
  Existing Class Rng.

  Record NearRing : SProp :=
  { #[reversible=no] near_ring_near_rng :> NearRng
  ; #[reversible=no] near_ring_near_rig :> NearRig
  }.
  Existing Class NearRing.

  Record LeftNearRing : SProp :=
  { #[reversible=no] lnear_ring_lnear_rng :> LeftNearRng
  ; #[reversible=no] lnear_ring_lnear_rig :> LeftNearRig
  }.
  Existing Class LeftNearRing.

  Record Ring : SProp :=
  { #[reversible=no] ring_rng :> Rng
  ; #[reversible=no] ring_rig :> Rig
  }.
  Existing Class Ring.

  Record CommutativeRing : SProp :=
  { #[reversible=no] comring_ring   :> Ring
  ; #[reversible=no] comring_comrig :> CommutativeRig
  }.
  Existing Class CommutativeRing.

  Class OneNonZero           : SProp := one_nonzero                       : (1 = 0 :> R)ᗮ.
  Class NoZeroDivisors       : SProp := no_zero_divisors        (x y : R) : x · y = 0 ⊸ x = 0 ⊞ y = 0.
  Class StrongNoZeroDivisors : SProp := strong_no_zero_divisors (x y : R) : x · y = 0 ⊸ x = 0 ∨ y = 0.

  Record IntegralDomain : SProp :=
  { #[reversible=no] intdom_comring :> CommutativeRing
  ; #[reversible=no] intdom_nontrivial :> OneNonZero
  ; #[reversible=no] intdom_no_zero_divisors :> NoZeroDivisors
  }.
  Existing Class IntegralDomain.
End rings.
Arguments add_cancel_l {_ _ _} _.
Arguments add_cancel_r {_ _ _} _.
Arguments mult_cancel_l {_ _ _ _} _ {_}.
Arguments mult_cancel_r {_ _ _ _} _ {_}.
Arguments one_nonzero {R _ _ _}.
Arguments no_zero_divisors {R _ _ _} _ _.
Arguments strong_no_zero_divisors {R _ _ _} _ _.
Arguments mult_0_l {R _ _ _ _} _.
Arguments mult_0_r {R _ _ _ _} _.
Arguments plus_mult_distr_l {R _ _ _ _} _ _ _.
Arguments plus_mult_distr_r {R _ _ _ _} _ _ _.
Global Hint Extern 2 (Injective (_ +)) => simple notypeclasses refine (add_cancel_l _) : typeclass_instances.
Global Hint Extern 2 (Injective (+ _)) => simple notypeclasses refine (add_cancel_r _) : typeclass_instances.
Global Hint Extern 2 (Injective (func_op2 ap1 mult _)) => simple notypeclasses refine (mult_cancel_l _) : typeclass_instances.
Global Hint Extern 2 (Injective (func_op2 ap2 mult _)) => simple notypeclasses refine (mult_cancel_r _) : typeclass_instances.
Global Hint Extern 2 (LeftAbsorb   mult 0) => simple notypeclasses refine mult_0_l : typeclass_instances.
Global Hint Extern 2 (RightAbsorb  mult 0) => simple notypeclasses refine mult_0_r : typeclass_instances.
Global Hint Extern 2 (LeftDistribute  mult (+)) => simple notypeclasses refine plus_mult_distr_l : typeclass_instances.
Global Hint Extern 2 (RightDistribute mult (+)) => simple notypeclasses refine plus_mult_distr_r : typeclass_instances.
Global Hint Extern 2 (apos (1 ≠ 0)) => simple notypeclasses refine one_nonzero : typeclass_instances.

Global Hint Extern 8 (Monoid            (AdditiveGroupOps ?X)) => change (AdditiveNonComMonoid X) : typeclass_instances.
Global Hint Extern 8 (Group             (AdditiveGroupOps ?X)) => change (AdditiveNonComGroup  X) : typeclass_instances.
Global Hint Extern 8 (CommutativeMonoid (AdditiveGroupOps ?X)) => change (AdditiveMonoid X) : typeclass_instances.
Global Hint Extern 8 (AbGroup           (AdditiveGroupOps ?X)) => change (AdditiveGroup  X) : typeclass_instances.
Global Hint Extern 8 (SemiGroup         (MultiplicativeGroupOps ?X)) => change (MultiplicativeSemiGroup X) : typeclass_instances.
Global Hint Extern 8 (Monoid            (MultiplicativeGroupOps ?X)) => change (MultiplicativeMonoid    X) : typeclass_instances.
Global Hint Extern 8 (CommutativeMonoid (MultiplicativeGroupOps ?X)) => change (MultiplicativeComMonoid X) : typeclass_instances.

(** Pointed morphisms *)

Definition aPointed_Morphism@{u} {X Y : set@{u}} := set:( λ (x:X) (y:Y) (f:X ⇾ Y), f x = y ).
Definition Pointed_Morphism@{u} {X Y : set@{u}} (x:X) (y:Y) (f:X ⇾ Y) : SProp := Eval simpl in aPointed_Morphism x y f.
Existing Class Pointed_Morphism.
Definition preserves_point@{u} {X Y : set@{u}} {x y} f {H:@Pointed_Morphism X Y x y f} : f x = y := H.
Definition Pointed_Morphism_fun@{u} {X Y : set@{u}} := make_fun_alt (eval_tuncurry3 (@Pointed_Morphism X Y)) (weaken_apred3 (@aPointed_Morphism X Y)).

Definition MonUnit_Pointed_Morphism@{u} {X Y:set@{u}} {Xunit:MonUnit X} {Yunit:MonUnit Y} := @Pointed_Morphism X Y mon_unit mon_unit.
Definition Top_Pointed_Morphism@{u}     {X Y:set@{u}} {Xtop:Top X} {Ytop:Top Y} := @Pointed_Morphism X Y ⊤ ⊤.
Definition Bottom_Pointed_Morphism@{u}  {X Y:set@{u}} {Xbot:Bottom X} {Ybot:Bottom Y} := @Pointed_Morphism X Y ⊥ ⊥.
Definition Zero_Pointed_Morphism@{u}    {X Y:set@{u}} {Xzero:Zero X} {Yzero:Zero Y} := @Pointed_Morphism X Y 0 0.
Definition One_Pointed_Morphism@{u}     {X Y:set@{u}} {Xone:One X} {Yone:One Y} := @Pointed_Morphism X Y 1 1.
Existing Class MonUnit_Pointed_Morphism.
Existing Class Top_Pointed_Morphism.
Existing Class Bottom_Pointed_Morphism.
Existing Class Zero_Pointed_Morphism.
Existing Class One_Pointed_Morphism.

Definition preserves_unit@{u}   : ∀ {X Y: set@{u}} {Xunit:MonUnit X} {Yunit:MonUnit Y} (f:X ⇾ Y) `{!MonUnit_Pointed_Morphism f}, f mon_unit = mon_unit := @preserves_point.
Definition preserves_top@{u}    : ∀ {X Y: set@{u}} {Xtop:Top X} {Ytop:Top Y} (f:X ⇾ Y) `{!Top_Pointed_Morphism f}, f ⊤ = ⊤ := @preserves_point.
Definition preserves_bottom@{u} : ∀ {X Y: set@{u}} {Xbot:Bottom X} {Ybot:Bottom Y} (f:X ⇾ Y) `{!Bottom_Pointed_Morphism f}, f ⊥ = ⊥ := @preserves_point.
Definition preserves_0@{u}      : ∀ {X Y: set@{u}} {Xzero:Zero X} {Yzero:Zero Y} (f:X ⇾ Y) `{!Zero_Pointed_Morphism f}, f 0 = 0 := @preserves_point.
Definition preserves_1@{u}      : ∀ {X Y: set@{u}} {Xone:One X}   {Yzero:One Y}  (f:X ⇾ Y) `{!One_Pointed_Morphism f},  f 1 = 1 := @preserves_point.

Canonical Structure MonUnit_Pointed_Morphism_fun {X Y} := make_fun_alt (eval_tuncurry3 (@MonUnit_Pointed_Morphism  X Y)) (@Pointed_Morphism_fun X Y).
Canonical Structure Top_Pointed_Morphism_fun     {X Y} := make_fun_alt (eval_tuncurry3 (@Top_Pointed_Morphism      X Y)) (@Pointed_Morphism_fun X Y).
Canonical Structure Bottom_Pointed_Morphism_fun  {X Y} := make_fun_alt (eval_tuncurry3 (@Bottom_Pointed_Morphism   X Y)) (@Pointed_Morphism_fun X Y).
Canonical Structure Zero_Pointed_Morphism_fun    {X Y} := make_fun_alt (eval_tuncurry3 (@Zero_Pointed_Morphism     X Y)) (@Pointed_Morphism_fun X Y).
Canonical Structure One_Pointed_Morphism_fun     {X Y} := make_fun_alt (eval_tuncurry3 (@One_Pointed_Morphism      X Y)) (@Pointed_Morphism_fun X Y).

(** Group morphisms *)
Section morphisms.
  Universes u.
  Local Open Scope sg_op_scope.
  Local Abbreviation e := mon_unit.

  Record SemiGroup_Morphism {X Y:set@{u}} {Xop:SgOp X} {Yop:SgOp Y} (f:X ⇾ Y) : SProp :=
  { #[reversible=no] sgmor_a :> SemiGroup X
  ; sgmor_b :  SemiGroup Y
  ; preserves_sg_op x y : f (x ∙ y) = f x ∙ f y
  }.
  Existing Class SemiGroup_Morphism.

  Record Monoid_Morphism {X Y:set@{u}} {Xop:SgOp X} {Xunit:MonUnit X} {Yop:SgOp Y} {Yunit:MonUnit Y} (f:X ⇾ Y) : SProp :=
  { #[reversible=no] monmor_a :> Monoid X
  ; monmor_b :  Monoid Y
  ; #[reversible=no] monmor_sgmor :> SemiGroup_Morphism f
  ; #[reversible=no] monmor_pointed :> MonUnit_Pointed_Morphism f
  }.
  Existing Class Monoid_Morphism.

  Local Open Scope star_scope.
  Record StarSemiGroup_Morphism {X Y:set@{u}} {Xop:SgOp X} {Yop:SgOp Y} {Xinv:Inv X} {Yinv:Inv Y} (f:X ⇾ Y) : SProp :=
  { #[reversible=no] ssgmor_a :> StarSemiGroup X
  ; ssgmor_b :  StarSemiGroup Y
  ; #[reversible=no] ssgmor_sgmor :> SemiGroup_Morphism f
  ; preserves_inv x : f (x*) = (f x)*
  }.
  Existing Class StarSemiGroup_Morphism.
  Local Close Scope star_scope.

  Record StarMonoid_Morphism {X Y:set@{u}} {Xop:SgOp X} {Yop:SgOp Y} {Xunit:MonUnit X} {Yunit:MonUnit Y} {Xinv:Inv X} {Yinv:Inv Y} (f:X ⇾ Y) : SProp :=
  { #[reversible=no] smonmor_a :> StarMonoid X
  ; smonmor_b :  StarMonoid Y
  ; #[reversible=no] smonmor_monmor :> Monoid_Morphism f
  ; #[reversible=no] smonmor_ssgmor :> StarSemiGroup_Morphism f
  }.
  Existing Class StarMonoid_Morphism.
End morphisms.
Arguments Build_SemiGroup_Morphism {X Y _ _} f {_ _}.
Arguments preserves_sg_op {X Y _ _} f {_} _ _.
Arguments preserves_inv {X Y _ _ _ _} f {_} _.

(** Lattice morphisms *)
Definition MeetSemiLattice_Morphism@{u}  {X Y:set@{u}} {Xmeet:Meet X} {Ymeet:Meet Y} (f : X ⇾ Y) := SemiGroup_Morphism (X:=MeetSemigroupOps X) (Y:=MeetSemigroupOps Y) f.
Definition JoinSemiLattice_Morphism@{u}  {X Y:set@{u}} {Xjoin:Join X} {Yjoin:Join Y} (f : X ⇾ Y) := SemiGroup_Morphism (X:=JoinSemigroupOps X) (Y:=JoinSemigroupOps Y) f.
Definition BoundedMeetSemiLattice_Morphism@{u}  {X Y:set@{u}} {Xmeet:Meet X} {Xtop:Top    X} {Ymeet:Meet Y} {Ytop:Top    Y} (f : X ⇾ Y) := Monoid_Morphism (X:=MeetSemigroupOps X) (Y:=MeetSemigroupOps Y) f.
Definition BoundedJoinSemiLattice_Morphism@{u}  {X Y:set@{u}} {Xjoin:Join X} {Xbot:Bottom X} {Yjoin:Join Y} {Ybot:Bottom Y} (f : X ⇾ Y) := Monoid_Morphism (X:=JoinSemigroupOps X) (Y:=JoinSemigroupOps Y) f.
Existing Class MeetSemiLattice_Morphism.
Existing Class JoinSemiLattice_Morphism.
Existing Class BoundedMeetSemiLattice_Morphism.
Existing Class BoundedJoinSemiLattice_Morphism.

Definition MeetSemiLattice_Flip_Morphism@{u} {X Y:set@{u}} {Xmeet:Meet X} {Yjoin:Join Y} (f : X ⇾ Y) := MeetSemiLattice_Morphism (X:=X) (Y:=order_op Y) f.
Definition JoinSemiLattice_Flip_Morphism@{u} {X Y:set@{u}} {Xjoin:Join X} {Ymeet:Meet Y} (f : X ⇾ Y) := JoinSemiLattice_Morphism (X:=X) (Y:=order_op Y) f.
Definition BoundedMeetSemiLattice_Flip_Morphism@{u} {X Y:set@{u}} {Xmeet:Meet X} {Xtop:Top X} {Yjoin:Join Y} {Ybot:Bottom Y} (f : X ⇾ Y) := BoundedMeetSemiLattice_Morphism (X:=X) (Y:=order_op Y) f.
Definition BoundedJoinSemiLattice_Flip_Morphism@{u} {X Y:set@{u}} {Xjoin:Join X} {Xbot:Bottom X} {Ymeet:Meet Y} {Ytop:Top Y} (f : X ⇾ Y) := BoundedJoinSemiLattice_Morphism (X:=X) (Y:=order_op Y) f.
Existing Class MeetSemiLattice_Flip_Morphism.
Existing Class JoinSemiLattice_Flip_Morphism.
Existing Class BoundedMeetSemiLattice_Flip_Morphism.
Existing Class BoundedJoinSemiLattice_Flip_Morphism.

Record Lattice_Morphism@{u} {X Y:set@{u}} {Xmeet:Meet X} {Xjoin:Join X} {Ymeet:Meet Y} {Yjoin:Join Y} (f : X ⇾ Y) : SProp :=
{ #[reversible=no] latmor_a :> Lattice X
; latmor_b :  Lattice Y
; #[reversible=no] latmor_meet_sl_mor :> MeetSemiLattice_Morphism f
; #[reversible=no] latmor_join_sl_mor :> JoinSemiLattice_Morphism f
}.
Existing Class Lattice_Morphism.

Definition Lattice_Flip_Morphism@{u} {X Y:set@{u}} {Xmeet:Meet X} {Xjoin:Join X} {Ymeet:Meet Y} {Yjoin:Join Y} (f : X ⇾ Y) := Lattice_Morphism (X:=X) (Y:=order_op Y) f.
Existing Class Lattice_Flip_Morphism.

Record BoundedLattice_Morphism@{u} {X Y:set@{u}} {Xmeet:Meet X} {Xjoin:Join X} {Xtop:Top X} {Xbot:Bottom X} {Ymeet:Meet Y} {Yjoin:Join Y} {Ytop:Top Y} {Ybot:Bottom Y} (f : X ⇾ Y) : SProp :=
{ #[reversible=no] bounded_latmor_a :> BoundedLattice X
; bounded_latmor_b : BoundedLattice Y
; #[reversible=no] bounded_latmor_meet :> BoundedMeetSemiLattice_Morphism f
; #[reversible=no] bounded_latmor_join :> BoundedJoinSemiLattice_Morphism f
}.
Existing Class BoundedLattice_Morphism.

Definition BoundedLattice_Flip_Morphism@{u} {X Y:set@{u}} {Xmeet:Meet X} {Xjoin:Join X} {Xtop:Top X} {Xbot:Bottom X} {Ymeet:Meet Y} {Yjoin:Join Y} {Ytop:Top Y} {Ybot:Bottom Y} (f : X ⇾ Y) := BoundedLattice_Morphism (X:=X) (Y:=order_op Y) f.
Existing Class BoundedLattice_Flip_Morphism.

(** Ring morphisms *)
Section ring_morphism_classes.
  Universes u.
  Definition AdditiveSemiGroup_Morphism       {X Y:set@{u}} {Xplus:Plus X} {Yplus:Plus Y} (f : X ⇾ Y) := SemiGroup_Morphism (X:=AdditiveGroupOps X) (Y:=AdditiveGroupOps Y) f.
  Definition AdditiveMonoid_Morphism          {X Y:set@{u}} {Xplus:Plus X} {Xzero:Zero X} {Yplus:Plus Y} {Yzero:Zero Y} (f : X ⇾ Y) := Monoid_Morphism    (X:=AdditiveGroupOps X)       (Y:=AdditiveGroupOps Y)       f.
  Definition MultiplicativeSemiGroup_Morphism {X Y:set@{u}} {Xmult:Mult X} {Ymult:Mult Y} (f : X ⇾ Y) := SemiGroup_Morphism (X:=MultiplicativeGroupOps X) (Y:=MultiplicativeGroupOps Y) f.
  Definition MultiplicativeMonoid_Morphism    {X Y:set@{u}} {Xmult:Mult X} {Xone :One X}  {Ymult:Mult Y} {Yone :One  Y} (f : X ⇾ Y) := Monoid_Morphism    (X:=MultiplicativeGroupOps X) (Y:=MultiplicativeGroupOps Y) f.
  Existing Class AdditiveSemiGroup_Morphism.
  Existing Class AdditiveMonoid_Morphism.
  Existing Class MultiplicativeSemiGroup_Morphism.
  Existing Class MultiplicativeMonoid_Morphism.

  Record Rg_Morphism {X Y:set@{u}} {Xplus:Plus X} {Yplus:Plus Y} {Xmult:Mult X} {Ymult:Mult Y} {Xzero:Zero X} {Yzero:Zero Y} (f : X ⇾ Y) : SProp :=
    { #[reversible=no] rgmor_plus_mor :> AdditiveMonoid_Morphism f
    ; #[reversible=no] rgmor_mult_mor :> MultiplicativeSemiGroup_Morphism f
    }.
  Existing Class Rg_Morphism.

  Record Rig_Morphism {X Y:set@{u}} {Xplus:Plus X} {Yplus:Plus Y} {Xmult:Mult X} {Ymult:Mult Y} {Xzero:Zero X} {Yzero:Zero Y} {Xone :One X}  {Yone :One  Y} (f : X ⇾ Y) : SProp :=
    { #[reversible=no] rigmor_plus_mor :> AdditiveMonoid_Morphism f
    ; #[reversible=no] rigmor_mult_mor :> MultiplicativeMonoid_Morphism f
    }.
  Existing Class Rig_Morphism.
End ring_morphism_classes.

Global Hint Extern 8 (Monoid_Morphism (X:=AdditiveGroupOps ?X) (Y:=AdditiveGroupOps ?Y) ?f)
  => change (AdditiveMonoid_Morphism (X:=X) (Y:=Y) f) : typeclass_instances.


Global Hint Extern 10 (SemiGroup ?X) =>
  match goal with
  | H : SemiGroup_Morphism     (Y:=X) _ |- _ => exact (sgmor_b _ H)
  | H : Monoid_Morphism        (Y:=X) _ |- _ => exact (sgmor_b _ H)
  | H : StarSemiGroup_Morphism (Y:=X) _ |- _ => exact (sgmor_b _ H)
  | H : StarMonoid_Morphism    (Y:=X) _ |- _ => exact (sgmor_b _ H)
  end : typeclass_instances.

Global Hint Extern 10 (Monoid ?X) =>
  match goal with
  | H : Monoid_Morphism     (Y:=X) _ |- _ => exact (monmor_b _ H)
  | H : StarMonoid_Morphism (Y:=X) _ |- _ => exact (monmor_b _ H)
  end : typeclass_instances.

Global Hint Extern 10 (StarSemiGroup ?X) =>
  match goal with
  | H : StarSemiGroup_Morphism (Y:=X) _ |- _ => exact (ssgmor_b _ H)
  | H : StarMonoid_Morphism    (Y:=X) _ |- _ => exact (ssgmor_b _ H)
  end : typeclass_instances.

Global Hint Extern 10 (StarMonoid ?X) =>
  match goal with
  | H : StarMonoid_Morphism (Y:=X) _ |- _ => exact (smonmor_b _ H)
  end : typeclass_instances.

Global Hint Extern 10 (Lattice ?X) =>
  match goal with
  | H : Lattice_Morphism (Y:=X) _ |- _ => exact (latmor_b _ H)
  end : typeclass_instances.

Global Hint Extern 10 (BoundedLattice ?X) =>
  match goal with
  | H : BoundedLattice_Morphism (Y:=X) _ |- _ => exact (bounded_latmor_b _ H)
  end : typeclass_instances.

