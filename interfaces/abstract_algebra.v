Require Export theory.set interfaces.common_props algebra_notation.
Require Import set_lambda.

Section groups.
  Local Open Scope grp_scope.
  Local Notation e := mon_unit.

  Universes i.
  Context (X:set@{i}) {op:SgOp X} {unit:MonUnit X} {inv:Inv X}.

  SubClass SemiGroup := @Associative X (∙).
  Existing Class SemiGroup.

  Record CommutativeSemiGroup : SProp :=
  { comsg_sg :> SemiGroup
  ; comsg_com :> Commutative (X:=X) (∙)
  }.
  Existing Class CommutativeSemiGroup.

  Record SemiLattice : SProp :=
  { semilattice_sg :> CommutativeSemiGroup
  ; semilattice_idempotent :> @BinaryIdempotent X (∙)
  }.
  Existing Class SemiLattice.

  Record Monoid : SProp :=
  { monoid_semigroup   :> SemiGroup
  ; monoid_left_id     :> LeftIdentity  (X:=X) (∙) e
  ; monoid_right_id    :> RightIdentity (X:=X) (∙) e
  }.
  Existing Class Monoid.

  Record CommutativeMonoid : SProp :=
  { commonoid_monoid  :> Monoid
  ; commonoid_com :> Commutative (X:=X) (∙)
  }.
  Existing Class CommutativeMonoid.

  Record BoundedSemiLattice : SProp :=
  { bounded_semilattice_sl :> SemiLattice
  ; bounded_semilattice_common :> CommutativeMonoid
  }.
  Existing Class BoundedSemiLattice.

  Record Group : SProp :=
  { group_monoid :> Monoid
  ; inverse_l :> LeftInverse  (X:=X) (∙) (⁻¹) e
  ; inverse_r :> RightInverse (X:=X) (∙) (⁻¹) e
  }.
  Existing Class Group.

  Record AbGroup : SProp :=
  { abgroup_group :> Group
  ; abgroup_com :> Commutative (X:=X) (∙)
  }.
  Existing Class AbGroup.
End groups.
Arguments inverse_l {X _ _ _ _} _.
Arguments inverse_r {X _ _ _ _} _.
Global Hint Extern 2 (Associative (X:=?X) sg_op) => change (SemiGroup X) : typeclass_instances.
Global Hint Extern 2 (LeftIdentity sg_op _) => simple notypeclasses refine monoid_left_id : typeclass_instances.
Global Hint Extern 2 (RightIdentity sg_op _) => simple notypeclasses refine monoid_right_id : typeclass_instances.

Section strong_groups.
  Local Open Scope grp_scope.
  Universes i.
  Context (X:set@{i}) {op:SgOp X} {unit:MonUnit X} {inv:Inv X}.

  Record StrongOpSemiGroup : SProp :=
  { strong_op_sg_sg :> SemiGroup X
  ; strong_sg_op :> StrongOp (X:=X) (∙)
  }.
  Existing Class StrongOpSemiGroup.

  Record StrongOpMonoid : SProp :=
  { strong_op_mon_mon :> Monoid X
  ; strong_op_mon_str :> StrongOp (X:=X) (∙)
  }.
  Existing Class StrongOpMonoid.
End strong_groups.
Arguments strong_sg_op {X _ _}.
Global Hint Extern 2 (StrongOp sg_op) => simple notypeclasses refine strong_sg_op : typeclass_instances.

Section lattices.
  Universes i.
  Context (L:set@{i}) `{Meet L} `{Join L} `{Top L} `{Bottom L}.
  Definition MeetSemiLattice := SemiLattice (MeetSemigroupOps L).
  Definition BoundedMeetSemiLattice := BoundedSemiLattice (MeetSemigroupOps L).
  Definition JoinSemiLattice := SemiLattice (JoinSemigroupOps L).
  Definition BoundedJoinSemiLattice := BoundedSemiLattice (JoinSemigroupOps L).
  Existing Class MeetSemiLattice.
  Existing Class JoinSemiLattice.
  Existing Class BoundedMeetSemiLattice.
  Existing Class BoundedJoinSemiLattice.

  Record Lattice : SProp := 
  { lattice_join :> JoinSemiLattice
  ; lattice_meet :> MeetSemiLattice
  ; join_meet_absorption : Absorption (X:=L) (⊔) (⊓)
  ; meet_join_absorption : Absorption (X:=L) (⊓) (⊔)
  }.
  Existing Class Lattice.

  Record DistributiveLattice : SProp := 
  { distr_lattice_lattice :> Lattice
  ; join_meet_distr_l : LeftDistribute (X:=L) (⊔) (⊓)
  ; meet_join_distr_l : LeftDistribute (X:=L) (⊓) (⊔)
  }.
  Existing Class DistributiveLattice.
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
  Universes i.
  Context (R:set@{i}) {Rplus: Plus R} {Rmult: Mult R} {Rzero: Zero R} {Rone: One R} {Rnegate: Negate R}.

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

  Class NoZeroDivisors : SProp := no_zero_divisors (x y : R) : x · y = 0 ⊸ x = 0 ⊞ y = 0.
  Class ZeroProduct    : SProp := zero_product     (x y : R) : x · y = 0 ⊸ x = 0 ∨ y = 0.

  Record NearRg : SProp :=
  { near_rg_plus_monoid    :> AdditiveNonComMonoid
  ; near_rg_mult_semigroup :> MultiplicativeSemiGroup
  ; plus_mult_distr_r : RightDistribute (X:=R) (·) (+)
  ; mult_0_l : LeftAbsorb  (X:=R) (·) 0
  }.
  Existing Class NearRg.

  Record LeftNearRg : SProp :=
  { lnear_rg_plus_monoid    :> AdditiveNonComMonoid
  ; lnear_rg_mult_semigroup :> MultiplicativeSemiGroup
  ; plus_mult_distr_l : LeftDistribute (X:=R) (·) (+)
  ; mult_0_r : RightAbsorb  (X:=R) (·) 0
  }.
  Existing Class LeftNearRg.

  Record Rg : SProp :=
  { rg_near_rg :> NearRg
  ; rg_lnear_rg :> LeftNearRg
  ; rg_plus_monoid    :> AdditiveMonoid
  }.
  Existing Class Rg.

  Record NearRig : SProp :=
  { near_rig_near_rg :> NearRg
  ; near_rig_multmon :> MultiplicativeMonoid
  }.
  Existing Class NearRig.

  Record LeftNearRig : SProp :=
  { lnear_rig_lnear_rg :> LeftNearRg
  ; lnear_rig_multmon :> MultiplicativeMonoid
  }.
  Existing Class LeftNearRig.

  Record Rig : SProp :=
  { rig_rg :> Rg
  ; rig_multmon :> MultiplicativeMonoid
  }.
  Existing Class Rig.

  Record CommutativeRig : SProp :=
  { comrig_rig :> Rig
  ; comrig_multcommon :> MultiplicativeComMonoid
  }.
  Existing Class CommutativeRig.

  Record NearRng : SProp :=
  { near_rng_near_rg :> NearRg
  ; near_rngplus_group :> AdditiveNonComGroup
  }.
  Existing Class NearRng.

  Record LeftNearRng : SProp :=
  { lnear_rng_lnear_rg :> LeftNearRg
  ; lnear_rngplus_group :> AdditiveNonComGroup
  }.
  Existing Class LeftNearRng.

  Record Rng : SProp :=
  { rng_rg :> Rg
  ; rngplus_abgroup :> AdditiveGroup
  }.
  Existing Class Rng.

  Record NearRing : SProp :=
  { near_ring_near_rng :> NearRng
  ; near_ring_near_rig :> NearRig
  }.
  Existing Class NearRing.

  Record LeftNearRing : SProp :=
  { lnear_ring_lnear_rng :> LeftNearRng
  ; lnear_ring_lnear_rig :> LeftNearRig
  }.
  Existing Class LeftNearRing.

  Record Ring : SProp :=
  { ring_rng :> Rng
  ; ring_rig :> Rig
  }.
  Existing Class Ring.

  Record CommutativeRing : SProp :=
  { comring_ring   :> Ring
  ; comring_comrig :> CommutativeRig
  }.
  Existing Class CommutativeRing.

End rings.
Arguments no_zero_divisors {R _ _ _} _ _.
Arguments zero_product     {R _ _ _} _ _.
Arguments mult_0_l {R _ _ _ _} _.
Arguments mult_0_r {R _ _ _ _} _.
Arguments plus_mult_distr_l {R _ _ _ _} _ _ _.
Arguments plus_mult_distr_r {R _ _ _ _} _ _ _.
Global Hint Extern 2 (LeftAbsorb   mult 0) => simple notypeclasses refine mult_0_l : typeclass_instances.
Global Hint Extern 2 (RightAbsorb  mult 0) => simple notypeclasses refine mult_0_r : typeclass_instances.
Global Hint Extern 2 (LeftDistribute  mult (+)) => simple notypeclasses refine plus_mult_distr_l : typeclass_instances.
Global Hint Extern 2 (RightDistribute mult (+)) => simple notypeclasses refine plus_mult_distr_r : typeclass_instances.

Global Hint Extern 8 (Monoid            (AdditiveGroupOps ?X)) => change (AdditiveNonComMonoid X) : typeclass_instances.
Global Hint Extern 8 (Group             (AdditiveGroupOps ?X)) => change (AdditiveNonComGroup  X) : typeclass_instances.
Global Hint Extern 8 (CommutativeMonoid (AdditiveGroupOps ?X)) => change (AdditiveMonoid X) : typeclass_instances.
Global Hint Extern 8 (AbGroup           (AdditiveGroupOps ?X)) => change (AdditiveGroup  X) : typeclass_instances.
Global Hint Extern 8 (SemiGroup         (MultiplicativeGroupOps ?X)) => change (MultiplicativeSemiGroup X) : typeclass_instances.
Global Hint Extern 8 (Monoid            (MultiplicativeGroupOps ?X)) => change (MultiplicativeMonoid    X) : typeclass_instances.
Global Hint Extern 8 (CommutativeMonoid (MultiplicativeGroupOps ?X)) => change (MultiplicativeComMonoid X) : typeclass_instances.

(** Pointed morphisms *)

Definition aPointed_Morphism {X Y : set} := set:( λ (x:X) (y:Y) (f:X ⇾ Y), f x = y ).
Definition Pointed_Morphism {X Y : set} (x:X) (y:Y) (f:X ⇾ Y) : SProp := Eval simpl in aPointed_Morphism x y f.
Existing Class Pointed_Morphism.
Definition preserves_point {X Y x y} f {H:@Pointed_Morphism X Y x y f} : f x = y := H.
Definition Pointed_Morphism_fun {X Y : set} := make_fun_alt (eval_tuncurry3 (@Pointed_Morphism X Y)) (weaken_apred3 (@aPointed_Morphism X Y)).

Definition MonUnit_Pointed_Morphism@{i} {X Y : set@{i}} {Xunit:MonUnit X} {Yunit:MonUnit Y} := @Pointed_Morphism X Y mon_unit mon_unit.
Definition Top_Pointed_Morphism@{i} {X Y : set@{i}} {Xtop:Top X} {Ytop:Top Y} := @Pointed_Morphism X Y ⊤ ⊤.
Definition Bottom_Pointed_Morphism@{i} {X Y : set@{i}} {Xbot:Bottom X} {Ybot:Bottom Y} := @Pointed_Morphism X Y ⊥ ⊥.
Definition Zero_Pointed_Morphism@{i} {X Y : set@{i}} {Xzero:Zero X} {Yzero:Zero Y} := @Pointed_Morphism X Y 0 0.
Definition One_Pointed_Morphism@{i} {X Y : set@{i}} {Xone:One X} {Yone:One Y} := @Pointed_Morphism X Y 1 1.
Existing Class MonUnit_Pointed_Morphism.
Existing Class Top_Pointed_Morphism.
Existing Class Bottom_Pointed_Morphism.
Existing Class Zero_Pointed_Morphism.
Existing Class One_Pointed_Morphism.
Definition preserves_unit@{i} : ∀ {X Y : set@{i}} {Xunit:MonUnit X} {Yunit:MonUnit Y} (f:X ⇾ Y) `{!MonUnit_Pointed_Morphism f}, f mon_unit = mon_unit := @preserves_point.
Definition preserves_top@{i} : ∀ {X Y : set@{i}} {Xtop:Top X} {Ytop:Top Y} (f:X ⇾ Y) `{!Top_Pointed_Morphism f}, f ⊤ = ⊤ := @preserves_point.
Definition preserves_bottom@{i} : ∀ {X Y : set@{i}} {Xbot:Bottom X} {Ybot:Bottom Y} (f:X ⇾ Y) `{!Bottom_Pointed_Morphism f}, f ⊥ = ⊥ := @preserves_point.
Definition preserves_0@{i} : ∀ {X Y : set@{i}} {Xzero:Zero X} {Yzero:Zero Y} (f:X ⇾ Y) `{!Zero_Pointed_Morphism f}, f 0 = 0 := @preserves_point.
Definition preserves_1@{i}  : ∀ {X Y : set@{i}} {Xone:One X}   {Yzero:One Y}  (f:X ⇾ Y) `{!One_Pointed_Morphism f},  f 1 = 1 := @preserves_point.

Canonical Structure MonUnit_Pointed_Morphism_fun {X Y} := make_fun_alt (eval_tuncurry3 (@MonUnit_Pointed_Morphism  X Y)) (@Pointed_Morphism_fun X Y).
Canonical Structure Top_Pointed_Morphism_fun     {X Y} := make_fun_alt (eval_tuncurry3 (@Top_Pointed_Morphism      X Y)) (@Pointed_Morphism_fun X Y).
Canonical Structure Bottom_Pointed_Morphism_fun  {X Y} := make_fun_alt (eval_tuncurry3 (@Bottom_Pointed_Morphism   X Y)) (@Pointed_Morphism_fun X Y).
Canonical Structure Zero_Pointed_Morphism_fun    {X Y} := make_fun_alt (eval_tuncurry3 (@Zero_Pointed_Morphism     X Y)) (@Pointed_Morphism_fun X Y).
Canonical Structure One_Pointed_Morphism_fun     {X Y} := make_fun_alt (eval_tuncurry3 (@One_Pointed_Morphism      X Y)) (@Pointed_Morphism_fun X Y).

(** Group morphisms *)
Section morphisms.
  Local Open Scope grp_scope.
  Local Notation e := mon_unit.

  Record SemiGroup_Morphism {X Y} {Xop:SgOp X} {Yop:SgOp Y} (f:X ⇾ Y) : SProp :=
  { sgmor_a :> SemiGroup X
  ; sgmor_b :  SemiGroup Y
  ; preserves_sg_op x y : f (x ∙ y) = f x ∙ f y
  }.
  Existing Class SemiGroup_Morphism.

  Record Monoid_Morphism {X Y} {Xop:SgOp X} {Xunit:MonUnit X} {Yop:SgOp Y} {Yunit:MonUnit Y} (f:X ⇾ Y) : SProp :=
  { monmor_a :> Monoid X
  ; monmor_b :  Monoid Y
  ; monmor_sgmor :> SemiGroup_Morphism f
  ; monmor_pointed :> MonUnit_Pointed_Morphism f
  }.
  Existing Class Monoid_Morphism.
End morphisms.
Arguments Build_SemiGroup_Morphism {X Y _ _} f {_ _}.
Arguments preserves_sg_op {X Y _ _} f {_} _ _.

(** Lattice morphisms *)
Definition MeetSemiLattice_Morphism  {X Y} {Xmeet:Meet X} {Ymeet:Meet Y} (f : X ⇾ Y) := SemiGroup_Morphism (X:=MeetSemigroupOps X) (Y:=MeetSemigroupOps Y) f.
Definition JoinSemiLattice_Morphism  {X Y} {Xjoin:Join X} {Yjoin:Join Y} (f : X ⇾ Y) := SemiGroup_Morphism (X:=JoinSemigroupOps X) (Y:=JoinSemigroupOps Y) f.
Definition BoundedMeetSemiLattice_Morphism  {X Y} {Xmeet:Meet X} {Xtop:Top    X} {Ymeet:Meet Y} {Ytop:Top    Y} (f : X ⇾ Y) := Monoid_Morphism (X:=MeetSemigroupOps X) (Y:=MeetSemigroupOps Y) f.
Definition BoundedJoinSemiLattice_Morphism  {X Y} {Xjoin:Join X} {Xbot:Bottom X} {Yjoin:Join Y} {Ybot:Bottom Y} (f : X ⇾ Y) := Monoid_Morphism (X:=JoinSemigroupOps X) (Y:=JoinSemigroupOps Y) f.
Existing Class MeetSemiLattice_Morphism.
Existing Class JoinSemiLattice_Morphism.
Existing Class BoundedMeetSemiLattice_Morphism.
Existing Class BoundedJoinSemiLattice_Morphism.

Record Lattice_Morphism {X Y} {Xmeet:Meet X} {Xjoin:Join X} {Ymeet:Meet Y} {Yjoin:Join Y} (f : X ⇾ Y) : SProp :=
{ latmor_a :> Lattice X
; latmor_b :  Lattice Y
; latmor_meet_sl_mor :> MeetSemiLattice_Morphism f
; latmor_join_sl_mor :> JoinSemiLattice_Morphism f
}.
Existing Class Lattice_Morphism.

(** Ring morphisms *)
Section ring_morphism_classes.
  Definition AdditiveSemiGroup_Morphism       {X Y} {Xplus:Plus X} {Yplus:Plus Y} (f : X ⇾ Y) := SemiGroup_Morphism (X:=AdditiveGroupOps X) (Y:=AdditiveGroupOps Y) f.
  Definition AdditiveMonoid_Morphism          {X Y} {Xplus:Plus X} {Xzero:Zero X} {Yplus:Plus Y} {Yzero:Zero Y} (f : X ⇾ Y) := Monoid_Morphism    (X:=AdditiveGroupOps X)       (Y:=AdditiveGroupOps Y)       f.
  Definition MultiplicativeSemiGroup_Morphism {X Y} {Xmult:Mult X} {Ymult:Mult Y} (f : X ⇾ Y) := SemiGroup_Morphism (X:=MultiplicativeGroupOps X) (Y:=MultiplicativeGroupOps Y) f.
  Definition MultiplicativeMonoid_Morphism    {X Y} {Xmult:Mult X} {Xone :One X}  {Ymult:Mult Y} {Yone :One  Y} (f : X ⇾ Y) := Monoid_Morphism    (X:=MultiplicativeGroupOps X) (Y:=MultiplicativeGroupOps Y) f.
  Existing Class AdditiveSemiGroup_Morphism.
  Existing Class AdditiveMonoid_Morphism.
  Existing Class MultiplicativeSemiGroup_Morphism.
  Existing Class MultiplicativeMonoid_Morphism.

  Record Rg_Morphism {X Y} {Xplus:Plus X} {Yplus:Plus Y} {Xmult:Mult X} {Ymult:Mult Y} {Xzero:Zero X} {Yzero:Zero Y} (f : X ⇾ Y) : SProp :=
    { rgmor_plus_mor :> AdditiveMonoid_Morphism f
    ; rgmor_mult_mor :> MultiplicativeSemiGroup_Morphism f
    }.
  Existing Class Rg_Morphism.

  Record Rig_Morphism {X Y} {Xplus:Plus X} {Yplus:Plus Y} {Xmult:Mult X} {Ymult:Mult Y} {Xzero:Zero X} {Yzero:Zero Y} {Xone :One X}  {Yone :One  Y} (f : X ⇾ Y) : SProp :=
    { rigmor_plus_mor :> AdditiveMonoid_Morphism f
    ; rigmor_mult_mor :> MultiplicativeMonoid_Morphism f
    }.
  Existing Class Rig_Morphism.
End ring_morphism_classes.

Global Hint Extern 8 (Monoid_Morphism (X:=AdditiveGroupOps ?X) (Y:=AdditiveGroupOps ?Y) ?f)
  => change (AdditiveMonoid_Morphism (X:=X) (Y:=Y) f) : typeclass_instances.


Global Hint Extern 10 (SemiGroup ?X) =>
  match goal with
  | H : SemiGroup_Morphism (Y:=X) _ |- _ => exact (sgmor_b _ H)
  | H : Monoid_Morphism (Y:=X) _ |- _ => exact (sgmor_b _ H)
  end : typeclass_instances.

Global Hint Extern 10 (Monoid ?X) =>
  match goal with
  | H : Monoid_Morphism (Y:=X) _ |- _ => exact (monmor_b _ H)
  end : typeclass_instances.

Global Hint Extern 10 (Lattice ?X) =>
  match goal with
  | H : Lattice_Morphism (Y:=X) _ |- _ => exact (latmor_b _ H)
  end : typeclass_instances.
