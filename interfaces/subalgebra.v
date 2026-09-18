Require Export interfaces.abstract_algebra interfaces.subset.

Local Open Scope sg_op_scope.
Local Abbreviation e := mon_unit.

Record SubSemiGroup {G op} (H : 𝒫 G) : SProp :=
{ #[reversible=no] SubSemiGroup_sg :> @SemiGroup G op
; sub_sg_closed (x y : G) : x ∊ H ⊠ y ∊ H ⊸ x ∙ y ∊ H
}.
Existing Class SubSemiGroup.
Arguments sub_sg_closed {_ _} H {_} _ _.

Record SubMonoid {M op unit} (N : 𝒫 M) : SProp :=
{ #[reversible=no] SubMonoid_mon :> @Monoid M op unit
; #[reversible=no] SubMonoid_sub_sg :> SubSemiGroup N
; sub_mon_unit_closed : e ∊ N
}.
Existing Class SubMonoid.
Arguments sub_mon_unit_closed {_ _ _} N {_}.

Local Open Scope star_scope.
Record SubStarSemiGroup {G op inv} (H : 𝒫 G) : SProp :=
{ #[reversible=no] SubStarSemiGroup_ssg :> @StarSemiGroup G op inv
; #[reversible=no] SubStarSemiGroup_sub_sg :> SubSemiGroup H
; sub_inv_closed (x : G) : x ∊ H ⊸ x* ∊ H
}.
Existing Class SubStarSemiGroup.
Arguments sub_inv_closed {_ _ _} H {_} _.
Local Close Scope star_scope.

Record SubStarMonoid {M op unit inv} (N : 𝒫 M) : SProp :=
{ #[reversible=no] SubStarMonoid_ssg :> @StarMonoid M op unit inv
; #[reversible=no] SubStarMonoid_sub_mon :> SubMonoid N
; #[reversible=no] SubStarMonoid_sub_ssg :> SubStarSemiGroup N
}.
Existing Class SubStarMonoid.

Record SubGroup {G op unit inv} (H : 𝒫 G) : SProp :=
{ #[reversible=no] SubGroup_grp :> @Group G op unit inv
; #[reversible=no] SubGroup_sub_sm :> SubStarMonoid H
}.
Existing Class SubGroup.

Local Open Scope grp_scope.
Record NormalSubGroup {G op unit inv} (H : 𝒫 G) : SProp :=
{ #[reversible=no] NormalSubGroup_sub_grp :> @SubGroup G op unit inv H
; normality (x : G) : x ∊ H ⊸ ∏ y : G, y ∙ x ∙ y⁻¹ ∊ H
}.
Existing Class NormalSubGroup.
Arguments normality {_ _ _ _} H {_} _.


Local Close Scope grp_scope.


(** Rings *)

Definition AdditiveSubSemiGroup@{u} : ∀ {X:set@{u}} {p:Plus X} (U : 𝒫 X), SProp := @SubSemiGroup.
Definition AdditiveSubMonoid@{u} : ∀ {X:set@{u}} {p:Plus X} {z:Zero X} (U : 𝒫 X), SProp := @SubMonoid.
Definition AdditiveSubGroup@{u}  : ∀ {X:set@{u}} {p:Plus X} {z:Zero X} {n:Negate X} (U : 𝒫 X), SProp := @SubGroup.
Definition AdditiveNormalSubGroup@{u} : ∀ {X:set@{u}} {p:Plus X} {z:Zero X} {n:Negate X} (U : 𝒫 X), SProp := @NormalSubGroup.

Definition MultiplicativeSubSemiGroup@{u} : ∀ {X:set@{u}} {m:Mult X} (U : 𝒫 X), SProp := @SubSemiGroup.
Definition MultiplicativeSubMonoid@{u} : ∀ {X:set@{u}} {m:Mult X} {o:One X} (U : 𝒫 X), SProp := @SubMonoid.

Existing Class AdditiveSubSemiGroup.
Existing Class AdditiveSubMonoid.
Existing Class AdditiveSubGroup.
Existing Class AdditiveNormalSubGroup.
Existing Class MultiplicativeSubSemiGroup.
Existing Class MultiplicativeSubMonoid.

Coercion AdditiveSubMonoid_sg `{H:@AdditiveSubMonoid X p z U} : AdditiveSubSemiGroup U := H.
Coercion AdditiveSubGroup_sub_mon `{H:@AdditiveSubGroup X p z n U} : AdditiveSubMonoid U := H.
Coercion AdditiveNormalSubGroup_sub_grp `{H:@AdditiveNormalSubGroup X p z n U} : AdditiveSubGroup U := H.

Coercion AdditiveSubSemiGroup_sg `{H:@AdditiveSubSemiGroup X p U} : AdditiveNonComSemiGroup X := @SubSemiGroup_sg _ _ _ H.
Coercion AdditiveSubMonoid_mon `{H:@AdditiveSubMonoid X p z U} : AdditiveNonComMonoid X := H.
Coercion AdditiveSubGroup_grp `{H:@AdditiveSubGroup X p z n U} : AdditiveNonComGroup X := H.

Coercion MultiplicativeSubMonoid_sg `{H:@MultiplicativeSubMonoid X m o U} : MultiplicativeSubSemiGroup U := H.

Coercion MultiplicativeSubSemiGroup_sg `{H:@MultiplicativeSubSemiGroup X m U} : MultiplicativeSemiGroup X := @SubSemiGroup_sg _ _ _ H.
Coercion MultiplicativeSubMonoid_mon `{H:@MultiplicativeSubMonoid X m o U} : MultiplicativeMonoid X := H.

Local Open Scope mult_scope.

Definition sub_add_sg_closed@{u} : ∀ `{H:@AdditiveSubSemiGroup@{u} X p U} (x y : X), x ∊ U ⊠ y ∊ U ⊸ x + y ∊ U := @sub_sg_closed.
Definition sub_mul_sg_closed@{u} : ∀ `{H:@MultiplicativeSubSemiGroup@{u} X m U} (x y : X), x ∊ U ⊠ y ∊ U ⊸ x · y ∊ U := @sub_sg_closed.

Definition sub_add_zero_closed@{u} : ∀ `{H:@AdditiveSubMonoid@{u} X p z U}, 0 ∊ U := @sub_mon_unit_closed.
Definition sub_mul_one_closed@{u} : ∀ `{H:@MultiplicativeSubMonoid@{u} X m o U}, 1 ∊ U := @sub_mon_unit_closed.

Definition sub_add_neg_closed@{u} `{H:@AdditiveSubGroup@{u} X p z n U} (x : X) : x ∊ U ⊸ -x ∊ U := sub_inv_closed _ _.


Record SubNearRg {R p m z} (S : 𝒫 R) : SProp :=
{ #[reversible=no] SubNearRg_near_rg :> @NearRg R p m z
; #[reversible=no] SubNearRg_sub_add_mon :> AdditiveSubMonoid S
; #[reversible=no] SubNearRg_sub_mul_sg :> MultiplicativeSubSemiGroup S
}.
Existing Class SubNearRg.

Record SubNearRig {R p m z o} (S : 𝒫 R) : SProp :=
{ #[reversible=no] SubNearRig_near_rig :> @NearRig R p m z o
; #[reversible=no] SubNearRig_sub_add_mon :> AdditiveSubMonoid S
; #[reversible=no] SubNearRig_sub_mul_mon :> MultiplicativeSubMonoid S
}.
Existing Class SubNearRig.

Record SubNearRng {R p m z n} (S : 𝒫 R) : SProp :=
{ #[reversible=no] SubNearRng_near_rng :> @NearRng R p m z n
; #[reversible=no] SubNearRng_sub_add_grp :> AdditiveSubGroup S
; #[reversible=no] SubNearRng_sub_mul_sg :> MultiplicativeSubSemiGroup S
}.
Existing Class SubNearRng.

Record SubNearRing {R p m z o n} (S : 𝒫 R) : SProp :=
{ #[reversible=no] SubNearRing_near_ring :> @NearRing R p m z o n
; #[reversible=no] SubNearRing_sub_add_grp :> AdditiveSubGroup S
; #[reversible=no] SubNearRing_sub_mul_mon :> MultiplicativeSubMonoid S
}.
Existing Class SubNearRing.


(** Lattices *)

Definition MeetSubSemiLattice@{u} : ∀ {L:set@{u}} {m:Meet L} (U : 𝒫 L), SProp := @SubSemiGroup.
Definition MeetSubBoundedSemiLattice@{u} : ∀ {L:set@{u}} {m:Meet L} {t:Top L} (U : 𝒫 L), SProp := @SubMonoid.
Definition JoinSubSemiLattice@{u} : ∀ {L:set@{u}} {j:Join L} (U : 𝒫 L), SProp := @SubSemiGroup.
Definition JoinSubBoundedSemiLattice@{u} : ∀ {L:set@{u}} {j:Join L} {b:Bottom L} (U : 𝒫 L), SProp := @SubMonoid.

Existing Class MeetSubSemiLattice.
Existing Class MeetSubBoundedSemiLattice.
Existing Class JoinSubSemiLattice.
Existing Class JoinSubBoundedSemiLattice.

Coercion MeetSubBoundedSemiLattice_sl `{H:@MeetSubBoundedSemiLattice L m t U} : MeetSubSemiLattice U := H.
Coercion JoinSubBoundedSemiLattice_sl `{H:@JoinSubBoundedSemiLattice L j b U} : JoinSubSemiLattice U := H.

Definition sub_meet_closed@{u} : ∀ `{H:@MeetSubSemiLattice@{u} L m U} (x y : L), x ∊ U ⊠ y ∊ U ⊸ x ⊓ y ∊ U := @sub_sg_closed.
Definition sub_join_closed@{u} : ∀ `{H:@JoinSubSemiLattice@{u} L j U} (x y : L), x ∊ U ⊠ y ∊ U ⊸ x ⊔ y ∊ U := @sub_sg_closed.
Definition sub_top_closed@{u} : ∀ `{H:@MeetSubBoundedSemiLattice@{u} L m t U}, ⊤ ∊ U := @sub_mon_unit_closed.
Definition sub_bot_closed@{u} : ∀ `{H:@JoinSubBoundedSemiLattice@{u} L j b U}, ⊥ ∊ U := @sub_mon_unit_closed.

Record SubLattice {L m j} (U : 𝒫 L) : SProp :=
{ #[reversible=no] SubLattice_lattice :> @Lattice L m j
; #[reversible=no] SubLattice_meet :> MeetSubSemiLattice U
; #[reversible=no] SubLattice_join :> JoinSubSemiLattice U
}.
Existing Class SubLattice.

