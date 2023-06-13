Require Export interfaces.abstract_algebra interfaces.subset.

Local Open Scope grp_scope.
Local Notation e := mon_unit.

Record SubSemiGroup {G op} (H : 𝒫 G) : SProp :=
{ SubSemiGroup_sg :> @SemiGroup G op
; sub_sg_closed (x y : G) : x ∊ H ⊠ y ∊ H ⊸ x ∙ y ∊ H
}.
Existing Class SubSemiGroup.
Arguments sub_sg_closed {_ _} H {_} _ _.

Record SubMonoid {M op unit} (N : 𝒫 M) : SProp :=
{ SubMonoid_mon :> @Monoid M op unit
; SubMonoid_sub_sg :> SubSemiGroup N
; sub_mon_unit_closed : e ∊ N
}.
Existing Class SubMonoid.
Arguments sub_mon_unit_closed {_ _ _} N {_}.

Record SubGroup {G op unit inv} (H : 𝒫 G) : SProp :=
{ SubGroup_grp :> @Group G op unit inv
; SubGroup_sub_mon :> SubMonoid H
; sub_grp_inv_closed (x : G) : x ∊ H ⊸ x⁻¹ ∊ H
}.
Existing Class SubGroup.
Arguments sub_grp_inv_closed {_ _ _ _} H {_} _.

Record NormalSubGroup {G op unit inv} (H : 𝒫 G) : SProp :=
{ NormalSubGroup_sub_grp :> @SubGroup G op unit inv H
; normality (x : G) : x ∊ H ⊸ ∏ y : G, y ∙ x ∙ y⁻¹ ∊ H
}.
Existing Class NormalSubGroup.
Arguments normality {_ _ _ _} H {_} _.


Local Close Scope grp_scope.


Definition AdditiveSubSemiGroup : ∀ {X:set} {p:Plus X} (U : 𝒫 X), SProp := @SubSemiGroup.
Definition AdditiveSubMonoid : ∀ {X:set} {p:Plus X} {z:Zero X} (U : 𝒫 X), SProp := @SubMonoid.
Definition AdditiveSubGroup  : ∀ {X:set} {p:Plus X} {z:Zero X} {n:Negate X} (U : 𝒫 X), SProp := @SubGroup.
Definition AdditiveNormalSubGroup : ∀ {X:set} {p:Plus X} {z:Zero X} {n:Negate X} (U : 𝒫 X), SProp := @NormalSubGroup.

Definition MultiplicativeSubSemiGroup : ∀ {X:set} {m:Mult X} (U : 𝒫 X), SProp := @SubSemiGroup.
Definition MultiplicativeSubMonoid : ∀ {X:set} {m:Mult X} {o:One X} (U : 𝒫 X), SProp := @SubMonoid.

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

Definition sub_add_sg_closed : ∀ `{H:@AdditiveSubSemiGroup X p U} (x y : X), x ∊ U ⊠ y ∊ U ⊸ x + y ∊ U := @sub_sg_closed.
Definition sub_mul_sg_closed : ∀ `{H:@MultiplicativeSubSemiGroup X m U} (x y : X), x ∊ U ⊠ y ∊ U ⊸ x · y ∊ U := @sub_sg_closed.

Definition sub_add_zero_closed : ∀ `{H:@AdditiveSubMonoid X p z U}, 0 ∊ U := @sub_mon_unit_closed.
Definition sub_mul_one_closed : ∀ `{H:@MultiplicativeSubMonoid X m o U}, 1 ∊ U := @sub_mon_unit_closed.

Definition sub_add_neg_closed : ∀ `{H:@AdditiveSubGroup X p z n U} (x : X), x ∊ U ⊸ -x ∊ U := @sub_grp_inv_closed.


Record SubNearRg {R p m z} (S : 𝒫 R) : SProp :=
{ SubNearRg_near_rg :> @NearRg R p m z
; SubNearRg_sub_add_mon :> AdditiveSubMonoid S
; SubNearRg_sub_mul_sg :> MultiplicativeSubSemiGroup S
}.
Existing Class SubNearRg.

Record SubNearRig {R p m z o} (S : 𝒫 R) : SProp :=
{ SubNearRig_near_rig :> @NearRig R p m z o
; SubNearRig_sub_add_mon :> AdditiveSubMonoid S
; SubNearRig_sub_mul_mon :> MultiplicativeSubMonoid S
}.
Existing Class SubNearRig.

Record SubNearRng {R p m z n} (S : 𝒫 R) : SProp :=
{ SubNearRng_near_rng :> @NearRng R p m z n
; SubNearRng_sub_add_grp :> AdditiveSubGroup S
; SubNearRng_sub_mul_sg :> MultiplicativeSubSemiGroup S
}.
Existing Class SubNearRng.

Record SubNearRing {R p m z o n} (S : 𝒫 R) : SProp :=
{ SubNearRing_near_ring :> @NearRing R p m z o n
; SubNearRing_sub_add_grp :> AdditiveSubGroup S
; SubNearRing_sub_mul_mon :> MultiplicativeSubMonoid S
}.
Existing Class SubNearRing.

