Require Export theory.common_props theory.pointed.
Require Import abstract_algebra theory.groups.
Require Import easy rewrite.
Require Import quote.base strip_coercions.

Local Notation add_ops := AdditiveGroupOps.

Global Hint Extern 2 (@AdditiveNonComSemiGroup (ring_op ?M) ?p) => change (@AdditiveNonComSemiGroup M p) : typeclass_instances.
Global Hint Extern 2 (@AdditiveNonComMonoid (ring_op ?M) ?p ?z) => change (@AdditiveNonComMonoid M p z) : typeclass_instances.
Global Hint Extern 2 (@AdditiveNonComGroup  (ring_op ?M) ?p ?z) => change (@AdditiveNonComGroup  M p z) : typeclass_instances.
Global Hint Extern 2 (@AdditiveSemiGroup (ring_op ?M) ?p   ) => change (@AdditiveSemiGroup M p ) : typeclass_instances.
Global Hint Extern 2 (@AdditiveMonoid (ring_op ?M) ?p ?z   ) => change (@AdditiveMonoid M p z  ) : typeclass_instances.
Global Hint Extern 2 (@AdditiveGroup  (ring_op ?M) ?p ?z ?n) => change (@AdditiveGroup  M p z n) : typeclass_instances.

Definition Build_AdditiveNonComSemiGroup `{Plus M} (H:@Associative M (+)) : AdditiveNonComSemiGroup M := H.

Definition alt_Build_AdditiveSemiGroup : ∀ `{Plus M},
   @Associative M (+)
 → Commutative (X:=M) (+)
 → AdditiveSemiGroup M
:= @alt_Build_CommutativeSemiGroup.

Definition alt_Build_AdditiveNonComMonoid : ∀ `{Plus M} `{Zero M},
   @Associative M (+)
 → LeftIdentity  (X:=M) (+) 0
 → RightIdentity  (X:=M) (+) 0
 → AdditiveNonComMonoid M
:= @alt_Build_Monoid.

Definition alt_Build_AdditiveMonoid : ∀ `{Plus M} `{Zero M},
   @Associative M (+)
 → Commutative (X:=M) (+)
 → LeftIdentity  (X:=M) (+) 0
 → AdditiveMonoid M
:= @alt_Build_CommutativeMonoid.

Definition alt_Build_AdditiveNonComGroup : ∀ `{Plus G} `{Zero G} `{Negate G},
   @Associative G (+)
 → LeftIdentity (X:=G) (+) 0
 → RightIdentity (X:=G) (+) 0
 → LeftInverse  (X:=G) (+) (-) 0
 → RightInverse  (X:=G) (+) (-) 0
 → AdditiveNonComGroup G
:= @alt_Build_Group.

Definition alt_Build_AdditiveGroup : ∀ `{Plus G} `{Zero G} `{Negate G},
   @Associative G (+)
 → Commutative  (X:=G) (+)
 → LeftIdentity (X:=G) (+) 0
 → LeftInverse  (X:=G) (+) (-) 0
 → AdditiveGroup G
:= @alt_Build_AbGroup.

Coercion additive_sg_nc_sg `{H:AdditiveSemiGroup R} : AdditiveNonComSemiGroup R := @comsg_sg _ _ H.
Coercion additive_nc_mon_sg `{H:AdditiveNonComMonoid R} : AdditiveNonComSemiGroup R := @monoid_semigroup _ _ _ H.
Coercion additive_monoid_nc_monoid `{H:AdditiveMonoid R} : AdditiveNonComMonoid R := H.
Coercion additive_monoid_sg `{H:AdditiveMonoid R} : AdditiveSemiGroup R := H.
Coercion additive_nc_group_nc_monoid `{H:AdditiveNonComGroup R} : AdditiveNonComMonoid R := H.
Coercion additive_group_monoid `{H:AdditiveGroup R} : AdditiveMonoid R := H.
Coercion additive_group_nc_group `{H:AdditiveGroup R} : AdditiveNonComGroup R := H.

Lemma plus_ass `{AdditiveNonComSemiGroup R} : Associative   (X:=R) (+).   Proof _ : SemiGroup (add_ops R).
Lemma plus_0_l `{AdditiveNonComMonoid    R} : LeftIdentity  (X:=R) (+) 0. Proof monoid_left_id  (add_ops R) _.
Lemma plus_0_r `{AdditiveNonComMonoid    R} : RightIdentity (X:=R) (+) 0. Proof monoid_right_id (add_ops R) _.

Lemma plus_com `{AdditiveSemiGroup R} : Commutative (X:=R) (+).  Proof comsg_com (add_ops R) _.

Global Hint Extern 2 (Inverse (@negate ?G ?f)) => notypeclasses refine (@negate G f) : typeclass_instances.

Lemma plus_negate_l     `{AdditiveNonComGroup R} : LeftInverse  (X:=R) (+) (-) 0.  Proof inverse_l (X:=add_ops R).
Lemma plus_negate_r     `{AdditiveNonComGroup R} : RightInverse (X:=R) (+) (-) 0.  Proof inverse_r (X:=add_ops R).
Lemma negate_involutive `{AdditiveNonComGroup R} : Involutive   (X:=R) (-).        Proof inverse_involutive (G:=add_ops R).
Lemma negate_plus_distr `{AdditiveGroup R} : ∀ x y : R, -(x + y) = -x - y.  Proof inverse_distr_ab (G:=add_ops R).
Lemma negate_plus_distr_alt `{AdditiveNonComGroup R} : ∀ x y : R, -(x + y) = -y - x.  Proof inverse_distr (G:=add_ops R).

Lemma negate_mon_mor `{AdditiveGroup G} : AdditiveMonoid_Morphism (@negate G _).
Proof abgrp_inverse_mor.
Global Hint Extern 2 (AdditiveMonoid_Morphism (-)) => simple notypeclasses refine negate_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (-)) => simple notypeclasses refine negate_mon_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (-)) => simple notypeclasses refine negate_mon_mor : typeclass_instances.


Global Hint Extern 2 (Associative   (+)    ) => simple notypeclasses refine plus_ass   : typeclass_instances.
Global Hint Extern 2 (Commutative   (+)    ) => simple notypeclasses refine plus_com   : typeclass_instances.
Global Hint Extern 2 (LeftIdentity  (+) _  ) => notypeclasses refine plus_0_l          : typeclass_instances.
Global Hint Extern 2 (RightIdentity (+) _  ) => notypeclasses refine plus_0_r          : typeclass_instances.
Global Hint Extern 2 (LeftInverse   (+) _ _) => notypeclasses refine plus_negate_l     : typeclass_instances.
Global Hint Extern 2 (RightInverse  (+) _ _) => notypeclasses refine plus_negate_r     : typeclass_instances.
Global Hint Extern 2 (Involutive    (-)    ) => notypeclasses refine negate_involutive : typeclass_instances.
Global Hint Extern 2 (Bijective     (-)    ) => notypeclasses refine negate_involutive : typeclass_instances.
Global Hint Extern 2 (Injective     (-)    ) => notypeclasses refine negate_involutive : typeclass_instances.
Global Hint Extern 2 (Surjective    (-)    ) => notypeclasses refine negate_involutive : typeclass_instances.

Lemma alt_Build_AdditiveCancellation `{AdditiveSemiGroup R} :
  (∀ z : R, Injective (z +)) → AdditiveCancellation R.
Proof. intro; split; trivial. now apply right_cancel_from_left. Defined.

Lemma add_group_cancel `{AdditiveNonComGroup R} : AdditiveCancellation R.
Proof. split.
+ exact (group_left_op_inj (G:=add_ops R)).
+ exact (group_right_op_inj (G:=add_ops R)).
Qed.
Coercion add_group_cancel : AdditiveNonComGroup >-> AdditiveCancellation.

Arguments add_cancel_l {_ _ _} _.
Arguments add_cancel_r {_ _ _} _.
Global Hint Extern 2 (Injective (_ +)) => simple notypeclasses refine (add_cancel_l _) : typeclass_instances.
Global Hint Extern 2 (Injective (+ _)) => simple notypeclasses refine (add_cancel_r _) : typeclass_instances.

Definition negate_0          `{AdditiveNonComGroup G} :       -0 = 0 :> G.  Proof inverse_unit (G:=add_ops G).
Definition negate_swap_r     `{AdditiveNonComGroup G} : ∀ x y : G,  x - y = -(y - x). Proof inverse_swap_r (G:=add_ops G).
Definition negate_swap_l     `{AdditiveGroup       G} : ∀ x y : G, -x + y = -(x - y). Proof inverse_swap_l_ab (G:=add_ops G).
Definition equal_by_zero_sum `{AdditiveNonComGroup G} : ∀ x y : G, x - y = 0 ⧟ x = y.  Proof equal_by_inverse (G:=add_ops G).
Definition flip_negate       `{AdditiveNonComGroup G} : ∀ x y : G, -x = y ⧟ x = -y.  Proof flip_inverse (G:=add_ops G).
Definition flip_negate_0     `{AdditiveNonComGroup G} : ∀ x y : G, -x = 0 ⧟ x = 0.  Proof flip_inverse_unit (G:=add_ops G).

Lemma plus_2_2 `{AdditiveNonComSemiGroup M} `{One M} : 2 + 2 = 4 :> M.
Proof. sym. exact (associativity _ _ _ _). Qed.

Definition add_monmor_sgmor : ∀ `{H:@AdditiveMonoid_Morphism X Y pX zX pY zY f}, AdditiveSemiGroup_Morphism f := @monmor_sgmor.
Coercion add_monmor_sgmor : AdditiveMonoid_Morphism >-> AdditiveSemiGroup_Morphism.

Canonical Structure AdditiveSemiGroup_Morphism_fun {X Y pX pY}
  := make_fun_alt (@AdditiveSemiGroup_Morphism X Y pX pY) (@SemiGroup_Morphism_fun X Y pX pY).

Canonical Structure AdditiveMonoid_Morphism_fun {X Y pX zX pY zY}
  := make_fun_alt (@AdditiveMonoid_Morphism X Y pX zX pY zY) (@Monoid_Morphism_fun X Y pX zX pY zY).

Definition preserves_plus `{AdditiveSemiGroup_Morphism (f:=f)} : ∀ x y, f (x+y) = f x + f y := preserves_sg_op (f:add_ops _ ⇾ add_ops _).
Arguments preserves_plus {_ _ _ _} f {_} x y.

Coercion AdditiveMonoid_Morphism_pointed `{AdditiveMonoid_Morphism (f:=f)} : Zero_Pointed_Morphism f := monmor_pointed f _.

Definition preserves_negate `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y} (f:X ⇾ Y) `{!AdditiveSemiGroup_Morphism f}
  x : f (-x) = -(f x) 
:= preserves_inverse (f:add_ops X ⇾ add_ops Y) _.

Definition preserves_minus `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y} (f:X ⇾ Y) `{!AdditiveSemiGroup_Morphism f}
  x y : f (x - y) = f x - f y
:= preserves_op_inverse_r (f:add_ops X ⇾ add_ops Y) _ _.

Definition id_addsg_mor `{AdditiveNonComSemiGroup M} : AdditiveSemiGroup_Morphism (id_fun M) := id_semigroup_mor (G:=add_ops M).
Definition id_addmon_mor `{AdditiveNonComMonoid M} : AdditiveMonoid_Morphism (id_fun M) := id_monoid_mor (M:=add_ops M).
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (id_fun _)) => simple notypeclasses refine id_addsg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (id_fun _)) => simple notypeclasses refine id_addmon_mor : typeclass_instances.

Definition compose_addsg_mor : ∀ {X Y Z} {op₁} {op₂} {op₃} {g f},
  @AdditiveSemiGroup_Morphism X Y op₁ op₂ f → @AdditiveSemiGroup_Morphism Y Z op₂ op₃ g
  → AdditiveSemiGroup_Morphism (g ∘ f)
:= @compose_semigroup_mor.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_addsg_mor _ _) : typeclass_instances.

Definition compose_addmon_mor : ∀ {X Y Z} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @AdditiveMonoid_Morphism X Y op₁ e₁ op₂ e₂ f → @AdditiveMonoid_Morphism Y Z op₂ e₂ op₃ e₃ g
  → AdditiveMonoid_Morphism (g ∘ f)
:= @compose_monoid_mor.
Global Hint Extern 2 (AdditiveMonoid_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_addmon_mor _ _) : typeclass_instances.

Local Open Scope fun_inv_scope.
Definition invert_addsg_mor `{AdditiveSemiGroup_Morphism (f:=f)} `{!Inverse f} `{!Bijective f}
  : AdditiveSemiGroup_Morphism f⁻¹
:= invert_semigroup_mor.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (_⁻¹)) => simple notypeclasses refine invert_addsg_mor : typeclass_instances.

Definition invert_addmon_mor `{AdditiveMonoid_Morphism (f:=f)} `{!Inverse f} `{!Bijective f}
  : AdditiveMonoid_Morphism f⁻¹
:= invert_monoid_mor.
Global Hint Extern 2 (AdditiveMonoid_Morphism (_⁻¹)) => simple notypeclasses refine invert_addmon_mor : typeclass_instances.

Definition alt_Build_AdditiveSemiGroup_Morphism 
 `{AdditiveNonComSemiGroup X} `{AdditiveNonComSemiGroup Y} {f : X ⇾ Y}
  : (∀ x y : X, f (x + y) = f x + f y)
 → AdditiveSemiGroup_Morphism f
:= λ P, Build_SemiGroup_Morphism (f:add_ops X ⇾ add_ops Y) P.

Definition alt_Build_AdditiveMonoid_Morphism :
  ∀ `{AdditiveNonComMonoid X} `{AdditiveNonComMonoid Y} {f : X ⇾ Y},
  (∀ x y : X, f (x + y) = f x + f y)
 → f 0 = 0
 → AdditiveMonoid_Morphism f
:= @alt_Build_Monoid_Morphism.

Lemma Build_AdditiveGroup_Morphism `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y} (f:X ⇾ Y) :
  (∀ x y, f (x + y) = f x + f y)
  → AdditiveMonoid_Morphism f.
Proof. intro. refine (group_mor (f:add_ops X ⇾ add_ops Y)). now split. Defined.


Definition projected_additive_non_com_monoid :
  ∀ `{AdditiveNonComMonoid M} `(f:X ⇾ M) `{!Injective f} `{Plus X} `{Zero X},
   (∀ x y, f (x + y) = f x + f y)
   → f 0 = 0
   → AdditiveNonComMonoid X
  := @projected_monoid.

Definition projected_additive_monoid :
  ∀ `{AdditiveMonoid M} `(f:X ⇾ M) `{!Injective f} `{Plus X} `{Zero X},
   (∀ x y, f (x + y) = f x + f y)
   → f 0 = 0
   → AdditiveMonoid X
  := @projected_commutative_monoid.

Definition projected_additive_non_com_group :
  ∀ `{AdditiveNonComGroup G} `(f:X ⇾ G) `{!Injective f} `{Plus X} `{Zero X} `{Negate X},
   (∀ x y, f (x + y) = f x + f y)
   → f 0 = 0
   → (∀ x, f (-x) = -(f x))
   → AdditiveNonComGroup X
  := @projected_group.

Definition projected_additive_group :
  ∀ `{AdditiveGroup G} `(f:X ⇾ G) `{!Injective f} `{Plus X} `{Zero X} `{Negate X},
   (∀ x y, f (x + y) = f x + f y)
   → f 0 = 0
   → (∀ x, f (-x) = -(f x))
   → AdditiveGroup X
  := @projected_abgroup.


Section quote.
  Universes i.
  Context `(f:X ⇾ Y) `{AdditiveSemiGroup_Morphism@{i} (X:=X) (Y:=Y) (f:=f)}.

  Lemma quote_plus_alt {x₁ y₁ x₂ y₂} :
    quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ + x₂) (y₁ + y₂).
  Proof quote_sg_op_alt (f:add_ops _ ⇾ add_ops _).

  Lemma quote_negate_alt `{Zero X} `{Zero Y} `{Negate X} `{Negate Y} `{!AdditiveNonComGroup X} `{!AdditiveNonComGroup Y} {x y} :
    quote f x y → quote f (-x) (-y).
  Proof quote_inverse_alt (f:add_ops _ ⇾ add_ops _).
End quote.

Global Hint Extern 4 (quote _ (_ + _) _) => quote_hint_strip (fun f => refine (quote_plus_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ + _)) => quote_hint_strip (fun f => refine (quote_plus_alt f _ _)) : quote.

Global Hint Extern 4 (quote _ (-_) _) => quote_hint_strip (fun f => refine (quote_negate_alt f _)) : quote.
Global Hint Extern 4 (quote _ _ (-_)) => quote_hint_strip (fun f => refine (quote_negate_alt f _)) : quote.

