Require Import interfaces.sprop.
Require Export theory.common_props theory.pointed.
Require Import abstract_algebra theory.groups.
Require Import easy rewrite.
Require Import quote.base strip_coercions simplify.

Local Abbreviation add_ops := AdditiveGroupOps.

Global Hint Extern 2 (@AdditiveNonComSemiGroup (ring_op ?M) ?p) => change (@AdditiveNonComSemiGroup M p) : typeclass_instances.
Global Hint Extern 2 (@AdditiveNonComMonoid (ring_op ?M) ?p ?z) => change (@AdditiveNonComMonoid M p z) : typeclass_instances.
Global Hint Extern 2 (@AdditiveNonComGroup  (ring_op ?M) ?p ?z) => change (@AdditiveNonComGroup  M p z) : typeclass_instances.
Global Hint Extern 2 (@AdditiveSemiGroup (ring_op ?M) ?p   ) => change (@AdditiveSemiGroup M p ) : typeclass_instances.
Global Hint Extern 2 (@AdditiveMonoid (ring_op ?M) ?p ?z   ) => change (@AdditiveMonoid M p z  ) : typeclass_instances.
Global Hint Extern 2 (@AdditiveGroup  (ring_op ?M) ?p ?z ?n) => change (@AdditiveGroup  M p z n) : typeclass_instances.

Definition Build_AdditiveNonComSemiGroup `{Plus M} (H:@Associative M (+)) : AdditiveNonComSemiGroup M := H.

Definition alt_Build_AdditiveSemiGroup@{u} : ∀ {M:set@{u}} `{Plus M},
   @Associative M (+)
 → Commutative (X:=M) (+)
 → AdditiveSemiGroup M
:= @alt_Build_CommutativeSemiGroup.

Definition alt_Build_AdditiveNonComMonoid@{u} : ∀ {M:set@{u}} `{Plus M} `{Zero M},
   @Associative M (+)
 → LeftIdentity  (X:=M) (+) 0
 → RightIdentity  (X:=M) (+) 0
 → AdditiveNonComMonoid M
:= @alt_Build_Monoid.

Definition alt_Build_AdditiveMonoid@{u} : ∀ {M:set@{u}} `{Plus M} `{Zero M},
   @Associative M (+)
 → Commutative (X:=M) (+)
 → LeftIdentity  (X:=M) (+) 0
 → AdditiveMonoid M
:= @alt_Build_CommutativeMonoid.

Definition alt_Build_AdditiveNonComGroup@{u} : ∀ {G:set@{u}} `{Plus G} `{Zero G} `{Negate G},
   @Associative G (+)
 → LeftIdentity (X:=G) (+) 0
 → RightIdentity (X:=G) (+) 0
 → LeftInverse  (X:=G) (+) (-) 0
 → RightInverse  (X:=G) (+) (-) 0
 → AdditiveNonComGroup G
:= @alt_Build_Group.

Definition alt_Build_AdditiveGroup@{u} : ∀ {G:set@{u}} `{Plus G} `{Zero G} `{Negate G},
   @Associative G (+)
 → Commutative  (X:=G) (+)
 → LeftIdentity (X:=G) (+) 0
 → LeftInverse  (X:=G) (+) (-) 0
 → AdditiveGroup G
:= @alt_Build_AbGroup.

Coercion zero_inhabited `{Zero M} : Inhabited M.  Proof. now exists 0. Defined.
Coercion add_nc_mon_inhabited `{AdditiveNonComMonoid M} : Inhabited M := _.

Coercion additive_sg_nc_sg `{H:AdditiveSemiGroup R} : AdditiveNonComSemiGroup R := @comsg_sg _ _ H.
Coercion additive_nc_mon_sg `{H:AdditiveNonComMonoid R} : AdditiveNonComSemiGroup R := @monoid_semigroup _ _ _ H.
Coercion additive_monoid_nc_monoid `{H:AdditiveMonoid R} : AdditiveNonComMonoid R := H.
Coercion additive_monoid_sg `{H:AdditiveMonoid R} : AdditiveSemiGroup R := H.
Coercion additive_nc_group_nc_monoid `{H:AdditiveNonComGroup R} : AdditiveNonComMonoid R := H.
Coercion additive_group_monoid `{H:AdditiveGroup R} : AdditiveMonoid R := H.
Coercion additive_group_nc_group `{H:AdditiveGroup R} : AdditiveNonComGroup R := H.

Lemma plus_ass `{AdditiveNonComSemiGroup R} : Associative   (X:=R) (+).   Proof. exact (_ : SemiGroup (add_ops R)). Qed.
Lemma plus_0_l `{AdditiveNonComMonoid    R} : LeftIdentity  (X:=R) (+) 0. Proof. exact (monoid_left_id  (X:=add_ops R)). Qed.
Lemma plus_0_r `{AdditiveNonComMonoid    R} : RightIdentity (X:=R) (+) 0. Proof. exact (monoid_right_id (X:=add_ops R)). Qed.

Lemma plus_com `{AdditiveSemiGroup R} : Commutative (X:=R) (+).  Proof. exact (comsg_com (add_ops R) _). Qed.

Global Hint Extern 2 (Inverse (@negate ?G ?f)) => notypeclasses refine (@negate G f) : typeclass_instances.

Lemma plus_negate_l     `{AdditiveNonComGroup R} : LeftInverse  (X:=R) (+) (-) 0.  Proof. exact (inverse_l (X:=add_ops R)). Qed.
Lemma plus_negate_r     `{AdditiveNonComGroup R} : RightInverse (X:=R) (+) (-) 0.  Proof. exact (inverse_r (X:=add_ops R)). Qed.
Lemma negate_involutive `{AdditiveNonComGroup R} : Involutive   (X:=R) (-).        Proof. exact (inv_involutive (X:=add_ops R)). Qed.
Lemma negate_plus_distr `{AdditiveGroup R} : ∀ x y : R, -(x + y) = -x - y.  Proof. exact (inv_distr_ab (G:=add_ops R)). Qed.
Lemma negate_plus_distr_alt `{AdditiveNonComGroup R} : ∀ x y : R, -(x + y) = -y - x.  Proof. exact (inv_distr (G:=add_ops R)). Qed.

Lemma negate_mon_mor `{AdditiveGroup G} : AdditiveMonoid_Morphism (@negate G _).
Proof. exact inv_com_mon_mor. Qed.
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


(** Simplification *)
Local Ltac simplify_chain tm := match goal with |- SimplifiesTo ?x ?y => change (SimplifiesToR (x,y)); trans tm end.

Lemma simplify_plus_zero_l `{AdditiveNonComMonoid M} {x x':M} `{!SimplifiesTo x x'} : SimplifiesTo (0 + x) x'.
Proof. simplify_chain x; trivial; split. exact (plus_0_l _). Qed.
Global Hint Extern 2 (SimplifiesTo (0 + _) _) => notypeclasses refine simplify_plus_zero_l : typeclass_instances.

Lemma simplify_plus_zero_r `{AdditiveNonComMonoid M} {x x':M} `{!SimplifiesTo x x'} : SimplifiesTo (x + 0) x'.
Proof. simplify_chain x; trivial; split. exact (plus_0_r _). Qed.
Global Hint Extern 2 (SimplifiesTo (_ + 0) _) => notypeclasses refine simplify_plus_zero_r : typeclass_instances.

Global Hint Extern 4 (SimplifiesTo (-(?x) + ?y) _) => match x with y => solve_simplify (plus_negate_l x) end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (?x - ?y) _) => match x with y => solve_simplify (plus_negate_r x) end : typeclass_instances.

Definition simplify_plus_inv_l_3 `{AdditiveNonComGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (y - x + x) y' := simplify_group_inv_l_3.
Definition simplify_plus_inv_r_3 `{AdditiveNonComGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (y + x - x) y' := simplify_group_inv_r_3.
Definition simplify_plus_assoc_inv_l_3 `{AdditiveNonComGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (-x + (x + y)) y' := simplify_group_assoc_inv_l_3.
Definition simplify_plus_assoc_inv_r_3 `{AdditiveNonComGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x + (-x + y)) y' := simplify_group_assoc_inv_r_3.
Definition simplify_abplus_inv_l_3 `{AdditiveGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (-x + y + x) y' := simplify_abgroup_inv_l_3.
Definition simplify_abplus_inv_r_3 `{AdditiveGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x + y - x) y' := simplify_abgroup_inv_r_3.
Definition simplify_abplus_assoc_inv_l_3 `{AdditiveGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (-x + (y + x)) y' := simplify_abgroup_assoc_inv_l_3.
Definition simplify_abplus_assoc_inv_r_3 `{AdditiveGroup G} {x y y' : G} `{!SimplifiesTo y y'} : SimplifiesTo (x + (y - x)) y' := simplify_abgroup_assoc_inv_r_3.

Global Hint Extern 4 (SimplifiesTo (_ - ?x + ?y) _) => match x with y => notypeclasses refine simplify_plus_inv_l_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (_ + ?x - ?y) _) => match x with y => notypeclasses refine simplify_plus_inv_r_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (- ?x + (?y + _)) _) => match x with y => notypeclasses refine simplify_plus_assoc_inv_l_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (?x + (- ?y + _)) _) => match x with y => notypeclasses refine simplify_plus_assoc_inv_r_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (-?x + _ + ?y) _) => match x with y => notypeclasses refine simplify_abplus_inv_l_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (?x + _ - ?y) _) => match x with y => notypeclasses refine simplify_abplus_inv_r_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (-?x + (_ + ?y)) _) => match x with y => notypeclasses refine simplify_abplus_assoc_inv_l_3 end : typeclass_instances.
Global Hint Extern 4 (SimplifiesTo (?x + (_ - ?y)) _) => match x with y => notypeclasses refine simplify_abplus_assoc_inv_r_3 end : typeclass_instances.

Lemma simplify_negate_involutive `{AdditiveNonComGroup G} {x x' : G} `{!SimplifiesTo x x'} : SimplifiesTo (--x) (x').
Proof. simplify_chain x; trivial; split. exact (negate_involutive _). Qed.
Global Hint Extern 4 (SimplifiesTo (-- _) _) => notypeclasses refine simplify_negate_involutive : typeclass_instances.


Lemma alt_Build_AdditiveCancellation `{AdditiveSemiGroup R} :
  (∀ z : R, Injective (z +)) → AdditiveCancellation R.
Proof. intro; split; trivial. now apply right_cancel_from_left. Defined.

Lemma add_group_cancel `{AdditiveNonComGroup R} : AdditiveCancellation R.
Proof. split.
+ exact (group_left_op_inj (G:=add_ops R)).
+ exact (group_right_op_inj (G:=add_ops R)).
Qed.
Coercion add_group_cancel : AdditiveNonComGroup >-> AdditiveCancellation.

Definition negate_0          `{AdditiveNonComGroup G} :       -0 = 0 :> G.  Proof. exact (inv_unit (G:=add_ops G)). Qed.
Definition negate_swap_r     `{AdditiveNonComGroup G} : ∀ x y : G,  x - y = -(y - x). Proof. exact (inv_swap_r (G:=add_ops G)). Qed.
Definition negate_swap_l     `{AdditiveGroup       G} : ∀ x y : G, -x + y = -(x - y). Proof. exact (inv_swap_l_ab (G:=add_ops G)). Qed.
Definition equal_by_zero_sum `{AdditiveNonComGroup G} : ∀ x y : G, x - y = 0 ⧟ x = y.  Proof. exact (equal_by_inverse (G:=add_ops G)). Qed.
Definition flip_negate       `{AdditiveNonComGroup G} : ∀ x y : G, -x = y ⧟ x = -y.  Proof. exact (flip_inv (G:=add_ops G)). Qed.
Definition flip_negate_0     `{AdditiveNonComGroup G} : ∀ x y : G, -x = 0 ⧟ x = 0.  Proof. exact (flip_inv_unit (G:=add_ops G)). Qed.

Global Hint Extern 4 (SimplifiesTo (-0) _) => solve_simplify negate_0 : typeclass_instances.

Lemma plus_2_2 `{AdditiveNonComSemiGroup M} `{One M} : 2 + 2 = 4 :> M.
Proof. sym. exact (associativity _ _ _ _). Qed.

Definition add_monmor_sgmor@{u} : ∀ {X Y : set@{u}} `{H:@AdditiveMonoid_Morphism X Y pX zX pY zY f}, AdditiveSemiGroup_Morphism f := @monmor_sgmor.
Coercion add_monmor_sgmor : AdditiveMonoid_Morphism >-> AdditiveSemiGroup_Morphism.

Canonical Structure AdditiveSemiGroup_Morphism_fun {X Y pX pY}
  := make_fun_alt (@AdditiveSemiGroup_Morphism X Y pX pY) (@SemiGroup_Morphism_fun X Y pX pY).

Canonical Structure AdditiveMonoid_Morphism_fun {X Y pX zX pY zY}
  := make_fun_alt (@AdditiveMonoid_Morphism X Y pX zX pY zY) (@Monoid_Morphism_fun X Y pX zX pY zY).

Definition preserves_plus `{AdditiveSemiGroup_Morphism (f:=f)} : ∀ x y, f (x+y) = f x + f y := preserves_sg_op (f:add_ops _ ⇾ add_ops _).
Arguments preserves_plus {_ _ _ _} f {_} x y.

Coercion AdditiveMonoid_Morphism_pointed `{AdditiveMonoid_Morphism (f:=f)} : Zero_Pointed_Morphism f := monmor_pointed f _.

Definition preserves_negate@{u} {X Y : set@{u}} `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y} (f:X ⇾ Y) `{!AdditiveSemiGroup_Morphism f}
  x : f (-x) = -(f x)
:= preserves_inv (f:add_ops X ⇾ add_ops Y) _.

Definition preserves_minus@{u} {X Y : set@{u}} `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y} (f:X ⇾ Y) `{!AdditiveSemiGroup_Morphism f}
  x y : f (x - y) = f x - f y
:= preserves_op_inv_r (f:add_ops X ⇾ add_ops Y) _ _.

Definition id_addsg_mor `{AdditiveNonComSemiGroup M} : AdditiveSemiGroup_Morphism (id_fun M) := id_semigroup_mor (G:=add_ops M).
Definition id_addmon_mor `{AdditiveNonComMonoid M} : AdditiveMonoid_Morphism (id_fun M) := id_monoid_mor (M:=add_ops M).
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (id_fun _)) => simple notypeclasses refine id_addsg_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism (id_fun _)) => simple notypeclasses refine id_addmon_mor : typeclass_instances.

Definition compose_addsg_mor@{u} : ∀ {X Y Z : set@{u}} {op₁} {op₂} {op₃} {g f},
  @AdditiveSemiGroup_Morphism X Y op₁ op₂ f → @AdditiveSemiGroup_Morphism Y Z op₂ op₃ g
  → AdditiveSemiGroup_Morphism (g ∘ f)
:= @compose_semigroup_mor.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_addsg_mor _ _) : typeclass_instances.

Definition compose_addmon_mor@{u} : ∀ {X Y Z : set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @AdditiveMonoid_Morphism X Y op₁ e₁ op₂ e₂ f → @AdditiveMonoid_Morphism Y Z op₂ e₂ op₃ e₃ g
  → AdditiveMonoid_Morphism (g ∘ f)
:= @compose_monoid_mor.
Global Hint Extern 2 (AdditiveMonoid_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_addmon_mor _ _) : typeclass_instances.

Local Open Scope fun_inv_scope.
Definition invert_addsg_mor `{AdditiveSemiGroup_Morphism (f:=f)} `{!Inverse f, !Bijective f}
  : AdditiveSemiGroup_Morphism f⁻¹
:= invert_semigroup_mor.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (_⁻¹)) => simple notypeclasses refine invert_addsg_mor : typeclass_instances.

Definition invert_addmon_mor `{AdditiveMonoid_Morphism (f:=f)} `{!Inverse f, !Bijective f}
  : AdditiveMonoid_Morphism f⁻¹
:= invert_monoid_mor.
Global Hint Extern 2 (AdditiveMonoid_Morphism (_⁻¹)) => simple notypeclasses refine invert_addmon_mor : typeclass_instances.

Definition alt_Build_AdditiveSemiGroup_Morphism@{u} {X Y : set@{u}}
 `{AdditiveNonComSemiGroup X} `{AdditiveNonComSemiGroup Y} {f : X ⇾ Y}
  : (∀ x y : X, f (x + y) = f x + f y)
 → AdditiveSemiGroup_Morphism f
:= λ P, Build_SemiGroup_Morphism (f:add_ops X ⇾ add_ops Y) P.

Definition alt_Build_AdditiveMonoid_Morphism@{u} :
  ∀ {X Y : set@{u}} `{AdditiveNonComMonoid X} `{AdditiveNonComMonoid Y} {f : X ⇾ Y},
  (∀ x y : X, f (x + y) = f x + f y)
 → f 0 = 0
 → AdditiveMonoid_Morphism f
:= @alt_Build_Monoid_Morphism.

Lemma Build_AdditiveGroup_Morphism@{u} {X Y : set@{u}} `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y} (f:X ⇾ Y) :
  (∀ x y, f (x + y) = f x + f y)
  → AdditiveMonoid_Morphism f.
Proof. intro. refine (group_mor (f:add_ops X ⇾ add_ops Y)). now split. Defined.

Definition add_group_mor@{u} `{AdditiveNonComGroup@{u} G₁} `{AdditiveNonComGroup@{u} G₂}
  (f : G₁ ⇾ G₂) `{!AdditiveSemiGroup_Morphism f}
  : AdditiveMonoid_Morphism f
  := group_mor (f:add_ops G₁ ⇾ add_ops G₂).
Global Hint Extern 10 (AdditiveMonoid_Morphism _) =>
  simple notypeclasses refine (add_group_mor _) : typeclass_instances.


Definition projected_additive_non_com_monoid@{u} :
  ∀ {X M : set@{u}} `{AdditiveNonComMonoid M} (f:X ⇾ M) `{!Injective f} `{Plus X} `{Zero X},
   (∀ x y, f (x + y) = f x + f y)
   → f 0 = 0
   → AdditiveNonComMonoid X
  := @projected_monoid.

Definition projected_additive_monoid@{u} :
  ∀ {X M : set@{u}} `{AdditiveMonoid M} (f:X ⇾ M) `{!Injective f} `{Plus X} `{Zero X},
   (∀ x y, f (x + y) = f x + f y)
   → f 0 = 0
   → AdditiveMonoid X
  := @projected_commutative_monoid.

Definition projected_additive_non_com_group@{u} :
  ∀ {X G : set@{u}} `{AdditiveNonComGroup G} (f:X ⇾ G) `{!Injective f} `{Plus X} `{Zero X} `{Negate X},
   (∀ x y, f (x + y) = f x + f y)
   → f 0 = 0
   → (∀ x, f (-x) = -(f x))
   → AdditiveNonComGroup X
  := @projected_group.

Definition projected_additive_group@{u} :
  ∀ {X G : set@{u}} `{AdditiveGroup G} (f:X ⇾ G) `{!Injective f} `{Plus X} `{Zero X} `{Negate X},
   (∀ x y, f (x + y) = f x + f y)
   → f 0 = 0
   → (∀ x, f (-x) = -(f x))
   → AdditiveGroup X
  := @projected_abgroup.


Section quote.
  Universes u.
  Context {X Y : set@{u}} (f:X ⇾ Y) `{AdditiveSemiGroup_Morphism@{u} (X:=X) (Y:=Y) (f:=f)}.

  Lemma quote_plus_alt {x₁ y₁ x₂ y₂} :
    quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ + x₂) (y₁ + y₂).
  Proof. exact (quote_sg_op_alt (f:add_ops _ ⇾ add_ops _)). Qed.

  Lemma quote_negate_alt `{Zero X} `{Zero Y} `{Negate X} `{Negate Y} `{!AdditiveNonComGroup X, !AdditiveNonComGroup Y} {x y} :
    quote f x y → quote f (-x) (-y).
  Proof. exact (quote_inv_alt (f:add_ops _ ⇾ add_ops _)). Qed.
End quote.

Global Hint Extern 4 (quote _ (_ + _) _) => quote_hint_strip (fun f => refine (quote_plus_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ + _)) => quote_hint_strip (fun f => refine (quote_plus_alt f _ _)) : quote.

Global Hint Extern 4 (quote _ (-_) _) => quote_hint_strip (fun f => refine (quote_negate_alt f _)) : quote.
Global Hint Extern 4 (quote _ _ (-_)) => quote_hint_strip (fun f => refine (quote_negate_alt f _)) : quote.

