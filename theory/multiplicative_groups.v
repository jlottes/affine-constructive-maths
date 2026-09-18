Require Import interfaces.sprop.
Require Export theory.common_props theory.pointed.
Require Import abstract_algebra theory.groups.
Require Import easy rewrite.
Require Import quote.base simplify.

Local Abbreviation mul_ops := MultiplicativeGroupOps.
Local Notation "X 'ᵒᵖ'" := (ring_op X) (at level 1, format "X 'ᵒᵖ'").

Local Open Scope mult_scope.

Definition alt_Build_MultiplicativeSemiGroup `{Mult M} `{H:@Associative M (·)}
  : MultiplicativeSemiGroup M
:= H.

Definition alt_Build_MultiplicativeMonoid : ∀ `{Mult M} `{One M},
   @Associative M (·)
 → LeftIdentity  (X:=M) (·) 1
 → RightIdentity (X:=M) (·) 1
 → MultiplicativeMonoid M
:= @alt_Build_Monoid.

Definition alt_Build_MultiplicativeComMonoid : ∀ `{Mult M} `{One M},
   @Associative M (·)
 → Commutative (X:=M) (·)
 → LeftIdentity  (X:=M) (·) 1
 → MultiplicativeComMonoid M
:= @alt_Build_CommutativeMonoid.

Coercion one_inhabited `{One M} : Inhabited M.  Proof. now exists 1. Defined.
Coercion mult_mon_inhabited `{MultiplicativeMonoid M} : Inhabited M := _.

Definition mult_monoid_semigroup `{H:MultiplicativeMonoid R} : MultiplicativeSemiGroup R := _ : SemiGroup (mul_ops R).
Definition mult_commonoid_monoid `{H:MultiplicativeComMonoid R} : MultiplicativeMonoid R := H.
Coercion mult_monoid_semigroup : MultiplicativeMonoid >-> MultiplicativeSemiGroup.
Coercion mult_commonoid_monoid : MultiplicativeComMonoid >-> MultiplicativeMonoid.

Lemma mult_ass    `{MultiplicativeSemiGroup R} : Associative   (X:=R) (·).  Proof. exact (_ : SemiGroup (mul_ops R)). Qed.
Lemma mult_com    `{MultiplicativeComMonoid R} : Commutative   (X:=R) (·).  Proof. exact (comsg_com (mul_ops R) _). Qed.
Lemma mult_1_l    `{MultiplicativeMonoid    R} : LeftIdentity  (X:=R) (·) 1. Proof. exact (monoid_left_id  (X:=mul_ops R)). Qed.
Lemma mult_1_r    `{MultiplicativeMonoid    R} : RightIdentity (X:=R) (·) 1. Proof. exact (monoid_right_id (X:=mul_ops R)). Qed.

Global Hint Extern 2 (Associative   (·)    ) => simple notypeclasses refine mult_ass   : typeclass_instances.
Global Hint Extern 2 (Commutative   (·)    ) => simple notypeclasses refine mult_com   : typeclass_instances.
Global Hint Extern 2 (LeftIdentity  (·) _  ) => notypeclasses refine mult_1_l          : typeclass_instances.
Global Hint Extern 2 (RightIdentity (·) _  ) => notypeclasses refine mult_1_r          : typeclass_instances.

(** Simplification *)
Local Ltac simplify_chain tm := match goal with |- SimplifiesTo ?x ?y => change (SimplifiesToR (x,y)); trans tm end.

Lemma simplify_mult_1_l `{MultiplicativeMonoid M} {x x':M} `{!SimplifiesTo x x'} : SimplifiesTo (1 · x) x'.
Proof. simplify_chain x; trivial; split. exact (mult_1_l _). Qed.
Global Hint Extern 2 (SimplifiesTo (1 · _) _) => notypeclasses refine simplify_mult_1_l : typeclass_instances.

Lemma simplify_mult_1_r `{MultiplicativeMonoid M} {x x':M} `{!SimplifiesTo x x'} : SimplifiesTo (x · 1) x'.
Proof. simplify_chain x; trivial; split. exact (mult_1_r _). Qed.
Global Hint Extern 2 (SimplifiesTo (_ · 1) _) => notypeclasses refine simplify_mult_1_r : typeclass_instances.


Lemma MultiplicativeSemiGroup_op `{MultiplicativeSemiGroup G} : MultiplicativeSemiGroup (G ᵒᵖ).  Proof. exact (_ : SemiGroup (semigroup_op (mul_ops G))). Qed.
Lemma MultiplicativeMonoid_op    `{MultiplicativeMonoid G}    : MultiplicativeMonoid    (G ᵒᵖ).  Proof. exact (_ : Monoid (semigroup_op (mul_ops G))). Qed.
Lemma MultiplicativeComMonoid_op `{MultiplicativeComMonoid G} : MultiplicativeComMonoid (G ᵒᵖ).  Proof. exact (_ : CommutativeMonoid (semigroup_op (mul_ops G))). Qed.
Global Hint Extern 2 (MultiplicativeSemiGroup (_ ᵒᵖ)) => simple notypeclasses refine MultiplicativeSemiGroup_op : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid    (_ ᵒᵖ)) => simple notypeclasses refine MultiplicativeMonoid_op    : typeclass_instances.
Global Hint Extern 2 (MultiplicativeComMonoid (_ ᵒᵖ)) => simple notypeclasses refine MultiplicativeComMonoid_op : typeclass_instances.

Canonical Structure MultiplicativeSemiGroup_Morphism_fun {X Y mX mY}
  := make_fun_alt (@MultiplicativeSemiGroup_Morphism X Y mX mY) (@SemiGroup_Morphism_fun X Y mX mY).

Canonical Structure MultiplicativeMonoid_Morphism_fun {X Y mX oX mY oY}
  := make_fun_alt (@MultiplicativeMonoid_Morphism X Y mX oX mY oY) (@Monoid_Morphism_fun X Y mX oX mY oY).

Definition multmon_mor_multsg_mor `{H:MultiplicativeMonoid_Morphism (f:=f)} : MultiplicativeSemiGroup_Morphism f := H.
Coercion multmon_mor_multsg_mor : MultiplicativeMonoid_Morphism >-> MultiplicativeSemiGroup_Morphism.

Definition preserves_mult `{MultiplicativeSemiGroup_Morphism (f:=f)} : ∀ x y, f (x · y) = f x · f y := preserves_sg_op (f:mul_ops _ ⇾ mul_ops _).
Arguments preserves_mult {_ _ _ _} f {_} x y.

Coercion MultiplicativeMonoid_Morphism_pointed `{MultiplicativeMonoid_Morphism (f:=f)} : One_Pointed_Morphism f := monmor_pointed f _.

Definition id_mulsg_mor `{MultiplicativeSemiGroup G} : MultiplicativeSemiGroup_Morphism (id_fun G) := id_semigroup_mor (G:=mul_ops G).
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (id_fun _)) => simple notypeclasses refine id_mulsg_mor : typeclass_instances.

Definition id_mulmon_mor `{MultiplicativeMonoid M} : MultiplicativeMonoid_Morphism (id_fun M) := id_monoid_mor (M:=mul_ops M).
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (id_fun _)) => simple notypeclasses refine id_mulmon_mor : typeclass_instances.

Definition compose_mulsg_mor@{u} : ∀ {X Y Z : set@{u}} {op₁ op₂ op₃} {g f},
  @MultiplicativeSemiGroup_Morphism X Y op₁ op₂ f → @MultiplicativeSemiGroup_Morphism Y Z op₂ op₃ g
  → MultiplicativeSemiGroup_Morphism (g ∘ f)
:= @compose_semigroup_mor.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_mulsg_mor _ _) : typeclass_instances.

Definition compose_mulmon_mor@{u} : ∀ {X Y Z : set@{u}} {op₁ e₁} {op₂ e₂} {op₃ e₃} {g f},
  @MultiplicativeMonoid_Morphism X Y op₁ e₁ op₂ e₂ f → @MultiplicativeMonoid_Morphism Y Z op₂ e₂ op₃ e₃ g
  → MultiplicativeMonoid_Morphism (g ∘ f)
:= @compose_monoid_mor.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_mulmon_mor _ _) : typeclass_instances.

Definition invert_mulsg_mor `{MultiplicativeSemiGroup_Morphism (f:=f)} `{!Inverse f, !Bijective f}
  : MultiplicativeSemiGroup_Morphism (inverse f)
:= invert_semigroup_mor.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (inverse _)) => simple notypeclasses refine invert_mulsg_mor : typeclass_instances.

Definition invert_mulmon_mor `{MultiplicativeMonoid_Morphism (f:=f)} `{!Inverse f, !Bijective f}
  : MultiplicativeMonoid_Morphism (inverse f)
:= invert_monoid_mor.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (inverse _)) => simple notypeclasses refine invert_mulmon_mor : typeclass_instances.


Definition Build_MultiplicativeSemiGroup_Morphism@{u} {X Y : set@{u}}
  `{MultiplicativeSemiGroup X} `{MultiplicativeSemiGroup Y} {f : X ⇾ Y} :
  (∀ x y : X, f (x · y) = f x · f y)
 → MultiplicativeSemiGroup_Morphism f
:= Build_SemiGroup_Morphism (f:mul_ops X ⇾ mul_ops Y).

Definition alt_Build_MultiplicativeMonoid_Morphism@{u} :
  ∀ {X Y : set@{u}} `{MultiplicativeMonoid X} `{MultiplicativeMonoid Y} {f : X ⇾ Y},
  (∀ x y : X, f (x · y) = f x · f y)
 → f 1 = 1
 → MultiplicativeMonoid_Morphism f
:= @alt_Build_Monoid_Morphism.

Definition projected_multiplicative_semigroup@{u} :
  ∀ {X S : set@{u}} `{MultiplicativeSemiGroup S} (f:X ⇾ S) `{!Injective f} `{Mult X},
   (∀ x y, f (x · y) = f x · f y)
   → MultiplicativeSemiGroup X
  := @projected_semigroup.

Definition projected_multiplicative_monoid@{u} :
  ∀ {X M : set@{u}} `{MultiplicativeMonoid M} (f:X ⇾ M) `{!Injective f} `{Mult X} `{One X},
   (∀ x y, f (x · y) = f x · f y)
   → f 1 = 1
   → MultiplicativeMonoid X
  := @projected_monoid.

Definition projected_multiplicative_com_monoid@{u} :
  ∀ {X M : set@{u}} `{MultiplicativeComMonoid M} (f:X ⇾ M) `{!Injective f} `{Mult X} `{One X},
   (∀ x y, f (x · y) = f x · f y)
   → f 1 = 1
   → MultiplicativeComMonoid X
  := @projected_commutative_monoid.


(** Quote *)

Lemma quote_mult_alt `(f:X ⇾ Y) `{MultiplicativeSemiGroup_Morphism (X:=X) (Y:=Y) (f:=f)}
  {x₁ y₁ x₂ y₂} : quote f x₁ y₁ → quote f x₂ y₂ → quote f (x₁ · x₂) (y₁ · y₂).
Proof. exact (quote_sg_op_alt (f:mul_ops _ ⇾ mul_ops _)). Qed.

Global Hint Extern 4 (quote _ (_ · _) _) => quote_hint_strip (fun f => refine (quote_mult_alt f _ _)) : quote.
Global Hint Extern 4 (quote _ _ (_ · _)) => quote_hint_strip (fun f => refine (quote_mult_alt f _ _)) : quote.

