Require Import abstract_algebra interfaces.sprop logic.srelations logic.aprop rewrite easy tactics.misc.

Lemma right_id_from_left `{!@Commutative X _ f} `{!LeftIdentity f x} : RightIdentity f x.
Proof. hnf; intros. rew (commutativity f _ _). exact (left_identity f _). Qed.

Lemma right_absorb_from_left `{!@Commutative X _ f} `{!LeftAbsorb f x} : RightAbsorb f x.
Proof. hnf; intros. rew (commutativity f _ _). exact (left_absorb f _). Qed.

Lemma right_inverse_from_left `{!@Commutative X Y f} `{!LeftInverse f i u} : RightInverse f i u.
Proof. hnf; intros. rew (commutativity f _ _). exact (left_inverse f _). Qed.

Lemma right_distr_from_left `{!@Commutative X X f} `{!LeftDistribute f g} : RightDistribute f g.
Proof. hnf; intros x y z. rew !3(commutativity f _ z). exact (distribute_l f g _ _ _). Qed.

Lemma left_distr_from_right `{!@Commutative X X f} `{!RightDistribute f g} : LeftDistribute f g.
Proof. hnf; intros x y z. rew !3(commutativity f x _). exact (distribute_r f g _ _ _). Qed.

Lemma involutive_bijective `{Involutive (f:=f)} : Bijective f (inv:=f).
Proof. split; hnf.
+ intros x y. rew <-(involutive f x) at 2. rew <-(involutive f y) at 2. exact (is_fun f _ _).
+ exact (involutive f).
Qed.
Coercion involutive_bijective : Involutive >-> Bijective.

Lemma left_or_right_absorb {X:set} (f:X ⊗ X ⇾ X) `{!LeftAbsorb f z} `{!RightAbsorb f z} (x y : X) : x = z ∨ y = z ⊸ f (x, y) = z.
Proof. apply aor_elim.
+ rew <-(left_absorb  f (x:=z) y) at 2. exact (is_fun (ap2 f y) _ _).
+ rew <-(right_absorb f (y:=z) x) at 2. exact (is_fun (ap1 f x) _ _).
Qed.

Lemma absorb_ne_left_and_right {X:set} (f:X ⊗ X ⇾ X) `{!LeftAbsorb f z} `{!RightAbsorb f z} (x y : X) : f (x, y) ≠ z ⊸ x ≠ z ∧ y ≠ z.
Proof acontra (left_or_right_absorb f x y).

Lemma left_par_right_absorb {X:set} `{!RefutativeEquality X} (f:X ⊗ X ⇾ X) `{!LeftAbsorb f z} `{!RightAbsorb f z} (x y : X)
  : x = z ⊞ y = z ⊸ f (x, y) = z.
Proof. now apply aor_apar_refutative, left_or_right_absorb. Qed.

Lemma absorb_ne_left_prod_right {X:set} `{!RefutativeEquality X} (f:X ⊗ X ⇾ X) `{!LeftAbsorb f z} `{!RightAbsorb f z} (x y : X)
  : f (x, y) ≠ z ⊸ x ≠ z ⊠ y ≠ z.
Proof acontra (left_par_right_absorb f x y).

Section cancellation.
  Universes i.
  Context {X Y Z : set@{i}} (f:X ⊗ Y ⇾ Z).

  Definition left_cancellation  x {H:Injective (ap1 f x)} : ∀ y₁ y₂, y₁ = y₂ ⧟ f(x, y₁) = f(x, y₂) := @injective_iff _ _ _ H.
  Definition right_cancellation y {H:Injective (ap2 f y)} : ∀ x₁ x₂, x₁ = x₂ ⧟ f(x₁, y) = f(x₂, y) := @injective_iff _ _ _ H.
End cancellation.

Lemma right_cancel_from_left `{!@Commutative X X f} : (∀ z, Injective (ap1 f z)) → (∀ z, Injective (ap2 f z)).
Proof. intros P z x y. change (f(x, z) = f(y, z) ⊸ x = y). rew !2(commutativity f _ z). apply P. Qed.

Section opposite.
  Ltac go H := hnf; intros; repeat change (func_op (?f ∘ tensor_swap _ _) (?a, ?b)) with (f (b, a));
    solve [ apply H | sym; apply H ].

  Lemma Associative_op `{H:Associative (f:=f)} : Associative (f ∘ tensor_swap _ _).  Proof. go H. Qed.
  Lemma Commutative_op `{H:Commutative (f:=f)} : Commutative (f ∘ tensor_swap _ _).  Proof. go H. Qed.
  Lemma BinaryIdempotent_op `{H:BinaryIdempotent (f:=f)} : BinaryIdempotent (f ∘ tensor_swap _ _).  Proof. go H. Qed.
  Lemma RightIdentity_op `{H:LeftIdentity (f:=f) (x:=x)} : RightIdentity (f ∘ tensor_swap _ _) x.  Proof. go H. Qed.
  Lemma LeftIdentity_op `{H:RightIdentity (f:=f) (y:=x)} : LeftIdentity (f ∘ tensor_swap _ _) x.  Proof. go H. Qed.
  Lemma RightAbsorb_op `{H:LeftAbsorb (f:=f) (x:=x)} : RightAbsorb (f ∘ tensor_swap _ _) x.  Proof. go H. Qed.
  Lemma LeftAbsorb_op `{H:RightAbsorb (f:=f) (y:=x)} : LeftAbsorb (f ∘ tensor_swap _ _) x.  Proof. go H. Qed.
  Lemma RightInverse_op `{H:LeftInverse (f:=f) (inv:=i) (unit:=x)} : RightInverse (f ∘ tensor_swap _ _) i x.  Proof. go H. Qed.
  Lemma LeftInverse_op `{H:RightInverse (f:=f) (inv:=i) (unit:=x)} : LeftInverse (f ∘ tensor_swap _ _) i x.  Proof. go H. Qed.
  Lemma RightDistribute_op `{H:LeftDistribute (f:=f) (g:=g)} : RightDistribute (f ∘ tensor_swap _ _) g.  Proof. go H. Qed.
  Lemma LeftDistribute_op `{H:RightDistribute (f:=f) (g:=g)} : LeftDistribute  (f ∘ tensor_swap _ _) g.  Proof. go H. Qed.
End opposite.
Global Hint Extern 2 (Associative      (_ ∘ tensor_swap _ _)    ) => notypeclasses refine Associative_op      : typeclass_instances.
Global Hint Extern 2 (Commutative      (_ ∘ tensor_swap _ _)    ) => notypeclasses refine Commutative_op      : typeclass_instances.
Global Hint Extern 2 (BinaryIdempotent (_ ∘ tensor_swap _ _)    ) => notypeclasses refine BinaryIdempotent_op : typeclass_instances.
Global Hint Extern 2 (RightIdentity    (_ ∘ tensor_swap _ _) _  ) => notypeclasses refine RightIdentity_op    : typeclass_instances.
Global Hint Extern 2 (LeftIdentity     (_ ∘ tensor_swap _ _) _  ) => notypeclasses refine LeftIdentity_op     : typeclass_instances.
Global Hint Extern 2 (RightAbsorb      (_ ∘ tensor_swap _ _) _  ) => notypeclasses refine RightAbsorb_op      : typeclass_instances.
Global Hint Extern 2 (LeftAbsorb       (_ ∘ tensor_swap _ _) _  ) => notypeclasses refine LeftAbsorb_op       : typeclass_instances.
Global Hint Extern 2 (RightInverse     (_ ∘ tensor_swap _ _) _ _) => notypeclasses refine RightInverse_op     : typeclass_instances.
Global Hint Extern 2 (LeftInverse      (_ ∘ tensor_swap _ _) _ _) => notypeclasses refine LeftInverse_op      : typeclass_instances.
Global Hint Extern 2 (RightDistribute  (_ ∘ tensor_swap _ _) _  ) => notypeclasses refine RightDistribute_op  : typeclass_instances.
Global Hint Extern 2 (LeftDistribute   (_ ∘ tensor_swap _ _) _  ) => notypeclasses refine LeftDistribute_op   : typeclass_instances.




