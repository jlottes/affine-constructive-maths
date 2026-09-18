Require Import abstract_algebra interfaces.naturals interfaces.bundled_algebra.
Require Import theory.set theory.rings logic.aprop.
Require Import nat.nno theory.nno nno_rig nno_naturals.
Require Import easy.

Definition nat_one@{u}  : One@{u}  Nat := nno_one.
Definition nat_plus@{u} : Plus@{u} Nat := nno_plus.
Definition nat_mult@{u} : Mult@{u} Nat := nno_mult.
Global Hint Extern 1 (One  Nat) => refine nat_one  : typeclass_instances.
Global Hint Extern 1 (Plus Nat) => refine nat_plus : typeclass_instances.
Global Hint Extern 1 (Mult Nat) => refine nat_mult : typeclass_instances.

Definition Nat_com_rig@{u} : CommutativeRig@{u} Nat := nno_com_rig@{u} (ℕ:=Nat).

Global Hint Extern 1 (CommutativeRig Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (Rig Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (Rg Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (NearRig Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (NearRg Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (LeftNearRig Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (LeftNearRg Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (AdditiveMonoid Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (AdditiveNonComMonoid Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (AdditiveNonComSemiGroup Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (AdditiveSemiGroup Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (MultiplicativeSemiGroup Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (MultiplicativeMonoid Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.
Global Hint Extern 1 (MultiplicativeComMonoid Nat) => notypeclasses refine Nat_com_rig : typeclass_instances.

Canonical Structure Nat_near_rig@{u} := make_near_rig@{u} Nat.

Definition Nat_to_mon@{u} : NaturalsToMon@{u} Nat := nno_to_mon.
Global Hint Extern 1 (NaturalsToMon Nat) => refine Nat_to_mon : typeclass_instances.
Global Hint Extern 1 (NaturalsToMon (near_rig_car Nat_near_rig)) => refine Nat_to_mon : typeclass_instances.

Lemma Nat_is_naturals@{u} : Naturals@{u} Nat.
Proof. now refine (nno_naturals _). Qed.
Global Hint Extern 1 (Naturals Nat) => refine Nat_is_naturals : typeclass_instances.
Global Hint Extern 1 (Naturals (near_rig_car Nat_near_rig)) => refine Nat_is_naturals : typeclass_instances.
Global Hint Extern 1 (AdditiveCancellation Nat) => refine Nat_is_naturals : typeclass_instances.
Global Hint Extern 1 (AdditiveCancellation (near_rig_car Nat_near_rig)) => refine Nat_is_naturals : typeclass_instances.

Canonical Structure Nat_naturals@{u} : naturals@{u} := Build_naturals Nat _ _.

Global Hint Extern 1 (Dec (A:=set_T (near_rig_car Nat_near_rig) ∗ _) (=)) => refine Nat_eq_dec : typeclass_instances.
Global Hint Extern 1 (Dec (A:=set_T (near_rig_car (nats_near_rig Nat_naturals)) ∗ _) (=)) => refine Nat_eq_dec : typeclass_instances.

