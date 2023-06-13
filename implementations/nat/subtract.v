Require Import theory.set theory.default_equality.
Require Import interfaces.naturals interfaces.bundled_algebra.
Require Import nat.nno nat.rig.
Require Import easy.

Definition Nat_subtract_raw := fix F (x y : Nat) := match x with
  | nat_0 => inl y
  | nat_S x' => match y with
    | nat_0 => inr x
    | nat_S y' => F x' y'
    end
  end.

Definition Nat_subtract : NatSubtract Nat := default_eq_func (tuncurry Nat_subtract_raw).
Global Hint Extern 1 (NatSubtract Nat) => refine Nat_subtract : typeclass_instances.
Global Hint Extern 1 (NatSubtract (near_rig_car (nats_near_rig Nat_naturals))) => refine Nat_subtract : typeclass_instances.

Lemma Nat_subtract_spec : NatSubtractSpec Nat.
Proof. hnf. unfold nat_subtract, Nat_subtract, func_op, default_eq_func, make_fun, tuncurry, proj1, proj2.
  refine (fix IH (x y : Nat) {struct x} := _); destruct x as [| x']; [ refl |].
+ destruct y as [| y' ]; cbn [ Nat_subtract_raw ]; [ refl |].
  specialize (IH x' y'). revert IH.
  destruct (Nat_subtract_raw x' y') as [z|z]; intros E;
    exact (sprop.andl (is_fun Nat_S _ _) E).
Qed.
Global Hint Extern 1 (NatSubtractSpec Nat) => refine Nat_subtract_spec : typeclass_instances.
Global Hint Extern 1 (NatSubtractSpec (near_rig_car (nats_near_rig Nat_naturals))) => refine Nat_subtract_spec : typeclass_instances.
