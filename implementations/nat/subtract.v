Require Import theory.set theory.default_equality.
Require Import interfaces.naturals interfaces.bundled_algebra.
Require Import nat.nno nat.rig.
Require Import theory.additive_groups theory.nno.
Require Import easy.


Definition Nat_subtract_raw : Nat → Nat → natsubtract.t Nat := fix F (x y : Nat) := match x with
  | nat_0 => match y with
    | nat_0 => natsubtract.is_eq
    | nat_S _ => natsubtract.is_lt_by y
    end
  | nat_S x' => match y with
    | nat_0 => natsubtract.is_gt_by x
    | nat_S y' => F x' y'
    end
  end.

Definition Nat_subtract : NatSubtract Nat := default_eq_func (tuncurry Nat_subtract_raw).
Global Hint Extern 1 (NatSubtract Nat) => refine Nat_subtract : typeclass_instances.
Global Hint Extern 1 (NatSubtract (near_rig_car (nats_near_rig Nat_naturals))) => refine Nat_subtract : typeclass_instances.

Lemma Nat_subtract_spec : NatSubtractSpec Nat.
Proof. hnf. unfold nat_subtract, Nat_subtract, func_op, default_eq_func, tuncurry, proj1, proj2.
  refine (fix IH (x y : Nat) {struct x} := _); destruct x as [| x']; destruct y as [| y']; cbn [ Nat_subtract_raw ].
+ refl.
+ split; [ apply plus_0_l | apply nno_suc_nonzero ].
+ split; [ apply symmetry; [ exact _ | apply plus_0_l ] | apply nno_suc_nonzero ].
+ specialize (IH x' y'). revert IH.
  destruct (Nat_subtract_raw x' y') as [z| |z].
  * intros [E ?]; split; trivial. exact (sprop.andl (is_fun Nat_S _ _) E).
  * intros E. exact (sprop.andl (is_fun Nat_S _ _) E).
  * intros [E ?]; split; trivial. exact (sprop.andl (is_fun Nat_S _ _) E).
Qed.

Global Hint Extern 1 (NatSubtractSpec Nat) => refine Nat_subtract_spec : typeclass_instances.
Global Hint Extern 1 (NatSubtractSpec (near_rig_car (nats_near_rig Nat_naturals))) => refine Nat_subtract_spec : typeclass_instances.

