Require Import abstract_algebra nat.nno.

Require Nat Datatypes Number.

Unset Universe Polymorphism.

Fixpoint to_stdlib_nat (x:nat) : Datatypes.nat :=
  match x with
  | nat_0 => Datatypes.O
  | nat_S y => Datatypes.S (to_stdlib_nat y)
  end.

Fixpoint of_stdlib_nat (x:Datatypes.nat) : nat :=
  match x with
  | Datatypes.O => nat_0
  | Datatypes.S y => nat_S (of_stdlib_nat y)
  end.

Definition of_num_uint (x:Number.uint) : nat := of_stdlib_nat (Nat.of_num_uint x).
Definition to_num_uint (x:nat) : Number.uint := Nat.to_num_uint (to_stdlib_nat x).

Number Notation nat of_num_uint to_num_uint : nat_scope.
