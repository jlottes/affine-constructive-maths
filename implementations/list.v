Require Export list.base list.tensor list.prod.

Require Import interfaces.set abstract_algebra bundled_algebra interfaces.free_monoid.
Require Import interfaces.sprop logic.aprop relations theory.set theory.groups theory.bundled_groups.
Require Import easy rewrite tactics.misc.

Local Open Scope grp_scope.

Lemma tensor_to_prod_list_is_fun {X} : @IsFun (TensorList X) (ProdList X) id.
Proof. refine (TensorList_sinduction_alt _ _ _); [ easy | intros a x IHx ].
  refine (TensorList_sdestruct _ _ _); [ easy | intros b y ].
  change (a = b ⊠ x = y ⊸ a = b ∧ id x = id y :> ProdList X).
  rew <-(IHx y). exact (aprod_aand _ _).
Qed.

Definition tensor_to_prod_list {X} := @make_fun _ _ _ (@tensor_to_prod_list_is_fun X).

Global Hint Extern 2 (Cast (TensorList ?X) (ProdList ?X)) => refine (tensor_to_prod_list X) : typeclass_instances.
Global Hint Extern 2 (Cast (TensorList ?X) (strong_op_monoid_car (ProdList_str_mon ?X))) => refine (tensor_to_prod_list X) : typeclass_instances.
Global Hint Extern 2 (Cast (monoid_car (TensorList_mon ?X)) (ProdList ?X)) => refine (tensor_to_prod_list X) : typeclass_instances.
Global Hint Extern 2 (Cast (monoid_car (TensorList_mon ?X)) (strong_op_monoid_car (ProdList_str_mon ?X))) => refine (tensor_to_prod_list X) : typeclass_instances.

Lemma dec_prod_to_tensor_list_is_fun {X} `{!DecidableEquality X} : @IsFun (ProdList X) (TensorList X) id.
Proof. refine (ProdList_sinduction_alt _ _ _); [ easy | intros a x IHx ].
  refine (ProdList_sdestruct _ _ _); [ easy | intros b y ].
  change (a = b ∧ x = y ⊸ a = b ⊠ x = y :> TensorList X).
  rew <-(IHx y). now apply aand_aprod_dec_l.
Qed.

Definition dec_prod_to_tensor_list {X} `{!DecidableEquality X}  := @make_fun _ _ _ (@dec_prod_to_tensor_list_is_fun X _).
