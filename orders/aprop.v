Require Export logic.aprop.
Require Import abstract_algebra relations theory.set orders.orders orders.lattices.
Require Import easy rewrite.

Global Hint Extern 2 (Le AProp) => exact aimpl : typeclass_instances.
Global Hint Extern 2 (Le (set_T AProp_set)) => exact aimpl : typeclass_instances.

Lemma AProp_is_preorder : PreOrder Ω.
Proof. split; now unfold le. Qed.
Global Hint Extern 2 (PreOrder Ω) => eexact AProp_is_preorder : typeclass_instances.

Lemma AProp_is_poset : Poset Ω.
Proof. now refine (induced_poset_poset _). Qed.
Global Hint Extern 2 (Poset AProp_set) => eexact AProp_is_poset : typeclass_instances.

Global Hint Extern 15 (apos (func_op ?f ?x ⊸ func_op ?g ?y)) =>
  change (apos (@le Ω aimpl (func_op f x) (func_op g y))) : proper.

Global Hint Extern 2 (Meet AProp_set) => eexact (aand_fun ∘ tensor_to_prod _ _) : typeclass_instances.
Global Hint Extern 2 (Join AProp_set) => eexact (aor_fun ∘ tensor_to_prod _ _) : typeclass_instances.

Lemma AProp_lattice_order : LatticeOrder Ω.
Proof. split.
+ split; [ exact _ |..].
  * exact aandl.
  * exact aandr.
  * intros P Q R. rew (aprod_aand _ _). exact (aand_lub _ _ _).
+ apply Build_JoinSemiLatticeOrder.
  * exact aorl.
  * exact aorr.
  * intros P Q R. rew (aprod_aand _ _). exact (aor_glb _ _ _).
Qed.
Global Hint Extern 2 (LatticeOrder AProp_set) => refine AProp_lattice_order : typeclass_instances.
Global Hint Extern 2 (MeetSemiLatticeOrder AProp_set) => refine AProp_lattice_order : typeclass_instances.
Global Hint Extern 2 (JoinSemiLatticeOrder AProp_set) => refine AProp_lattice_order : typeclass_instances.
Global Hint Extern 2 (Lattice AProp_set) => refine AProp_lattice_order : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice AProp_set) => refine AProp_lattice_order : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice AProp_set) => refine AProp_lattice_order : typeclass_instances.
