Require Import interfaces.notation interfaces.orders interfaces.abstract_algebra.
Require Import theory.set theory.default_equality theory.lattices orders.orders orders.lattices.
Require Import logic.srelations logic.aprop.
Require Import easy simplify.

Global Hint Extern 2 (Equiv bool) => exact leq : typeclass_instances.
Canonical Structure bool_set : set := default_set_make bool.
Notation "𝟐" := bool : set_scope.

Declare Scope bool_scope.
Bind Scope bool_scope with bool.
Delimit Scope bool_scope with bool.

Global Hint Extern 2 (DefaultEquality bool_set) => refine default_set_make_prop : typeclass_instances.
Global Hint Extern 2 (AffirmativeEquality bool_set) => refine default_set_make_prop : typeclass_instances.

Definition andb : bool ∗ bool → bool := λ '(p, q), if p then q else false.
Definition orb : bool ∗ bool → bool := λ '(p, q), if p then true else q.
Definition notb (p : bool) := if p then false else true.
Definition xorb : bool ∗ bool → bool := λ '(p, q), if p then notb q else q.

Canonical Structure andb_fun : 𝟐 ⊗ 𝟐 ⇾ 𝟐 := default_eq_func (X:=𝟐 ⊗ 𝟐) andb.
Canonical Structure orb_fun  : 𝟐 ⊗ 𝟐 ⇾ 𝟐 := default_eq_func (X:=𝟐 ⊗ 𝟐) orb.
Canonical Structure notb_fun : 𝟐 ⇾ 𝟐 := default_eq_func notb.
Canonical Structure xorb_fun  : 𝟐 ⊗ 𝟐 ⇾ 𝟐 := default_eq_func (X:=𝟐 ⊗ 𝟐) xorb.

Notation "x && y" := (andb (pair x y)) : bool_scope.
Notation "x || y" := (orb  (pair x y)) : bool_scope.

Definition bool_eq_dec : Dec (A:=bool∗bool) (=) := λ '(p, q), if p then q else (if q then false else true).
Global Hint Extern 2 (Dec (A:=bool∗_) (=)) => refine bool_eq_dec : typeclass_instances.
Global Hint Extern 2 (Dec (A:=set_T bool_set ∗ _) (=)) => refine bool_eq_dec : typeclass_instances.

Definition bool_eq_code (p q : bool) : Ω := if dec (=) (p, q) then 𝐓 else 𝐅.
Lemma bool_eq_encode (p q : bool) : p = q → bool_eq_code p q.
Proof. intros []. clear q. destruct p as [|]; now change 𝐓. Defined.

Definition true_ne_false : true ≠ false := bool_eq_encode _ _.
Definition false_ne_true : false ≠ true := bool_eq_encode _ _.

Lemma bool_eq_is_dec : IsDecEq 𝟐.
Proof. hnf; unfold dec; intros [[|] [|]]; cbn [ bool_eq_dec ]; [ refl | refine (bool_eq_encode _ _).. | refl ]. Qed.
Global Hint Extern 2 (IsDecEq bool_set) => refine bool_eq_is_dec : typeclass_instances.

Global Hint Extern 2 (DecidableEquality bool_set) => refine bool_eq_is_dec : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality bool_set) => refine bool_eq_is_dec : typeclass_instances.
Global Hint Extern 2 (StrongSet bool_set) => refine bool_eq_is_dec : typeclass_instances.

Lemma bool_ind (P:𝟐 ⇾ Ω) : P false ∧ P true ⊸ all P.
Proof. apply all_adj; intros [|]; now simplify. Qed.

Lemma bool_ind_alt (P:𝟐 → Ω) : P false → P true → all P.
Proof. intros. apply (bool_ind (default_eq_func P)); now split. Qed.

Definition bool_to_aprop : bool → AProp := λ p, if p then 𝐓 else 𝐅.
Canonical Structure bool_to_Ω : 𝟐 ⇾ Ω := default_eq_func bool_to_aprop.

Lemma bool_to_aprop_decidable : ∀ b, Decidable (bool_to_aprop b).
Proof. intros [|]; [ left | right ]; exact sprop.I. Qed.
Global Hint Extern 2 (Decidable (bool_to_aprop _)) => simple notypeclasses refine (bool_to_aprop_decidable _) : typeclass_instances.
Global Hint Extern 2 (Affirmative (bool_to_aprop _)) => simple notypeclasses refine (bool_to_aprop_decidable _) : typeclass_instances.
Global Hint Extern 2 (Refutative (bool_to_aprop _)) => simple notypeclasses refine (bool_to_aprop_decidable _) : typeclass_instances.

Lemma bool_to_aprop_injective : Injective bool_to_Ω.
Proof. intros [|] [|]; full_tautological. Qed.
Global Hint Extern 2 (Injective bool_to_Ω) => simple notypeclasses refine bool_to_aprop_injective : typeclass_instances.

Global Hint Extern 2 (SimplifiesTo (bool_to_aprop false) ?out) => change (SimplifiesTo afalse out) : typeclass_instances.
Global Hint Extern 2 (SimplifiesTo (bool_to_aprop true ) ?out) => change (SimplifiesTo atrue  out) : typeclass_instances.


Definition bool_le : Le bool := λ '(p, q), bool_to_aprop (notb p || q).
Global Hint Extern 2 (Le bool) => refine bool_le : typeclass_instances.
Global Hint Extern 2 (Le (set_T bool_set)) => refine bool_le : typeclass_instances.

Definition bool_le_dec : Dec (A:=bool∗bool) (≤) := λ '(p, q), (notb p || q)%bool.
Global Hint Extern 2 (Dec (A:=bool∗_) le) => refine bool_le_dec : typeclass_instances.
Global Hint Extern 2 (Dec (A:=set_T bool_set ∗ _) le) => refine bool_le_dec : typeclass_instances.
Lemma bool_le_is_dec : IsDecLe bool.  Proof. intros [[|][|]]; exact sprop.I. Qed.
Global Hint Extern 2 (IsDecLe bool) => refine bool_le_is_dec : typeclass_instances.
Global Hint Extern 2 (DecidableLe bool) => refine bool_le_is_dec : typeclass_instances.
Global Hint Extern 2 (AffirmativeLe bool) => refine bool_le_is_dec : typeclass_instances.
Global Hint Extern 2 (RefutativeLe bool) => refine bool_le_is_dec : typeclass_instances.
Global Hint Extern 2 (IsDecLe (set_T bool_set)) => refine bool_le_is_dec : typeclass_instances.
Global Hint Extern 2 (DecidableLe (set_T bool_set)) => refine bool_le_is_dec : typeclass_instances.
Global Hint Extern 2 (AffirmativeLe (set_T bool_set)) => refine bool_le_is_dec : typeclass_instances.
Global Hint Extern 2 (RefutativeLe (set_T bool_set)) => refine bool_le_is_dec : typeclass_instances.

Lemma bool_poset : Poset bool_set.
Proof. pose proof true_ne_false. pose proof false_ne_true.
 apply alt_Build_Poset; hnf; [ repeat intros [|] .. | intros [[|][|]] | repeat intros [|] ]; full_tautological.
Qed.

Global Hint Extern 2 (Poset bool_set) => refine bool_poset : typeclass_instances.
Global Hint Extern 2 (PreOrder bool_set) => refine bool_poset : typeclass_instances.
Global Hint Extern 2 (WeakPoset bool_set) => refine bool_poset : typeclass_instances.

Lemma bool_dec_order : DecidableOrder bool_set.  Proof. now split. Qed.
Global Hint Extern 2 (DecidableOrder bool_set) => refine bool_dec_order : typeclass_instances.
Global Hint Extern 2 (AffirmativeOrder bool_set) => refine bool_dec_order : typeclass_instances.
Global Hint Extern 2 (RefutativeOrder bool_set) => refine bool_dec_order : typeclass_instances.
Global Hint Extern 2 (StrongLe bool) => refine bool_dec_order : typeclass_instances.
Global Hint Extern 2 (StrongLe (set_T bool_set)) => refine bool_dec_order : typeclass_instances.
Global Hint Extern 2 (StrongPoset bool_set) => refine bool_dec_order : typeclass_instances.

Lemma bool_total_order : TotalOrder bool_set.
Proof. split; try exact _; intros [|] [|]; [left|right|left..]; exact sprop.I. Qed.
Global Hint Extern 2 (TotalOrder bool_set) => refine bool_total_order : typeclass_instances.
Global Hint Extern 2 (LinearOrder bool_set) => refine bool_total_order : typeclass_instances.

Definition bool_trich : Trich bool_set := λ '(p, q),
  if p then (if q then is_eq else is_gt) else (if q then is_lt else is_eq).
Global Hint Extern 2 (Trich bool_set) => exact bool_trich : typeclass_instances.
Lemma bool_is_trich : IsTrich bool_set.
Proof. split; try exact _; intros [|] [|]; now simpl. Qed.
Global Hint Extern 2 (IsTrich bool_set) => exact bool_is_trich : typeclass_instances.

Global Hint Extern 2 (Bottom bool_set) => refine false : typeclass_instances.
Global Hint Extern 2 (Top bool_set) => refine true : typeclass_instances.
Global Hint Extern 2 (Meet bool_set) => refine andb_fun : typeclass_instances.
Global Hint Extern 2 (Join bool_set) => refine orb_fun : typeclass_instances.

Lemma bool_lattice : LatticeOrder bool_set.
Proof. split; split; try exact _; repeat intros [|]; simpl; tautological. Qed.

Global Hint Extern 2 (LatticeOrder bool_set) => simple notypeclasses refine bool_lattice : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice bool_set) => simple notypeclasses refine bool_lattice : typeclass_instances.
Global Hint Extern 2 (JoinSemiLatticeOrder bool_set) => simple notypeclasses refine bool_lattice : typeclass_instances.
Global Hint Extern 2 (Lattice bool_set) => simple notypeclasses refine bool_lattice : typeclass_instances.
Global Hint Extern 2 (MeetSemiLatticeOrder bool_set) => simple notypeclasses refine bool_lattice : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice bool_set) => simple notypeclasses refine bool_lattice : typeclass_instances.

Lemma bool_distr_lattice : DistributiveLattice bool_set.  Proof. exact _. Qed.
Global Hint Extern 2 (DistributiveLattice bool_set) => simple notypeclasses refine bool_distr_lattice : typeclass_instances.

Lemma bool_bounded_meet_sl : BoundedMeetSemiLattice bool_set.
Proof. apply alt_Build_BoundedMeetSemiLattice; try exact _; now intros [|]. Qed.
Global Hint Extern 2 (BoundedMeetSemiLattice bool_set) => simple notypeclasses refine bool_bounded_meet_sl : typeclass_instances.

Lemma bool_bounded_join_sl : BoundedJoinSemiLattice bool_set.
Proof. apply alt_Build_BoundedJoinSemiLattice; try exact _; now intros [|]. Qed.
Global Hint Extern 2 (BoundedJoinSemiLattice bool_set) => simple notypeclasses refine bool_bounded_join_sl : typeclass_instances.


Lemma bool_to_aprop_lattice_mor : Lattice_Morphism bool_to_Ω.
Proof. split; try exact _.
+ apply Build_MeetSemiLattice_Morphism. intros [|][|]; full_tautological.
+ apply Build_JoinSemiLattice_Morphism. intros [|][|]; full_tautological.
Qed.
Global Hint Extern 2 (Lattice_Morphism bool_to_Ω) => simple notypeclasses refine bool_to_aprop_lattice_mor : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice_Morphism bool_to_Ω) => simple notypeclasses refine bool_to_aprop_lattice_mor : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Morphism bool_to_Ω) => simple notypeclasses refine bool_to_aprop_lattice_mor : typeclass_instances.

Definition bool_to_aprop_order_embedding : OrderEmbedding bool_to_Ω := join_sl_mor_embedding _.
Global Hint Extern 2 (OrderEmbedding bool_to_Ω) => simple notypeclasses refine bool_to_aprop_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving bool_to_Ω) => simple notypeclasses refine bool_to_aprop_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting bool_to_Ω) => simple notypeclasses refine bool_to_aprop_order_embedding : typeclass_instances.

