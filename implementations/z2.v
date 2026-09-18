Require Import interfaces.notation theory.set theory.default_equality.
Require Import logic.srelations logic.aprop.
Require Import abstract_algebra theory.rings.
Require Import implementations.bool.
Require Import easy rewrite change_quantifiers simplify.


Definition ℤ₂ := bool_set.

Global Hint Extern 2 (DefaultEquality ℤ₂) => refine default_set_make_prop : typeclass_instances.
Global Hint Extern 2 (Dec (A:=set_T ℤ₂ ∗ _) (=)) => refine bool_eq_dec : typeclass_instances.
Global Hint Extern 2 (IsDecEq ℤ₂) => refine bool_eq_is_dec : typeclass_instances.
Global Hint Extern 2 (DecidableEquality ℤ₂) => refine bool_eq_is_dec : typeclass_instances.
Global Hint Extern 2 (AffirmativeEquality ℤ₂) => refine bool_eq_is_dec : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality ℤ₂) => refine bool_eq_is_dec : typeclass_instances.
Global Hint Extern 2 (StrongSet ℤ₂) => refine bool_eq_is_dec : typeclass_instances.

Global Hint Extern 2 (Zero   ℤ₂) => exact false : typeclass_instances.
Global Hint Extern 2 (One    ℤ₂) => exact true  : typeclass_instances.
Global Hint Extern 2 (Plus   ℤ₂) => exact xorb_fun : typeclass_instances.
Global Hint Extern 2 (Negate ℤ₂) => exact (id_fun ℤ₂) : typeclass_instances.
Global Hint Extern 2 (Mult   ℤ₂) => exact andb_fun : typeclass_instances.

Lemma ℤ₂_is_comring : CommutativeRing ℤ₂.
Proof. apply alt_Build_CommutativeRing2; hnf; now repeat intros [|]. Qed.

Global Hint Extern 2 (CommutativeRing ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.

Global Hint Extern 2 (AdditiveCancellation ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (AdditiveGroup ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComGroup ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComMonoid ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComSemiGroup ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (CommutativeRig ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (LeftNearRg ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (LeftNearRig ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (LeftNearRing ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (LeftNearRng ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (MultiplicativeComMonoid ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (NearRg ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (NearRig ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (NearRing ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (NearRng ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (Rg ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (Rig ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (Ring ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.
Global Hint Extern 2 (Rng ℤ₂) => simple notypeclasses refine ℤ₂_is_comring : typeclass_instances.

Definition ℤ₂_nontrivial : OneNonZero ℤ₂ := true_ne_false.
Global Hint Extern 2 (OneNonZero ℤ₂) => simple notypeclasses refine ℤ₂_nontrivial : typeclass_instances.

Definition ℤ₂_ind (P:ℤ₂ ⇾ Ω) : P 0 ∧ P 1 ⊸ all P := bool_ind P.
Definition ℤ₂_ind_alt (P:ℤ₂ → Ω) : P 0 → P 1 → all P := bool_ind_alt P.
Ltac ℤ₂_induction := hnf; try change_quantifiers; apply ℤ₂_ind_alt.

Local Open Scope mult_scope.

Lemma ℤ₂_strong_no_zero_divisors : StrongNoZeroDivisors ℤ₂.
Proof. ℤ₂_induction; now simplify. Qed.
Global Hint Extern 2 (StrongNoZeroDivisors ℤ₂) => simple notypeclasses refine ℤ₂_strong_no_zero_divisors : typeclass_instances.
Global Hint Extern 2 (NoZeroDivisors ℤ₂) => simple notypeclasses refine ℤ₂_strong_no_zero_divisors : typeclass_instances.

Lemma ℤ₂_int_domain : IntegralDomain ℤ₂.  Proof. now split. Qed.
Global Hint Extern 2 (IntegralDomain ℤ₂) => simple notypeclasses refine ℤ₂_int_domain : typeclass_instances.
Global Hint Extern 2 (NonZeroMultiplicativeCancellation ℤ₂) => simple notypeclasses refine ℤ₂_int_domain : typeclass_instances.

