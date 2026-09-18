Require Import abstract_algebra interfaces.naturals.
Require Import theory.set theory.default_equality
  theory.rings interfaces.sprop logic.aprop logic.dec.
Require Import easy rewrite.

Inductive nat : Set := nat_0 : nat | nat_S : nat → nat.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.

Global Hint Extern 0 (Equiv nat) => exact leq : typeclass_instances.

Canonical Structure Nat@{u} : set@{u} := default_set_make@{u} nat.
Global Hint Extern 2 (DefaultEquality Nat) => simple notypeclasses refine default_set_make_prop : typeclass_instances.
Global Hint Extern 2 (AffirmativeEquality Nat) => simple notypeclasses refine default_set_make_prop : typeclass_instances.

Canonical Structure Nat_S : Nat ⇾ Nat := default_eq_func nat_S.
Global Hint Extern 0 (Zero Nat) => exact nat_0 : typeclass_instances.
Global Hint Extern 0 (Successor Nat) => exact Nat_S : typeclass_instances.

Section NNO.
  Universes u.
  Instance Nat_rec : FromNNO Nat@{u} := λ (X:set@{u}) z s, default_eq_func@{u} (
    fix F (x:Nat@{u}) := match x with
    | nat_0 => z
    | nat_S y => s (F y)
    end).

  Lemma Nat_NNO : NaturalNumbersObject Nat@{u}.
  Proof. split; intros X z s.
  + split; [ do 2 red |]; easy.
  + intros f ?.
    refine (fix IH (x:Nat) := match x with | nat_0 => _ | nat_S x' => _ end).
    * exact (preserves_0 f).
    * change (f (suc x') = suc (nno_to_set Nat X x')).
      rew <-(IH x' : f x' = nno_to_set Nat X x').
      exact (preserves_suc _ _).
  Qed.
End NNO.
Global Hint Extern 0 (FromNNO Nat) => refine Nat_rec : typeclass_instances.
Global Hint Extern 0 (NaturalNumbersObject Nat) => refine Nat_NNO : typeclass_instances.

Import modality_notation.
Import projection_notation.

Lemma Nat_ind (P:nat → Ω) : (∏ n, P n ⊸ P (suc n)) → (P 0 ⊸ all P).
Proof. intro Ps. apply all_adj. refine (fix IH n := match n with
 | nat_0 => _
 | nat_S m => _
 end).
+ refl.
+ rew (IH m). exact (Ps m).
Qed.

Lemma Nat_sind (P:nat → Ω) : P 0 → (∀ n, P n → P (suc n)) → all P.
Proof. intros P0 Ps. apply ( Nat_ind (λ n, ! (P n)) ); trivial.
  intros n. apply affirmative_aimpl. exact (Ps n).
Qed.

Definition Nat_destruct {X:set} : X × (Nat ⇾ X) → (Nat ⇾ X) :=
  λ '(x, f), default_eq_func (λ n, match n with
  | nat_0 => x
  | nat_S m => f m
  end).

Lemma Nat_destruct_is_fun {X:set} : IsFun (@Nat_destruct X).
Proof. intros [x f][y g]. change (x = y ∧ f = g ⊸ ∏ n, Nat_destruct (x, f) n = Nat_destruct (y, g) n).
  rew <-all_adj. intros [| m].
  + apply aandl.
  + rew (aandr _ _). exact (all_lb _ _).
Qed.

Canonical Structure Nat_destruct_fun {X:set} : _ ⇾ _ := @func_make _ _ _ (@Nat_destruct_is_fun X).

Section dec.
  Local Open Scope set_scope.
  Local Definition eq_code : Nat → Nat → Ω := fix F (a b : Nat) := match (a, b) with
  | (nat_0, nat_0) => 𝐓
  | (nat_S _, nat_0) => 𝐅
  | (nat_0, nat_S _) => 𝐅
  | (nat_S m, nat_S n) => F m n
  end.
  Local Definition eq_encode : ∀ m n, m = n → eq_code m n.
  Proof. intros n _ []. revert n. refine (fix F a := match a with
    | nat_0 => I
    | nat_S m => F m
    end).
  Defined.
  Local Definition eq_decode : ∀ m n, eq_code m n → m = n.
  Proof. notypeclasses refine (fix F (a b : Nat) {struct a} := match (a, b) as p return (eq_code (π₁ p) (π₂ p) → π₁ p = π₂ p) with
    | (nat_0, nat_0) => λ c, _
    | (nat_S _, nat_0) => λ c, match c with end
    | (nat_0, nat_S _) => λ c, match c with end
    | (nat_S m, nat_S n) => λ c : eq_code m n, _
    end).
    + now change (nat_0 = nat_0).
    + change (Nat_S m = Nat_S n). now apply (is_fun Nat_S), F.
  Qed.

  Instance Nat_S_inj : Injective (X:=Nat) suc.
  Proof. intros m n. apply affirmative_aimpl. intro E.
    apply eq_decode. exact (eq_encode _ _ E).
  Qed.

  Definition Nat_S_nonzero (n:Nat) : suc n ≠ 0 := eq_encode _ _.

  Definition nat_eq_dec := fix F (a b : nat) :=
    match a with
    | nat_0 => match b with
      | nat_0 => true
      | nat_S _ => false
      end
    | nat_S m => match b with
      | nat_0 => false
      | nat_S n => F m n
      end
    end.

  Instance Nat_eq_dec : Dec (A:=Nat∗Nat) (=) := tuncurry nat_eq_dec.

  Instance Nat_eq_is_dec : IsDecEq Nat.
  Proof. intros [x y]. change (if nat_eq_dec x y then x = y else x ≠ y).
    refine ((fix IH (a b : nat) := _) x y); clear x y.
    destruct a as [| m], b as [| n]; cbn [ nat_eq_dec ].
  + refl.
  + intro E; pose proof eq_encode _ _ E as [].
  + intro E; pose proof eq_encode _ _ E as [].
  + specialize (IH m n). revert IH.
    destruct (nat_eq_dec m n) as [|].
    * apply (is_fun Nat_S m n).
    * apply (contrapositive (injective suc m n)).
  Qed.

  Definition Nat_decidable : DecidableEquality Nat := Nat_eq_is_dec.
End dec.
Global Hint Extern 2 (Injective (X:=Nat) suc) => refine Nat_S_inj : typeclass_instances.
Global Hint Extern 2 (DecidableEquality Nat) => refine Nat_decidable : typeclass_instances.
Global Hint Extern 2 (AffirmativeEquality Nat) => refine Nat_decidable : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality Nat) => refine Nat_decidable : typeclass_instances.
Global Hint Extern 2 (StrongSet Nat) => refine Nat_decidable : typeclass_instances.

Global Hint Extern 2 (Dec (A:=nat) (=)) => refine Nat_eq_dec : typeclass_instances.
Global Hint Extern 2 (Dec (A:=set_T Nat) (=)) => refine Nat_eq_dec : typeclass_instances.
Global Hint Extern 2 (@IsDecEq _ Nat_eq_dec) => simple notypeclasses refine Nat_eq_is_dec : typeclass_instances.

