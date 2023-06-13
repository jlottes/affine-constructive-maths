Require Import abstract_algebra interfaces.naturals.
Require Import theory.set interfaces.sprop logic.aprop.
Require Import implementations.nat.nno.
Require Import easy rewrite.
Require Import quote.base rewrite_preserves change_quantifiers.

Import modality_notation.

Section quote.
  Universes i.
  Context `(f:X ⇾ Y) `{MaybeAlgebra_Morphism@{i} (X:=X) (Y:=Y) (f:=f)}.

  Lemma quote_suc {x y} : quote f x y → quote f (suc x) (suc y).
  Proof. unfold quote. intros E. now rew (preserves_suc f _), E. Qed.
End quote.

Global Hint Extern 4 (quote _ (func_op suc _) _) => quote_hint_strip (fun f => refine (quote_suc f _)) : quote.
Global Hint Extern 4 (quote _ _ (func_op suc _)) => quote_hint_strip (fun f => refine (quote_suc f _)) : quote.

Lemma alt_Build_MaybeAlgebra_Morphism `{Zero X} `{Successor X} `{Zero Y} `{Successor Y} (f:X ⇾ Y) :
  f 0 = 0 → (∀ x, f (suc x) = suc (f x)) → MaybeAlgebra_Morphism f.
Proof. now split. Qed.

Lemma id_maybe_algebra_morphism `{Zero X} `{Successor X} : MaybeAlgebra_Morphism (id_fun X).
Proof. now apply alt_Build_MaybeAlgebra_Morphism. Qed.
Global Hint Extern 2 (MaybeAlgebra_Morphism (id_fun _)) => simple notypeclasses refine id_maybe_algebra_morphism : typeclass_instances.

Lemma compose_maybe_algebra_morphism
  `{Zero X₁} `{Successor X₁}
  `{Zero X₂} `{Successor X₂}
  `{Zero X₃} `{Successor X₃}
  {f:X₁ ⇾ X₂} {g:X₂ ⇾ X₃}
 : MaybeAlgebra_Morphism f → MaybeAlgebra_Morphism g → MaybeAlgebra_Morphism (g ∘ f).
Proof. intros. apply alt_Build_MaybeAlgebra_Morphism; change (func_op (g ∘ f) ?x) with (g (f x)).
+ rewrite_preserves f. exact (preserves_0 g).
+ intro. rewrite_preserves f. exact (preserves_suc _ _).
Qed.
Global Hint Extern 2 (MaybeAlgebra_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_maybe_algebra_morphism _ _) : typeclass_instances.

Local Open Scope fun_inv_scope.

Lemma invert_maybe_algebra_morphism `{MaybeAlgebra_Morphism (f:=f)} `{!Inverse f} `{!Bijective f}
  : MaybeAlgebra_Morphism f⁻¹.
Proof. apply alt_Build_MaybeAlgebra_Morphism.
+ quote_injective f. exact (surjective_applied f _).
+ intro y. quote_injective f. now rew !2(surjective_applied f _).
Qed.
Global Hint Extern 2 (MaybeAlgebra_Morphism (_⁻¹)) => simple notypeclasses refine invert_maybe_algebra_morphism : typeclass_instances.

Lemma nno_initial_alt `{NaturalNumbersObject N}
  `{Zero X} `{Successor X} (f g : N ⇾ X)
  `{!MaybeAlgebra_Morphism f} `{!MaybeAlgebra_Morphism g}
  : f = g.
Proof. now rew [ (nno_initial f) | (nno_initial g) ]. Qed.


Global Hint Extern 5 (Inverse (nno_to_set ?N₁ ?N₂)) => refine (nno_to_set N₂ N₁) : typeclass_instances.
Lemma nno_to_nno_bijective `{NaturalNumbersObject N₁} `{NaturalNumbersObject N₂}
  : Bijective (nno_to_set N₁ N₂).
Proof. apply alt_Build_Bijective; unfold inverse; now apply nno_initial_alt. Qed.
Global Hint Extern 5 (Bijective (nno_to_set _ _)) => simple notypeclasses refine nno_to_nno_bijective : typeclass_instances.
Global Hint Extern 10 (Injective (nno_to_set _ _)) => simple notypeclasses refine nno_to_nno_bijective : typeclass_instances.
Global Hint Extern 5 (Surjective (nno_to_set _ _)) => simple notypeclasses refine nno_to_nno_bijective : typeclass_instances.

Require Import set_lambda.

Section contents.
  Universes i.
  Context `{NaturalNumbersObject@{i} ℕ}.

  Let ψ := (nno_to_set@{i} ℕ Nat).
  Local Hint Extern 2 => progress unfold ψ : typeclass_instances.

  Let inst : MaybeAlgebra_Morphism ψ := _.
  Let inst2 : Bijective ψ := _.
  Let inst3 : MaybeAlgebra_Morphism ψ⁻¹ := _.

  Instance nno_suc_inj : Injective (X:=ℕ) suc.
  Proof. intros x y. rew !2(injective_iff ψ _ _). rewrite_preserves ψ.
    exact (injective suc _ _).
  Qed.

  Lemma nno_suc_nonzero (n:ℕ) : suc n ≠ 0.
  Proof. quote_ne ψ. exact (Nat_S_nonzero _). Qed.

  Instance nno_dec_eq : DecidableEquality ℕ.
  Proof. intros x y. now rew (injective_iff ψ _ _). Qed.
  Let inst4 := nno_dec_eq.

  Lemma nno_zero_or_suc (n:ℕ) : n = 0 ∨ ∐ m, n = suc m.
  Proof. generalize (bijective_applied ψ n). destruct (ψ n) as [| m'].
  + change (ψ⁻¹ nat_0) with (ψ⁻¹ 0).
    rewrite_preserves ψ⁻¹. intro E. now left.
  + change (ψ⁻¹ (nat_S m')) with (ψ⁻¹ (suc m')).
    rewrite_preserves ψ⁻¹. intro E. right. now exists (ψ⁻¹ m').
  Qed.

  Section induction.
    Context (P:func_set@{i} ℕ AProp_set@{i}).

    Lemma nno_ind : (∀ n, P n ⊸ P (suc n)) → (P 0 ⊸ all P).
    Proof. intros Ps.
      enough (P (ψ⁻¹ 0) ⊸ (∏ n, P (ψ⁻¹ n))) as HP'.
      + rew <-all_adj. intros y. now rew HP', (all_lb _ (ψ y)), (bijective_applied ψ y).
      + apply ( Nat_ind (λ n, P (ψ⁻¹ n)) ).
        intros n. rew (Ps (ψ⁻¹ n)). now rewrite_preserves (ψ⁻¹).
    Qed.
  End induction.

  Lemma nno_ind_alt (P:ℕ → Ω) : (∀ n m, n = m → P n → P m)
    → P 0 → (∀ n, P n → P (suc n)) → all P.
  Proof. intros Pp P0 Ps.
    simple notypeclasses refine (let P' := make_fun (λ n, ! (P n)) in _).
    + intros n m. apply affirmative_aimpl. intros E. change (! (P n) ⧟ ! (P m)).
      apply affirmative_aiff. change (P n ↔ P m). split; now apply Pp.
    + apply ( nno_ind P' ); trivial. intros n. change (! (P n) ⊸ ! (P (suc n))).
      apply affirmative_aimpl, Ps.
  Qed.

  Context {X:set@{i}}.

  Notation ϕ f x := (@nno_to_set ℕ _ X x f).
  Let base (f:X ⇾ X) (x:X) : ϕ f x 0 = x.  Proof. exact (maybe_alg_preserves_zero (ϕ f x) (zY:=x) (sY:=f)). Qed.
  Let step (f:X ⇾ X) (x:X) : ∀ n, ϕ f x (suc n) = f (ϕ f x n).  Proof. exact (preserves_suc (ϕ f x) (zY:=x) (sY:=f)). Qed.

  Local Instance nno_rec_is_fun (f : X ⇾ X) : IsFun (λ (x:X), ϕ f x).
  Proof.
    intros x₁ x₂. rew <-(base f x₁) at 1. rew <-(base f x₂) at 1.
    simple refine (let P := make_fun (λ n, ϕ f x₁ n = ϕ f x₂ n) in nno_ind P _).
    + intros n m. apply affirmative_aimpl. intro E. change ((ϕ f x₁ n = ϕ f x₂ n) ⧟ (ϕ f x₁ m = ϕ f x₂ m)). now rew E.
    + intros n. change (ϕ f x₁ n = ϕ f x₂ n ⊸ ϕ f x₁ (suc n) = ϕ f x₂ (suc n)).
      rew [ (step f x₁ n) | (step f x₂ n) ]. exact (is_fun f _ _).
  Qed.

  Definition nno_rec@{| Set < i} (f:X ⇾ X) : X × ℕ ⇾ X.
  Proof. simple refine (strong_op (uncurry (make_fun (λ x : X, ϕ f x)))); try exact _. refine (dec_strong_op_r _). Defined.

  Definition nno_rec_base f x : nno_rec f (x, 0) = x := base f x.
  Definition nno_rec_step f x n : nno_rec f (x, suc n) = f (nno_rec f (x, n)) := step f x n.

  Context `{!StrongSet@{i} X}.

  Local Instance nno_rec_strong_is_fun@{} : IsFun nno_rec.
  Proof. intros f g.
    change ((∏ x, f x = g x) ⊸ (∏ p, nno_rec f p = nno_rec g p)).
    rew <-all_adj. intros [y n]. revert y. rew all_adj.
    change ((∏ x, f x = g x) ⊸ ∏ (x:X), ϕ f x n = ϕ g x n).
    revert n. apply nno_ind_alt.
    + intros n m E. now rew E.
    + rew <-all_adj. intros x. rew [ (base f x) | (base g x) ]. now rew (aiff_is_true (_ : x = x)).
    + intros n IH. rew <-all_adj. intros x.
      rew [ (step f x n) | (step g x n) ].
      rew <-( strong_transitivity (=) (f (ϕ f x n)) (g (ϕ f x n)) (g (ϕ g x n)) ).
      apply aand_intro.
      * now rew (all_lb _ (ϕ f x n)).
      * rew [ IH | <-(is_fun g _ _) ]. now rew (all_lb _ x).
  Qed.

  Definition nno_rec_fun := make_fun nno_rec.
  Definition nno_rec_fun_base f x : nno_rec_fun f (x, 0) = x := base f x.
  Definition nno_rec_fun_step f x n : nno_rec_fun f (x, suc n) = f (nno_rec f (x, n)) := step f x n.
End contents.
Coercion nno_suc_inj : NaturalNumbersObject >-> Injective.
Coercion nno_dec_eq : NaturalNumbersObject >-> DecidableEquality.
Arguments nno_rec ℕ {_ _ _ _ X} f.
Arguments nno_rec_base {_ _ _ _ _ X f x}.
Arguments nno_rec_step {_ _ _ _ _ X f x} n.
Canonical Structure nno_rec_fun.
Arguments nno_rec_fun ℕ {_ _ _ _ X _}.
Arguments nno_rec_fun_base {_ _ _ _ _ X _ f x}.
Arguments nno_rec_fun_step {_ _ _ _ _ X _ f x} n.


Ltac nno_induction :=
    hnf; try change_quantifiers;
    apply nno_ind_alt; [
      intros ??; let E := fresh "E" in intro E; now rew E
    |..].

