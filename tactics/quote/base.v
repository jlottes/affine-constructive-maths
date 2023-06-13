Require Import abstract_algebra logic.aprop.
Require Import rewrite tactics.misc strip_coercions.

Definition quote `(f:X ⇾ Y) (x:X) (y:Y) : SProp := f x = y.
Definition quote_wrap `(f:X ⇾ Y) (P:SProp) := P.

Definition quote_refl `(f:X ⇾ Y) (x:X) : quote f x (f x) := reflexivity (=) (f x).

Lemma quote_equation `(f:X ⇾ Y) {x₁ y₁ x₂ y₂} :
  quote f x₁ y₁ → quote f x₂ y₂ → (x₁ = x₂ ⊸ y₁ = y₂).
Proof. unfold quote. intros P Q. rew [ <-P | <-Q ]. exact (is_fun f _ _). Qed.

Lemma quote_ne `(f:X ⇾ Y) {x₁ y₁ x₂ y₂} :
  quote f x₁ y₁ → quote f x₂ y₂ → (y₁ ≠ y₂ ⊸ x₁ ≠ x₂).
Proof. intros P Q. exact (contrapositive (quote_equation f P Q)). Qed.

Lemma quote_injective `(f:X ⇾ Y) `{!Injective f} {x₁ y₁ x₂ y₂} :
  quote f x₁ y₁ → quote f x₂ y₂ → (x₁ = x₂ ⧟ y₁ = y₂).
Proof. unfold quote. intros P Q. rew [ <-P | <-Q ]. exact (injective_iff f _ _). Qed.

Lemma quote_injective_ne `(f:X ⇾ Y) `{!Injective f} {x₁ y₁ x₂ y₂} :
  quote f x₁ y₁ → quote f x₂ y₂ → (x₁ ≠ x₂ ⧟ y₁ ≠ y₂).
Proof. intros P Q. exact (contrapositive_iff (quote_injective f P Q)). Qed.

Create HintDb quote discriminated.
Ltac solve_quote := typeclasses eauto with quote nocore.

Tactic Notation "quote_hint_strip" tactic(tac) :=
  let f := lazymatch goal with |- quote ?f _ _ => strip_coercions f end in tac f.
Ltac quote_unwrap := change (quote_wrap _ ?P) with P.

Global Hint Extern 100 (quote ?f _ _) => refine (quote_refl f _) : quote.

Global Hint Extern 2 (quote_wrap ?f (apos (_ ⊸ _ = _))) => quote_unwrap; refine (quote_equation f _ _) : quote.
Global Hint Extern 2 (quote_wrap ?f (apos (_ = _ ⊸ _))) => quote_unwrap; refine (quote_equation f _ _) : quote.

Global Hint Extern 2 (quote_wrap ?f (apos (_ ⊸ _ ≠ _))) => quote_unwrap; refine (quote_ne f _ _) : quote.
Global Hint Extern 2 (quote_wrap ?f (apos (_ ≠ _ ⊸ _))) => quote_unwrap; refine (quote_ne f _ _) : quote.

Global Hint Extern 2 (quote_wrap ?f (apos (_ ⧟ _ = _))) => quote_unwrap; refine (quote_injective f _ _) : quote.
Global Hint Extern 2 (quote_wrap ?f (apos (_ = _ ⧟ _))) => quote_unwrap; refine (quote_injective f _ _) : quote.

Global Hint Extern 2 (quote_wrap ?f (apos (_ ⧟ _ ≠ _))) => quote_unwrap; refine (quote_injective_ne f _ _) : quote.
Global Hint Extern 2 (quote_wrap ?f (apos (_ ≠ _ ⧟ _))) => quote_unwrap; refine (quote_injective_ne f _ _) : quote.

Ltac quote_source f expr :=
  lazymatch constr:(ltac:(solve_quote) : quote f expr _) with ?P => P end.

Ltac quote_target f expr :=
  lazymatch constr:(ltac:(solve_quote) : quote f _ expr) with ?P => P end.

Ltac quote_wrap f P :=
  lazymatch constr:(ltac:(solve_quote) : quote_wrap f P) with ?Q => Q end.

Ltac quote_injective f :=
  lazymatch goal with |- apos ?E =>
    let q := quote_wrap f uconstr:(apos (E ⧟ _)) in
    simple notypeclasses refine (sprop.andr (aiff_iff_pos q) _)
  end.

Ltac quote_ne f :=
  lazymatch goal with |- apos ?E =>
    let q := quote_wrap f uconstr:(apos (_ ⊸ E)) in
    simple notypeclasses refine (aimpl_impl_pos q _)
  end.



