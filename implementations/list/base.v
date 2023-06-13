Require Import interfaces.set abstract_algebra bundled_algebra.
Require Import interfaces.sprop logic.aprop.
Require Import nat.
Require Import easy rewrite.

Local Open Scope grp_scope.

Section type.
  Universes i.
  Context {X:set@{i}}.

  Inductive list : Type@{i} :=
  | nil : list
  | cons : X → list → list.

  Definition list_elim {Y:set} : Y → (X → list → Y → Y) → (list → Y)
  := λ f₀ f₁, fix F l := match l with
  | nil => f₀
  | cons x l' => f₁ x l' (F l')
  end.

  Definition fold_right {Y:set@{i}} (f: X * Y → Y) : list → Y → Y := fix F x y₀ :=
  match x with
  | nil => y₀
  | cons x₀ x' => f (x₀, F x' y₀)
  end.

  Lemma list_induction (P : list → Ω) : (∏ x₀ x, P x ⊸ P (cons x₀ x)) → (P nil ⊸ all P).
  Proof. intros Ps. rew <-all_adj. simple notypeclasses refine (fix F x := match x with | nil => _ | cons x₀ x => _ end).
  + refl.
  + specialize (F x). now rew <-(Ps x₀ x).
  Qed.

  Definition list_sinduction (P:list → SProp) : P nil → (∀ x₀ x, P x → P (cons x₀ x)) → ∀ x, P x
  := λ P0 Ps, fix F x := match x with
  | nil => P0
  | cons x₀ x => Ps x₀ x (F x)
  end.

  Lemma list_destruct (P : list → Ω) : (P nil ∧ ∏ x₀ x, P (cons x₀ x)) ⊸ all P.
  Proof. rew <-all_adj. intros [| x₀ x]; [ exact _ |].
    rew (aandr _ _), (all_lb _ x₀). exact (all_lb _ _).
  Qed.

  Lemma list_sdestruct (P : list → SProp) : P nil → (∀ x₀ x, P (cons x₀ x)) → ∀ x, P x.
  Proof. intros. change ((λ x, of_course (P x)) x) . apply list_destruct; now split. Qed.


  (*
  Definition list_rec_op {Y:set@{i}} (g: X ⊗ Y ⇾ Y) (y₀:Y) : list → Y := fix F x :=
  match x with
  | nil => y₀
  | cons x₀ x' => g (f x₀, F x')
  end.
  *)

  (* Definition concat (x : list) := match x with
  | nil => y
  | cons x₀ x' => cons x₀ (concat x' y)
  end. *)

  Instance list_equiv (a:Ω → Ω → Ω) : Equiv list := fix F x y :=
  match x with
  | nil =>
    match y with
    | nil => 𝐓
    | cons _ _ => 𝐅
    end
  | cons x₀ x' =>
    match y with
    | nil => 𝐅
    | cons y₀ y' => a (x₀ = y₀) (F x' y')
    end
  end.

  (* Context {M:monoid@{i}} (f:X ⇾ M).

  Fixpoint list_to_monoid (x:list) : M := match x with
  | nil => mon_unit
  | cons x₀ x => f x₀ ∙ list_to_monoid x
  end. *)
End type.
Arguments list X : clear implicits.

Declare Scope list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.
Local Open Scope list_scope.

Module notation.
  Notation "[ ]" := nil (format "[ ]") : list_scope.
  Notation "[ x ]" := (cons x nil) : list_scope.
  Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End notation.
Import notation.


Section nth.
  Fixpoint ListInBounds {X:set} (l:list X) (n:Nat) {struct l} : SProp :=
  match l with
  | nil => False
  | cons x l' =>
    match n with
    | nat_0 => True
    | nat_S n' => ListInBounds l' n'
    end
  end.
  Existing Class ListInBounds.

  Fixpoint list_nth {X:set} (l:list X) : ∀ (n:Nat) (p:ListInBounds l n), X :=
  match l with
  | nil => λ _ p, match p with end
  | cons x l' => λ n,
    match n with
    | nat_0 => λ _, x
    | nat_S n' => list_nth l' n'
    end
  end.
  Global Arguments list_nth {X} l n {p}.
End nth.

Global Hint Extern 10 (ListInBounds _ _) => exact I : typeclass_instances.

Definition list_map {X Y:set} (f:X → Y) : list X → list Y := fix F l :=
match l with
| nil => nil
| cons x l' => cons (f x) (F l')
end.

Lemma list_map_in_bounds {X Y:set} (f:X → Y) : ∀ (l:list X) n,  ListInBounds l n → ListInBounds (list_map f l) n.
Proof. refine (list_sinduction _ _ _).
+ intros ? [].
+ intros x Γ' IH [| m].
  * intros _. exact I.
  * intros H. specialize (IH _ H). exact IH.
Qed.
Global Hint Extern 2 (ListInBounds (list_map ?f ?l) ?n) => simple notypeclasses refine (list_map_in_bounds f l n _) : typeclass_instances.

