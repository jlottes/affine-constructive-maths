(** Classical AProp kernel — used ONLY by the classical conservativity build
    (scripts/classical-build.sh), which installs this file in place of
    interfaces/aprop_kernel.v.  It must export exactly the same names, at the
    same signatures, as the constructive kernel.

    Here the [Classicality] field of [AProp] is decidability of the
    positive/negative pair, derived from an SProp-level excluded-middle
    axiom.  Under this kernel the antithesis model collapses to classical
    logic: every [Ω] is [Decidable] (see classical/sanity.v) and undecided
    pairs such as (𝐅,𝐅) cannot be constructed.  Files in counterexamples/
    are exactly those that must fail to build against this kernel. *)
Require Import interfaces.notation sprop.

Local Open Scope sprop_scope.

Definition NotBoth (P Q : SProp) := ¬ (P ∧ Q).

(** The classical axiom.  Confined to this file, which is never part of the
    default (constructive) build. *)
Axiom slem : ∀ P : SProp, P ∨ ¬ P.

Definition Classicality (P N : SProp) : SProp := P ∨ N.

Definition atrue_cl  : Classicality 𝐓 𝐅 := or_introl _ I.
Definition afalse_cl : Classicality 𝐅 𝐓 := or_intror _ I.

Definition anot_cl {P N : SProp} : Classicality P N → Classicality N P.
Proof. intros [p|n].
+ right; exact p.
+ left; exact n.
Qed.

Definition aand_cl {P N Q M : SProp}
  : Classicality P N → Classicality Q M → Classicality (P ∧ Q) (N ∨ M).
Proof. intros [p|n] [q|m].
+ left; exact (conj p q).
+ right; right; exact m.
+ right; left; exact n.
+ right; left; exact n.
Qed.

Definition aor_cl {P N Q M : SProp}
  : Classicality P N → Classicality Q M → Classicality (P ∨ Q) (N ∧ M).
Proof. intros [p|n] [q|m].
+ left; left; exact p.
+ left; left; exact p.
+ left; right; exact q.
+ right; exact (conj n m).
Qed.

Definition aprod_cl {P N Q M : SProp} (np : NotBoth P N) (nq : NotBoth Q M)
  : Classicality P N → Classicality Q M → Classicality (P ∧ Q) ((P → M) ∧ (Q → N)).
Proof. intros [p|n] [q|m].
+ left; exact (conj p q).
+ right; refine (conj (λ _, m) (λ q, _)). destruct (nq (conj q m)).
+ right; refine (conj (λ p, _) (λ _, n)). destruct (np (conj p n)).
+ right; exact (conj (λ _, m) (λ _, n)).
Qed.

Definition apar_cl {P N Q M : SProp} (np : NotBoth P N) (nq : NotBoth Q M)
  : Classicality P N → Classicality Q M → Classicality ((N → Q) ∧ (M → P)) (N ∧ M).
Proof. intros [p|n] [q|m].
+ left; exact (conj (λ _, q) (λ _, p)).
+ left; refine (conj (λ n, _) (λ _, p)). destruct (np (conj p n)).
+ left; refine (conj (λ _, q) (λ m, _)). destruct (nq (conj q m)).
+ right; exact (conj n m).
Qed.

Definition aimpl_cl {P N Q M : SProp} (np : NotBoth P N) (nq : NotBoth Q M)
  : Classicality P N → Classicality Q M → Classicality ((P → Q) ∧ (M → N)) (P ∧ M).
Proof. intros [p|n] [q|m].
+ left; refine (conj (λ _, q) (λ m, _)). destruct (nq (conj q m)).
+ right; exact (conj p m).
+ left; exact (conj (λ _, q) (λ _, n)).
+ left; refine (conj (λ p, _) (λ _, n)). destruct (np (conj p n)).
Qed.

Definition of_course_cl (P : SProp) : Classicality P (¬ P) := slem P.

Definition not_of_course_cl (P : SProp) : Classicality (¬ P) P.
Proof. destruct (slem P) as [p|np].
+ right; exact p.
+ left; exact np.
Qed.

Definition all_cl {A : Type} {P N : A → SProp}
  : (∀ x, Classicality (P x) (N x)) → Classicality (∀ x, P x) (∃ x, N x).
Proof. intros h. destruct (slem (∃ x, N x)) as [e|ne].
+ right; exact e.
+ left. intros x. destruct (h x) as [p|n].
  - exact p.
  - destruct (ne (exists N x n)).
Qed.

Definition aex_cl {A : Type} {P N : A → SProp}
  : (∀ x, Classicality (P x) (N x)) → Classicality (∃ x, P x) (∀ x, N x).
Proof. intros h. destruct (slem (∃ x, P x)) as [e|ne].
+ left; exact e.
+ right. intros x. destruct (h x) as [p|n].
  - destruct (ne (exists P x p)).
  - exact n.
Qed.
