(** AProp kernel: the [NotBoth] and [Classicality] field types of the [AProp]
    record, together with one "filler" combinator per connective producing the
    [Classicality] field.

    This is the file swapped out by the classical conservativity build
    (scripts/classical-build.sh): classical/aprop_kernel.v is installed in its
    place, where [Classicality P N := P ∨ N] and the fillers are derived from
    an SProp-level excluded-middle axiom.  Everything outside counterexamples/
    must compile against both kernels, so:
      - both kernels must export the same names at the same signatures, and
      - shared code must never apply [Build_AProp] directly; raw record
        construction is reserved for interfaces/aprop.v (which goes through
        these fillers) and for counterexamples/, which is excluded from the
        classical build.

    In this, the default constructive kernel, the field is trivial. *)
Require Import interfaces.notation sprop.

Local Open Scope sprop_scope.

Definition NotBoth (P Q : SProp) := ¬ (P ∧ Q).

Definition Classicality (P N : SProp) : SProp := 𝐓.

Definition atrue_cl  : Classicality 𝐓 𝐅 := I.
Definition afalse_cl : Classicality 𝐅 𝐓 := I.

Definition anot_cl {P N : SProp} : Classicality P N → Classicality N P := λ _, I.

Definition aand_cl {P N Q M : SProp}
  : Classicality P N → Classicality Q M → Classicality (P ∧ Q) (N ∨ M)
  := λ _ _, I.
Definition aor_cl {P N Q M : SProp}
  : Classicality P N → Classicality Q M → Classicality (P ∨ Q) (N ∧ M)
  := λ _ _, I.

Definition aprod_cl {P N Q M : SProp} (np : NotBoth P N) (nq : NotBoth Q M)
  : Classicality P N → Classicality Q M → Classicality (P ∧ Q) ((P → M) ∧ (Q → N))
  := λ _ _, I.
Definition apar_cl {P N Q M : SProp} (np : NotBoth P N) (nq : NotBoth Q M)
  : Classicality P N → Classicality Q M → Classicality ((N → Q) ∧ (M → P)) (N ∧ M)
  := λ _ _, I.
Definition aimpl_cl {P N Q M : SProp} (np : NotBoth P N) (nq : NotBoth Q M)
  : Classicality P N → Classicality Q M → Classicality ((P → Q) ∧ (M → N)) (P ∧ M)
  := λ _ _, I.

Definition of_course_cl     (P : SProp) : Classicality P (¬ P) := I.
Definition not_of_course_cl (P : SProp) : Classicality (¬ P) P := I.

Definition all_cl {A : Type} {P N : A → SProp}
  : (∀ x, Classicality (P x) (N x)) → Classicality (∀ x, P x) (∃ x, N x)
  := λ _, I.
Definition aex_cl {A : Type} {P N : A → SProp}
  : (∀ x, Classicality (P x) (N x)) → Classicality (∃ x, P x) (∀ x, N x)
  := λ _, I.
