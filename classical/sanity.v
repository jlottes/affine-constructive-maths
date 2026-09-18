(** Sanity checks for the classical conservativity build — this file is only
    ever compiled against classical/aprop_kernel.v (the build script appends
    it to the generated _RocqProject; it is not part of the default build,
    and indeed does not compile against the constructive kernel).

    With [Classicality P N := P ∨ N], the [classicality] field of [AProp] is
    literally decidability, so the internal law of excluded middle holds and
    the anticlassical witness statement of counterexamples/ is refutable.
    Together with the constructive build this exhibits the two models
    disagreeing about LEM — i.e. LEM is independent of the shared
    development. *)
Require Import interfaces.notation interfaces.aprop.

(** Every affine proposition is decidable... *)
Definition all_decidable (P : Ω) : Decidable P := classicality P.

(** ...equivalently, the internal (additive) law of excluded middle. *)
Definition internal_lem : ∏ P : Ω, P ∨ P ᗮ := λ P, classicality P.

(** The anticlassical statement witnessed in the constructive model by an
    undecided pair (𝐅,𝐅) is refuted here. *)
Definition no_undecided : (∐ P : Ω, (P ∨ P ᗮ) ᗮ) ᗮ := λ P, classicality P.
