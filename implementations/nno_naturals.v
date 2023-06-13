Require Import abstract_algebra interfaces.naturals interfaces.bundled_algebra.
Require Import interfaces.sprop logic.aprop.
Require Import theory.nno theory.rings.
Require Import easy rewrite rewrite_preserves.

Section initial_mon.
  Universes i.
  Context `{NaturalNumbersObject@{i} ℕ}.

  Instance nno_to_mon : NaturalsToMon ℕ := λ M pM zM oM, nno_to_set ℕ M.

  Context `{One@{i} ℕ} `{Plus@{i} ℕ} `{Mult@{i} ℕ}.
  Context `{!NearRig@{i} ℕ}.
  Context (suc_correct : ∀ n:ℕ, suc n = 1 + n).

  Section another_monoid.
    Context `{AdditiveNonComMonoid M} {oM:One M}.

    Local Notation ϕ := (nno_to_set ℕ M).

    Lemma nno_to_mon_one : ϕ 1 = 1.
    Proof.
      rew <-(plus_0_r (R:=ℕ) 1), <-(suc_correct _).
      rewrite_preserves constr:(ϕ).
      exact (plus_0_r _).
    Qed.

    Lemma nno_to_mon_plus : ∀ x y, ϕ (x + y) = ϕ x + ϕ y.
    Proof. nno_induction.
    + intros y. now rew (plus_0_l _), (preserves_0 ϕ), (plus_0_l _).
    + intros n IHn y.
      rew (suc_correct n) at 1. rew <-(associativity (+) _ _ _), <-(suc_correct _).
      rewrite_preserves constr:(ϕ). rew (IHn y).
      exact (associativity (+) _ _ _).
    Qed.

    Context (f:ℕ ⇾ M) `{!AdditiveMonoid_Morphism f} `{!One_Pointed_Morphism f}.

    Local Instance: MaybeAlgebra_Morphism f.
    Proof. split; try exact _.
      intros x. rew (suc_correct x). now rewrite_preserves f.
    Qed.

    Lemma nno_to_mon_unique : f = ϕ.
    Proof nno_initial f.
  End another_monoid.

  Lemma nno_naturals : Naturals ℕ.
  Proof. split; trivial; intros M; intros.
  + apply alt_Build_AdditiveMonoid_Morphism.
    * exact nno_to_mon_plus.
    * exact (preserves_0 (nno_to_set ℕ M)).
  + exact nno_to_mon_one.
  + now apply nno_to_mon_unique.
  Qed.
End initial_mon.
