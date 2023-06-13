Require Export interfaces.integers.
Require Import abstract_algebra interfaces.bundled_algebra interfaces.naturals.
Require Import interfaces.group_completion.
Require Import interfaces.sprop logic.aprop theory.rings theory.bundled_rings.
Require Import theory.naturals theory.group_completion.
Require Import implementations.nat implementations.grothendieck_group.
Require Import easy rewrite strip_coercions.


Lemma integers_initial_alt `{Integers Z} `{AdditiveNonComGroup G} {oG:One G}
  (f g : Z ⇾ G) `{!AdditiveMonoid_Morphism f} `{!AdditiveMonoid_Morphism g}
  `{!One_Pointed_Morphism f} `{!One_Pointed_Morphism g}
  : f = g.
Proof. now rew [ (integers_initial f) | (integers_initial g) ]. Qed.

Local Open Scope fun_inv_scope.

Global Hint Extern 5 (Inverse (integers_to_group ?Z₁ ?Z₂)) => refine (integers_to_group Z₂ Z₁) : typeclass_instances.
Lemma integers_to_integers_bijective `{Integers Z₁} `{Integers Z₂}
  : Bijective (integers_to_group Z₁ Z₂).
Proof. apply alt_Build_Bijective; unfold inverse; now apply integers_initial_alt. Qed.
Global Hint Extern 5 (Bijective (integers_to_group _ _)) => simple notypeclasses refine integers_to_integers_bijective : typeclass_instances.
Global Hint Extern 10 (Injective (integers_to_group _ _)) => simple notypeclasses refine integers_to_integers_bijective : typeclass_instances.
Global Hint Extern 5 (Surjective (integers_to_group _ _)) => simple notypeclasses refine integers_to_integers_bijective : typeclass_instances.


(** The group completion of the naturals is the integers *)

Section from_group_completion.
  Universes i.
  Context `{Ring@{i} Z}.
  Context `{Naturals@{i} N} (i:N ⇾ Z) `{!Rig_Morphism i}.
  Context `{!GroupCompletion i (U:=U2)}.

  Instance naturals_completion_to_group : IntegersToGroup Z.
  Proof. intros R; intros. exact (from_group_completion2 i (naturals_to_mon N R)). Defined.

  Lemma naturals_completion_integers : Integers Z.
  Proof. split; [ exact _ | intros R; intros; unfold integers_to_group, naturals_completion_to_group ..]; try exact _.
    apply (from_group_completion2_unique _).
    exact (naturals_initial _).
  Qed.
End from_group_completion.

Global Hint Extern 2 (IntegersToGroup (GrothendieckPairs ?N))
  => notypeclasses refine (naturals_completion_to_group (to_grothendieck_group N)) : typeclass_instances.
Global Hint Extern 2 (Integers (GrothendieckPairs ?N))
  => notypeclasses refine (naturals_completion_integers (to_grothendieck_group N)) : typeclass_instances.


(** The integers are the group completion of the naturals *)

Section is_group_completion.
  Universes i.
  Context `{Integers@{i} Z} `{Naturals@{i} N}.
  Local Notation i := (naturals_to_mon N Z).

  Instance integers_from_group_completion : FromGroupCompletion i := λ G f Hf, integers_to_group Z G (oG:=f 1).

  Instance integers_group_completion : GroupCompletion i.
  Proof. split; try exact _. intros G f ?.
    unfold from_group_completion, integers_from_group_completion.
    simple refine (let oG : One G := f 1 in _); try exact _.
    assert (One_Pointed_Morphism f) by now change (f 1 = f 1).
    assert (One_Pointed_Morphism (integers_to_group Z G (oG:=f 1))) by (exact (preserves_1 _)).
    split.
  + exact _.
  + exact (naturals_initial_alt _ _).
  + intros h ? E. simple refine (integers_initial h); try exact _.
    change (h 1 = f 1). now rew [ <-E | <-(preserves_1 i) ].
  Qed.

  Instance naturals_to_integers_inj : Injective (naturals_to_mon N Z).
  Proof to_group_completion_inj _.

  Definition integers_split : Z → N ⊗ N := group_completion_split i.

  Context (f:N ⇾ Z) `{!AdditiveMonoid_Morphism f} `{!One_Pointed_Morphism f}.

  Instance naturals_to_integers_inj_alt : Injective f.
  Proof. now rew (naturals_initial f). Qed.

  Import projection_notation.
  Lemma integers_split_spec (x:Z) : x = f (π₁ (integers_split x)) - f (π₂ (integers_split x)).
  Proof. rew (naturals_initial f). unfold integers_split.
    exact (group_completion_split_spec i x).
  Qed.

  Lemma integers_decompose (x:Z) : ∐ (n:N), x = f n ∨ x = -(f n).
  Proof. generalize (integers_split_spec x).
    destruct (integers_split x) as [a b]; unfold proj1, proj2.
    intros E; rew E; clear x E.
    pose proof naturals_distance a b as [n [E|E]]; 
      exists n; [ rew <-E; right | rew E; left ]; rew (preserves_plus f _ _).
    1: rew (negate_plus_distr _ _).
    2: rew <-(associativity (+) _ _ _), (commutativity (+) (f n) _).
    all: rew (associativity (+) _ _ _), (plus_negate_r _); exact (plus_0_l _).
  Qed.
End is_group_completion.
Global Hint Extern 2 (FromGroupCompletion (naturals_to_mon _ _)) => simple notypeclasses refine integers_from_group_completion : typeclass_instances.
Global Hint Extern 2 (GroupCompletion (naturals_to_mon _ _)) => simple notypeclasses refine integers_group_completion : typeclass_instances.


(** Properties that follow from being the group completion of the naturals *)

Section properties.
  Universes u.
  Context `{Integers@{u} Z}.
  Local Notation i := (naturals_to_mon Nat Z).

  Lemma integers_dec_eq : DecidableEquality Z.
  Proof group_completion_dec_eq i.

  Lemma integers_com_ring : CommutativeRing Z.
  Proof group_completion_is_com_ring (i:=i).

  (*
  Local Open Scope mult_scope.

  Lemma integers_to_ring_mor `{Ring R} : Rig_Morphism (integers_to_group Z R).
  Proof.
    pose proof from_group_completion_rig_mor (i:=i) (f:=(naturals_to_mon Nat R)) as P.
    enough ( integers_to_group Z R (oG:=1+0) = integers_to_group Z R ) as E by now rew <-E.
    refine (integers_initial_alt _ _).
  Qed.
  *)
End properties.
Coercion integers_dec_eq : Integers >-> DecidableEquality.
Coercion integers_com_ring : Integers >-> CommutativeRing.

Coercion integers_as_com_ring (Z:integers) := make_commutative_ring Z.
Global Hint Extern 2 (StripCoercions (integers_as_com_ring ?X)) => strip_coercions_chain X : strip_coercions.

Section properties.
  Universes u.
  Context `{Integers@{u} Z} `{NearRing@{u} R}.
  Local Notation i := (naturals_to_mon Nat Z).
  Local Notation ϕ := (naturals_to_mon Nat R).
  Local Notation ψ := (integers_to_group Z R).
  Local Open Scope mult_scope.

  Lemma integers_to_near_ring_mor : Rig_Morphism ψ.
  Proof. split; try exact _. apply alt_Build_MultiplicativeMonoid_Morphism; [ | exact (preserves_1 _) ].
    intros x y.
    pose proof integers_decompose i x as [n[E|E]]; rew E; clear x E.
    all: pose proof integers_decompose i y as [m[E|E]]; rew E; clear y E.
    2: rew <-(negate_mult_distr_r _ _).
    3: rew <-(negate_mult_distr_l _ _).
    4: rew (negate_mult_negate _ _).
    2,3,4: rew [ (preserves_negate ψ _) | (preserves_negate ψ _) ].
    all: rew <-(preserves_mult i _ _); change (ψ (i ?n)) with ((ψ ∘ i) n); rew (naturals_initial (ψ ∘ i)).
    + exact (preserves_mult ϕ _ _).
    + rew [ (naturals_to_near_ring_negate_mult_r _) | (naturals_to_near_ring_negate_mult_r _) ].
      rew (preserves_mult ϕ _ _). sym. now apply associativity.
    + rew (preserves_mult ϕ _ _). exact (negate_mult_distr_l _ _).
    + rew (naturals_to_near_ring_negate_mult_r n), <-(associativity (·) _ _ _).
      rew <-(negate_mult _), (negate_involutive _).
      exact (preserves_mult ϕ _ _).
  Qed.
End properties.

Global Hint Extern 2 (Rig_Morphism (integers_to_group _ _)) => simple notypeclasses refine integers_to_near_ring_mor : typeclass_instances.
Global Hint Extern 2 (Rg_Morphism (integers_to_group _ _)) => simple notypeclasses refine integers_to_near_ring_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (integers_to_group _ _)) => simple notypeclasses refine integers_to_near_ring_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (integers_to_group _ _)) => simple notypeclasses refine integers_to_near_ring_mor : typeclass_instances.


Section retract_is_int.
  Local Open Scope fun_inv_scope.
  Context `{Integers Z} `{Ring R} (f:Z ⇾ R).
  Context `{!Surjective f (inv:=f_inv)}.
  Context `{!AdditiveMonoid_Morphism f} `{!AdditiveMonoid_Morphism f⁻¹}.
  Context `{!One_Pointed_Morphism f} `{!One_Pointed_Morphism f⁻¹}.

  Instance retract_is_int_to_group : IntegersToGroup R.
  Proof. intros G; intros. exact (integers_to_group Z G ∘ f⁻¹). Defined.

  Lemma retract_is_int : Integers R.
  Proof. split; [ exact _ | intros G; intros; unfold integers_to_group, retract_is_int_to_group .. ]; try exact _.
    rew <-(surjective_compose_cancel f _ _).
    exact (integers_initial_alt _ _).
  Qed.
End retract_is_int.

