Require Import abstract_algebra  interfaces.bundled_algebra.
Require Export interfaces.group_completion.
Require Import interfaces.sprop logic.aprop theory.bundled_groups theory.rings.
Require Import grothendieck_group.
Require Import easy replc rewrite_preserves.
Require Import tactics.algebra.com_monoids.

Local Open Scope fun_inv_scope.

Definition from_group_completion2 `{U:FromGroupCompletion (M:=M) (K:=K) i} `{AdditiveNonComGroup A} (f : M ⇾ A) `{!AdditiveMonoid_Morphism f}
  : K ⇾ A
:= from_group_completion i (A:=make_additive_non_com_group A) f.
Arguments from_group_completion2 {M _ _ K} i {U A _ _ _ _} f {_}.
Local Notation ψ := from_group_completion2.

Section from_group_completion2.
  Universes i.
  Context `{GroupCompletion@{i} (M:=M) (K:=K) i}.
  Context `{AdditiveNonComGroup A} {f:M ⇾ A} `{!AdditiveMonoid_Morphism f}.

  Lemma from_group_completion2_mor : AdditiveMonoid_Morphism (ψ i f).
  Proof. apply (from_group_completion_prop (A:=make_additive_non_com_group A) f). Qed.

  Lemma from_group_completion2_spec : (ψ i f) ∘ i = f.
  Proof. apply (from_group_completion_prop (A:=make_additive_non_com_group A) f). Qed.

  Lemma from_group_completion2_unique (h:K ⇾ A) `{!AdditiveMonoid_Morphism h} : h ∘ i = f → h = ψ i f.
  Proof. now apply (from_group_completion_prop (A:=make_additive_non_com_group A) f). Qed.
End from_group_completion2.

Global Hint Extern 2 (AdditiveMonoid_Morphism (ψ _ _)) => simple notypeclasses refine from_group_completion2_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (ψ _ _)) => simple notypeclasses refine from_group_completion2_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (ψ _ _)) => simple notypeclasses refine from_group_completion2_mor : typeclass_instances.


(** The group completion is unique up to isomorphism *)

Global Hint Extern 6 (Inverse (ψ ?i₁ ?i₂)) => refine (ψ i₂ i₁) : typeclass_instances.


Lemma group_completion_iso_aux
  `{AdditiveMonoid M} `{AdditiveGroup K₁} `{AdditiveGroup K₂}
  `{!GroupCompletion (M:=M) (K:=K₁) i₁ (U:=U₁)}
  `{!GroupCompletion (M:=M) (K:=K₂) i₂ (U:=U₂)} :
  ψ i₁ i₂ ∘ ψ i₂ i₁ = id.
Proof. refine (andl (transitivity _ _ _ _) _); split.
+ apply (from_group_completion2_unique (ψ i₁ i₂ ∘ ψ i₂ i₁)).
  change (ψ i₁ i₂ ∘ (ψ i₂ i₁ ∘ i₂) = i₂).
  rew from_group_completion2_spec.
  exact from_group_completion2_spec.
+ sym. now apply (from_group_completion2_unique id).
Qed.

Lemma group_completion_iso
  `{AdditiveMonoid M} `{AdditiveGroup K₁} `{AdditiveGroup K₂}
  `{!GroupCompletion (M:=M) (K:=K₁) i₁ (U:=U₁)}
  `{!GroupCompletion (M:=M) (K:=K₂) i₂ (U:=U₂)} :
  Bijective (ψ i₁ i₂).
Proof. apply alt_Build_Bijective; exact group_completion_iso_aux. Qed.

Global Hint Extern 5  (Bijective  (ψ _ _)) => simple notypeclasses refine group_completion_iso : typeclass_instances.
Global Hint Extern 10 (Injective  (ψ _ _)) => simple notypeclasses refine group_completion_iso : typeclass_instances.
Global Hint Extern 5  (Surjective (ψ _ _)) => simple notypeclasses refine group_completion_iso : typeclass_instances.

Import projection_notation.

Section properties.
  Universes i.
  Context `{AdditiveMonoid M} `{AdditiveGroup K} i `{!GroupCompletion@{i} (M:=M) (K:=K) i (U:=U)}.

  Local Notation ϕ := (to_grothendieck_group M).
  Local Notation ψ' := (ψ i ϕ).

  Definition group_completion_split (k:K) : M ⊗ M := let x := ψ' k in (pos x, neg x).
  Notation s := group_completion_split.

  Lemma group_completion_split_spec (k:K) : k = i (π₁ (s k)) - i (π₂ (s k)).
  Proof. sym. exact (group_completion_iso_aux (i₁ := ϕ) (i₂:=i) k). Qed.

  Lemma group_completion_decompose : ∏ k:K, ∐ p n : M, k = i p - i n.
  Proof. intros k. exists (π₁ (s k)). exists (π₂ (s k)).
    apply group_completion_split_spec.
  Qed.

  Lemma group_completion_aff_eq `{!AffirmativeEquality M} : AffirmativeEquality K.
  Proof. intros x y. now rew (injective_iff ψ' _ _). Qed.

  Context `{!AdditiveCancellation M}.

  Lemma to_group_completion_inj : Injective i.
  Proof. intros x y.
    rew <-(injective ϕ x y).
    rew <-(from_group_completion2_spec : ψ' ∘ i = ϕ).
    exact (is_fun ψ' _ _).
  Qed.

  Lemma group_completion_strong `{!StrongOp (X:=M) (+)} : StrongSet K.
  Proof. intros x y z. rew ?(injective_iff ψ' _ _). now apply strong_transitivity. Qed.

  Lemma group_completion_dec_eq `{!DecidableEquality M} : DecidableEquality K.
  Proof. intros x y. now rew ?(injective_iff ψ' _ _). Qed.

  Lemma group_completion_ref_eq `{!RefutativeEquality M} : RefutativeEquality K.
  Proof. intros x y. now rew ?(injective_iff ψ' _ _). Qed.
End properties.

Local Open Scope mult_scope.

Section one_pointed.
  Universes i.
  Context `{AdditiveMonoid M} `{AdditiveGroup K} `{!GroupCompletion@{i} (M:=M) (K:=K) i (U:=U)}.
  Context {oM:One M} {oK:One K} `{!One_Pointed_Morphism i}.

  Context `{AdditiveNonComGroup A} {f: M ⇾ A} `{!AdditiveMonoid_Morphism f}.
  Context {oA:One A} `{!One_Pointed_Morphism f}.

  Lemma from_group_completion_one_pointed : One_Pointed_Morphism (ψ i f).
  Proof. change (ψ i f 1 = 1). rew <-(preserves_1 i).
    change (ψ i f (i ?a)) with ((ψ i f ∘ i) a).
    rew from_group_completion2_spec.
    exact (preserves_1 f).
  Qed.
End one_pointed.
Global Hint Extern 2 (One_Pointed_Morphism (ψ _ _)) => simple notypeclasses refine from_group_completion_one_pointed : typeclass_instances.

Section ring.
  Universes i.
  Context `{Rig S} `{Ring K} {i: S ⇾ K} `{!Rig_Morphism@{i} i}.
  Context `{!GroupCompletion (M:=S) (K:=K) i (U:=U)}.

  Context `{Ring R} {f: S ⇾ R} `{!Rig_Morphism f}.

  Lemma from_group_completion_rig_mor : Rig_Morphism (ψ i f).
  Proof. split; [ exact _ |]. apply alt_Build_MultiplicativeMonoid_Morphism; [| exact (preserves_1 _) ].
    intros x y.
    pose proof (group_completion_decompose i x) as [a [b E]]; rew E; clear E x.
    pose proof (group_completion_decompose i y) as [c [d E]]; rew E; clear E y.
    rewrite_preserves (ψ i f).
    change (ψ i f (i ?a)) with ((ψ i f ∘ i) a).
    rew from_group_completion2_spec.
    rew [ (mult_minus_distr_l _ _ _) | (mult_minus_distr_l _ _ _) ].
    rew [ (mult_minus_distr_r _ _ _) | (mult_minus_distr_r _ _ _) | (mult_minus_distr_r _ _ _) | (mult_minus_distr_r _ _ _) ].
    rew <-exact:(negate_swap_r (f b · f d) (f a · f d)).
    rew <-exact:(negate_swap_r (i b · i d) (i a · i d)).
    replc (i a · i c - i b · i c + (i b · i d - i a · i d)) with
          ( i (a · c + b · d) - i (a · d + b · c) )
        by (rewrite_preserves i; rew (negate_plus_distr (i a · i d) (i b · i c)); add_mon) and
          (f a · f c - f b · f c + (f b · f d - f a · f d)) with
          ( f (a · c + b · d) - f (a · d + b · c) )
        by (rewrite_preserves f; rew (negate_plus_distr (f a · f d) (f b · f c)); add_mon).
    rewrite_preserves (ψ i f).
    change (ψ i f (i ?a)) with ((ψ i f ∘ i) a).
    now rew from_group_completion2_spec.
  Qed.
End ring.
Global Hint Extern 2 (Rig_Morphism (ψ _ _)) => simple notypeclasses refine from_group_completion_rig_mor : typeclass_instances.
Global Hint Extern 2 (Rg_Morphism (ψ _ _)) => simple notypeclasses refine from_group_completion_rig_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (ψ _ _)) => simple notypeclasses refine from_group_completion_rig_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (ψ _ _)) => simple notypeclasses refine from_group_completion_rig_mor : typeclass_instances.


Section commutative_ring.
  Universes i.
  Context `{H:CommutativeRig S} `{!StrongSet S} `{Ring K} {i: S ⇾ K} `{!Rig_Morphism@{i} i}.
  Context `{!GroupCompletion (M:=S) (K:=K) i (U:=U)}.

  Let inst : AdditiveMonoid S := _.

  Local Notation ϕ := (@to_grothendieck_group S _ _ inst).

  Lemma group_completion_is_com_ring : CommutativeRing K.
  Proof. apply (comring_from_ring _). intros x y.
    apply (injective (ψ i ϕ)). rewrite_preserves (ψ i ϕ).
    exact (commutativity (·) _ _).
  Qed.
End commutative_ring.


