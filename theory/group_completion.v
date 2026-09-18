Require Import abstract_algebra  interfaces.bundled_algebra.
Require Export interfaces.group_completion.
Require Import interfaces.sprop logic.aprop logic.relations theory.bundled_groups theory.rings.
Require Import interfaces.ring_order orders.orders orders.groups orders.rings.
Require Import grothendieck_group.
Require Import easy replc rewrite_preserves simplify.
Require Import tactics.algebra.com_monoids.

Local Open Scope fun_inv_scope.

Definition from_group_completion2 `{U:FromGroupCompletion (M:=M) (K:=K) i} `{AdditiveNonComGroup A} (f : M ⇾ A) `{!AdditiveMonoid_Morphism f}
  : K ⇾ A
:= from_group_completion i (A:=make_additive_non_com_group A) f.
Arguments from_group_completion2 {M _ _ K} i {U A _ _ _ _} f {_}.
Local Abbreviation ψ := from_group_completion2.

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
  ψ i₁ i₂ ∘ ψ i₂ i₁ = id_fun _.
Proof. refine (andl (transitivity _ _ _ _) _); split.
+ apply (from_group_completion2_unique (ψ i₁ i₂ ∘ ψ i₂ i₁)).
  change (ψ i₁ i₂ ∘ (ψ i₂ i₁ ∘ i₂) = i₂).
  rew from_group_completion2_spec.
  exact from_group_completion2_spec.
+ sym. now apply (from_group_completion2_unique (id_fun _)).
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

  Local Abbreviation ϕ := (to_grothendieck_group M).
  Local Abbreviation ψ' := (ψ i ϕ).

  Definition group_completion_split (k:K) : M ⊗ M := ψ' k.
  Abbreviation s := group_completion_split.

  Lemma group_completion_split_spec (k:K) : k = i (π₁ (s k)) - i (π₂ (s k)).
  Proof. sym. exact (group_completion_iso_aux (i₁ := ϕ) (i₂:=i) k). Qed.

  Lemma group_completion_decompose : ∏ k:K, ∐ p n : M, k = i p - i n.
  Proof. intros k. exists (π₁ (s k)). exists (π₂ (s k)).
    apply group_completion_split_spec.
  Qed.

  Lemma group_completion_aff_eq `{!AffirmativeEquality M} : AffirmativeEquality K.
  Proof. intros [x y]. now rew (injective_iff ψ' _ _). Qed.

  Context `{!AdditiveCancellation M}.

  Lemma to_group_completion_inj : Injective i.
  Proof. intros x y.
    rew <-(injective ϕ x y).
    rew <-(from_group_completion2_spec : ψ' ∘ i = ϕ).
    exact (is_fun ψ' _ _).
  Qed.

  Lemma group_completion_strong `{!StrongOp (X:=M) (+)} : StrongSet K.
  Proof. intros x y z. rew (injective_iff ψ' _ _). now apply strong_transitivity. Qed.

  Lemma group_completion_dec_eq `{!DecidableEquality M} : DecidableEquality K.
  Proof. intros [x y]. now rew (injective_iff ψ' _ _). Qed.

  Lemma group_completion_ref_eq `{!RefutativeEquality M} : RefutativeEquality K.
  Proof. intros [x y]. now rew (injective_iff ψ' _ _). Qed.
End properties.

Section order.
  Universes i.
  Context `{AdditiveMonoidOrder M} `{AdditiveGroup K} i `{!GroupCompletion@{i} (M:=M) (K:=K) i (U:=U)}.

  Context {Kle: Le@{i} K}.
  Context (le_correct: ∀ x y a b c d, x = i a - i b → y = i c - i d → x ≤ y ⧟ a + d ≤ c + b).
  Arguments le_correct {x y a b c d} _ _.

  Let inst : Injective i.  Proof. exact (to_group_completion_inj i). Qed.

  Lemma aux a b c d : i a - i b = i c - i d ⧟ a + d = c + b.
  Proof.
    rew (injective_iff_simp (+(i b + i d)) (i a - i b) (i c - i d)).
    replc (i a - i b + (i b + i d)) with (i a + i d + (i b - i b)) by add_mon
      and (i c - i d + (i b + i d)) with (i c + i b + (i d - i d)) by add_mon.
    simplify.
    rew <-(preserves_plus i _ _).
    sym. exact (injective_iff i _ _).
  Qed.

  Local Instance: Poset K.
  Proof. apply alt_Build_Poset.
  + intros x. pose proof group_completion_decompose i x as [a[b Ex]]. now rew (le_correct Ex Ex).
  + intros x y z.
    pose proof group_completion_decompose i x as [a[b Ex]].
    pose proof group_completion_decompose i y as [c[d Ey]].
    pose proof group_completion_decompose i z as [e[f Ez]].
    rew [(le_correct Ex Ey)|(le_correct Ey Ez)|(le_correct Ex Ez)].
    rew (order_embedding (+f) _ _ : _ ⧟ a + d + f ≤ c + b + f).
    rew (order_embedding (+b) _ _ : _ ⧟ c + f + b ≤ e + d + b).
    rew (order_embedding (+d) _ _ : _ ⧟ a + f + d ≤ e + b + d).
    rew <-(associativity (+) _ _ _).
    rew [(commutativity (+) f b)|(commutativity (+) d b)|(commutativity (+) f d)].
    now apply transitivity.
  + intros [x y].
    pose proof group_completion_decompose i x as [a[b Ex]].
    pose proof group_completion_decompose i y as [c[d Ey]].
    rew (le_correct Ex Ey), <-(eq_le _ _). rew [Ex|Ey].
    apply (aux _ _ _ _).
  + intros x y.
    pose proof group_completion_decompose i x as [a[b Ex]].
    pose proof group_completion_decompose i y as [c[d Ey]].
    rew [(le_correct Ex Ey)|(le_correct Ey Ex)].
    rew [Ex|Ey]. rew (aux _ _ _ _). apply le_antisym.
  Qed.
  Let inst2 : Poset K.  Proof. exact _. Qed.

  Lemma group_completion_add_grp_order : AdditiveGroupOrder K.
  Proof. split; try apply _. intros z. apply alt_Build_OrderPreserving. intros x y; simplify.
    change (x ≤ y ⊸ z + x ≤ z + y).
    pose proof group_completion_decompose i x as [a[b Ex]].
    pose proof group_completion_decompose i y as [c[d Ey]].
    pose proof group_completion_decompose i z as [e[f Ez]].
    rew (le_correct Ex Ey).
    assert (z + x = i (e + a) - i (f + b)) as Elhs by
      (rew [Ez|Ex]; rewrite_preserves i; rew (negate_plus_distr _ _); add_mon).
    assert (z + y = i (e + c) - i (f + d)) as Erhs by
      (rew [Ez|Ey]; rewrite_preserves i; rew (negate_plus_distr _ _); add_mon).
    rew (le_correct Elhs Erhs).
    replc (e + a + (f + d)) with (e + f + (a + d)) by add_mon
      and (e + c + (f + b)) with (e + f + (c + b)) by add_mon.
    exact (order_preserving ((e+f)+) _ _).
  Qed.
  Let inst3 : AdditiveGroupOrder K.  Proof. exact group_completion_add_grp_order. Qed.

  Lemma to_group_completion_order_embedding : OrderEmbedding i.
  Proof. apply alt_Build_OrderEmbedding.
    assert (∀ x, i x = i x - i 0) as E by now (intros x; rewrite_preserves i; simplify; exact _).
    intros x y. rew (le_correct (E _) (E _)). simplify. exact _.
  Qed.
End order.

Definition grothendieck_pairs_add_grp_order `{AdditiveMonoidOrder M} : AdditiveGroupOrder (GrothendieckPairs M)
  := group_completion_add_grp_order _ grothendieck_group_le_correct.
Global Hint Extern 2 (AdditiveGroupOrder (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_add_grp_order : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoidOrder (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_add_grp_order : typeclass_instances.
Global Hint Extern 2 (Poset (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_add_grp_order : typeclass_instances.
Global Hint Extern 2 (PreOrder (set_T (GrothendieckPairs _))) => simple notypeclasses refine grothendieck_pairs_add_grp_order : typeclass_instances.
Global Hint Extern 2 (WeakPoset (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_add_grp_order : typeclass_instances.

Definition to_grothendieck_pairs_order_embedding `{AdditiveMonoidOrder M} : OrderEmbedding (to_grothendieck_group M)
  := to_group_completion_order_embedding _ grothendieck_group_le_correct.
Global Hint Extern 2 (OrderEmbedding (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_pairs_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_pairs_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_pairs_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderMorphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_pairs_order_embedding : typeclass_instances.

Section order2.
  Universes i.
  Context `{AdditiveMonoidOrder M} `{AdditiveGroupOrder K} i `{!GroupCompletion@{i} (M:=M) (K:=K) i (U:=U)}.
  Context `{!OrderEmbedding i}.

  Lemma group_completion_order_le {x y a b c d} : x = i a - i b → y = i c - i d → x ≤ y ⧟ a + d ≤ c + b.
  Proof. intros Ex Ey. rew Ex, Ey.
    rew (order_embedding (+(i b + i d)) _ _ : _ ⧟ i a - i b + (i b + i d) ≤ i c - i d + (i b + i d) ).
    replc (i a - i b + (i b + i d)) with (i a + i d + (i b - i b)) by add_mon
      and (i c - i d + (i b + i d)) with (i c + i b + (i d - i d)) by add_mon.
    rew (plus_negate_r _), (plus_0_r _).
    rew <-(preserves_plus i _ _).
    sym. exact (order_embedding i _ _).
  Qed.
  Abbreviation le_correct := group_completion_order_le.

  Lemma group_completion_strong_poset `{!StrongPoset M} : StrongPoset K.
  Proof. split; try exact _.
    intros x y z.
    pose proof group_completion_decompose i x as [a[b Ex]].
    pose proof group_completion_decompose i y as [c[d Ey]].
    pose proof group_completion_decompose i z as [e[f Ez]].
    rew [(le_correct Ex Ey)|(le_correct Ey Ez)|(le_correct Ex Ez)].
    rew (order_embedding (+f) _ _ : _ ⧟ a + d + f ≤ c + b + f).
    rew (order_embedding (+b) _ _ : _ ⧟ c + f + b ≤ e + d + b).
    rew (order_embedding (+d) _ _ : _ ⧟ a + f + d ≤ e + b + d).
    rew <-(associativity (+) _ _ _).
    rew [(commutativity (+) f b)|(commutativity (+) d b)|(commutativity (+) f d)].
    now apply strong_transitivity.
  Qed.

  Local Ltac go := split; try exact _; intros x y; 
    pose proof group_completion_decompose i x as [a[b Ex]];
    pose proof group_completion_decompose i y as [c[d Ey]];
    repeat match goal with
      | |- context [ x ≤ y ] => rew (le_correct Ex Ey)
      | |- context [ y ≤ x ] => rew (le_correct Ey Ex)
    end.
  Local Ltac go2 := split; try exact _; intros [x y]; 
    pose proof group_completion_decompose i x as [a[b Ex]];
    pose proof group_completion_decompose i y as [c[d Ey]];
    repeat match goal with
      | |- context [ x ≤ y ] => rew (le_correct Ex Ey)
      | |- context [ y ≤ x ] => rew (le_correct Ey Ex)
    end.

  Lemma group_completion_linear_order `{!LinearOrder M} : LinearOrder K.  Proof. go; now apply pseudo_total. Qed.
  Lemma group_completion_total_order `{!TotalOrder M} : TotalOrder K.  Proof. go; now apply total. Qed.
  Lemma group_completion_refutative_order `{!RefutativeOrder M} : RefutativeOrder K.  Proof. now go2. Qed.
  Lemma group_completion_affirmative_order `{!AffirmativeOrder M} : AffirmativeOrder K.  Proof. now go2. Qed.
  Lemma group_completion_decidable_order `{!DecidableOrder M} : DecidableOrder K.  Proof. now go2. Qed.
End order2.

Global Hint Extern 2 (StrongPoset      (GrothendieckPairs ?M)) => simple notypeclasses refine (group_completion_strong_poset (to_grothendieck_group M)) : typeclass_instances.
Global Hint Extern 2 (LinearOrder      (GrothendieckPairs ?M)) => simple notypeclasses refine (group_completion_linear_order (to_grothendieck_group M)) : typeclass_instances.
Global Hint Extern 2 (TotalOrder       (GrothendieckPairs ?M)) => simple notypeclasses refine (group_completion_total_order (to_grothendieck_group M)) : typeclass_instances.
Global Hint Extern 2 (RefutativeOrder  (GrothendieckPairs ?M)) => simple notypeclasses refine (group_completion_refutative_order (to_grothendieck_group M)) : typeclass_instances.
Global Hint Extern 2 (AffirmativeOrder (GrothendieckPairs ?M)) => simple notypeclasses refine (group_completion_affirmative_order (to_grothendieck_group M)) : typeclass_instances.
Global Hint Extern 2 (DecidableOrder   (GrothendieckPairs ?M)) => simple notypeclasses refine (group_completion_decidable_order (to_grothendieck_group M)) : typeclass_instances.


Local Open Scope mult_scope.

Section one_pointed.
  Universes i.
  Context `{AdditiveMonoid M} `{AdditiveGroup K} `{!GroupCompletion@{i} (M:=M) (K:=K) i (U:=U)}.
  Context {oM:One M} {oK:One K} `{!One_Pointed_Morphism i}.

  Lemma group_completion_nontrivial `{!AdditiveCancellation M, !OneNonZero M} : OneNonZero K.
  Proof. pose proof to_group_completion_inj i.
    red. rew [<-(preserves_1 i) | <-(preserves_0 i)].
    now apply ( contrapositive (injective i 1 0) ).
  Qed.

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

Global Hint Extern 2 (OneNonZero (GrothendieckPairs ?M)) => simple notypeclasses refine (group_completion_nontrivial (i:=to_grothendieck_group M)) : typeclass_instances.

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
    rew (mult_minus_distr_l _ _ _). rew (mult_minus_distr_r _ _ _).
    rew <-(negate_swap_r (f b · f d) (f a · f d)).
    rew <-(negate_swap_r (i b · i d) (i a · i d)).
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

  Local Abbreviation ϕ := (@to_grothendieck_group S _ _ inst).

  Lemma group_completion_is_com_ring : CommutativeRing K.
  Proof. apply (comring_from_ring _). intros x y.
    apply (injective (ψ i ϕ)). rewrite_preserves (ψ i ϕ).
    exact (commutativity (·) _ _).
  Qed.
End commutative_ring.


Section ordered_ring.
  Universes i.
  Context `{StrongLinearRefutativeRigOrder (R:=S)} `{Ring K} {i: S ⇾ K} `{!Rig_Morphism@{i} i}.
  Context `{!GroupCompletion (M:=S) (K:=K) i (U:=U)}.

  Context {Kle: Le@{i} K} `{!AdditiveGroupOrder K, !OrderEmbedding i}.

  Abbreviation le_correct := (group_completion_order_le i).

  Lemma group_completion_ring_order : StrongLinearRefutativeRingOrder K.
  Proof. split; try exact _.
  + exact (group_completion_strong_poset i).
  + exact (group_completion_linear_order i).
  + exact (group_completion_refutative_order i).
  + intros x y.
    pose proof (group_completion_decompose i x) as [a [b Ex]].
    pose proof (group_completion_decompose i y) as [c [d Ey]].
    assert (x · y = i (a · c + b · d) - i (a · d + b · c)) as Exy. {
      rew [Ex|Ey]; rewrite_preserves i. rew (negate_plus_distr _ _).
      rew (plus_mult_distr_l _ _ _). rew <-(negate_mult_distr_r (i a - i b) (i d)).
      rew ?(plus_mult_distr_r (i a) (-(i b)) _).
      rew <-(negate_mult_distr_l (i b) _).
      rew <-(negate_swap_l _ _).
      add_mon.
    }
    assert (0 = i 0 - i 0) as E0 by now (rewrite_preserves i; simplify).
    apply by_contrapositive.
    rew [(le_correct Ex E0)|(le_correct Ey E0)|(le_correct Exy E0)].
    apply by_contrapositive. simplify.
    apply mult_lt_compat_full.
  Qed.
End ordered_ring.

Definition grothendieck_pairs_ring_order `{StrongLinearRefutativeRigOrder R} : StrongLinearRefutativeRingOrder (GrothendieckPairs R).
Proof. exact (group_completion_ring_order (i:=to_grothendieck_group R)). Qed.
Global Hint Extern 2 (StrongLinearRefutativeRingOrder (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_ring_order : typeclass_instances.
Global Hint Extern 2 (StrongLinearRefutativeRigOrder (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_ring_order : typeclass_instances.
Global Hint Extern 2 (NonZeroMultiplicativeCancellation (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_ring_order : typeclass_instances.
Global Hint Extern 2 (NoZeroDivisors (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_ring_order : typeclass_instances.

Section integral_domain.
  Universes i.
  Context `{StrongLinearRefutativeRigOrder@{i} (R:=S)} `{!CommutativeRig S, !OneNonZero S}.
  Context `{Ring K} {i: S ⇾ K} `{!Rig_Morphism@{i} i}.
  Context `{!GroupCompletion (M:=S) (K:=K) i (U:=U)}.

  Let inst : CommutativeRing K.  Proof. exact group_completion_is_com_ring. Qed.
  Let inst2: OneNonZero K.  Proof. exact (group_completion_nontrivial (i:=i)). Qed.

  Local Abbreviation ϕ := (to_grothendieck_group S).
  Local Abbreviation ψ' := (ψ i ϕ).

  Let inst3 : CommutativeRing (GrothendieckPairs S).
  Proof. exact _. Qed.

  Lemma group_completion_int_domain : IntegralDomain K.
  Proof. split; try exact _. intros x y.
    rew (injective_iff ψ' _ _). rewrite_preserves ψ'.
    apply no_zero_divisors.
  Qed.
End integral_domain.

Definition grothendieck_pairs_int_domain `{StrongLinearRefutativeRigOrder R} `{!CommutativeRig R, !OneNonZero R} : IntegralDomain (GrothendieckPairs R).
Proof. exact (group_completion_int_domain (i:=to_grothendieck_group R)). Qed.
Global Hint Extern 2 (IntegralDomain (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_int_domain : typeclass_instances.
