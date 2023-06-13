Require Import interfaces.set abstract_algebra interfaces.group_completion.
Require Import logic.aprop logic.relations theory.rings theory.bundled_groups.
Require Import tactics.algebra.com_monoids.
Require Import easy replc rewrite_preserves.


Record GrothendieckPairsT (M:set) := { pos : M ; neg : M }.
Arguments pos {M} _.
Arguments neg {M} _.

Local Notation "[ x ]-[ y ]" := ({| pos := x; neg := y |}).
Local Notation "P ⁺" := (pos P) (at level 7, no associativity, format "P ⁺").
Local Notation "P ⁻" := (neg P) (at level 7, no associativity, format "P ⁻").

Local Open Scope mult_scope.

Section ops.
  Universes i.
  Context (M:set@{i}) {pM:Plus M} {zM:Zero M}.
  Local Notation K := (GrothendieckPairsT M).
  Definition grothendieck_pairs_equiv : Equiv K
    := λ x y, ∐ k, x⁺ + y⁻ + k = y⁺ + x⁻ + k.
  Definition grothendieck_pairs_zero : K := [0]-[0].
  Local Definition plus_op (x y : K) : K := [x⁺ + y⁺]-[x⁻ + y⁻].
  Local Definition negate_op (x : K) : K := [x⁻]-[x⁺].

  Context {mM:Mult M} {oM:One M}.
  Definition grothendieck_pairs_one : K := [1]-[0].
  Local Definition mult_op (x y : K) : K := [x⁺ · y⁺ + x⁻ · y⁻]-[ x⁺ · y⁻ + x⁻ · y⁺].
End ops.

Global Hint Extern 1 (Equiv (GrothendieckPairsT ?M)) => simple notypeclasses refine (grothendieck_pairs_equiv M) : typeclass_instances.

Local Ltac unf G :=
  repeat change (?x = ?y :> GrothendieckPairsT _) with (∐ k, pos x + neg y + k = pos y + neg x + k);
  repeat change (?x = ?y :> G) with (∐ k, pos x + neg y + k = pos y + neg x + k);
  repeat change (func_op (@plus G _) (?a, ?b)) with (plus_op _ a b);
  repeat change (func_op (@negate G _) ?a) with (negate_op _ a);
  repeat change (func_op (@mult G _) (?a, ?b)) with (mult_op _ a b);
  repeat change (@zero G ?z) with z;
  repeat change (@one G ?o) with o;
  cbn [ pos neg plus_op mult_op tuncurry negate_op grothendieck_pairs_zero grothendieck_pairs_one proj1 proj2 ].

Section set.
  Universes i.
  Context `{AdditiveMonoid@{i} M}.
  Local Notation T := (GrothendieckPairsT M).

  Instance grothendieck_pairs_is_set : IsSet T.
  Proof. split.
  + intros x; unf constr:(T). now exists 0.
  + intros x y; unf constr:(T).
    rew <-aex_adj. intros k. rew <-(aex_ub _ k). now apply symmetry.
  + intros x y z; unf constr:(T).
    rew <-aex_adj2; intros k₁ k₂.
    rew <-(aex_ub _ (y⁺ + y⁻ + k₁ + k₂)).
    replc (x⁺ + z⁻ + (y⁺ + y⁻ + k₁ + k₂)) with
          ( (x⁺ + y⁻ + k₁) + (y⁺ + z⁻ + k₂) ) by add_mon
     and  (z⁺ + x⁻ + (y⁺ + y⁻ + k₁ + k₂)) with
          ( (y⁺ + x⁻ + k₁) + (z⁺ + y⁻ + k₂) ) by add_mon.
    exact (is_fun (+) (_, _) (_, _)).
  Qed.

  Definition GrothendieckPairs := set_make T.
End set.
Arguments GrothendieckPairs M {_ _ _}.
Global Hint Extern 2 (Zero   (GrothendieckPairs ?M)) => notypeclasses refine (grothendieck_pairs_zero   M) : typeclass_instances.
Global Hint Extern 2 (One    (GrothendieckPairs ?M)) => notypeclasses refine (grothendieck_pairs_one    M) : typeclass_instances.

Section funs.
  Universes i.
  Context `{AdditiveMonoid@{i} M}.
  Local Notation T := (GrothendieckPairsT M).
  Local Notation G := (GrothendieckPairs M).

  Lemma grothendieck_pairs_eq_alt `{!AdditiveCancellation M} (x y : G)
    : x = y ⧟ x⁺ + y⁻ = y⁺ + x⁻.
  Proof. split.
  + apply aex_adj. intro k. apply (injective (+k)).
  + unf constr:(G). rew <-(aex_ub _ 0). exact (is_fun (+0) _ _).
  Qed.

  Local Lemma neg_is_fun : IsFun (negate_op M : G → G).
  Proof. intros x y; unf constr:(G).
    apply aex_adj. intros k. rew <-(aex_ub _ k).
    rew [ (commutativity (+) y⁻ x⁺) | (commutativity (+) x⁻ y⁺) ].
    now apply symmetry.
  Qed.
  Definition grothendieck_pairs_negate := @make_fun _ _ _ neg_is_fun.

  Local Lemma plus_is_fun : IsFun (tuncurry (plus_op M) : G ⊗ G → G).
  Proof. intros [x₁ y₁][x₂ y₂].
    unfold_pair_eq; unf constr:(G).
    apply aex_adj2. intros k₁ k₂. rew <-(aex_ub _ (k₁ + k₂)).
    replc ( x₁⁺ + y₁⁺ + (x₂⁻ + y₂⁻) + (k₁ + k₂) ) with
          ( (x₁⁺ + x₂⁻ + k₁) + (y₁⁺ + y₂⁻ + k₂) ) by add_mon
      and ( x₂⁺ + y₂⁺ + (x₁⁻ + y₁⁻) + (k₁ + k₂) ) with
          ( (x₂⁺ + x₁⁻ + k₁) + (y₂⁺ + y₁⁻ + k₂) ) by add_mon.
    exact (is_fun (+) (_, _) (_, _)).
  Qed.

  Definition grothendieck_pairs_plus := @make_fun _ _ _ plus_is_fun.

  Hint Extern 1 (Negate G) => refine grothendieck_pairs_negate : typeclass_instances.
  Hint Extern 1 (Plus G) => refine grothendieck_pairs_plus : typeclass_instances.

  Instance grothendieck_pairs_is_group : AdditiveGroup G.
  Proof. apply alt_Build_AdditiveGroup; hnf; intros; unf constr:(G); exists 0; add_mon. Qed.
End funs.
Arguments grothendieck_pairs_negate M {_ _ _}.
Arguments grothendieck_pairs_plus M {_ _ _}.
Global Hint Extern 2 (Negate (GrothendieckPairs ?M)) => notypeclasses refine (grothendieck_pairs_negate M) : typeclass_instances.
Global Hint Extern 2 (Plus   (GrothendieckPairs ?M)) => notypeclasses refine (grothendieck_pairs_plus   M) : typeclass_instances.

Global Hint Extern 2 (AdditiveGroup           (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_is_group : typeclass_instances.
Global Hint Extern 2 (AdditiveCancellation    (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_is_group : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid          (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_is_group : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComGroup     (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_is_group : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComMonoid    (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_is_group : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComSemiGroup (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_is_group : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup       (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_pairs_is_group : typeclass_instances.

Section embedding.
  Universes i.
  Context `{AdditiveMonoid@{i} M}.
  Notation K := (GrothendieckPairs M).

  Definition to_grothendieck_group_op (x:M) : K := [x]-[0].
  Instance to_grothendieck_group_is_fun : IsFun to_grothendieck_group_op.
  Proof. intros x y. unfold to_grothendieck_group_op. unf constr:(K).
    rew <-(aex_ub _ 0). now replc (x+0+0) with x by add_mon and (y+0+0) with y by add_mon.
  Qed.
  Definition to_grothendieck_group : M ⇾ K := make_fun to_grothendieck_group_op.
  Local Instance to_grothendieck_group_is_add_mor : AdditiveMonoid_Morphism to_grothendieck_group.
  Proof. apply alt_Build_AdditiveMonoid_Morphism; [| easy ].
    intros x y. exists 0. change (x + y + (0 + 0) + 0 = x + y + 0 + 0). add_mon.
  Qed.

  Local Notation i := to_grothendieck_group.

  Lemma grothendieck_group_split (x:K) : x = i x⁺ - i x⁻.
  Proof. change (∐ k, x⁺ + (0+x⁻) + k = (x⁺+0) + x⁻ + k). exists 0. add_mon. Qed.

  Section another_group.
    Context {A:additive_non_com_group@{i}} (f:M ⇾ A) `{!AdditiveMonoid_Morphism f}.

    Definition from_grothendieck_pairs_op (x:K) : A := f x⁺ - f x⁻.
    Lemma from_grothendieck_pairs_is_fun : IsFun from_grothendieck_pairs_op.
    Proof. intros x y. unf constr:(K). apply aex_adj. intros k.
      change (?P ⊸ _) with (P ⊸ (f x⁺ - f x⁻) = (f y⁺ - f y⁻)).
      rew (right_cancellation (+) (f (x⁻ + y⁻) + f k) _ _).
      rew (commutativity (+) x⁻ y⁻) at 2.
      rewrite_preserves f.
      rew ?(associativity (+) _ _ _).
      rew [ <-(associativity (+) (f x⁺) _ _) | <-(associativity (+) (f y⁺) _ _) ].
      rew [ ( plus_negate_l _ ) | (plus_negate_l _) ].
      rew [ ( plus_0_r _ ) | (plus_0_r _) ].
      rew (is_fun f _ _). now rewrite_preserves f.
    Qed.
    Definition from_grothendieck_group := @make_fun _ _ _ from_grothendieck_pairs_is_fun.

    Let swap_f_negate x y : f x - f y = -f y + f x.
    Proof.
      apply (right_cancellation (+) (f y) _ _).
      rew <-(associativity (+) (f x) _ _), (plus_negate_l _), (plus_0_r _).
      apply (left_cancellation (+) (f y) _ _).
      rew ?(associativity (+) _ _ _). rew (plus_negate_r _), (plus_0_l _).
      rew <-!2(preserves_plus f _ _).
      now rew (commutativity (+) _ _).
    Qed.

    Lemma from_grothendieck_group_is_add_mor : AdditiveMonoid_Morphism from_grothendieck_group.
    Proof. apply Build_AdditiveGroup_Morphism. intros x y.
      change ((f (x⁺ + y⁺) - f (x⁻ + y⁻)) = (f x⁺ - f x⁻) + (f y⁺ - f y⁻)).
      rew (associativity (+) _ _ _), <-(associativity (+) (f x⁺) _ _).
      rew <-(swap_f_negate _ _). rew (associativity (+) _ _ _), <-(preserves_plus f x⁺ _).
      rew <-(associativity (+) _ _ _).
      apply (is_fun (f (x⁺ + y⁺) +)).
      rew <-(negate_plus_distr_alt _ _), <-(preserves_plus f _ _).
      now rew (commutativity (+) _ _).
    Qed.
  End another_group.

  Lemma grothendieck_group_is_completion : GroupCompletion i (U:=@from_grothendieck_group).
  Proof. split; try exact _. intros A f ?; split.
  + simple refine (from_grothendieck_group_is_add_mor f).
  + intros x. change (f x - f 0 = f x). rewrite_preserves f.
    now rew exact:(negate_0 (G:=A)), (plus_0_r _).
  + intros h ? E x. rew (grothendieck_group_split x) at 1.
    rewrite_preserves h.
    change ((h ∘ i) x⁺ - (h ∘ i) x⁻ = f x⁺ - f x⁻).
    now rew E.
  Qed.
End embedding.
Arguments to_grothendieck_group M {_ _ _}.
Global Hint Extern 2 (AdditiveMonoid_Morphism    (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_add_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_add_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism      (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_add_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid_Morphism    (from_grothendieck_group _)) => simple notypeclasses refine from_grothendieck_group_is_add_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (from_grothendieck_group _)) => simple notypeclasses refine from_grothendieck_group_is_add_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism      (from_grothendieck_group _)) => simple notypeclasses refine from_grothendieck_group_is_add_mor : typeclass_instances.

Global Hint Extern 2 (FromGroupCompletion (to_grothendieck_group ?M)) =>
  notypeclasses refine (@from_grothendieck_group M _ _ _) : typeclass_instances.
Global Hint Extern 2 (GroupCompletion (to_grothendieck_group _)) =>
  simple notypeclasses refine grothendieck_group_is_completion : typeclass_instances.

Section properties.
  Universes i.
  Context `{AdditiveMonoid@{i} M}.
  Notation K := (GrothendieckPairs M).

  Lemma grothendieck_group_aff_eq `{!AffirmativeEquality M} : AffirmativeEquality K.
  Proof. intros x y; now unf constr:(K). Qed.

  Context `{!AdditiveCancellation M}.

  Lemma to_grothendieck_group_inj : Injective (to_grothendieck_group M).
  Proof. intros x y. rew (grothendieck_pairs_eq_alt (M:=M) _ _).
    change (x+0 = y+0 ⊸ x = y).
    now rew !2(plus_0_r _).
  Qed.

  Lemma grothendieck_group_strong `{!StrongOp (X:=M) (+)} : StrongSet K.
  Proof. intros x y z. rew ?(grothendieck_pairs_eq_alt (M:=M) _ _).
    rew (right_cancellation (+) (y⁺ + y⁻) (x⁺ + z⁻) _).
    replc (x⁺ + z⁻ + (y⁺ + y⁻)) with
          ((x⁺ + y⁻) + (y⁺ + z⁻)) by add_mon
      and (z⁺ + x⁻ + (y⁺ + y⁻)) with
          ((y⁺ + x⁻) + (z⁺ + y⁻)) by add_mon.
    exact (is_fun (strong_op (+)) (_, _) (_, _)).
  Qed.

  Lemma grothendieck_group_dec_eq `{!DecidableEquality M} : DecidableEquality K.
  Proof. intros x y. now rew (grothendieck_pairs_eq_alt (M:=M) _ _). Qed.

  Lemma grothendieck_group_ref_eq `{!RefutativeEquality M} : RefutativeEquality K.
  Proof. intros x y. now rew (grothendieck_pairs_eq_alt (M:=M) _ _). Qed.
End properties.
Global Hint Extern 2 (AffirmativeEquality (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_aff_eq : typeclass_instances.
Global Hint Extern 2 (Injective (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_inj : typeclass_instances.
Global Hint Extern 2 (StrongSet (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_strong : typeclass_instances.
Global Hint Extern 2 (DecidableEquality (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_dec_eq : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_ref_eq : typeclass_instances.

Section ring.
  Universes i.
  Context `{H:Rig@{i} R} `{!StrongSet R}.
  Notation K := (GrothendieckPairs R).

  Lemma mult_is_fun : @IsFun (K ⊗ K) K (tuncurry (mult_op R)).
  Proof. apply coordinatewise_is_fun; intros x y z; unf constr:(K); apply aex_adj; intros k.
  + rew <-(aex_ub _ (k·z⁺+k·z⁻)).
    replc ( x⁺ · z⁺ + x⁻ · z⁻ + (y⁺ · z⁻ + y⁻ · z⁺) + (k · z⁺ + k · z⁻) ) with
          ( (x⁺·z⁺+y⁻·z⁺+k·z⁺) + (y⁺·z⁻+x⁻·z⁻+k·z⁻) ) by add_mon
      and ( y⁺ · z⁺ + y⁻ · z⁻ + (x⁺ · z⁻ + x⁻ · z⁺) + (k · z⁺ + k · z⁻) ) with
          ( (y⁺·z⁺+x⁻·z⁺+k·z⁺) + (x⁺·z⁻+y⁻·z⁻+k·z⁻) ) by add_mon.
    rew <-?(plus_mult_distr_r _ _ _).
    rew <-exact:(is_fun (strong_op (+)) ((x⁺ + y⁻ + k) · z⁺, (y⁺ + x⁻ + k) · z⁻) ((y⁺ + x⁻ + k) · z⁺, (x⁺ + y⁻ + k) · z⁻)).
    unfold_pair_eq. apply aand_intro.
    * exact (is_fun (·z⁺) _ _).
    * rew (symmetry_iff (=) (x⁺+y⁻+k) _). exact (is_fun (·z⁻) _ _).
  + rew <-(aex_ub _ (x⁺·k + x⁻·k)).
    replc ( x⁺ · y⁺ + x⁻ · y⁻ + (x⁺ · z⁻ + x⁻ · z⁺) + (x⁺ · k + x⁻ · k) ) with
          ( (x⁺·y⁺+x⁺·z⁻+x⁺·k) + (x⁻·z⁺+x⁻·y⁻+x⁻·k) ) by add_mon
      and ( x⁺ · z⁺ + x⁻ · z⁻ + (x⁺ · y⁻ + x⁻ · y⁺) + (x⁺ · k + x⁻ · k) ) with
          ( (x⁺·z⁺+x⁺·y⁻+x⁺·k) + (x⁻·y⁺+x⁻·z⁻+x⁻·k) ) by add_mon.
    rew <-?(plus_mult_distr_l _ _ _).
    rew <-exact:(is_fun (strong_op (+)) (x⁺ · (y⁺ + z⁻ + k), x⁻ · (z⁺ + y⁻ + k)) (x⁺ · (z⁺ + y⁻ + k), x⁻ · (y⁺ + z⁻ + k))).
    unfold_pair_eq. apply aand_intro.
    * exact (is_fun (x⁺·) _ _).
    * rew (symmetry_iff (=) (y⁺+z⁻+k) _). exact (is_fun (x⁻·) _ _).
  Qed.
  Definition grothendieck_pairs_mult := @make_fun _ _ _ mult_is_fun.

  Local Hint Extern 1 (Mult K) => refine grothendieck_pairs_mult : typeclass_instances.

  Ltac expand_and_solve :=
    rew ?(plus_mult_distr_l (l:=H) _ _ _);
    rew ?(plus_mult_distr_r (n:=H) _ _ _);
    rew ?(mult_ass (H:=H) _ _ _);
    add_mon.

  Local Instance: Associative (X:=K) (·).
  Proof. intros x y z; unf constr:(K). exists 0. expand_and_solve. Qed.

  Local Instance: LeftIdentity (X:=K) (·) 1.
  Proof. intros x; unf constr:(K). exists 0.
    rew (mult_1_l x⁺). rew exact:(mult_1_l x⁻).
    rew ?(mult_0_l _).
    add_mon.
  Qed.

  Local Instance: RightIdentity (X:=K) (·) 1.
  Proof. intros x; unf constr:(K). exists 0.
    rew (mult_1_r x⁺). rew exact:(mult_1_r x⁻).
    rew ?(mult_0_r (l:=H) _).
    add_mon.
  Qed.

  Local Instance: LeftDistribute (X:=K) (·) (+).
  Proof. intros x y z; unf constr:(K). exists 0. expand_and_solve. Qed.

  Local Instance: RightDistribute (X:=K) (·) (+).
  Proof. intros x y z; unf constr:(K). exists 0. expand_and_solve. Qed.

  Local Instance grothendieck_group_is_ring : Ring K.
  Proof. now apply alt_Build_Ring2. Qed.

  Lemma grothendieck_group_is_com_ring `{!Commutative (X:=R) (·)} : CommutativeRing K.
  Proof. apply (comring_from_ring _). intros x y; unf constr:(K); exists 0.
    rew [ (commutativity (·) y⁺ x⁺) | (commutativity (·) y⁻ x⁻)
        | (commutativity (·) y⁻ x⁺) | (commutativity (·) y⁺ x⁻) ].
    add_mon.
  Qed.
End ring.
Arguments grothendieck_pairs_mult R {_ _ _ _ _ _}.
Global Hint Extern 2 (Mult (GrothendieckPairs ?M)) => notypeclasses refine (grothendieck_pairs_mult M) : typeclass_instances.
Global Hint Extern 2 (Ring (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (CommutativeRing (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_com_ring : typeclass_instances.

Global Hint Extern 2 (LeftNearRg (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (LeftNearRig (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (LeftNearRing (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (LeftNearRng (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (NearRg (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (NearRig (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (NearRing (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (NearRng (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (Rg (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (Rig (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.
Global Hint Extern 2 (Rng (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_ring : typeclass_instances.

Global Hint Extern 2 (CommutativeRig (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_com_ring : typeclass_instances.
Global Hint Extern 2 (MultiplicativeComMonoid (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_is_com_ring : typeclass_instances.


Section ring_embedding.
  Universes i.
  Context `{H:Rig@{i} R} `{!StrongSet R}.
  Notation K := (GrothendieckPairs R).

  Lemma to_grothendieck_group_is_rig_mor : Rig_Morphism (to_grothendieck_group R).
  Proof. split; try exact _. apply alt_Build_MultiplicativeMonoid_Morphism.
  + intros x y. change (∐ k : R, x · y + (x·0 + 0·y) + k = (x·y + 0·0) + 0 + k).
    exists 0. rew [ (mult_0_r x) | (mult_0_l y) | (mult_0_l 0) ]. add_mon.
  + refl.
  Qed.
End ring_embedding.
Global Hint Extern 2 (Rig_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.

Global Hint Extern 2 (Rg_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.

