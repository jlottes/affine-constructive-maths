Require Import interfaces.set abstract_algebra interfaces.group_completion.
Require Import logic.aprop logic.relations theory.rings theory.bundled_groups.
Require Import interfaces.subset.
Require Import set_lambda.
Require Import theory.additive_groups.
Require Import theory.product_algebras theory.quotients theory.subrings orders.rings.
Require Import tactics.algebra.com_monoids.
Require Import easy replc rewrite_preserves simplify.

Import quotient_set_notation.

Section add_grp.
  Universes i.
  Context (M:set@{i}) `{AdditiveMonoid M}.

  Definition grothendieck_pairs_rel
    := { '((a,b),(c,d)) : (M ⊗ M) ⊗ (M ⊗ M) | ∐ k, a + d + k = c + b + k } .

  Local Abbreviation R := grothendieck_pairs_rel.
  Local Instance grothendieck_pairs_rel_equivalence : Equivalence R.
  Proof. split.
  * intros [a b]. change (∐ k, a + b + k = a + b + k). now exists 0.
  * intros [a b][c d].
    change ((∐ k, a + d + k = c + b + k) ⊸ ∐ k, c + b + k = a + d + k).
    rew <-aex_adj; intros k. rew <-(aex_ub _ k).
    now apply symmetry.
  * intros [a b][c d][e f].
    change ((∐ k, a + d + k = c + b + k)
          ⊠ (∐ k, c + f + k = e + d + k)
          ⊸  ∐ k, a + f + k = e + b + k).
    rew <-aex_adj2; intros k₁ k₂.
    rew <-(aex_ub _ (c + d + k₁ + k₂)).
    replc (a + f + (c + d + k₁ + k₂)) with ((a + d + k₁) + (c + f + k₂)) by add_mon
      and (e + b + (c + d + k₁ + k₂)) with ((c + b + k₁) + (e + d + k₂)) by add_mon.
    exact (is_fun (+) (_, _) (_, _)).
  Qed.

  Local Instance grothendieck_pairs_rel_congruence : AdditiveSubSemiGroup R.
  Proof. apply alt_Build_AdditiveSubSemiGroup. intros [[a b][c d]][[e f][g h]].
    change ( (∐ k, a + d + k = c + b + k)
           ⊠ (∐ k, e + h + k = g + f + k)
           ⊸  ∐ k, (a+e) + (d+h) + k = (c+g) + (b+f) + k).
    rew <-aex_adj2; intros k₁ k₂.
    rew <-(aex_ub _ (k₁ + k₂)).
    replc (a + e + (d + h) + (k₁ + k₂)) with ((a + d + k₁) + (e + h + k₂)) by add_mon
      and (c + g + (b + f) + (k₁ + k₂)) with ((c + b + k₁) + (g + f + k₂)) by add_mon.
    exact (is_fun (+) (_, _) (_, _)).
  Qed.

  Definition GrothendieckPairs := (M ⊗ M) / R .
  Local Abbreviation K := GrothendieckPairs.

  Local Instance grothendieck_pairs_zero : Zero K := @zero ((M ⊗ M) / R) _.
  Local Instance grothendieck_pairs_plus : Plus K := @plus ((M ⊗ M) / R) _.

  Local Instance grothendieck_pairs_add_mon : AdditiveMonoid K := _ : AdditiveMonoid ((M ⊗ M) / R).

  Local Instance grothendieck_paris_negate_closed
    : MapsTo (tensor_map (tensor_swap M M) (tensor_swap M M)) R R.
  Proof. intros [[a b][c d]].
    change ((∐ k, a + d + k = c + b + k)
           ⊸ ∐ k, b + c + k = d + a + k).
    rew <-aex_adj; intros k. rew <-(aex_ub _ k).
    replc (b + c) with (c + b) by add_mon and (d + a) with (a + d) by add_mon.
    now apply symmetry.
  Qed.
  Local Instance grothendieck_pairs_negate : Negate K := quotient_lift_op (R:=R) (tensor_swap M M).

  Let inst := grothendieck_pairs_add_mon.

  Local Instance grothendieck_pairs_add_grp : AdditiveGroup K.
  Proof. apply alt_Build_AdditiveGroup; try exact _.
    intros [x y]. exists 0. change (y + x + 0 + 0 = 0 + (x + y) + 0). add_mon.
  Qed.
End add_grp.

Global Hint Extern 2 (Zero   (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_zero _) : typeclass_instances.
Global Hint Extern 2 (Plus   (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_plus _) : typeclass_instances.
Global Hint Extern 2 (Negate (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_negate _) : typeclass_instances.

Global Hint Extern 2 (AdditiveMonoid (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_add_mon _) : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComMonoid (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_add_mon _) : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComSemiGroup (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_add_mon _) : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_add_mon _) : typeclass_instances.

Global Hint Extern 2 (AdditiveGroup (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_add_grp _) : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComGroup (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_add_grp _) : typeclass_instances.
Global Hint Extern 2 (AdditiveCancellation (GrothendieckPairs _)) => simple notypeclasses refine (grothendieck_pairs_add_grp _) : typeclass_instances.


Definition to_grothendieck_group (M:set) `{AdditiveMonoid (R:=M)} : M ⇾ GrothendieckPairs M := to_quotient (grothendieck_pairs_rel M) ∘ add_mon_inl M M.

Lemma to_grothendieck_group_add_mon_mor `{AdditiveMonoid (R:=M)} : AdditiveMonoid_Morphism (to_grothendieck_group M).
Proof. now unfold to_grothendieck_group. Qed.

Global Hint Extern 2 (AdditiveMonoid_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_add_mon_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_add_mon_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_add_mon_mor : typeclass_instances.


Section grothendieck_pairs_map.
  Context `{AdditiveMonoid (R:=X)} `{AdditiveMonoid (R:=Y)} (f:X ⇾ Y) `{!AdditiveMonoid_Morphism f}.

  Local Instance grothendieck_pairs_map_closed:
    MapsTo (tensor_map (tensor_map f f) (tensor_map f f)) (grothendieck_pairs_rel _) (grothendieck_pairs_rel _).
  Proof. intros [[a b][c d]].
    change ((∐ k, a + d + k = c + b + k) ⊸ ∐ k, f a + f d + k = f c + f b + k).
    rew <-aex_adj; intros k. rew <-(aex_ub _ (f k)).
    rew (is_fun f (a + d + k) (c + b + k)).
    now rewrite_preserves f.
  Qed.
  Definition grothendieck_pairs_map : GrothendieckPairs X ⇾ GrothendieckPairs Y
    := quotient_lift_op (tensor_map f f).
End grothendieck_pairs_map.
Lemma grothendieck_pairs_map_mor `{AdditiveMonoid (R:=X)} `{AdditiveMonoid (R:=Y)} {f:X ⇾ Y} `{!AdditiveMonoid_Morphism f}
  : AdditiveMonoid_Morphism (grothendieck_pairs_map f).
Proof. now unfold grothendieck_pairs_map. Qed.

Global Hint Extern 2 (AdditiveMonoid_Morphism (grothendieck_pairs_map _)) => simple notypeclasses refine grothendieck_pairs_map_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (grothendieck_pairs_map _)) => simple notypeclasses refine grothendieck_pairs_map_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (grothendieck_pairs_map _)) => simple notypeclasses refine grothendieck_pairs_map_mor : typeclass_instances.

Lemma grothendieck_pairs_map_id `{AdditiveMonoid (R:=M)}
  : grothendieck_pairs_map (id_fun M) = id_fun _.
Proof. exact (λ x, reflexivity (=) _). Qed.


Section grothendieck_pairs_extract.
  Universes i.
  Context M `{AdditiveGroup@{i} M}.
  Abbreviation K := (GrothendieckPairs M).

  Lemma grothendieck_pairs_extract_is_fun : @IsFun K M ( λ '(x, y):M ⊗ M, x - y ).
  Proof. intros [a b][c d].
    change ((∐ k, a + d + k = c + b + k) ⊸ a - b = c - d).
    rew <-aex_adj; intros k.
    rew (is_fun (+ ((-k)+(-b)+(-d))) _ _ : a + d + k = c + b + k ⊸ _ ).
    change (a + d + k + ((-k)+(-b)+(-d)) = c + b + k + ((-k)+(-b)+(-d)) ⊸ a - b = c - d).
    replc (a + d + k + ((-k)+(-b)+(-d))) with (a - b + (d - d) + (k - k)) by add_mon
      and (c + b + k + ((-k)+(-b)+(-d))) with (c - d + (b - b) + (k - k)) by add_mon.
    now simplify.
  Qed.
  Definition grothendieck_pairs_extract : _ ⇾ _ := @func_make _ _ _ grothendieck_pairs_extract_is_fun.
End grothendieck_pairs_extract.

Lemma grothendieck_pairs_extract_mor `{AdditiveGroup (R:=M)}: AdditiveMonoid_Morphism (grothendieck_pairs_extract M).
Proof. apply Build_AdditiveGroup_Morphism. intros [a b][c d].
  change ((a + c) - (b + d) = (a - b) + (c - d)).
  rew (negate_plus_distr _ _).
  add_mon.
Qed.
Global Hint Extern 2 (AdditiveMonoid_Morphism (grothendieck_pairs_extract _)) => simple notypeclasses refine grothendieck_pairs_extract_mor : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (grothendieck_pairs_extract _)) => simple notypeclasses refine grothendieck_pairs_extract_mor : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (grothendieck_pairs_extract _)) => simple notypeclasses refine grothendieck_pairs_extract_mor : typeclass_instances.

Import projection_notation.

Section group_completion.
  Universes i.
  Context `{AdditiveMonoid@{i} M}.
  Abbreviation K := (GrothendieckPairs M).
  Abbreviation i := (to_grothendieck_group M).

  Lemma grothendieck_group_split (x:K) : x = i (π₁ x) - i (π₂ x).
  Proof. change (∐ k, π₁ x + (0+π₂ x) + k = (π₁ x+0) + π₂ x + k). exists 0. add_mon. Qed.

  Section another_group.
    Context {A:additive_non_com_group@{i}} (f:M ⇾ A) `{!AdditiveMonoid_Morphism f}.

    Definition from_grothendieck_group_image := { x : A | ∐ a b : M, x = f a - f b } .
    Abbreviation B := from_grothendieck_group_image.

    Lemma from_grothendieck_group_commute x y : f x + f y = f y + f x.
    Proof.
      rew <-(preserves_plus f _ _).
      now rew (commutativity (+) _ _) at 1.
    Qed.

    Lemma from_grothendieck_group_swap_negate x y : f x - f y = -f y + f x.
    Proof.
      rew (injective_iff_simp (+ f y) _ _).
      rew (injective_iff_simp (f y +) _ _).
      rew (associativity (+) _ _ _). simplify.
      exact (from_grothendieck_group_commute _ _).
    Qed.

    Lemma from_grothendieck_group_image_sub_grp: AdditiveSubGroup B.
    Proof. apply alt_Build_AdditiveSubGroup.
    + intros x y. change ((∐ a b : M, x = f a - f b) ⊠ (∐ a b : M, y = f a - f b) ⊸ (∐ a b : M, x + y  = f a - f b)).
      rew <-aex_adj2; intros a c. rew <-aex_adj2; intros b d.
      rew (is_fun (+) (x, y) (_, _) : x = _ ⊠ y = _ ⊸ _).
      rew <-(aex_ub _ (a + c)). rew <-(aex_ub _ (d + b)).
      rewrite_preserves f.
      rew (negate_plus_distr_alt _ _).
      rew (associativity (+) _ _ _).
      rew <-(associativity (+) (f a) (f c) (-f b)).
      rew (from_grothendieck_group_swap_negate c b).
      now rew (associativity (+) _ _ _).
    + exists 0. exists 0. change (0 = f 0 - f 0).
      rewrite_preserves f. now simplify.
    + intros x. change ((∐ a b : M, x = f a - f b) ⊸ (∐ a b : M, -x  = f a - f b)).
      rew <-aex_adj; intros a. rew <-aex_adj; intros b.
      rew <-(aex_ub _ b). rew <-(aex_ub _ a).
      rew (is_fun (-) x _).
      rew (negate_plus_distr_alt _ _). now simplify.
    Qed.
    Let inst : AdditiveSubGroup B. Proof. exact from_grothendieck_group_image_sub_grp. Qed.
    Let inst2 : AdditiveNonComGroup B. Proof. exact _. Qed.

    Lemma from_grothendieck_group_image_com_grp : AdditiveGroup B.
    Proof. apply alt_Build_AdditiveGroup; try exact _.
      intros [x [a[b Ex]]] [y [c[d Ey]]].
      change (apos (x = f a - f b :> A)) in Ex.
      change (apos (y = f c - f d :> A)) in Ey.
      change (apos (x + y = y + x)). rew [Ex | Ey].
      rew (associativity (+) _ _ _).
      rew [<-(associativity (+) _ (-f b) _) | <-(associativity (+) _ (-f d) _)].
      rew <-(from_grothendieck_group_swap_negate _ _).
      rew (associativity (+) _ _ _).
      rew (from_grothendieck_group_commute c a).
      rew <-(associativity (+) _ _ _).
      rew <-(negate_plus_distr_alt _ _).
      now rew (from_grothendieck_group_commute d b).
    Qed.
    Let inst3 : AdditiveGroup B. Proof. exact from_grothendieck_group_image_com_grp. Qed.

    Local Instance from_grothendieck_group_restrict_el (x:M) : f x ∊ B.
    Proof. exists x. exists 0. simplify. rewrite_preserves f. now simplify. Qed.
    Definition from_grothendieck_group_restrict : M ⇾ B := @func_make _ _ (λ x:M, to_subset (U := B) (f x)) (is_fun f).
    Abbreviation g := from_grothendieck_group_restrict.

    Lemma from_grothendieck_group_restrict_add_mon_mor : AdditiveMonoid_Morphism g.
    Proof. apply alt_Build_AdditiveMonoid_Morphism.
    + exact (preserves_plus f).
    + exact (preserves_0 f).
    Qed.
    Let inst4 : AdditiveMonoid_Morphism g. Proof. exact from_grothendieck_group_restrict_add_mon_mor. Qed.

    Definition from_grothendieck_group := from_subset _ ∘ grothendieck_pairs_extract _ ∘ grothendieck_pairs_map g.
    Lemma from_grothendieck_group_is_add_mor : AdditiveMonoid_Morphism from_grothendieck_group.
    Proof. unfold from_grothendieck_group. now repeat refine (compose_addmon_mor _ _). Qed.
  End another_group.

  Lemma grothendieck_group_is_completion : GroupCompletion i (U:=@from_grothendieck_group).
  Proof. split; try exact _. intros A f ?; split.
  + simple refine (from_grothendieck_group_is_add_mor f).
  + intros x. change (f x - f 0 = f x). rewrite_preserves f. now simplify.
  + intros h ? E x. rew (grothendieck_group_split x) at 1.
    rewrite_preserves h.
    change ((h ∘ i) (π₁ x) - (h ∘ i) (π₂ x) = f (π₁ x) - f (π₂ x)).
    now rew E.
  Qed.
End group_completion.
Global Hint Extern 2 (AdditiveMonoid_Morphism    (from_grothendieck_group _)) => simple notypeclasses refine (from_grothendieck_group_is_add_mor _) : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (from_grothendieck_group _)) => simple notypeclasses refine (from_grothendieck_group_is_add_mor _) : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism      (from_grothendieck_group _)) => simple notypeclasses refine (from_grothendieck_group_is_add_mor _) : typeclass_instances.

Global Hint Extern 2 (FromGroupCompletion (to_grothendieck_group ?M)) =>
  notypeclasses refine (@from_grothendieck_group M _ _ _) : typeclass_instances.
Global Hint Extern 2 (GroupCompletion (to_grothendieck_group _)) =>
  simple notypeclasses refine grothendieck_group_is_completion : typeclass_instances.


Section properties.
  Universes i.
  Context `{AdditiveMonoid@{i} M}.
  Abbreviation K := (GrothendieckPairs M).

  Lemma grothendieck_group_aff_eq `{!AffirmativeEquality M} : AffirmativeEquality K.
  Proof. intros [[a b][c d]]. now change (Affirmative (∐ k, a + d + k = c + b + k)). Qed.

  Context `{!AdditiveCancellation M}.

  Lemma grothendieck_pairs_eq_alt (x y : K): x = y ⧟ π₁ x + π₂ y = π₁ y + π₂ x.
  Proof. destruct x as [a b]. destruct y as [c d].
    change ((∐ k, a + d + k = c + b + k) ⧟ a + d = c + b). split.
  + apply aex_adj; intro k. apply (injective (+k)).
  + rew <-(aex_ub _ 0). exact (is_fun (+0) _ _).
  Qed.

  Lemma to_grothendieck_group_inj : Injective (to_grothendieck_group M).
  Proof. intros x y. rew (grothendieck_pairs_eq_alt _ _). exact (injective (+0) _ _). Qed.

  Lemma grothendieck_group_strong `{!StrongOp (X:=M) (+)} : StrongSet K.
  Proof. intros [a b] [c d] [e f]. rew ?(grothendieck_pairs_eq_alt _ _); unfold proj1, proj2.
    rew (right_cancellation (+) (c + d) (a + f) _).
    replc (a + f + (c + d)) with ((a + d) + (c + f)) by add_mon
      and (e + b + (c + d)) with ((c + b) + (e + d)) by add_mon.
    exact (is_fun (strong_op (+)) (_, _) (_, _)).
  Qed.

  Lemma grothendieck_group_dec_eq `{!DecidableEquality M} : DecidableEquality K.
  Proof. intros [x y]. now rew (grothendieck_pairs_eq_alt _ _). Qed.

  Lemma grothendieck_group_ref_eq `{!RefutativeEquality M} : RefutativeEquality K.
  Proof. intros [x y]. now rew (grothendieck_pairs_eq_alt _ _). Qed.
End properties.
Global Hint Extern 2 (AffirmativeEquality (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_aff_eq : typeclass_instances.
Global Hint Extern 2 (Injective (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_inj : typeclass_instances.
Global Hint Extern 2 (StrongSet (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_strong : typeclass_instances.
Global Hint Extern 2 (DecidableEquality (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_dec_eq : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality (GrothendieckPairs _)) => simple notypeclasses refine grothendieck_group_ref_eq : typeclass_instances.


(** Order *)
Definition grothendieck_group_le M `{AdditiveMonoid M} {Mle: Le M} : Le (GrothendieckPairs M)
  := λ '((a, b),(c, d)), a + d ≤ c + b .
Global Hint Extern 2 (Le (set_T (GrothendieckPairs ?M))) => refine (grothendieck_group_le M) : typeclass_instances.

Section order.
  Context `{AdditiveMonoidOrder M}.
  Abbreviation i := (to_grothendieck_group M).

  Lemma grothendieck_group_le_correct : ∀ x y a b c d, x = i a - i b → y = i c - i d → x ≤ y ⧟ a + d ≤ c + b.
  Proof. intros [a b][c d] e f g h.
    repeat change (i ?e - i ?f) with ((e + 0, 0 + f)).
    rew (grothendieck_pairs_eq_alt _ _); simplify; intros E1 E2.
    change (a + d ≤ c + b ⧟ e + h ≤ g + f).
    rew (order_embedding_simp (+f) (a + d) (c + b)).
    rew (order_embedding_simp (+d) (e + h) (g + f)).
    replc (a + d + f) with (a + f + d) by add_mon; rew E1.
    replc (e + b + d) with (e + d + b) by add_mon
      and (c + b + f) with (c + f + b) by add_mon.
    rew <-(order_embedding_simp (+b) (e + d) (c + f)).
    replc (g + f + d) with (g + d + f) by add_mon; rew <-E2.
    replc (e + h + d) with (e + d + h) by add_mon
      and (c + h + f) with (c + f + h) by add_mon.
    exact (order_embedding (+h) _ _).
  Qed.
End order.

Local Open Scope mult_scope.

Section ring.
  Universes i.
  Context `{H:Rig@{i} R} `{!StrongSet R}.
  Abbreviation K := (GrothendieckPairs R).

  Local Instance grothendieck_pairs_one : One K := to_quotient _ (add_mon_inl R R 1).

  Lemma mult_is_fun : @IsFun (K ⊗ K) K (tuncurry (λ '(a, b), λ '(c, d), (a · c + b · d, a · d + b · c))).
  Proof. apply coordinatewise_is_fun; intros [a b][c d][e f]; unfold tuncurry, proj1, proj2; apply aex_adj; intros k;
    change ((?x, ?y) = (?z, ?w) :> K) with (∐ k, x + w + k = z + y + k ).
  + rew <-(aex_ub _ (k·e+k·f)).
    replc ( a · e + b · f + (c · f + d · e) + (k · e + k · f) ) with
          ( (a·e+d·e+k·e) + (c·f+b·f+k·f) ) by add_mon
      and ( c · e + d · f + (a · f + b · e) + (k · e + k · f) ) with
          ( (c·e+b·e+k·e) + (a·f+d·f+k·f) ) by add_mon.
    rew <-?(plus_mult_distr_r _ _ _).
    rew <-(is_fun (strong_op (+)) ((a + d + k) · e, (c + b + k) · f) ((c + b + k) · e, (a + d + k) · f)).
    unfold_pair_eq. apply aand_intro.
    * exact (is_fun (·e) _ _).
    * rew (symmetry_iff (=) (a+d+k) _). exact (is_fun (·f) _ _).
  + rew <-(aex_ub _ (a·k + b·k)).
    replc ( a · c + b · d + (a · f + b · e) + (a · k + b · k) ) with
          ( (a·c+a·f+a·k) + (b·e+b·d+b·k) ) by add_mon
      and ( a · e + b · f + (a · d + b · c) + (a · k + b · k) ) with
          ( (a·e+a·d+a·k) + (b·c+b·f+b·k) ) by add_mon.
    rew <-?(plus_mult_distr_l _ _ _).
    rew <-(is_fun (strong_op (+)) (a · (c + f + k), b · (e + d + k)) (a · (e + d + k), b · (c + f + k))).
    unfold_pair_eq. apply aand_intro.
    * exact (is_fun (a·) _ _).
    * rew (symmetry_iff (=) (c+f+k) _). exact (is_fun (b·) _ _).
  Qed.
  Definition grothendieck_pairs_mult : _ ⇾ _ := @func_make _ _ _ mult_is_fun.

  Local Hint Extern 1 (Mult K) => refine grothendieck_pairs_mult : typeclass_instances.

  Local Ltac expand :=
    change (@mult _ grothendieck_pairs_mult) with grothendieck_pairs_mult;
    change (@one _ grothendieck_pairs_one) with (@one R _, @zero R _);
    repeat (unfold grothendieck_pairs_mult, func_op, tuncurry, proj1, proj2;
    repeat change ((?x, ?y) + (?z, ?w)) with ((x + z, y + w)));
    rew ?(plus_mult_distr_l (l:=H) _ _ _);
    rew ?(plus_mult_distr_r (n:=H) _ _ _);
    rew ?(mult_ass (H:=H) _ _ _).

  Local Instance: Associative (X:=K) (·).
  Proof. intros [a b][c d][e f]; apply quotient_subrel; split; expand; add_mon. Qed.

  Local Instance: LeftDistribute (X:=K) (·) (+).
  Proof. intros [a b][c d][e f]; apply quotient_subrel; split; expand; add_mon. Qed.

  Local Instance: RightDistribute (X:=K) (·) (+).
  Proof. intros [a b][c d][e f]; apply quotient_subrel; split; expand; add_mon. Qed.

  Local Instance: LeftIdentity (X:=K) (·) 1.
  Proof. intros [a b]; apply quotient_subrel; split; expand; rew (mult_1_l _), (mult_0_l _); add_mon. Qed.

  Local Instance: RightIdentity (X:=K) (·) 1.
  Proof. intros [a b]; apply quotient_subrel; split; expand; rew (mult_1_r (H:=H) _), (mult_0_r _); add_mon. Qed.

  Local Instance grothendieck_group_is_ring : Ring K.
  Proof. now apply alt_Build_Ring2. Qed.

  Lemma grothendieck_group_is_com_ring `{!Commutative (X:=R) (·)} : CommutativeRing K.
  Proof. apply (comring_from_ring _). intros [a b][c d]; apply quotient_subrel; split; expand;
    [| rew (commutativity (+) _ _) at 1];
    apply (is_fun (+)); split; exact (commutativity _ _ _).
  Qed.
End ring.
Arguments grothendieck_pairs_one  R {_ _ _ _ _}.
Arguments grothendieck_pairs_mult R {_ _ _ _ _ _}.
Global Hint Extern 2 (One  (GrothendieckPairs ?M)) => notypeclasses refine (grothendieck_pairs_one M) : typeclass_instances.
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
  Abbreviation K := (GrothendieckPairs R).

  Lemma to_grothendieck_group_is_rig_mor : Rig_Morphism (to_grothendieck_group R).
  Proof. split; try exact _. apply alt_Build_MultiplicativeMonoid_Morphism.
  + intros x y. change (∐ k : R, x · y + (x·0 + 0·y) + k = (x·y + 0·0) + 0 + k).
    exists 0. now simplify.
  + refl.
  Qed.
End ring_embedding.
Global Hint Extern 2 (Rig_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.

Global Hint Extern 2 (Rg_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (to_grothendieck_group _)) => simple notypeclasses refine to_grothendieck_group_is_rig_mor : typeclass_instances.
