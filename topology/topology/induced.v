Require Import interfaces.set algebra_notation.
Require Import logic.aprop relations.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology.
Require Import theory.set orders.orders orders.subset.
Require Import orders.subset_images.
Require Import easy rewrite simplify.

Local Open Scope topology_scope.

Section induced.
  Universes u.
  Context (A:Type@{u}).

  Local Instance pred_le : Le (A → Ω) := λ '(U, V), ∏ x, U x ⊸ V x.
  Local Instance pred_eq : Equiv (A → Ω) := λ '(U, V), ∏ x, U x ⧟ V x.
  Local Instance pred_preorder : PreOrder (A → Ω).
  Proof. split.
  + now intros U x.
  + intros U V W. unfold le, pred_le. rew <-all_adj. intros x.
    rew (all_lb _ x).
    now apply transitivity.
  Qed.

  Lemma pred_eq_correct (U V : A → Ω) : U = V ⧟ U ≤ V ∧ V ≤ U.
  Proof. unfold equiv, le, pred_le, pred_eq. split.
  + apply aand_intro.
    * rew <-all_adj. intros x. rew (all_lb _ x). apply aandl.
    * rew <-all_adj. intros x. rew (all_lb _ x). apply aandr.
  + rew <-all_adj. intros x. now rew (all_lb _ x).
  Qed.

  Definition Pred := induced_poset pred_eq_correct.

  Context (N:A → Pred → Ω).

  Context (refl: ∀ x U, N x U ⊸ U x).
  Context (isotony: ∀ x U V, N x U ⊠ (∏ y, U y ⊸ V y) ⊸ N x V).
  Context (nul_add: ∀ x, N x (λ x, 𝐓)).
  Context (bin_add: ∀ x U V, N x U ⊠ N x V ⊸ N x (λ y, U y ∧ V y)).
  Context (trans: ∀ x U, N x U ⊸ N x (λ y, N y U)).

  Local Instance induced_top_le : Le A := λ '(x, y), ∏ (U:Pred), N y U ⊸ N x U.
  Local Instance induced_top_eq : Equiv A := λ '(x, y), ∏ (U:Pred), N x U ⧟ N y U.

  Local Instance induced_top_preorder : PreOrder A.
  Proof. split.
  + now intros x U.
  + intros x y z. unfold le, induced_top_le. rew <-all_adj. intros U.
    rew (all_lb _ U).
    rew (aprod_com _ _). now apply transitivity.
  Qed.

  Lemma induced_top_eq_correct (x y : A) : x = y ⧟ x ≤ y ∧ y ≤ x.
  Proof. unfold equiv, le, induced_top_le, induced_top_eq. split.
  + apply aand_intro.
    * rew <-all_adj. intros U. rew (all_lb _ U). apply aandr.
    * rew <-all_adj. intros U. rew (all_lb _ U). apply aandl.
  + rew <-all_adj. intros U. rew (all_lb _ U).
    now rew (aand_com _ _).
  Qed.

  Definition induced_topology_set := induced_poset induced_top_eq_correct.
  Local Abbreviation X := induced_topology_set.

  Lemma induced_nbrhood_isfun : @IsFun (X ⊗ 𝒫 X) Ω (λ '(x, U), N x U).
  Proof. enough (∀ (x y : X) (U V : 𝒫 X), (∏ (W:Pred), N x W ⧟ N y W) ⊠ U = V ⊸ (N x U ⊸ N y V)) as P.
  + intros [x U][y V]. change ((∏ (W:Pred), N x W ⧟ N y W) ⊠ U = V ⊸ (N x U ⧟ N y V)).
    apply aand_intro.
    * apply P.
    * rew <-(P y x V U). apply aprod_proper_aimpl.
      - rew <-all_adj. intros W. rew (all_lb _ W). now apply symmetry.
      - now apply symmetry.
  + intros x y U V. rew (all_lb _ (V: Pred)). rew (aandl _ _ : (N x V ⧟ N y V) ⊸ _). rew (aprod_com _ _).
    enough (U = V ⊸ (N x U ⊸ N x V)) as E by (rew E; now apply transitivity).
    rew <-(isotony x U V). rew <-(aprod_adj _ _ _). rew (aprod_com _ _) at 1.
    enough (U = V ⊸ ∏ y, U y ⊸ V y) as E by now rew E.
    exact (eq_le U V).
  Qed.

  Local Instance induced_nbrhood : Neighborhood X := @func_make _ _ _ induced_nbrhood_isfun.

  Lemma induced_topology : Topology X.
  Proof. split.
  + intros x U. apply refl.
  + intros x U V. apply isotony.
  + intros x. apply nul_add.
  + intros x U V. apply bin_add.
  + intros x U. apply trans.
  Qed.

  Lemma pred_interior_is_fun (W:Pred) : @IsFun X Ω (λ z, N z W).
  Proof. intros a b. exact (all_lb _ W). Qed.

  Definition pred_interior (W:Pred) : 𝒫 X := @func_make _ _ _ (pred_interior_is_fun W).

  Lemma N_iff_pred_interior (z:X) (W:Pred) : N z W ⧟ N z (pred_interior W).
  Proof. split.
  + exact (trans z W).
  + rew <-(isotony z (pred_interior W) W).
    enough (∏ y, N y W ⊸ W y) by now simplify.
    intros y. exact (refl y W).
  Qed.

  Lemma induced_topology_T₀ : Separation_T₀ X.
  Proof. intros x y.
    change ((∏ U : 𝒫 X, N x U ⧟ N y U) ⊸ (∏ W : Pred, N x W ⧟ N y W)).
    rew <-all_adj. intros W.
    rew (N_iff_pred_interior _ W).
    exact (all_lb _ (pred_interior W)).
  Qed.
End induced.


