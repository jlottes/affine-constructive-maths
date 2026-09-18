Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base uniform.basis uniform.subspace.
Require Import interfaces.unif_born unif_born.base bornology.base bornology.basis.
Require Import easy rewrite replc simplify strip_coercions tactics.misc.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Local Open Scope sg_op_scope.
Local Open Scope grp_scope.
Import projection_notation.
Import image_notation.
Import tensor_map_notation.
Import thicken_notation.

Local Abbreviation ι := from_subset.
Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").
Local Notation "f ♭" := ((func_op ⟨f,f⟩)⁎) (at level 1, left associativity, format "f ♭").

Import set_internalize.notation.

Section dense_collar.
  Universes u.
  Context `{Φ:Uniformity@{u} X} {𝒜:Bornology X} `{!WCUnifSpace X}.
  Context `{Ψ:Uniformity@{u} Y} {ℬ:Bornology Y} `{!WCUnifSpace Y}.
  Context {f:X ⇾ Y} `{!Dense f} `{!BornologyReflecting f}.
  Context (P : ∀ K:ℬ, UniformlyReflecting (f ∘ ι (f* K))).

  (** The bornology-indexed density-collar entourage on [Y].  Over each bounded
      [K], a genuine *symmetric* collar [S₀ ⊆ S] thickened so that [S₀[K]] stays
      bounded (wcunif_thicken), wrapping the image [f♭ R] of an X-entourage [R].
      The box [K ⊗ K] confines the endpoints — and hence, in a composition, the
      shared middle — to a bounded set, where local reflectivity bites. *)

  Definition collar_entourage (R:𝒫 (X ⊗ X)) (S:𝒫 (Y ⊗ Y)) : 𝒫 (Y ⊗ Y)
    := { '(y, y') : (Y ⊗ Y)%set |
           ∐ (K:ℬ) (S₀:Ψ), of_course (
               (powerset_pt S₀)⁻¹ = (powerset_pt S₀)
             ⊠ (powerset_pt S₀ ⊆ S)
             ⊠ (S₀.[powerset_pt K] ∊ ℬ) )
             ⊠ ((y, y') ∊ (powerset_pt K ⊗ powerset_pt K)
                          ⊓ (powerset_pt S₀ ∙ f♭ R ∙ powerset_pt S₀)) }.

  Lemma collar_reflexive (R:𝒫 (X ⊗ X)) (S:Ψ) : id_rel X ⊆ R → id_rel Y ⊆ collar_entourage R S.
  Proof. intros HR.
    change (id_rel Y ⊆ collar_entourage R S) with (∏ p, π₁ p = π₂ p ⊸ p ∊ collar_entourage R S).
    intros [y y'].
    change (y = y' ⊸ ∐ (K:ℬ) (S₀:Ψ), of_course ((S₀⁻¹ = S₀) ⊠ (powerset_pt S₀ ⊆ S) ⊠ (S₀.[powerset_pt K] ∊ ℬ)) ⊠ ((y, y') ∊ (powerset_pt K ⊗ powerset_pt K) ⊓ (powerset_pt S₀ ∙ f♭ R ∙ powerset_pt S₀))).
    pose (K := born_pt y ⊔ born_pt y').
    pose proof (wcunif_thicken Y K) as [W HW].
    pose proof (uniform_sym_alt (S ⊓ W)) as [S₀ [ES₀ PS₀]].
    pose proof (uniform_dense_range f y S₀) as [x Hx].
    rew <-(aex_ub _ K), <-(aex_ub _ S₀).
    assert (S₀ ≤ S) as HA. { rew <-(meet_lb_l S W). exact PS₀. }
    assert (S₀ ≤ W) as HSW. { rew <-(meet_lb_r S W). exact PS₀. }
    assert (S₀.[powerset_pt K] ⊆ W.[powerset_pt K]) as Hle. { rew <-HSW. easy. }
    assert (S₀.[powerset_pt K] ∊ ℬ) as HB. { now apply (down_closed ℬ _ W.[powerset_pt K]). }
    assert ( of_course (S₀⁻¹ = S₀ ⊠ S₀ ⊆ S ⊠ S₀.[powerset_pt K] ∊ ℬ) ) as Q by (now split);
      rew (aprod_true_l Q); clear Q.
    change (y = y' ⊸ (y, y') ∊ powerset_pt K ⊗ powerset_pt K ∧ (y, y') ∊ powerset_pt S₀ ∙ f♭ R ∙ powerset_pt S₀); apply aand_intro.
    + match goal with |- apos (_ ⊸ ?P) => enough P by now simplify end.
      split; [ now left | now right ].
    + do 2 (change ( (?a, ?c) ∊ ?A ∙ ?B ) with (∐ b, (a, b) ∊ A ⊠ (b, c) ∊ B); rew <-(aex_ub _ (f x))).
      rew <-( equal_element S₀ (f x, y) (f x, y') ); unfold_pair_eq.
      enough ( (y, f x) ∊ S₀ ⊠ (f x, y) ∊ S₀ ⊠ (f x, f x) ∊ f♭ R ⊠ f x = f x ) as G by (revert G; tautological).
      split; [ exact _ | split; [| split; [| easy]] ].
      * now rew <-(ES₀ : powerset_pt _ = powerset_pt _).
      * change ( ⟨f,f⟩ (x,x) ∊ f♭ R ). rew <-(image_el _ _ _). apply HR. now change (x = x).
  Qed.

  Lemma sandwich_flip (T:𝒫 (Y ⊗ Y)) (R:𝒫 (X ⊗ X)) : T⁻¹ = T → (T ∙ f♭ R ∙ T)⁻¹ = T ∙ f♭ (R⁻¹) ∙ T.
  Proof. intros HT. rew (inv_distr _ _), (inv_distr _ _).
    rew HT, (flip_image_tensor_map_alt f f R : (f♭ R)⁻¹ = f♭ (R⁻¹)).
    now apply associativity.
  Qed.
  Lemma collar_sym (R:𝒫 (X ⊗ X)) (S:Ψ) : collar_entourage (R⁻¹) S ⊆ (collar_entourage R S)⁻¹.
  Proof.
    change (collar_entourage (R⁻¹) S ⊆ (collar_entourage R S)⁻¹) with (∏ p, p ∊ collar_entourage (R⁻¹) S ⊸ p ∊ (collar_entourage R S)⁻¹).
    intros [y y'].
    change ((y, y') ∊ (collar_entourage R S)⁻¹) with ((y', y) ∊ collar_entourage R S).
    change ((y, y') ∊ collar_entourage (R⁻¹) S) with (∐ (K:ℬ) (S₀:Ψ), of_course ((S₀⁻¹ = S₀) ⊠ (powerset_pt S₀ ⊆ S) ⊠ (S₀.[powerset_pt K] ∊ ℬ)) ⊠ ((y, y') ∊ (powerset_pt K ⊗ powerset_pt K) ⊓ (powerset_pt S₀ ∙ f♭ (R⁻¹) ∙ powerset_pt S₀))).
    change ((y', y) ∊ collar_entourage R S) with (∐ (K:ℬ) (S₀:Ψ), of_course ((S₀⁻¹ = S₀) ⊠ (powerset_pt S₀ ⊆ S) ⊠ (S₀.[powerset_pt K] ∊ ℬ)) ⊠ ((y', y) ∊ (powerset_pt K ⊗ powerset_pt K) ⊓ (powerset_pt S₀ ∙ f♭ R ∙ powerset_pt S₀))).
    rew <-aex_adj; intros K. rew <-aex_adj; intros S₀.
    rew <-(aex_ub _ K), <-(aex_ub _ S₀).
    apply of_course_aprod_aimpl_l.
    intros H.
    pose proof (andl H) as Hsym.
    assert (of_course (S₀⁻¹ = S₀ ⊠ powerset_pt S₀ ⊆ S ⊠ S₀.[powerset_pt K] ∊ ℬ)) as Qoc by exact H;
      rew (aprod_true_l Qoc); clear Qoc.
    change ((y, y') ∊ powerset_pt K ⊗ powerset_pt K ⊓ powerset_pt S₀ ∙ f♭ (R⁻¹) ∙ powerset_pt S₀) with ((y, y') ∊ powerset_pt K ⊗ powerset_pt K ∧ (y, y') ∊ powerset_pt S₀ ∙ f♭ (R⁻¹) ∙ powerset_pt S₀).
    change ((y', y) ∊ powerset_pt K ⊗ powerset_pt K ⊓ powerset_pt S₀ ∙ f♭ R ∙ powerset_pt S₀) with ((y', y) ∊ powerset_pt K ⊗ powerset_pt K ∧ (y', y) ∊ powerset_pt S₀ ∙ f♭ R ∙ powerset_pt S₀).
    apply aand_proper_aimpl.
    + change ((y', y) ∊ powerset_pt K ⊗ powerset_pt K) with ((y, y') ∊ (powerset_pt K ⊗ powerset_pt K)⁻¹).
      rew (tensor_subset_flip (powerset_pt K) (powerset_pt K) : (powerset_pt K ⊗ powerset_pt K)⁻¹ = powerset_pt K ⊗ powerset_pt K). easy.
    + change ((y', y) ∊ powerset_pt S₀ ∙ f♭ R ∙ powerset_pt S₀) with ((y, y') ∊ (powerset_pt S₀ ∙ f♭ R ∙ powerset_pt S₀)⁻¹).
      rew (sandwich_flip (powerset_pt S₀) R (Hsym : (powerset_pt S₀)⁻¹ = powerset_pt S₀)). easy.
  Qed.


End dense_collar.
