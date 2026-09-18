Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.subgroups.
Require Import theory.lattices orders.lattices theory.sublattices orders.sublattices.
Require Import topology.topology topology.uniform.base uniform.basis uniform.product topology.uniform.induced.
Require Import easy rewrite replc simplify strip_coercions.

Local Open Scope subset_scope.
Local Open Scope topology_scope.
Import projection_notation.
Import image_notation.
Import tensor_map_notation.

Local Notation "f ♯" := (⟨f,f⟩*) (at level 1, left associativity, format "f ♯").

Coercion CauchyFilter_sub_lattice `{@CauchyFilter X Φ F} : SubLattice F.
Proof. exact filter_sub_lattice. Qed.

Coercion CauchyFilter_meet_sub_semi_lattice `{@CauchyFilter X Φ F} : MeetSubBoundedSemiLattice F.
Proof. exact filter_bounded_meet_sub_sl. Qed.

Record cauchy_filter X {Φ:Uniformity X} :=
{ cauchy_filter_subset :> 𝒫² X
; #[canonical=no, reversible=no] cauchy_filter_prop :> CauchyFilter cauchy_filter_subset
}.
Arguments cauchy_filter_subset {_ _} _.
#[global] Hint Extern 2 (StripCoercions (cauchy_filter_subset ?F)) => strip_coercions_chain F : strip_coercions.
#[global] Hint Extern 4 (CauchyFilter ?F) => exact_strip_coercions F : typeclass_instances.
Local Abbreviation 𝒞 := cauchy_filter.

Lemma cauchy_filter_inhabited `{F:@𝒞 X Φ} {A:F} : Inhabited A.
Proof. enough (∐ x, x ∊ A) as [x ?] by now exists (to_subset x).
  rew <-nonempty_alt.
  rew <-(member_apart_nonmember F _ _).
  simplify.
  now apply cauchy_proper.
Qed.
#[global] Hint Extern 2 ( Inhabited (set_T (@subset_to_set _ (@powerset_pt _ (@cauchy_filter_subset _ _ _) _))) )
  => simple notypeclasses refine cauchy_filter_inhabited : typeclass_instances.

Local Open Scope sg_op_scope.
Local Open Scope grp_scope.

Definition cauchy_equiv X `{@UniformSpace X Φ} : Equiv (𝒞 X)
  := λ '(F, G) : 𝒞 X ∗ 𝒞 X, ∏ (U:Φ), ∐ (A:F) (B:G), A ⊗ B ⊆ U.
#[global] Hint Extern 2 (Equiv (𝒞 ?X)) => refine (cauchy_equiv X) : typeclass_instances.

Definition cauchy_basis `{@UniformSpace X Φ} (U:Φ)
  := λ '(F, G) : 𝒞 X ∗ 𝒞 X, ∏ (V:Φ), ∐ (A:F) (B:G), A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ U ∙ V).

Lemma cauchy_compose `{@UniformSpace X Φ} (E F G : 𝒞 X) (U V:Φ) :
  (∐ (A:E) (B:F), A ⊗ B ⊆ U) ⊠ (∐ (A:F) (B:G), A ⊗ B ⊆ V) ⊸ ∐ (A:E) (B:G), A ⊗ B ⊆ powerset_pt (U ∙ V) .
Proof.
  rew <-aex_adj2; intros A B₂. rew <-aex_adj2; intros B₁ C. rew <-(aex_ub _ A), <-(aex_ub _ C).
  rew [<-(meet_lb_l B₁ B₂) | <-(meet_lb_r B₁ B₂)].
  now apply tensor_subset_compose.
Qed.

Lemma alt_Build_CauchyFilter `{@UniformSpace X Φ} {F:𝒫² X} `{!Filter F}
  : (∅ ∊̸ F)
  → (∏ U:Φ, ∐ (A:F), A ⊗ A ⊆ U)
  → CauchyFilter F.
Proof. intros ? P. split; trivial. intros U. specialize (P U) as [A PA].
  exists A. intros x y. change (x ∊ A ⊠ y ∊ A ⊸ (x, y) ∊ U).
  now rew <-PA.
Qed. 

Lemma cauchy_alt `{@CauchyFilter X Φ F} (U:Φ) : ∐ (A:F), A ⊗ A ⊆ U.
Proof. pose proof cauchy F U as [A PA]. exists A. intros [x y]. exact (PA x y). Qed.
Arguments cauchy_alt {_ _} F {_} U.

Section uniform.
  Context `{@UniformSpace X Φ}.
  Abbreviation basis := (@cauchy_basis X _ _).
  
  Lemma cauchy_basis_refl U F : basis U (F, F).
  Proof. intros V.
    pose proof cauchy F (V⁻¹ ∙ U ∙ V) as [A PA].
    exists A; exists A; intros [x y]. exact (PA x y).
  Qed.

  Lemma cauchy_basis_sym U : ∐ V, ∏ F G, basis V (G, F) ⊸ basis U (F, G).
  Proof. exists U⁻¹. intros F G. unfold basis.
    rew <-all_adj; intros V. rew (all_lb _ V).
    rew <-aex_adj; intros B. rew <-aex_adj; intros A.
    rew <-(aex_ub _ A), <-(aex_ub _ B).
    replc (V⁻¹ ∙ U⁻¹ ∙ V) with ((V⁻¹ ∙ U ∙ V)⁻¹) by now group_simplify.
    now rew (ufm_tensor_subset_flip _ _ _).
  Qed.

  Lemma cauchy_basis_sep F G : F = G ⧟ (∏ V, basis V (F, G)).
  Proof. change ((∏ U:Φ, ∐ (A:F) (B:G), A ⊗ B ⊆ U) ⧟ (∏ V, basis V (F, G))); split.
  + rew <-all_adj; intros V. unfold basis. rew <-all_adj; intros W.
    rew (all_lb _ (W⁻¹ ∙ V ∙ W)).
    rew <-aex_adj; intros A; rew <-(aex_ub _ A).
    rew <-aex_adj; intros B; rew <-(aex_ub _ B).
    easy.
  + rew <-all_adj; intros U. pose proof uniform_split_sym3 U as [V [EV PV]].
    rew (all_lb _ V). unfold basis. rew (all_lb _ V).
    rew <-aex_adj; intros A; rew <-(aex_ub _ A).
    rew <-aex_adj; intros B; rew <-(aex_ub _ B).
    now rew [EV | <-PV].
  Qed.

  Lemma cauchy_basis_compat U F F' G G' : F = F' ⊠ basis U (F', G') ⊠ G' = G ⊸ basis U (F, G).
  Proof. change (?x = ?y) with (∏ U:Φ, ∐ (A:x) (B:y), A ⊗ B ⊆ U); unfold basis.
    rew <-all_adj; intros V.
    pose proof uniform_split_sym V as [W [EW PW]].
    rew (all_lb _ W).
    rew !2(cauchy_compose _ _ _ _ _).
    rew <-EW at 4.
    replc (W ∙ (W⁻¹ ∙ U ∙ W ∙ W⁻¹)) with ( (W∙W⁻¹)⁻¹ ∙ U ∙ (W∙W⁻¹) ) by now group_simplify.
    now rew EW, PW.
  Qed.

  Lemma cauchy_basis_split U : ∐ V, ∏ E F G, basis V (E, F) ⊠ basis V (F, G) ⊸ basis U (E, G).
  Proof. pose proof uniform_split_sym6 U as [V [EV PV]].
    exists V. intros E F G. unfold basis.
    rew <-all_adj; intros W.
    rew (all_lb _ V).
    rew (cauchy_compose _ _ _ _ _).
    rew EV.
    replc (V ∙ V ∙ V ∙ (V ∙ V ∙ V)) with (V ∙ V ∙ V ∙ V ∙ V ∙ V) by now group_simplify.
    rew PV.
    now rew <-(ufm_compose_ub_l (W⁻¹ ∙ U) _), <-(ufm_compose_ub_r _ _).
  Qed.
  
  Lemma cauchy_basis_down (U V: Φ) : ∐ (W:Φ), ∏ p, cauchy_basis W p ⊸ cauchy_basis U p ∧ cauchy_basis V p.
  Proof. exists (U ⊓ V). intros [F G]. apply aand_intro; unfold basis.
  + now rew (meet_lb_l U V).
  + now rew (meet_lb_r U V).
  Qed.
  
  Lemma cauchy_basis_axioms : InducedUniformBasis (𝒞 X) cauchy_basis.
  Proof. split.
  + exact cauchy_basis_refl.
  + exact cauchy_basis_sym.
  + exact cauchy_basis_split.
  + exact cauchy_basis_down.
  + exact cauchy_basis_sep.
  + exact cauchy_basis_compat.
  Qed.
End uniform.
#[global] Hint Extern 2 (InducedUniformBasis _ cauchy_basis) => simple notypeclasses refine cauchy_basis_axioms : typeclass_instances.

Lemma cauchy_filter_is_set `{@UniformSpace X Φ} : IsSet (𝒞 X).
Proof. apply (induced_uniform_is_set _ cauchy_basis). Qed.
#[global] Hint Extern 2 (IsSet (𝒞 _)) => simple notypeclasses refine cauchy_filter_is_set : typeclass_instances.

Canonical Structure cauchy_filter_set X `{@UniformSpace X Φ} := set_make (𝒞 X).
Local Notation "'𝒞'" := cauchy_filter_set (only printing) : set_scope.

Lemma cauchy_basis_isfun `{@UniformSpace X Φ} {U:Φ} : @IsFun (𝒞 X ⊗ 𝒞 X) Ω (cauchy_basis U).
Proof. exact (induced_basis_isfun _ cauchy_basis). Qed.
#[global] Hint Extern 2 (IsFun (cauchy_basis _)) => simple notypeclasses refine cauchy_basis_isfun : typeclass_instances.

Canonical Structure cauchy_basis_fun `{@UniformSpace X Φ} (U:Φ) : 𝒫 (𝒞 X ⊗ 𝒞 X)
  := func_make (cauchy_basis U).

Definition cauchy_uniformity X `{@UniformSpace X Φ} : Uniformity (𝒞 X) := presented_uniformity cauchy_basis_fun.
#[global] Hint Extern 0 (Uniformity (@cauchy_filter_set ?X ?Φ ?H)) => simple notypeclasses refine (@cauchy_uniformity X Φ H) : typeclass_instances.

Lemma cauchy_uniformity_presented `{@UniformSpace X Φ} : UniformityPresentation (𝒞 X) cauchy_basis_fun.
Proof. now unfold cauchy_basis_fun. Qed.
#[global] Hint Extern 2 (UniformityPresentation (cauchy_filter_set _) _) => simple notypeclasses refine cauchy_uniformity_presented : typeclass_instances.
#[global] Hint Extern 2 (FilterPresentation (cauchy_uniformity _) _) => simple notypeclasses refine cauchy_uniformity_presented : typeclass_instances.

Lemma cauchy_filter_space `{@UniformSpace X Φ} : SeparatedUniformSpace (𝒞 X).
Proof. exact (induced_separated_uniform_space _ cauchy_basis _). Qed.
#[global] Hint Extern 2 (SeparatedUniformSpace (cauchy_filter_set _)) => simple notypeclasses refine cauchy_filter_space : typeclass_instances.
#[global] Hint Extern 2 (UniformSpace (cauchy_filter_set _)) => simple notypeclasses refine cauchy_filter_space : typeclass_instances.
#[global] Hint Extern 2 (Topology (cauchy_filter_set _)) => simple notypeclasses refine cauchy_filter_space : typeclass_instances.
#[global] Hint Extern 2 (Hausdorff (cauchy_filter_set _)) => simple notypeclasses refine cauchy_filter_space : typeclass_instances.
#[global] Hint Extern 2 (Separation_T₀ (cauchy_filter_set _)) => simple notypeclasses refine cauchy_filter_space : typeclass_instances.


(** The basis is a monotone function of the index. *)

Lemma cauchy_basis_isfun2 `{@UniformSpace X Φ} : IsFun (cauchy_basis_fun (X:=X)).
Proof.
 intros U₁ U₂. change (U₁ = U₂ ⊸ ∏ p : 𝒞 X ∗ 𝒞 X,
   ( ∏ (V:Φ), ∐ (A:proj1 p) (B:proj2 p), A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ U₁ ∙ V) )
   ⧟ ( ∏ (V:Φ), ∐ (A:proj1 p) (B:proj2 p), A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ U₂ ∙ V) ) ).
 rew <-all_adj. intros [F G]. enough (∀ W₁ W₂ : Φ, W₁ = W₂ ⊸
   ( ∏ (V:Φ), ∐ (A:F) (B:G), A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ W₁ ∙ V) )
   ⊸ ( ∏ (V:Φ), ∐ (A:F) (B:G), A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ W₂ ∙ V) ) ) as P.
 + apply aand_intro; [ apply P |]. rew (symmetry_iff (=) _ _). apply P.
 + clear U₁ U₂; intros U₁ U₂.
   rew <-(aprod_adj _ _ _), <-all_adj; intros V; rew (all_lb _ V).
   rew aex_frob_l, <-aex_adj; intros A; rew <-(aex_ub _ A).
   rew aex_frob_l, <-aex_adj; intros B; rew <-(aex_ub _ B).
   rew (aprod_adj _ _ _).
   let f := constr:( set:(λ U:Φ, A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ U ∙ V)) ) in rew (is_fun f U₁ U₂).
   exact (aandl _ _).
Qed.
#[global] Hint Extern 2 (IsFun cauchy_basis_fun) => simple notypeclasses refine cauchy_basis_isfun2 : typeclass_instances.

Canonical Structure cauchy_basis_fun2 `{@UniformSpace X Φ} : Φ ⇾ 𝒫 (𝒞 X ⊗ 𝒞 X)
  := func_make cauchy_basis_fun.

Lemma cauchy_basis_order_preserving `{@UniformSpace X Φ} : OrderPreserving (cauchy_basis_fun2 (X:=X)).
Proof. apply alt_Build_OrderPreserving.
 intros U₁ U₂. change (U₁ ≤ U₂ ⊸ ∏ p : 𝒞 X ∗ 𝒞 X,
   ( ∏ (V:Φ), ∐ (A:proj1 p) (B:proj2 p), A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ U₁ ∙ V) )
   ⊸ ( ∏ (V:Φ), ∐ (A:proj1 p) (B:proj2 p), A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ U₂ ∙ V) ) ).
 rew <-all_adj. intros [F G].
 rew <-(aprod_adj _ _ _), <-all_adj; intros V; rew (all_lb _ V).
 rew aex_frob_l, <-aex_adj; intros A; rew <-(aex_ub _ A).
 rew aex_frob_l, <-aex_adj; intros B; rew <-(aex_ub _ B).
 change (powerset_el F) in A. change (powerset_el G) in B.
 rew (aprod_com _ _).
 rew (order_preserving_simp (V⁻¹ ∙) U₁ U₂).
 rew (order_preserving_simp (∙ V) (V⁻¹ ∙ U₁) (V⁻¹ ∙ U₂)).
 refine (transitivity le _ _ _).
Qed.
#[global] Hint Extern 2 (OrderPreserving cauchy_basis_fun2) => simple notypeclasses refine cauchy_basis_order_preserving : typeclass_instances.


(** Layered basis. *)

Definition cauchy_basis_alt `{@UniformityBasis X Φ Λ β, !UniformSpace X} {i}
  := filter_presentation_basis (@cauchy_uniformity X Φ _) cauchy_basis_fun (β i).
Arguments cauchy_basis_alt {_ _ _} β {_ _} i.

Lemma cauchy_uniformity_basis `{@UniformityBasis X Φ Λ β, !UniformSpace X}
  : UniformityBasis (cauchy_basis_alt β).
Proof. pose proof uniformity_presentation_basis_correct (X:=𝒞 X).
  intros V.
  pose proof uniformity_basis V as [U PU].
  pose proof uniformity_basis U as [i Pi].
  exists i. rew <-PU. change (cauchy_basis_fun2 (β i) ⊆ cauchy_basis_fun2 U).
  now rew Pi.
Qed.
#[global] Hint Extern 0 (UniformityBasis (X:=cauchy_filter_set _) _) => notypeclasses refine cauchy_uniformity_basis : typeclass_instances.

Lemma cauchy_basis_alt_is_fun@{u} `{@UniformSpace@{u} X Φ} {Λ:set@{u}} (β:Λ ⇾ Φ) `{!UniformityBasis β}
  : IsFun (cauchy_basis_alt β).
Proof. intros i j. rew (is_fun β i j). exact (is_fun cauchy_basis_fun2 _ _). Qed.

Canonical Structure cauchy_basis_alt_fun@{u} `{@UniformSpace@{u} X Φ} {Λ:set@{u}} (β:Λ ⇾ Φ) `{!UniformityBasis β} : _ ⇾ _
  := @func_make _ _ _ (cauchy_basis_alt_is_fun β).

Lemma cauchy_basis_alt_mono@{u} `{@UniformSpace@{u} X Φ} {Λ:set@{u}} {Λle:Le Λ} {β:Λ ⇾ Φ} `{!UniformityBasis β} `{!OrderPreserving β}
  : OrderPreserving (cauchy_basis_alt_fun β).
Proof. apply alt_Build_OrderPreserving. intros i j. rew (order_preserving β i j).
  exact (order_preserving cauchy_basis_fun2 _ _).
Qed.
#[global] Hint Extern 2 (OrderPreserving (cauchy_basis_alt_fun _)) => simple notypeclasses refine cauchy_basis_alt_mono : typeclass_instances.

Definition cauchy_entourage X `{@UniformSpace X Φ} := cauchy_basis_alt_fun (id_fun Φ).
Lemma cauchy_entourage_mono `{@UniformSpace X Φ} : OrderPreserving (cauchy_entourage X).
Proof. now unfold cauchy_entourage. Qed.
#[global] Hint Extern 2 (OrderPreserving (cauchy_entourage _)) => simple notypeclasses refine cauchy_entourage_mono : typeclass_instances.
Local Abbreviation C := cauchy_entourage.

Lemma cauchy_entourage_basis `{@UniformSpace X Φ} (U:cauchy_uniformity X) : ∐ V:Φ, C X V ≤ U.
Proof. exact (uniformity_basis U). Qed.

Lemma cauchy_entourage_flip `{@UniformSpace X Φ} (U:Φ) : C X U⁻¹ = (C X U)⁻¹.
Proof. intros [F G].
  change (  (∏ (W:Φ), ∐ (A:F) (B:G), A ⊗ B ⊆ powerset_pt (W⁻¹ ∙ U⁻¹ ∙ W))
          ⧟ (∏ (W:Φ), ∐ (B:G) (A:F), B ⊗ A ⊆ powerset_pt (W⁻¹ ∙ U ∙ W)) ).
  apply all_proper_aiff; intros W.
  enough (∀ (A:F) (B:G), A ⊗ B ⊆ powerset_pt (W⁻¹ ∙ U⁻¹ ∙ W) ⧟ B ⊗ A ⊆ powerset_pt (W⁻¹ ∙ U ∙ W)) as P.
+ split; (rew <-aex_adj; intros A; rew <-aex_adj; intros B; now rew <-(aex_ub _ B), <-(aex_ub _ A), (P _ _)).
+ intros A B. rew (order_embedding flip (A ⊗ B) _), (tensor_subset_flip _ _).
  change (flip (powerset_pt ?V)) with (powerset_pt (V⁻¹)).
  now group_simplify.
Qed.

Lemma cauchy_entourage_split `{@UniformSpace X Φ} (U V:Φ) : V ∙ V ∙ V ≤ U ⊸ C X V ∙ C X V ≤ C X U.
Proof. change (?a ≤ ?b) with (∏ p, p ∊ a ⊸ p ∊ b) at 2. rew <-all_adj; intros [F G].
  change (V ∙ V ∙ V ≤ U ⊸ (∐ E:𝒞 X, (∏ (W:Φ), ∐ (A:F) (B:E), A ⊗ B ⊆ powerset_pt (W⁻¹ ∙ V ∙ W))
                                  ⊠ (∏ (W:Φ), ∐ (A:E) (B:G), A ⊗ B ⊆ powerset_pt (W⁻¹ ∙ V ∙ W)) )
     ⊸ ∏ (W:Φ), ∐ (A:F) (B:G), A ⊗ B ⊆ powerset_pt (W⁻¹ ∙ U ∙ W)).
  rew <-(aprod_adj _ _ _), <-all_adj; intros W.
  rew aex_frob_l, <-aex_adj; intros E.
  pose proof uniform_split_sym V as [V'[EV' HV']].
  pose (W' := V' ⊓ W). rew [(all_lb _ W')|(all_lb _ W')].
  rew (cauchy_compose _ _ _ _ _).
  rew aex_frob_l, <-aex_adj; intros A. rew aex_frob_l, <-aex_adj; intros B.
  rew <-(aex_ub _ A), <-(aex_ub _ B).
  enough (V ∙ V ∙ V ≤ U ⊸ W'⁻¹ ∙ V ∙ W' ∙ (W'⁻¹ ∙ V ∙ W') ≤ W⁻¹ ∙ U ∙ W ) as Q by
    (rew Q, (aprod_com _ _); exact (transitivity (≤) _ _ _)).
  pose proof meet_lb_l V' W : W' ≤ V' as H1. pose proof meet_lb_r V' W : W' ≤ W as H2.
  rew H2 at 1 4. rew H1.
  replc (W⁻¹ ∙ V ∙ V' ∙ (V'⁻¹ ∙ V ∙ W)) with (W⁻¹ ∙ (V ∙ (V' ∙ V'⁻¹) ∙ V) ∙ W) by now rew ?(associativity (∙) _ _ _).
  rew EV', HV'.
  let t := constr:(order_preserving (∙ W) (W⁻¹ ∙ (V∙V∙V)) (W⁻¹ ∙ U) : _ ⊸ W⁻¹ ∙ (V ∙ V ∙ V) ∙ W ≤ W⁻¹ ∙ U ∙ W ) in rew <-t.
  let t := constr:(order_preserving (W⁻¹ ∙) (V∙V∙V) U) in exact t.
Qed.

Lemma cauchy_entourage_split_alt `{@UniformSpace X Φ} (U:Φ) : ∐ (V:Φ), C X V ∙ C X V ≤ C X U.
Proof. pose proof uniform_split_sym3 U as [V[EV HV]]. exists V. now rew <-(cauchy_entourage_split _ _). Qed.

(** Constructing uniformly continuous functions into 𝒞 X.

Given a raw operation f : X → 𝒫² Y with [f x] a proper filter for each x,
Cauchy-ness of each (f x) and functionhood of f (f respects equality on X)
both follow from uniform continuity expressed on the raw f.

*)

Record CauchyUniformContinuity@{u} {X Y:set@{u}} (f:X → 𝒫² Y) {Φ Ψ} {HX:@UniformSpace X Φ} {HY:@UniformSpace Y Ψ} : SProp :=
{ cauchy_ufm_conty_filter {x:X} : Filter (f x)
; cauchy_ufm_conty_proper {x:X} : ∅ ∊̸ f x
; cauchy_ufm_conty (V:Ψ) : ∐ U:Φ, ∏ x y, (x, y) ∊ U
      ⊸ ∏ W : Ψ, ∐ (A : f x) (B : f y), A ⊗ B ⊆ powerset_pt (W⁻¹ ∙ V ∙ W)
}.
Existing Class CauchyUniformContinuity.

Section mk_ufm_cont_cauchy.
  Context `{H:@CauchyUniformContinuity X Y f Φ Ψ HX HY}.
  
  Local Instance mk_ufm_cont_cauchy (x:X) : CauchyFilter (f x).
  Proof. destruct H as [HF HP uc].  apply alt_Build_CauchyFilter; trivial. intros V.
    pose proof uniform_split_sym3 V as [W[EW PW]].
    specialize (uc W) as [U P]. pose proof (P x x : _ ⊸ _) as P'; clear P.
    rew (aimpl_true_l (near_refl U x : (x, x) ∊ U)) in P'.
    specialize (P' W) as [A[B P]].
    rew EW, PW in P.
    pose proof filter_sub_lattice : SubLattice (f x).
    exists (A ⊓ B).
    rew (meet_lb_l A B) at 1.
    now rew (meet_lb_r _ _).
  Qed.

  Lemma mk_ufm_cont_cauchy_conty : UniformContinuity (λ x, Build_cauchy_filter _ _ (f x) _).
  Proof. apply ufm_conty_by_basis. apply H. Qed.
End mk_ufm_cont_cauchy.
Arguments mk_ufm_cont_cauchy {X Y} f {_ _ _ _ _} x.
Arguments mk_ufm_cont_cauchy_conty {X Y} f {_ _ _ _ _}.


Lemma cauchy_ufm_conty_by_basis@{u}
  `{@UniformityBasis@{u} X Φ Λ₁ α, !UniformSpace X}
  `{@UniformityBasis@{u} Y Ψ Λ₂ β, !UniformSpace Y}
  (f:X → 𝒫² Y)
  `{∀ x, Filter (f x)}
  (proper: ∀ x, ∅ ∊̸ f x)
  (uc: ∀ j:Λ₂, ∐ i, ∏ x y, (x, y) ∊ α i ⊸ ∏ W : Ψ, ∐ (A : f x) (B : f y), A ⊗ B ⊆ powerset_pt (W⁻¹ ∙ β j ∙ W))
 : CauchyUniformContinuity f.
Proof. simple notypeclasses refine (Build_CauchyUniformContinuity _ _ _ _ _ _ _ _ _ _); trivial.
  intros V. pose proof uniformity_basis V as [j Pj].
  specialize (uc j) as [i uc]. exists (α i). now rew <-Pj.
Qed.


(** The unit X ⇾ 𝒞 X *)

Definition principal_subset_filter {X:set} : X ⇾ 𝒫² X := set:(λ x:X, {A:𝒫 X | x ∊ A}).

Lemma principal_subset_filter_alt {X:set} : @principal_subset_filter X = principal_filter ∘ singleton.
Proof. intros x A. change (x ∊ A ⧟ ∏ y, x = y ⊸ y ∊ A). split.
+ rew <-all_adj; intros y. rew <-(aprod_adj _ _ _), (aprod_com _ _). now apply equal_element.
+ rew (all_lb _ x). now simplify.
Qed.

Lemma principal_subset_filter_filter {X:set} {x:X} : Filter (principal_subset_filter x).
Proof. rew principal_subset_filter_alt. now simplify. Qed.

#[global] Hint Extern 2 (Filter (func_op principal_subset_filter _)) => simple notypeclasses refine principal_subset_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (DownDirectedSubset (func_op principal_subset_filter _)) => simple notypeclasses refine principal_subset_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (Inhabited (func_op principal_subset_filter _)) => simple notypeclasses refine principal_subset_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (DownDirected (func_op principal_subset_filter _)) => simple notypeclasses refine principal_subset_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (UpSet (func_op principal_subset_filter _)) => simple notypeclasses refine principal_subset_filter_filter : typeclass_instances.

Definition principal_subset_filter_elt `{@UniformSpace X Φ} (U:Φ) (x:X)
  := @to_subset _ (principal_subset_filter x) (near U x) (near_refl U x).

Lemma principal_filter_cauchy_ufm_conty `{@UniformSpace X Φ}
   : CauchyUniformContinuity (principal_subset_filter (X:=X)).
Proof. split; try exact _.
+ intros x. now change 𝐓.
+ intros U. exists U. intros x y.
  rew <-all_adj; intros V.
  rew <-(aex_ub _ (principal_subset_filter_elt V x)), <-(aex_ub _ (principal_subset_filter_elt V y)).
  change ((x, y) ∊ U ⊸ near V x ⊗ near V y ⊆ powerset_pt ((V⁻¹ ∙ U) ∙ V)).
  rew <-(near_singleton_compose_r_alt (near V x) y (V⁻¹ ∙ U) V).
  rew <-(near_singleton_compose_l_alt (singleton y) x U V).
  exact (andr (singleton_subset (x, y) U)).
Qed.
#[global] Hint Extern 2 (CauchyUniformContinuity (func_op principal_subset_filter)) => simple notypeclasses refine principal_filter_cauchy_ufm_conty : typeclass_instances.

Lemma principal_subset_filter_cauchy `{@UniformSpace X Φ} : ∀ {x:X}, CauchyFilter (principal_subset_filter x).
Proof. exact (mk_ufm_cont_cauchy _). Qed.
#[global] Hint Extern 2 (CauchyFilter (func_op principal_subset_filter _)) => simple notypeclasses refine principal_subset_filter_cauchy : typeclass_instances.

Definition to_cauchy_pt `{@UniformSpace X Φ} (x:X) : 𝒞 X := Build_cauchy_filter X _ (principal_subset_filter x) _.

Lemma to_cauchy_pt_ufm_conty `{@UniformSpace X Φ} : UniformContinuity to_cauchy_pt.
Proof. exact (mk_ufm_cont_cauchy_conty principal_subset_filter). Qed.
#[global] Hint Extern 2 (UniformContinuity to_cauchy_pt) => simple notypeclasses refine to_cauchy_pt_ufm_conty : typeclass_instances.
#[global] Hint Extern 2 (IsFun to_cauchy_pt) => simple notypeclasses refine uniform_continuity_is_fun : typeclass_instances.

Canonical Structure to_cauchy `{@UniformSpace X Φ} : X ⇾ 𝒞 X := func_make to_cauchy_pt.
#[global] Hint Extern 2 (UniformContinuity (func_op to_cauchy)) => simple notypeclasses refine to_cauchy_pt_ufm_conty : typeclass_instances.
Arguments to_cauchy X {_ _}.

Local Abbreviation η := to_cauchy.

Lemma to_cauchy_ufm_cont `{@UniformSpace X Φ} : UniformlyContinuous (η X).
Proof. now split. Qed.
#[global] Hint Extern 2 (UniformlyContinuous (η _)) => simple notypeclasses refine to_cauchy_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (η _)) => simple notypeclasses refine to_cauchy_ufm_cont : typeclass_instances.

(** Basis-closeness of two principal filters reflects to closeness of the
    points — the "points-reflect" atom of η-initiality. *)
Lemma cauchy_basis_points `{@UniformSpace X Φ} (U V:Φ)
  (EV : V⁻¹ = V) (PV : V ∙ V ∙ V ≤ U)
  : (η X)♯ (C X V) ⊆ U.
Proof. intros [x y].
  change ((∏ W:Φ, ∐ (A:η X x) (B:η X y), A ⊗ B ⊆ powerset_pt (W⁻¹ ∙ V ∙ W)) ⊸ (x, y) ∊ U).
  rew (all_lb _ V).
  rew <-aex_adj; intros A. rew <-aex_adj; intros B.
  rew EV, PV.
  enough ((x, y) ∊ A ⊗ B) as Hp.
  + change ((∏ p, p ∊ A ⊗ B ⊸ p ∊ U) ⊸ (x, y) ∊ U).
    now rew (all_lb _ (x,y)), (aimpl_true_l Hp).
  + split. exact (subset_pt_is_el A). exact (subset_pt_is_el B).
Qed.

Lemma cauchy_basis_points_alt `{@UniformSpace X Φ} (U V:Φ)
  (EV : V⁻¹ = V) (PV : V ∙ V ∙ V ≤ U) (x y : X)
  : (η X x, η X y) ∊ C X V ⊸ (x, y) ∊ U.
Proof. exact (cauchy_basis_points U V EV PV (x, y)). Qed.

Lemma to_cauchy_initial `{@UniformSpace X Φ} : UniformlyInitial (η X).
Proof. split; try exact _. apply ufm_refl_by_basis_alt.
  intros U. pose proof uniform_split_sym3 U as [V [EV PV]]. exists V.
  exact (cauchy_basis_points U V EV PV).
Qed.
#[global] Hint Extern 2 (UniformlyInitial (η _)) => simple notypeclasses refine to_cauchy_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (η _)) => simple notypeclasses refine to_cauchy_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (η _))) => simple notypeclasses refine to_cauchy_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (η _)) => simple notypeclasses refine to_cauchy_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (η _)) => simple notypeclasses refine to_cauchy_initial : typeclass_instances.

(** If X is separated then η is an embedding via [uniform_initial_embedding]. *)
Lemma to_cauchy_embedding `{@SeparatedUniformSpace X Φ} : UniformlyEmbedding (η X).
Proof. exact uniform_initial_embedding. Qed.
#[global] Hint Extern 2 (UniformlyEmbedding (η _)) => simple notypeclasses refine to_cauchy_embedding : typeclass_instances.
#[global] Hint Extern 2 (Injective (η _)) => simple notypeclasses refine to_cauchy_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (η _)) => simple notypeclasses refine to_cauchy_embedding : typeclass_instances.


(** A Cauchy filter is basis-close to the principal filter of any point of a
    small member — the "near-member" atom of η-density. *)
Lemma cauchy_basis_near_member_r `{@UniformSpace X Φ} (F : 𝒞 X) (U:Φ) (A:F) {x:X}
  (elx : x ∊ A) (PA : A ⊗ A ⊆ U)
  : (F, η X x) ∊ C X U.
Proof. intros V. exists A. exists (principal_subset_filter_elt V x).
  change (A ⊗ near V x ⊆ powerset_pt (V⁻¹ ∙ U ∙ V)).
  rew <-(near_singleton_compose_r_alt A x _ _).
  replc (singleton (x:X)) with (A : 𝒫 X) using le by now rew (singleton_subset _ _).
  now rew <-(ufm_compose_ub_r _ _).
Qed.

Lemma cauchy_basis_near_member_l `{@UniformSpace X Φ} (F : 𝒞 X) (U:Φ) (A:F) {x:X}
  (elx : x ∊ A) (PA : A ⊗ A ⊆ U)
  : (η X x, F) ∊ C X U.
Proof. change ((F, η X x) ∊ (C X U)⁻¹). rew <-(cauchy_entourage_flip _).
  refine (cauchy_basis_near_member_r F U⁻¹ A elx _).
  now rew <-(order_reflecting flip _ _), (tensor_subset_flip _ _).
Qed.

Lemma to_cauchy_dense@{u} `{@UniformSpace@{u} X Φ} : Dense (η X).
Proof. rew uniform_basis_Dense_iff. intros F U.
  pose proof cauchy_alt F U as [A PA].
  pose proof inhabited A as [x _]. exists x.
  exact (cauchy_basis_near_member_r F U A _ PA).
Qed.
#[global] Hint Extern 2 (Dense (func_op (η _))) => simple notypeclasses refine to_cauchy_dense : typeclass_instances.

Import tensor_map_notation.

(** The map (f : X ⇾ Y) → (𝒞 f : 𝒞 X ⇾ 𝒞 Y) *)
Section map.
  Universes u.
  Constraint 1 <= u.
  Context `{@UniformlyContinuous@{u} X Y Φ Ψ f}.
  
  Local Instance cauchy_map_aux (F:𝒞 X) U `{U ∊ F} : f* (f⁎ U) ∊ F.
  Proof. now apply (up_closed F U). Qed.
  
  Local Instance cauchy_map_filter_inhabited (F:𝒞 X) : ∐ B : 𝒫 Y, f* B ∊ F.
  Proof. pose proof down_directed_subset_inhabited (U:=F) as [U elU]. now exists (f⁎ U). Qed.

  Definition cauchy_map_filter_elt `{@UniformSpace X Φ} (F:𝒞 X) (A:F)
    := @to_subset _ ((f*)* F) (f⁎ A) (cauchy_map_aux F A).
 
  Local Instance cauchy_map_cauchy_uc : CauchyUniformContinuity (X:=𝒞 X) (Y:=Y) (λ F, f** F).
  Proof. pose proof _ : UniformSpace Y. apply cauchy_ufm_conty_by_basis.
  + now intros F.
  + intros F. change (f* ∅ ∊̸ F). rew (preserves_bottom f*). now apply cauchy_proper.
  + intros ε. exists (ufm_preimage f ε). intros F G. change (id ε) with ε.
    match goal with |- apos (?P ⊸ ?Q) => change P with
      (∏ V:Φ, ∐ (A:F) (B:G), A ⊗ B ⊆ powerset_pt (V⁻¹ ∙ ufm_preimage f ε ∙ V) )
    end.
    rew <-all_adj; intros W. rew (all_lb _ (ufm_preimage f W)).
    rew <-(ufm_preimage_inv f W). rew !2(ufm_preimage_compose f _ _).
    pose (V := W⁻¹ ∙ ε ∙ W); change ( W⁻¹ ∙ ε ∙ W ) with V; clearbody V; clear W ε.
    rew <-aex_adj; intros A; rew <-aex_adj; intros B.
    change (powerset_pt (ufm_preimage f V)) with (⟨f,f⟩* V).
    rew <-(image_preimage_adj _ _ _), (image_tensor_map _ _ _ _).
    now rew <-(aex_ub _ (cauchy_map_filter_elt F A)), <-(aex_ub _ (cauchy_map_filter_elt G B)).
  Qed.

  Local Instance cauchy_map_filter_cauchy : ∀ {F:𝒞 X}, CauchyFilter (f** F).
  Proof. exact (mk_ufm_cont_cauchy _). Qed.

  Definition cauchy_map_pt (F:𝒞 X) : 𝒞 Y := Build_cauchy_filter Y _ (f** F) _.

  Local Instance cauchy_map_ufm_conty : UniformContinuity@{u} (X:=𝒞 X) cauchy_map_pt.
  Proof. exact (mk_ufm_cont_cauchy_conty (λ F:𝒞 X, f** F)). Qed.

  Definition cauchy_map : 𝒞 X ⇾ 𝒞 Y := @func_make _ _ cauchy_map_pt uniform_continuity_is_fun.

  Lemma cauchy_map_ufm_cont : UniformlyContinuous@{u} cauchy_map.
  Proof. now split. Qed.
  
  Lemma cauchy_map_spec : cauchy_map ∘ η X = η Y ∘ f.
  Proof. now intros x. Qed.

  Lemma cauchy_map_dense `{!Dense f} : Dense cauchy_map.
  Proof. apply (Dense_factor_right (η _)). now rew cauchy_map_spec. Qed.
End map.
Arguments cauchy_map_pt {_ _ _ _} f {_} F.
Arguments cauchy_map {_ _ _ _} f {_}.
Canonical cauchy_map.
Arguments cauchy_map_spec {_ _ _ _} f {_}.

#[global] Hint Extern 2 (UniformContinuity (cauchy_map_pt ?f)) => simple notypeclasses refine (cauchy_map_ufm_conty (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (IsFun (cauchy_map_pt _)) => simple notypeclasses refine uniform_continuity_is_fun : typeclass_instances.
#[global] Hint Extern 2 (UniformContinuity (func_op (cauchy_map ?f))) => simple notypeclasses refine (cauchy_map_ufm_conty (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (cauchy_map ?f)) => simple notypeclasses refine (cauchy_map_ufm_cont (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (Continuous (cauchy_map ?f)) => simple notypeclasses refine (cauchy_map_ufm_cont (f:=f)) : typeclass_instances.

#[global] Hint Extern 2 (Dense (func_op (cauchy_map ?f))) => simple notypeclasses refine (cauchy_map_dense (f:=f)) : typeclass_instances.

Lemma cauchy_map_initial@{u} {X Y:set@{u}}  `{@UniformlyInitial X Y Φ Ψ f}
  : UniformlyInitial (cauchy_map f).
Proof. refine (ufm_dense_initial (η _) _); try exact _. now rew (cauchy_map_spec _). Qed.

#[global] Hint Extern 2 (UniformlyInitial (cauchy_map ?f)) => simple notypeclasses refine (cauchy_map_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (cauchy_map ?f)) => simple notypeclasses refine (cauchy_map_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (cauchy_map ?f))) => simple notypeclasses refine (cauchy_map_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (cauchy_map ?f)) => simple notypeclasses refine (cauchy_map_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (cauchy_map ?f)) => simple notypeclasses refine (cauchy_map_initial (f:=f)) : typeclass_instances.

#[global] Hint Extern 2 (UniformlyEmbedding (cauchy_map _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (cauchy_map _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.

Lemma cauchy_map_compose@{u} {X Y Z:set@{u}}  `{@UniformlyContinuous X Y Φ Ψ f}  `{@UniformlyContinuous Y Z Ψ Ξ g}
  : cauchy_map@{u} (g ∘ f) = cauchy_map@{u} g ∘ cauchy_map@{u} f.
Proof. now intros F. Qed.

Lemma cauchy_map_id@{u}  `{@UniformSpace@{u} X Φ} : cauchy_map@{u} (id_fun X) = id_fun (𝒞 X).
Proof. now intros F. Qed.

(** Universal property, from dense reflecting (f : X ⇾ Y) construct
    g : Y ⇾ 𝒞 X such that g ∘ f = η *)
Section UP.
  Universes u.
  Constraint 1 <= u.
  Context `{@UniformlyReflecting@{u} X Y Φ Ψ f, !Dense f}.

  Definition cauchy_reflect_basis := set:(λ (y:Y) (V:Ψ), f* (near V y)).
  Local Abbreviation B := cauchy_reflect_basis.

  Local Instance cauchy_reflect_basis_monotone (y:Y) : OrderPreserving@{u} (B y).
  Proof. apply alt_Build_OrderPreserving. intros V₁ V₂.
    change (V₁ ≤ V₂ ⊸ f* (near V₁ y) ⊆ f* (near V₂ y)).
    rew <-(order_preserving f* _ _).
    change ( (∏ p, p ∊ V₁ ⊸ p ∊ V₂) ⊸ (∏ y', (y, y') ∊ V₁ ⊸ (y, y') ∊ V₂) ).
    rew <-all_adj; intros y'. now rew (all_lb _ (y, y')).
  Qed.

  Definition cauchy_reflect_filter := set:(λ y:Y, { A : 𝒫 X | ∐ V:Ψ, B y V ⊆ A }).
  Local Abbreviation F := cauchy_reflect_filter.

  Lemma cauchy_reflect_filter_alt (y:Y) : F y = point_upward_closure (range (B y)).
  Proof. now rew (point_upward_closure_range _). Qed.
  
  Local Instance cauchy_reflect_is_filter (y:Y) : Filter (F y).
  Proof. pose proof _ : UniformSpace Y. now rew (cauchy_reflect_filter_alt _). Qed.

  Local Instance cauchy_reflect_basis_elt y (V:Ψ) : B y V ∊ F y.
  Proof. now exists V. Qed.

  Local Instance cauchy_reflect_cauchy_uc : CauchyUniformContinuity (X:=Y) (Y:=X) F.
  Proof. pose proof _ : UniformSpace Y. split.
  + now intros y.
  + intros y V. pose proof uniform_dense_range f y V as [x Px].
    exists x. now change (near V y (f x) ⊠ 𝐓).
  + intros U. pose proof ufm_reflection_alt f U as [V PV].
    pose proof uniform_split_sym3 V as [V' [EV PV3]].
    exists V'. intros y y'.
    rew <-all_adj; intros W.
    rew <-(aex_ub _ (to_subset (U:=F y) (B y V'))), <-(aex_ub _ (to_subset (U:=F y') (B y' V'))).
    rew <-(ufm_compose_ub_l (W⁻¹ ∙ U) W), <-(ufm_compose_ub_r W⁻¹ U).
    rew <-PV.
    change ((y, y') ∊ V' ⊸ ⟨f,f⟩* (near V' y ⊗ near V' y') ⊆ ⟨f,f⟩* V).
    rew <-(order_preserving ⟨f,f⟩* _ _).
    rew <-PV3.
    rew <-(near_singleton_compose_r_alt _ _ (V' ∙ V') V').
    rew <-EV at 3.
    rew <-(near_singleton_compose_l_alt _ _ V' V').
    refine (andr (singleton_subset _ _)).
  Qed.

  Local Instance cauchy_reflect_filter_cauchy : ∀ {y:Y}, CauchyFilter (F y).
  Proof. exact (mk_ufm_cont_cauchy _). Qed.

  Definition cauchy_reflect_pt (y:Y) : 𝒞 X := Build_cauchy_filter X _ (F y) _.

  Local Instance cauchy_reflect_pt_ufm_conty : UniformContinuity@{u} (X:=Y) (Y:=𝒞 X) cauchy_reflect_pt.
  Proof. exact (mk_ufm_cont_cauchy_conty cauchy_reflect_filter). Qed.

  Definition cauchy_reflect : Y ⇾ 𝒞 X := @func_make _ _ cauchy_reflect_pt uniform_continuity_is_fun.

  Lemma cauchy_reflect_ufm_cont : UniformlyContinuous@{u} cauchy_reflect.
  Proof. now split. Qed.

  Lemma cauchy_reflect_spec : cauchy_reflect ∘ f = η _.
  Proof. rew (symmetry_iff (=) _ _). intros x U.
    pose proof uniform_split_sym U as [U' [EU' PU']].
    pose proof ufm_reflection_alt f U' as [V PV].
    exists (principal_subset_filter_elt U' x).
    exists (to_subset (B (f x) V)).
    change (near U' x ⊗ B (f x) V  ⊆ U).
    rew <-PU'. rew <-EU' at 2.
    rew <-(near_singleton_compose_l_alt _ _ U' U').
    change (singleton x ⊗ f* (near V (f x)) ⊆ U').
    rew <-PV, <-(image_preimage_adj _ _ _), (image_tensor_map _ _ _ _).
    rew [(image_preimage_counit _ _)|(image_singleton_alt _ _)].
    apply near_singleton_r.
  Qed.
  
  Lemma cauchy_reflect_dense : Dense cauchy_reflect.
  Proof. apply (Dense_factor_right f). now rew cauchy_reflect_spec. Qed.
End UP.
Arguments cauchy_reflect_pt {_ _ _ _} f {_ _} y.
Arguments cauchy_reflect    {_ _ _ _} f {_ _}.
Canonical cauchy_reflect.
Arguments cauchy_reflect_spec {_ _ _ _} f {_ _}.

#[global] Hint Extern 2 (UniformContinuity (cauchy_reflect_pt ?f)) => simple notypeclasses refine (cauchy_reflect_pt_ufm_conty (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (IsFun (cauchy_reflect_pt _)) => simple notypeclasses refine uniform_continuity_is_fun : typeclass_instances.
#[global] Hint Extern 2 (UniformContinuity (func_op (cauchy_reflect ?f))) => simple notypeclasses refine (cauchy_reflect_pt_ufm_conty (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyContinuous (cauchy_reflect ?f)) => simple notypeclasses refine (cauchy_reflect_ufm_cont (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (Continuous (cauchy_reflect ?f)) => simple notypeclasses refine (cauchy_reflect_ufm_cont (f:=f)) : typeclass_instances.

#[global] Hint Extern 2 (Dense (func_op (cauchy_reflect ?f))) => simple notypeclasses refine (cauchy_reflect_dense (f:=f)) : typeclass_instances.

Lemma cauchy_reflect_initial@{u} `{@UniformlyInitial@{u} X Y Φ Ψ f, !Dense f}
  : UniformlyInitial (cauchy_reflect f).
Proof. enough (UniformlyInitial (cauchy_reflect f ∘ f)) by exact (ufm_dense_initial f _).
  now rew (cauchy_reflect_spec _).
Qed.
#[global] Hint Extern 2 (UniformlyInitial (cauchy_reflect ?f)) => simple notypeclasses refine (cauchy_reflect_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (cauchy_reflect ?f)) => simple notypeclasses refine (cauchy_reflect_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (UniformReflection (func_op (cauchy_reflect ?f))) => simple notypeclasses refine (cauchy_reflect_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (cauchy_reflect ?f)) => simple notypeclasses refine (cauchy_reflect_initial (f:=f)) : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (cauchy_reflect ?f)) => simple notypeclasses refine (cauchy_reflect_initial (f:=f)) : typeclass_instances.

#[global] Hint Extern 2 (UniformlyEmbedding (cauchy_reflect _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (cauchy_reflect _)) => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.

Definition cauchy_completion_reflect@{u} `{@UniformSpace@{u} X Φ} : CompletionReflect@{u} (η@{u} X)
  := λ Y, @cauchy_reflect X Y _.

#[global] Hint Extern 2 (CompletionReflect (X:=?X) to_cauchy) => notypeclasses refine (@cauchy_completion_reflect X _ _) : typeclass_instances.
#[global] Hint Extern 2 (CompletionReflect (X:=?X) (Y:=𝒞 ?X) _) => notypeclasses refine (@cauchy_completion_reflect X _ _) : typeclass_instances.
#[global] Hint Extern 2 (CompletionReflect (X:=?X) (Y:=cauchy_filter_set ?X) _) => notypeclasses refine (@cauchy_completion_reflect X _ _) : typeclass_instances.

Lemma cauchy_completion@{u} `{@UniformSpace@{u} X Φ} : Completion@{u} (η X).
Proof. split; try exact _; intros ?? f ??.
+ now change (UniformlyContinuous (cauchy_reflect f)).
+ exact (cauchy_reflect_spec _).
Qed.
#[global] Hint Extern 2 (Completion (η _)) => simple notypeclasses refine cauchy_completion : typeclass_instances.


