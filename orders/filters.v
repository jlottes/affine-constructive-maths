Require Import interfaces.sprop.
Require Import interfaces.orders interfaces.subset theory.sublattices.
Require Import orders.orders orders.lattices orders.sublattices orders.suborders orders.maps orders.closure orders.subset.
Require Import orders.subset_images.
Require Import logic.aprop.
Require Import set_lambda.
Require Import easy rewrite simplify.

Local Notation "X 'ᵒᵖ'" := (Order_op X) (at level 1, format "X 'ᵒᵖ'").

(** Build lemmas for the dual structures *)

Lemma Build_Ideal {X:set} {Xle:Le X} {U : 𝒫 X} :
  DownSet U → UpDirectedSubset U → Ideal U.
Proof. now split. Qed.

Lemma Build_IdealPresentation@{u} {X:set@{u}} {Xle:Le X} {U : 𝒫 X} {Λ:Type@{u}} {β:Λ → X} :
  WeakPoset X → (∀ x, x ∊ U ⧟ ∐ i, x ≤ β i) → IdealPresentation U β.
Proof. now split. Qed.

Lemma Build_IdealBasis@{u} {X:set@{u}} {Xle:Le X} {U : 𝒫 X} {Λ:Type@{u}} {β:Λ → U} :
  (∀ x:U, ∐ i, x ≤ β i) → IdealBasis β.
Proof. exact (λ H, H). Qed.

(** Opposite order instances *)

Definition Filter_op `{H:@Ideal X Xle U} : Filter (X:=X ᵒᵖ) U := H.
Definition Ideal_op `{H:@Filter X Xle U} : Ideal (X:=X ᵒᵖ) U := H.
Global Hint Extern 2 (Filter (X:=_ ᵒᵖ) _) => simple notypeclasses refine Filter_op : typeclass_instances.
Global Hint Extern 2 (Ideal (X:=_ ᵒᵖ) _) => simple notypeclasses refine Ideal_op : typeclass_instances.

(** Substructure predicates respect equality of subsets. *)
Lemma Filter_proper_impl {X:set} {Xle:Le X} (U V : 𝒫 X)
  : U = V → Filter U → Filter V.
Proof. intros E P. split; now rew <-E. Qed.
Canonical Structure Filter_fun {X:set} {Xle:Le X} :=
  make_weak_spred (@Filter X Xle) Filter_proper_impl.

Definition Ideal_proper_impl {X:set} {Xle:Le X} (U V : 𝒫 X)
  : U = V → Ideal U → Ideal V
  := Filter_proper_impl (X:=X ᵒᵖ) U V.
Canonical Structure Ideal_fun {X:set} {Xle:Le X} :=
  make_weak_spred (@Ideal X Xle) Ideal_proper_impl.

(** Filter on a MeetSemiLatticeOrder is a MeetSubSemiLattice *)

Lemma filter_meet_sub_sl `{MeetSemiLatticeOrder L} {U:𝒫 L} `{!Filter U} : MeetSubSemiLattice U.
Proof. apply alt_Build_MeetSubSemiLattice. intros x y.
  rew (down_directed_subset (U:=U) x y).
  rew <-aex_adj. intros z.
  rew (meet_glb x y z).
  rew (aprod_com _ _), (aprod_adj _ _ _).
  now apply up_closed.
Qed.

Lemma filter_sub_lattice `{LatticeOrder L} {U:𝒫 L} `{!Filter U} : SubLattice U.
Proof. split; try exact _.
+ exact filter_meet_sub_sl.
+ exact upset_join_sub_sl.
Qed.

Lemma ideal_join_sub_sl `{JoinSemiLatticeOrder L} {U:𝒫 L} `{!Ideal U} : JoinSubSemiLattice U.
Proof. exact (filter_meet_sub_sl (L:=L ᵒᵖ)). Qed.

Lemma ideal_sub_lattice `{LatticeOrder L} {U:𝒫 L} `{!Ideal U} : SubLattice U.
Proof. split; try exact _.
+ exact downset_meet_sub_sl.
+ exact ideal_join_sub_sl.
Qed.

Lemma sub_meet_sl_order_down_directed `{MeetSemiLatticeOrder L} {U:𝒫 L} `{!MeetSubSemiLattice U} : 
  (∐ x, x ∊ U) → DownDirectedSubset U.
Proof. intro. apply Build_DownDirectedSubset; trivial. intros x y.
  rew <-(aex_ub _ (x ⊓ y)).
  rew [ (aiff_is_true (meet_lb_l _ _)) | (aiff_is_true (meet_lb_r _ _)) ]; simplify.
  now apply sub_meet_closed.
Qed.

Lemma sub_join_sl_order_up_directed `{JoinSemiLatticeOrder L} {U:𝒫 L} `{!JoinSubSemiLattice U} :
  (∐ x, x ∊ U) → UpDirectedSubset U.
Proof. exact (sub_meet_sl_order_down_directed (L:=L ᵒᵖ)). Qed.


(** FilterSubset on a BoundedMeetSemiLatticeOrder is a MeetSubBoundedSemiLattice *)

Lemma filter_top `{BoundedMeetSemiLatticeOrder L} {U:𝒫 L} `{!Filter U} : ⊤ ∊ U.
Proof. pose proof  _ : sprop.Inhabited U as [[x el] _].
  enough (x ∊ U ⊸ ⊤ ∊ U) as E by now rew <-E.
  rew <-(up_closed _ x _).
  apply below_top.
Qed.

Lemma filter_bounded_meet_sub_sl `{BoundedMeetSemiLatticeOrder L} {U:𝒫 L} `{!Filter U} : MeetSubBoundedSemiLattice U.
Proof. apply alt_Build_MeetSubBoundedSemiLattice. apply filter_meet_sub_sl. exact filter_top. Qed.

Lemma ideal_bottom `{BoundedJoinSemiLatticeOrder L} {U:𝒫 L} `{!Ideal U} : ⊥ ∊ U.
Proof. exact (filter_top (L:=L ᵒᵖ)). Qed.

Lemma ideal_bounded_join_sub_sl `{BoundedJoinSemiLatticeOrder L} {U:𝒫 L} `{!Ideal U} : JoinSubBoundedSemiLattice U.
Proof. exact (filter_bounded_meet_sub_sl (L:=L ᵒᵖ)). Qed.


Lemma sub_bounded_meet_sl_order_down_directed `{BoundedMeetSemiLatticeOrder L} {U:𝒫 L} `{!MeetSubBoundedSemiLattice U} : DownDirectedSubset U.
Proof. apply sub_meet_sl_order_down_directed. exists top. now apply sub_top_closed. Qed.

Lemma sub_bounded_join_sl_order_up_directed `{BoundedJoinSemiLatticeOrder L} {U:𝒫 L} `{!JoinSubBoundedSemiLattice U} : UpDirectedSubset U.
Proof. exact (sub_bounded_meet_sl_order_down_directed (L:=L ᵒᵖ)). Qed.

(** Principal filter *)

Definition principal_filter `{WeakPoset X} : X ⇾ 𝒫 X := set:(λ x:X, { y:X | x ≤ y}).

Global Hint Extern 1 (apos (?y ∊ func_op (@principal_filter ?X ?Xle _) ?x)) => change (@le X Xle (x, y)) : typeclass_instances.

Lemma principal_filter_closure `{WeakPoset X} : principal_filter (X:=X) = upward_closure ∘ singleton.
Proof. intros x y; split.
+ change (x ≤ y ⊸ ∐ b, x = b ⊠ b ≤ y).
  rew <-(aex_ub _ x). now simplify.
+ change ((∐ b, x = b ⊠ b ≤ y) ⊸ x ≤ y).
  rew <-aex_adj. intros b. rew (eq_le x b). now apply transitivity.
Qed.

Lemma principal_filter_point_closure `{WeakPoset X} (x:X) : principal_filter x = point_upward_closure (singleton x).
Proof. rew [ principal_filter_closure | (point_upward_closure_alt _) ].
  now rew (of_course_singleton _).
Qed.

Lemma principal_filter_least_upset `{WeakPoset X} {x:X} : LeastUpSet (principal_filter x).
Proof. now rew (principal_filter_point_closure _). Qed.
#[global] Hint Extern 2 (LeastUpSet (func_op principal_filter _)) => simple notypeclasses refine principal_filter_least_upset : typeclass_instances.

Lemma principal_filter_filter `{WeakPoset X} {x:X} : Filter (principal_filter x).
Proof. now rew (principal_filter_point_closure _). Qed.

#[global] Hint Extern 2 (Filter (func_op principal_filter _)) => simple notypeclasses refine principal_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (DownDirectedSubset (func_op principal_filter _)) => simple notypeclasses refine principal_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (Inhabited (func_op principal_filter _)) => simple notypeclasses refine principal_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (DownDirected (func_op principal_filter _)) => simple notypeclasses refine principal_filter_filter : typeclass_instances.
#[global] Hint Extern 2 (UpSet (func_op principal_filter _)) => simple notypeclasses refine principal_filter_filter : typeclass_instances.

Lemma principal_filter_order_embedding_flip `{WeakPoset X} : OrderEmbeddingFlip (principal_filter (X:=X)).
Proof. apply alt_Build_OrderEmbeddingFlip. intros x y. change (x ≤ y ⧟ ∏ z, y ≤ z ⊸ x ≤ z). split.
+ rew <-all_adj; intros z. rew <-(aprod_adj _ _ _). now apply transitivity.
+ rew (all_lb _ y). now simplify.
Qed.
#[global] Hint Extern 2 (OrderEmbeddingFlip principal_filter) => simple notypeclasses refine principal_filter_order_embedding_flip : typeclass_instances.
#[global] Hint Extern 2 (OrderPreservingFlip principal_filter) => simple notypeclasses refine principal_filter_order_embedding_flip : typeclass_instances.
#[global] Hint Extern 2 (OrderReflectingFlip principal_filter) => simple notypeclasses refine principal_filter_order_embedding_flip : typeclass_instances.

(** Principal ideal *)

Definition principal_ideal `{WeakPoset X} : X ⇾ 𝒫 X := set:(λ x:X, { y:X | y ≤ x}). (*principal_filter (X:=X ᵒᵖ).*)

Global Hint Extern 1 (apos (?y ∊ func_op (@principal_ideal ?X ?Xle _) ?x)) => change (@le X Xle (y, x)) : typeclass_instances.

Definition principal_ideal_closure `{WeakPoset X} : principal_ideal (X:=X) = downward_closure ∘ singleton
  := principal_filter_closure (X:=X ᵒᵖ).

Definition principal_ideal_point_closure `{WeakPoset X} (x:X) : principal_ideal x = point_downward_closure (singleton x)
  := principal_filter_point_closure (X:=X ᵒᵖ) x.

Definition principal_ideal_least_downset `{WeakPoset X} {x:X} : LeastDownSet (principal_ideal x)
  := principal_filter_least_upset (X:=X ᵒᵖ) (x:=x).

Definition principal_ideal_ideal `{WeakPoset X} {x:X} : Ideal (principal_ideal x)
  := principal_filter_filter (X:=X ᵒᵖ) (x:=x).

#[global] Hint Extern 2 (Ideal (func_op principal_ideal _)) => simple notypeclasses refine principal_ideal_ideal : typeclass_instances.
#[global] Hint Extern 2 (UpDirectedSubset (func_op principal_ideal _)) => simple notypeclasses refine principal_ideal_ideal : typeclass_instances.
#[global] Hint Extern 2 (Inhabited (func_op principal_ideal _)) => simple notypeclasses refine principal_ideal_ideal : typeclass_instances.
#[global] Hint Extern 2 (UpDirected (func_op principal_ideal _)) => simple notypeclasses refine principal_ideal_ideal : typeclass_instances.
#[global] Hint Extern 2 (LeastDownSet (func_op principal_ideal _)) => simple notypeclasses refine principal_ideal_least_downset : typeclass_instances.
#[global] Hint Extern 2 (DownSet (func_op principal_ideal _)) => simple notypeclasses refine principal_ideal_ideal : typeclass_instances.

Lemma principal_ideal_order_embedding `{WeakPoset X} : OrderEmbedding (principal_ideal (X:=X)).
Proof. apply alt_Build_OrderEmbedding. intros x y. change (x ≤ y ⧟ ∏ z, z ≤ x ⊸ z ≤ y). split.
+ rew <-all_adj; intros z. rew <-(aprod_adj _ _ _), (aprod_com _ _). now apply transitivity.
+ rew (all_lb _ x). now simplify.
Qed.
#[global] Hint Extern 2 (OrderEmbedding principal_ideal) => simple notypeclasses refine principal_ideal_order_embedding : typeclass_instances.
#[global] Hint Extern 2 (OrderPreserving principal_ideal) => simple notypeclasses refine principal_ideal_order_embedding : typeclass_instances.
#[global] Hint Extern 2 (OrderReflecting principal_ideal) => simple notypeclasses refine principal_ideal_order_embedding : typeclass_instances.

(** Filter bases *)

Definition presented_filter@{u} `{WeakPoset@{u} X} {Λ:Type@{u}} (β:Λ → X) : 𝒫 X
  := { x : X | ∐ i, β i ≤ x }.

Lemma presented_filter_correct@{u} `{WeakPoset@{u} X} {Λ:Type@{u}} (β:Λ → X)
  : FilterPresentation (presented_filter β) β.
Proof. now split. Qed.
#[global] Hint Extern 2 (FilterPresentation (presented_filter _) _)
  => simple notypeclasses refine presented_filter_correct : typeclass_instances.

Lemma filter_presentation_alt@{u}  `{@FilterPresentation@{u} X Xle U Λ β}
  : U = point_upward_closure (range β).
Proof.  rew (point_upward_closure_range _). intros x. apply H. Qed.

Coercion filter_presentation_least_upset@{u} `{@FilterPresentation@{u} X Xle U Λ β}
  : LeastUpSet U.
Proof. now rew filter_presentation_alt. Qed.

Lemma presented_filter_filter@{u}
  `{@OrderPreserving@{u} Λ X Λle Xle β, U:𝒫 X, !FilterPresentation U β, !DownDirected Λ}
  : Filter U.
Proof. now rew filter_presentation_alt. Qed.

Lemma presented_filter_filter_alt@{u} `{@FilterPresentation@{u} X Xle U Λ β, !Inhabited Λ}
  (down: ∀ i j : Λ, ∐ k, β k ≤ β i ⊠ β k ≤ β j)
  : Filter U.
Proof. split; try exact _. apply Build_DownDirectedSubset.
+ pose proof inhabited Λ as [i _]. exists (β i). rew (filter_presentation U β _). now exists i.
+ intros x y. rew [(filter_presentation U β x)|(filter_presentation U β y)].
  rew <-aex_adj2; intros i j.
  pose proof down i j as [k [E1 E2]]; rew [ <-E1 | <-E2 ].
  rew <-(aex_ub _ (β k)). enough (β k ∊ U) by now rew (aprod_true_l (_ : β k ∊ U)).
  rew (filter_presentation U β _). now exists k.
Qed.
    
Lemma filter_basis_self `{WeakPoset X} : FilterBasis (@id X).
Proof. intros x. now exists x. Qed.
#[global] Hint Extern 100 (FilterBasis _) => notypeclasses refine filter_basis_self : typeclass_instances.

Lemma filter_basis_compose@{u}
  `{WeakPoset@{u} X} `{WeakPoset@{u} Y}
  {Λ : set@{u}} (α:Λ ⇾ X) (β:X ⇾ Y)
  `{!FilterBasis α, !FilterBasis β, !OrderPreserving β}
  : FilterBasis (β ∘ α).
Proof. intros y. pose proof filter_basis β y as [x Hx]. rew <-Hx.
  pose proof filter_basis α x as [i Hi]. exists i.
  change (β (α i) ≤ β x). now rew Hi.
Qed.
#[global] Hint Extern 2 (FilterBasis (func_op (_ ∘ _))) => simple notypeclasses refine (filter_basis_compose _ _) : typeclass_instances.

Import tensor_map_notation.
Lemma tensor_filter_basis@{u}
  `{WeakPoset@{u} X} `{WeakPoset@{u} Y}
  {Λ₁ Λ₂ : set@{u}} (α:Λ₁ ⇾ X) (β:Λ₂ ⇾ Y)
  `{!FilterBasis α, !FilterBasis β}
  : FilterBasis ⟨α, β⟩.
Proof. intros [x y].
  pose proof filter_basis α x as [i Pi].
  pose proof filter_basis β y as [j Pj].
  exists (i, j). now rew [<-Pi | <-Pj].
Qed.
#[global] Hint Extern 2 (FilterBasis (func_op ⟨_, _⟩)) => simple notypeclasses refine (tensor_filter_basis _ _) : typeclass_instances.

Lemma filter_presentation_basis_elt@{u} `{@FilterPresentation@{u} X Xle U Λ β} {i:Λ} : β i ∊ U.
Proof. rew (filter_presentation U _ _). now exists i. Qed.

Definition filter_presentation_basis@{u} `{@FilterPresentation@{u} X Xle U Λ β} (i:Λ) : U
  := @to_subset X U (β i) filter_presentation_basis_elt.
Arguments filter_presentation_basis {_ _} U {_} β {_} i.

Lemma filter_presentation_basis_correct@{u} `{@FilterPresentation@{u} X Xle U Λ β}
  : FilterBasis (filter_presentation_basis U β).
Proof. intros [x Hx]. change (∐ i, β i ≤ x). revert Hx. now rew (filter_presentation U β _). Qed.
#[global] Hint Extern 2 (FilterBasis (filter_presentation_basis _ _)) => simple notypeclasses refine filter_presentation_basis_correct : typeclass_instances.

Lemma filter_presentation_basis_is_fun@{u} {Λ X:set@{u}} {β:Λ ⇾ X} `{@FilterPresentation@{u} X Xle U Λ β}
  : IsFun (filter_presentation_basis U β).
Proof. intros x y. exact (is_fun β x y). Qed.

Definition filter_presentation_basis_fun@{u} {Λ X:set@{u}} (U:𝒫 X) (β:Λ ⇾ X) `{@FilterPresentation@{u} X Xle U Λ β} : _ ⇾ _
  := @func_make _ _ _ (filter_presentation_basis_is_fun (β:=β) (U:=U)).
Canonical filter_presentation_basis_fun.
#[global] Hint Extern 2 (FilterBasis (func_op (filter_presentation_basis_fun _ _))) => simple notypeclasses refine filter_presentation_basis_correct : typeclass_instances.

Lemma filter_presentation_basis_order_preserving@{u}
  `{@WeakPoset@{u} Λ Λle} {X:set@{u}} {U:𝒫 X} {β:Λ ⇾ X} `{@FilterPresentation@{u} X Xle U Λ β, !OrderPreserving β}
  : OrderPreserving (filter_presentation_basis_fun U β).
Proof. apply alt_Build_OrderPreserving. exact (order_preserving β). Qed.
#[global] Hint Extern 2 (OrderPreserving (filter_presentation_basis_fun _ _)) => simple notypeclasses refine filter_presentation_basis_order_preserving : typeclass_instances.

(** Ideal bases *)

Definition presented_ideal@{u} `{WeakPoset@{u} X} {Λ:Type@{u}} (β:Λ → X) : 𝒫 X
  := { x : X | ∐ i, x ≤ β i }. (*presented_filter (X:=X ᵒᵖ) β A.*)

Lemma presented_ideal_correct@{u} `{WeakPoset@{u} X} {Λ:Type@{u}} (β:Λ → X)
  : IdealPresentation (presented_ideal β) β.
Proof. now split. Qed.
#[global] Hint Extern 2 (IdealPresentation (presented_ideal _) _)
  => simple notypeclasses refine presented_ideal_correct : typeclass_instances.

Coercion IdealPresentation_poset@{u} `{H:@IdealPresentation@{u} X Xle U Λ β} : WeakPoset X
  := WeakPoset_op (X:=X ᵒᵖ) (H:=filter_presentation_poset U β H).

Lemma ideal_presentation_alt@{u}  `{@IdealPresentation@{u} X Xle U Λ β}
  : U = point_downward_closure (range β).
Proof. exact (filter_presentation_alt (X:=X ᵒᵖ)). Qed.

Coercion ideal_presentation_least_downset@{u} `{@IdealPresentation@{u} X Xle U Λ β}
  : LeastDownSet U.
Proof. now rew ideal_presentation_alt. Qed.

Lemma presented_ideal_ideal@{u}
  `{@OrderPreserving@{u} Λ X Λle Xle β, U:𝒫 X, !IdealPresentation U β, !UpDirected Λ}
  : Ideal U.
Proof. now rew ideal_presentation_alt. Qed.

Lemma presented_ideal_ideal_alt@{u} `{@IdealPresentation@{u} X Xle U Λ β, !Inhabited Λ}
  (up: ∀ i j : Λ, ∐ k, β i ≤ β k ⊠ β j ≤ β k)
  : Ideal U.
Proof. exact (presented_filter_filter_alt (X:=X ᵒᵖ) up). Qed.

Lemma ideal_basis_self `{WeakPoset X} : IdealBasis (@id X).
Proof. intros x. now exists x. Qed.
#[global] Hint Extern 100 (IdealBasis _) => notypeclasses refine ideal_basis_self : typeclass_instances.

Lemma ideal_basis_compose@{u}
  `{WeakPoset@{u} X} `{WeakPoset@{u} Y}
  {Λ : set@{u}} (α:Λ ⇾ X) (β:X ⇾ Y)
  `{!IdealBasis α, !IdealBasis β, !OrderPreserving β}
  : IdealBasis (β ∘ α).
Proof. exact (filter_basis_compose (X:=X ᵒᵖ) (Y:=Y ᵒᵖ) α β). Qed.
#[global] Hint Extern 2 (IdealBasis (_ ∘ _)) => simple notypeclasses refine (ideal_basis_compose _ _) : typeclass_instances.

Lemma tensor_ideal_basis@{u}
  `{WeakPoset@{u} X} `{WeakPoset@{u} Y}
  {Λ₁ Λ₂ : set@{u}} (α:Λ₁ ⇾ X) (β:Λ₂ ⇾ Y)
  `{!IdealBasis α, !IdealBasis β}
  : IdealBasis ⟨α, β⟩.
Proof. exact (tensor_filter_basis (X:=X ᵒᵖ) (Y:=Y ᵒᵖ) α β). Qed.
#[global] Hint Extern 2 (IdealBasis (func_op ⟨_, _⟩)) => simple notypeclasses refine tensor_ideal_basis : typeclass_instances.

Lemma ideal_presentation_basis_elt@{u} `{@IdealPresentation@{u} X Xle U Λ β} {i:Λ} : β i ∊ U.
Proof. rew (ideal_presentation U _ _). now exists i. Qed.

Definition ideal_presentation_basis@{u} `{@IdealPresentation@{u} X Xle U Λ β} (i:Λ) : U
  := @to_subset X U (β i) ideal_presentation_basis_elt.
Arguments ideal_presentation_basis {_ _} U {_} β {_} i.

Lemma ideal_presentation_basis_correct@{u} `{@IdealPresentation@{u} X Xle U Λ β}
  : IdealBasis (ideal_presentation_basis U β).
Proof. exact (filter_presentation_basis_correct (X:=X ᵒᵖ)). Qed.
#[global] Hint Extern 2 (IdealBasis (ideal_presentation_basis _ _)) => simple notypeclasses refine ideal_presentation_basis_correct : typeclass_instances.

Lemma ideal_presentation_basis_is_fun@{u} {Λ X:set@{u}} {β:Λ ⇾ X} `{@IdealPresentation@{u} X Xle U Λ β}
  : IsFun (ideal_presentation_basis U β).
Proof. intros x y. exact (is_fun β x y). Qed.

Definition ideal_presentation_basis_fun@{u} {Λ X:set@{u}} (U:𝒫 X) (β:Λ ⇾ X) `{@IdealPresentation@{u} X Xle U Λ β} : _ ⇾ _
  := @func_make _ _ _ (ideal_presentation_basis_is_fun (β:=β) (U:=U)).
Canonical ideal_presentation_basis_fun.
#[global] Hint Extern 2 (IdealBasis (func_op (ideal_presentation_basis_fun _ _))) => simple notypeclasses refine ideal_presentation_basis_correct : typeclass_instances.

Lemma ideal_presentation_basis_order_preserving@{u}
  `{@WeakPoset@{u} Λ Λle} {X:set@{u}} {U:𝒫 X} {β:Λ ⇾ X} `{@IdealPresentation@{u} X Xle U Λ β, !OrderPreserving β}
  : OrderPreserving (ideal_presentation_basis_fun U β).
Proof. apply alt_Build_OrderPreserving. exact (order_preserving β). Qed.
#[global] Hint Extern 2 (OrderPreserving (ideal_presentation_basis_fun _ _)) => simple notypeclasses refine ideal_presentation_basis_order_preserving : typeclass_instances.


(** Pullback *)

Import image_notation.

Lemma preimage_upset `{@OrderPreserving X Y Xle Yle f} `{@UpSet Y Yle U} : UpSet (f* U).
Proof. apply Build_UpSet. intros x y. change (x ≤ y ⊸ f x ∊ U ⊸ f y ∊ U).
  rew (order_preserving f x y). now apply up_closed.
Qed.
#[global] Hint Extern 2 (UpSet (func_op2 preimage _ _)) => simple notypeclasses refine preimage_upset : typeclass_instances.

Lemma preimage_filter `{MeetSemiLatticeOrder Q, MeetSemiLatticeOrder P, g:Q ⇾ P, !MeetSemiLattice_Morphism g}
  `{!Filter F} `{∐ x, g x ∊ F} : Filter (g* F).
Proof. pose proof meet_sl_mor_preserving _ : OrderPreserving g.
  pose proof filter_meet_sub_sl : MeetSubSemiLattice F.
  split; try exact _.
  apply Build_DownDirectedSubset; trivial.
  intros x y. change (g x ∊ F ⊠ g y ∊ F ⊸ ∐ z, g z ∊ F ⊠ z ≤ x ⊠ z ≤ y).
  rew <-(aex_ub _ (x ⊓ y)).
  enough (g x ∊ F ⊠ g y ∊ F ⊸ g (x ⊓ y) ∊ F) by
    (pose proof meet_lb_l x y; pose proof meet_lb_r x y; now simplify).
  rew (preserves_meet g _ _).
  apply sub_meet_closed.
Qed. 
#[global] Hint Extern 2 (Filter (func_op2 preimage _ _)) => simple notypeclasses refine preimage_filter : typeclass_instances.

Definition preimage_downset `{@OrderPreserving X Y Xle Yle f} `{@DownSet Y Yle U} : DownSet (f* U)
  := preimage_upset (X:=X ᵒᵖ) (Y:=Y ᵒᵖ).
#[global] Hint Extern 2 (DownSet (func_op2 preimage _ _)) => simple notypeclasses refine preimage_downset : typeclass_instances.

Definition preimage_ideal `{JoinSemiLatticeOrder Q, JoinSemiLatticeOrder P, g:Q ⇾ P, !JoinSemiLattice_Morphism g}
  `{!Ideal F} `{∐ x, g x ∊ F} : Ideal (g* F)
  := preimage_filter (Q:=Q ᵒᵖ) (P:=P ᵒᵖ).
#[global] Hint Extern 2 (Ideal (func_op2 preimage _ _)) => simple notypeclasses refine preimage_ideal : typeclass_instances.


