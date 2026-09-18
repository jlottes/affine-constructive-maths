Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.bornology.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import orders.subset_images.
Require Import theory.lattices theory.subgroups orders.lattices theory.sublattices orders.sublattices.
Require Import bornology.base.
Require Import easy rewrite replc simplify tactics.misc.

Local Abbreviation id := (id_fun _).

Import image_notation.

Definition presented_bornology@{u} {Λ:Type@{u}} {X:set@{u}} (basis:Λ → 𝒫 X) : Bornology X
  := presented_ideal basis.

Lemma presented_bornology_prop@{u} {Λ:Type@{u}} {X:set@{u}} {basis:Λ → 𝒫 X}
  : BornologyPresentation X (𝒜:=presented_bornology basis) basis.
Proof. now unfold BornologyPresentation, presented_bornology. Qed.
#[global] Hint Extern 2 (BornologyPresentation _ (𝒜:=presented_bornology _) _)
  => simple notypeclasses refine presented_bornology_prop : typeclass_instances.

Lemma presented_bornology_elt@{u} {Λ:Type@{u}} {X:set@{u}} {basis:Λ → 𝒫 X} {i}
  : basis i ∊ presented_bornology basis.
Proof. exact (ideal_presentation_basis_elt (H:=presented_bornology_prop)). Qed.
#[global] Hint Extern 2 (apos (?b _ ∊ presented_bornology ?b)) => simple notypeclasses refine presented_bornology_elt : typeclass_instances.

Coercion BornologyPresentationBasis `{@BornologyPresentation X 𝒜 Λ β}
  : @BornologyBasis X 𝒜 Λ (ideal_presentation_basis 𝒜 β)
:= ideal_presentation_basis_correct.

Definition bornology_basis@{u} `{H:@BornologyBasis@{u} X 𝒜 Λ β}
  := @ideal_basis _ _ _ _ H.

Lemma bornology_basis_self `{𝒜:Bornology X} : @BornologyBasis X 𝒜 𝒜 id.
Proof. exact ideal_basis_self. Qed.
#[global] Hint Extern 100 (BornologyBasis _) => notypeclasses refine bornology_basis_self : typeclass_instances.

Section presented_bornological_space.
  Universes u.
  Context {Λ X:set@{u}} {Λle:Le Λ} {β:Λ ⇾ 𝒫 X} {𝒜:Bornology X}.
  Context `{!BornologyPresentation X β, !OrderPreserving β, !UpDirected Λ}.
  Context (cover: ∀ x:X, ∐ i, x ∊ β i).

  Local Instance presented_bornology_ideal : Ideal 𝒜.
  Proof. exact presented_ideal_ideal. Qed.

  Lemma presented_bornological_space : BornologicalSpace X.
  Proof. apply Build_BornologicalSpace. exact _.
    intros x. rew (ideal_presentation 𝒜 β _).
    pose proof cover x as [i Hi]. rew <-(aex_ub _ i).
    now rew (singleton_subset _ _).
  Qed.
End presented_bornological_space.

Section bornology_basis_converse.
  Universes u.
  Context `{H:@BornologyBasis@{u} X 𝒜 Λ β}.

  Lemma bornology_basis_cover `{!BornologicalSpace X} (x:X) : ∐ i, x ∊ β i.
  Proof. pose proof bornology_singleton x as Hsx.
    pose proof ideal_basis β (to_subset (singleton x)) as [i Hi].
    exists i. rew <-(singleton_subset _ _). exact Hi.
  Qed.

  Context `{!BornologicalSpace X}.

  Lemma bornology_basis_inhabited : Inhabited Λ.
  Proof. pose proof (_ : Inhabited 𝒜) as [A _].
    pose proof ideal_basis β A as [i _]. now exists i.
  Qed.

  Lemma bornology_basis_up_directed i₁ i₂ : ∐ i₃, β i₁ ⊆ β i₃ ⊠ β i₂ ⊆ β i₃.
  Proof. pose proof up_directed (β i₁) (β i₂) as [U [H1 H2]].
    pose proof ideal_basis β U as [i₃ P]. exists i₃. now rew <-P.
  Qed.
End bornology_basis_converse.

Lemma born_by_basis@{u}
  `{HA:@BornologyBasis@{u} X 𝒜 Λ₁ α} `{!BornologicalSpace X}
  `{HB:@BornologyBasis@{u} Y ℬ Λ₂ β} `{!BornologicalSpace Y} (f:X ⇾ Y) :
  (∀ i, ∐ j, f⁎ (α i) ⊆ β j) → Bornological f.
Proof. intros P. split; try exact _.
  intros A. pose proof ideal_basis α A as [i Hi]. pose proof (P i) as [j Hj].
  apply (down_closed ℬ (f⁎ A) (β j)).
  + rew <-Hj. apply (order_preserving f⁎). exact Hi.
  + exact (subset_pt_is_el _).
Qed.

Lemma bornology_refl_by_basis@{u}
  `{HA:@BornologyBasis@{u} X 𝒜 Λ₁ α} `{!BornologicalSpace X}
  `{HB:@BornologyBasis@{u} Y ℬ Λ₂ β} `{!BornologicalSpace Y} (f:X ⇾ Y) :
  (∀ j, ∐ i, f* (β j) ⊆ α i) → BornologyReflecting f.
Proof. intros P. split; try exact _.
  intros B. pose proof ideal_basis β B as [j Hj]. pose proof (P j) as [i Hi].
  apply (down_closed 𝒜 (f* B) (α i)).
  + rew <-Hi. apply (order_preserving f*). exact Hj.
  + exact (subset_pt_is_el _).
Qed.

(** Trivial bornology — all subsets bounded *)

Definition trivial_bornology@{u} (X:set@{u}) : Bornology@{u} X
  := presented_bornology set:(λ _:unit, full_subset X).

Lemma trivial_bornology_correct@{u} {X:set@{u}} : TrivialBornology (trivial_bornology X).
Proof. now unfold TrivialBornology, trivial_bornology. Qed.
#[global] Hint Extern 0 (TrivialBornology (trivial_bornology _)) => simple notypeclasses refine trivial_bornology_correct : typeclass_instances.
#[global] Hint Extern 2 (BornologyPresentation _ (𝒜:=trivial_bornology _) _) => simple notypeclasses refine trivial_bornology_correct : typeclass_instances.

Section trivial_bornology.
  Universes u.
  Context `{H:@TrivialBornology@{u} X 𝒜}.

  Lemma trivial_bornology_bounded (A:𝒫 X) : A ∊ 𝒜.
  Proof. rew (ideal_presentation 𝒜 _ A). exists tt. exact (below_top _). Qed.

  Local Instance trivial_bornological_space : BornologicalSpace X.
  Proof. refine (presented_bornological_space _); try exact _.
    intros x. now exists tt.
  Qed.

  Lemma into_trivial_bornological `{@BornologicalSpace Y ℬ} (f:Y ⇾ X) : Bornological f.
  Proof. split; try exact _. intros A. exact (trivial_bornology_bounded _). Qed.

  Lemma from_trivial_bornology_reflecting `{@BornologicalSpace Y ℬ} (f:X ⇾ Y) : BornologyReflecting f.
  Proof. split; try exact _. intros B. exact (trivial_bornology_bounded _). Qed.
End trivial_bornology.

#[global] Hint Extern 2 (@BornologicalSpace _ (trivial_bornology _)) => simple notypeclasses refine trivial_bornological_space : typeclass_instances.
#[global] Hint Extern 2 (@Bornological _ _ _ (trivial_bornology _) _) => simple notypeclasses refine into_trivial_bornological : typeclass_instances.
#[global] Hint Extern 2 (@Bornological _ _ (trivial_bornology _) _ _) => simple notypeclasses refine from_trivial_bornology_reflecting : typeclass_instances.

(** The empty subset is bounded in any bornological space. *)

Lemma bottom_bounded `{@BornologicalSpace X 𝒜} : ⊥ ∊ 𝒜.
Proof. exact ideal_bottom. Qed.

(** Initial and terminal objects *)

#[global] Hint Extern 20 (Bornology 𝟎) => notypeclasses refine (trivial_bornology _) : typeclass_instances.
#[global] Hint Extern 20 (Bornology 𝟏) => notypeclasses refine (trivial_bornology _) : typeclass_instances.

Lemma from_empty_bornological@{u} `{@BornologicalSpace 𝟎 𝒜} `{@BornologicalSpace@{u} Y ℬ}
  : Bornological (from_Empty Y).
Proof. split; try exact _. intros A.
  refine (aimpl_impl_pos (aimpl_impl_pos (down_closed ℬ _ ⊥ ) _) bottom_bounded). exact _.
  intros y. full_tautological. 
Qed.
#[global] Hint Extern 2 (Bornological (from_Empty _)) => simple notypeclasses refine from_empty_bornological : typeclass_instances.

Lemma unit_subset_singleton (A : 𝒫 𝟏) : A ⊆ singleton tt.
Proof. intros y. full_tautological. Qed.

Section unit.
  Universes u.
  Context `{@BornologicalSpace 𝟏 ℬ}.

  Local Instance unit_bornology_trivial : TrivialBornology ℬ.
  Proof. apply Build_IdealPresentation. exact _. intros A. split.
  + rew <-(aex_ub _ tt). rew (aiff_is_true (below_top A)). now simplify.
  + rew <-aex_adj; intros ?.
    pose proof (aimpl_impl_pos (aimpl_impl_pos (down_closed ℬ A (singleton tt)) (unit_subset_singleton A)) (bornology_singleton tt)) as p.
    rew (aiff_is_true p). now simplify.
  Qed.

  Lemma to_unit_bornological `{@BornologicalSpace X 𝒜} : Bornological (to_Unit X).
  Proof. split; try exact _. intros A. exact (trivial_bornology_bounded _). Qed.
End unit.

#[global] Hint Extern 2 (@TrivialBornology 𝟏 _) => simple notypeclasses refine unit_bornology_trivial : typeclass_instances.
#[global] Hint Extern 2 (@BornologyBasis 𝟏 _ _ _) => simple notypeclasses refine unit_bornology_trivial : typeclass_instances.
#[global] Hint Extern 2 (Bornological (to_Unit _)) => simple notypeclasses refine to_unit_bornological : typeclass_instances.

(** Constant maps — in particular global points [𝟏 ⇾ X] — are bornological. *)

Lemma const_bornological@{u} `{@BornologicalSpace@{u} X 𝒜} `{@BornologicalSpace@{u} Y ℬ} {y:Y}
  : Bornological (const (X:=X) y).
Proof. split; try exact _. intros A.
  refine (aimpl_impl_pos (aimpl_impl_pos (down_closed ℬ _ (singleton y)) _) (bornology_singleton y)). exact _.
  intros z. full_tautological.
Qed.
#[global] Hint Extern 2 (Bornological (func_op const _)) => simple notypeclasses refine const_bornological : typeclass_instances.
