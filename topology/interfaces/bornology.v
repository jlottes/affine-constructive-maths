Require Export interfaces.set algebra_notation.
Require Import logic.aprop relations.
Require Import set_lambda.
Require Export interfaces.orders interfaces.subset.

Import image_notation.

(** Bornologies *)

Set Typeclasses Unique Instances.

Definition Bornology X := 𝒫² X.
Existing Class Bornology.
Identity Coercion Bornology_double_subset : Bornology >-> double_subset.
#[global] Hint Mode Bornology + : typeclass_instances.

Unset Typeclasses Unique Instances.

Class BornologicalSpace X {𝒜:Bornology X} : SProp :=
{ bornology_ideal : Ideal 𝒜
; bornology_singleton (x:X) : singleton x ∊ 𝒜
}.
Coercion bornology_ideal : BornologicalSpace >-> Ideal.

SubClass BornologyPresentation@{u} X {𝒜:Bornology@{u} X} {Λ:Type@{u}} (basis:Λ → 𝒫 X)
  := IdealPresentation 𝒜 basis.
SubClass BornologyBasis@{u} `{𝒜:Bornology@{u} X} {Λ:Type@{u}} (β:Λ → 𝒜) := IdealBasis β.
Existing Class BornologyPresentation.
Existing Class BornologyBasis.

SubClass TrivialBornology@{u} {X:set@{u}} (𝒜:Bornology@{u} X)
  := BornologyPresentation X (𝒜:=𝒜) set:(λ _:unit, full_subset X).
Existing Class TrivialBornology.

(** Regularity, mirroring [UniformRegularity] with the ideal's variance: the
    uniformity (a filter) picks an inner witness [V ⊆ U], the bornology (an
    ideal) picks an outer witness [K ⊆ K'], and in both the decision reads
    "in the bigger, or refutably outside the smaller" — the cover form of
    well-inside, distinct from the thickening form used by well-containment. *)
Local Open Scope subset_scope.

Class BornologyRegularity X {𝒜:Bornology X} : SProp :=
  bornology_regularity (K:𝒜) : ∐ (K':𝒜), K ⊆ K' ⊠ powerset_pt K' ⊔ K ᗮ = ⊤.

Local Close Scope subset_scope.

Record RegularBornologicalSpace X {𝒜:Bornology X} : SProp :=
{ #[canonical=no, reversible=no] regular_born_space_born :> BornologicalSpace X
; #[canonical=no, reversible=no] regular_born_space_regular :> BornologyRegularity X
}.
Existing Class RegularBornologicalSpace.

Section product_bornology.
  Universes u.
  Context {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y}.

  Definition tensor_product_bornology_presentation : 𝒜 ⊗ ℬ ⇾ 𝒫 (X ⊗ Y) :=
    set:(λ '(A, B) : 𝒜 ⊗ ℬ, (subset_pt A ⊗ subset_pt B)%subset).
  Definition cartesian_product_bornology_presentation : 𝒜 ⊗ ℬ ⇾ 𝒫 (X × Y) :=
    set:(λ '(A, B) : 𝒜 ⊗ ℬ, (subset_pt A × subset_pt B)%subset).

  Definition TensorProductBornology    (𝒞:Bornology (X ⊗ Y)) := BornologyPresentation (X ⊗ Y) tensor_product_bornology_presentation.
  Definition CartesianProductBornology (𝒞:Bornology (X × Y)) := BornologyPresentation (X × Y) cartesian_product_bornology_presentation.
End product_bornology.
Arguments tensor_product_bornology_presentation    {X Y} 𝒜 ℬ.
Arguments cartesian_product_bornology_presentation {X Y} 𝒜 ℬ.
Arguments TensorProductBornology    {X Y} 𝒜 ℬ 𝒞.
Arguments CartesianProductBornology {X Y} 𝒜 ℬ 𝒞.
Existing Class TensorProductBornology.
Existing Class CartesianProductBornology.

Record Bornological@{u} {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] born_X :> BornologicalSpace X
; born_Y : BornologicalSpace Y
; bornological (A:𝒜) : f⁎ A ∊ ℬ
}.
Existing Class Bornological.
Arguments bornological {_ _ _ _} f {_} A.

Record BornologyReflecting@{u} {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] born_refl_X :> BornologicalSpace X
; born_refl_Y : BornologicalSpace Y
; bornology_reflecting (B:ℬ) : f* B ∊ 𝒜
}.
Existing Class BornologyReflecting.
Arguments bornology_reflecting {_ _ _ _} f {_} B.

Record BornologyInitial@{u} {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] born_init_born :> Bornological f
; #[canonical=no, reversible=no] born_init_refl :> BornologyReflecting f
}.
Existing Class BornologyInitial.

Record BornologyEmbedding@{u} {X Y:set@{u}} {𝒜:Bornology X} {ℬ:Bornology Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] born_emb_init :> BornologyInitial f
; #[canonical=no, reversible=no] born_emb_inj :> Injective f
}.
Existing Class BornologyEmbedding.


#[global] Hint Extern 10 (BornologicalSpace ?Y) =>
  match goal with
  | H : Bornological (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : BornologyInitial (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : BornologyEmbedding (Y:=Y) _ |- _ => exact (born_Y _ H)
  | H : BornologyReflecting (Y:=Y) _ |- _ => exact (born_refl_Y _ H)
  end : typeclass_instances.
