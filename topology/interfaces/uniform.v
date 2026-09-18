Require Export topology.interfaces.topology.
Require Import logic.aprop relations orders.subset.
Require Import rewrite easy.
Require Import set_lambda.

Import image_notation.
Import tensor_map_notation.

Local Open Scope topology_scope.

(** Uniform spaces *)

Set Typeclasses Unique Instances.

Definition Uniformity X := 𝒫² (X ⊗ X).
Existing Class Uniformity.
Identity Coercion Uniformity_double_subset : Uniformity >-> double_subset.
#[global] Hint Mode Uniformity + : typeclass_instances.

Unset Typeclasses Unique Instances.

Definition near `{Φ:Uniformity X} : Φ ⇾ X ⇾ 𝒫 X := set:(λ (U:Φ) x, {y:X | (x, y) ∊ U}).
Definition thicken `{Φ:Uniformity X}
  := set:(λ '(U, A) : Φ ⊗ 𝒫 X, { y:X | ∐ x, x ∊ A ⊠ (x, y) ∊ U}).

Module thicken_notation.
  Notation "U .[ A ]" := (func_op thicken (U, A))
    (at level 1, A at level 200, format "U .[ A ]") : topology_scope.
End thicken_notation.

(** The "uniformly below" relation of pointfree topology (Picado-Pultr):
    [K ◁ S] when [S] is a uniform neighborhood of [K].  This is the uniform
    leg of the WCUnif well-containment relation [⋐]; the bornological leg
    [K ∊ 𝒜] is conjoined where a bornology is present. *)
Section uniformly_below.
  Import thicken_notation.
  Definition uniformly_below `{Φ:Uniformity X}
    := { '(K, S) : 𝒫 X ⊗ 𝒫 X | ∐ U:Φ, U.[K] ⊆ S }.
End uniformly_below.
Notation "K ◁ S" := (func_op uniformly_below (K, S)) (at level 70, no associativity) : topology_scope.

Local Open Scope grp_scope.
Class PreUniformSpace X {Φ:Uniformity X} : SProp :=
{ uniform_refl U : U ∊ Φ ⊸ id_rel X ⊆ U
; uniform_sym U : U ∊ Φ ⊸ U⁻¹ ∊ Φ
; uniform_split (U:Φ) : ∐ (V:Φ), V ⋄ V ⊆ U
}.

Record UniformSpace X {Φ:Uniformity X} : SProp :=
{ #[canonical=no, reversible=no] uniform_filter :> Filter Φ
; #[canonical=no, reversible=no] uniform_pre :> PreUniformSpace X
}.
Existing Class UniformSpace.

Class StrongUniformSplit X {Φ:Uniformity X} : SProp :=
  strong_uniform_split (U:Φ) : ∐ (V:Φ), ∏ x y z, near V x y ∧ near V y z ⊸ near U x z .
Record StrongUniformSpace X {Φ:Uniformity X} : SProp :=
{ #[canonical=no, reversible=no] strong_uniform_space_uniform :> UniformSpace X
; #[canonical=no, reversible=no] strong_uniform_space_split :> StrongUniformSplit X
}.
Existing Class StrongUniformSpace.

Record SeparatedUniformSpace X {Φ:Uniformity X} : SProp :=
{ #[canonical=no, reversible=no] separated_uniform_space_uniform :> UniformSpace X
; uniform_separated x y : (∏ (U:Φ), near U x y) ⊸ x = y
}.
Existing Class SeparatedUniformSpace.
Arguments uniform_separated {X _ _} x y.

Record SeparatedStrongUniformSpace X {Φ:Uniformity X} : SProp :=
{ #[canonical=no, reversible=no] separated_strong_ufm_space_separated :> SeparatedUniformSpace X
; #[canonical=no, reversible=no] separated_strong_ufm_space_strong :> StrongUniformSpace X
}.
Existing Class SeparatedStrongUniformSpace.

Local Open Scope subset_scope.

Class UniformRegularity X {Φ:Uniformity X} : SProp :=
  uniform_regularity (U:Φ) : ∐ (V:Φ), V ⊆ U ⊠ powerset_pt U ⊔ V ᗮ = ⊤.

Local Close Scope subset_scope.

Record RegularUniformSpace X {Φ:Uniformity X} : SProp :=
{ #[canonical=no, reversible=no] regular_uniform_space_uniform :> UniformSpace X
; #[canonical=no, reversible=no] regular_uniform_space_regular :> UniformRegularity X
}.
Existing Class RegularUniformSpace.

Record SeparatedRegularUniformSpace X {Φ:Uniformity X} : SProp :=
{ #[canonical=no, reversible=no] sep_regular_uniform_space_reg :> RegularUniformSpace X
; #[canonical=no, reversible=no] sep_regular_uniform_space_sep :> SeparatedUniformSpace X
}.
Existing Class SeparatedRegularUniformSpace.


Coercion UniformNeighborhood `{Φ:Uniformity X} : Neighborhood X :=
  set:(λ '(x, N), ∐ U, ∏ (y: X), @near X Φ U x y ⊸ y ∊ N).
Global Hint Extern 40 (Neighborhood ?X) => simple notypeclasses refine UniformNeighborhood : typeclass_instances.

SubClass UniformityPresentation@{u} X {Φ:Uniformity@{u} X} {Λ:Type@{u}} (β:Λ → 𝒫 (X ⊗ X))
  := FilterPresentation Φ β.
SubClass UniformityBasis@{u} `{Φ:Uniformity@{u} X} {Λ:Type@{u}} (β:Λ → Φ) := FilterBasis β.
Existing Class UniformityPresentation.
Existing Class UniformityBasis.

Class UniformContinuity@{u}  {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X → Y) : SProp :=
  ufm_continuity (V:Ψ) : ∐ (U:Φ), ∏ x y, near U x y ⊸ near V (f x) (f y).
Arguments ufm_continuity {X Y _ _} f {_} V.

Record UniformlyContinuous@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] ufm_cont_X :> UniformSpace X
; ufm_cont_Y : UniformSpace Y
; #[canonical=no, reversible=no] ufm_cont :> UniformContinuity f
}.
Existing Class UniformlyContinuous.

Class UniformReflection@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X → Y) : SProp :=
  ufm_reflection (U:Φ) : ∐ (V:Ψ), ∏ x y, near V (f x) (f y) ⊸ near U x y.
Arguments ufm_reflection {X Y _ _} f {_} U.

Record UniformlyReflecting@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] ufm_reflecting_X :> UniformSpace X
; ufm_reflecting_Y : UniformSpace Y
; #[canonical=no, reversible=no] ufm_reflecting :> UniformReflection f
}.
Existing Class UniformlyReflecting.

Record UniformlyInitial@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] ufm_initial_cont :> UniformlyContinuous f
; #[canonical=no, reversible=no] ufm_initial_refl :> UniformlyReflecting f
}.
Existing Class UniformlyInitial.

Record UniformlyEmbedding@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] ufm_embedding_initial :> UniformlyInitial f
; #[canonical=no, reversible=no] ufm_embedding_inj :> Injective f
}.
Existing Class UniformlyEmbedding.


Section product_uniformity.
  Universes u.
  Context {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y}.

  Definition tensor_product_uniform_presentation :=
    set:(λ '(U, V) : Φ ⊗ Ψ,
           { '((x₁, y₁), (x₂, y₂)) : (X ⊗ Y) ⊗ (X ⊗ Y) | (x₁, x₂) ∊ powerset_pt U ⊠ (y₁, y₂) ∊ powerset_pt V : Ω }).
  Definition cartesian_product_uniform_presentation :=
    set:(λ '(U, V) : Φ ⊗ Ψ,
           { '((x₁, y₁), (x₂, y₂)) : (X × Y) ⊗ (X × Y) | (x₁, x₂) ∊ powerset_pt U ∧ (y₁, y₂) ∊ powerset_pt V : Ω }).

  Definition TensorProductUniformity    (Ξ:Uniformity (X ⊗ Y)) := UniformityPresentation (X ⊗ Y) tensor_product_uniform_presentation.
  Definition CartesianProductUniformity (Ξ:Uniformity (X × Y)) := UniformityPresentation (X × Y) cartesian_product_uniform_presentation.
End product_uniformity.
Arguments TensorProductUniformity    {X Y} Φ Ψ Ξ.
Arguments CartesianProductUniformity {X Y} Φ Ψ Ξ.
Existing Class TensorProductUniformity.
Existing Class CartesianProductUniformity.

(** Discrete and indiscrete uniformities.  The discrete uniformity is the
    finest: every relation containing the identity is an entourage.  The
    indiscrete uniformity is the coarsest: only the full relation is. *)
Section discrete_uniformity.
  Universes u.
  Context {X:set@{u}}.

  SubClass DiscreteUniformity   (Φ:Uniformity@{u} X) := UniformityPresentation X set:(λ _:unit, id_rel X).
  SubClass IndiscreteUniformity (Φ:Uniformity@{u} X) := UniformityPresentation X set:(λ _:unit, full_subset (X ⊗ X)).
End discrete_uniformity.
Arguments DiscreteUniformity   {X} Φ.
Arguments IndiscreteUniformity {X} Φ.
Existing Class DiscreteUniformity.
Existing Class IndiscreteUniformity.


Record CauchyFilter `{Φ:Uniformity X} (F:𝒫² X) : SProp :=
{ #[canonical=no, reversible=no] cauchy_filter_filter :> Filter F
; cauchy_proper : ∅ ∊̸ F
; cauchy (U:Φ) : ∐ A : F, (∏ x y, x ∊ A ⊠ y ∊ A ⊸ near U x y)
}.
Existing Class CauchyFilter.
Arguments cauchy {_ _} F {_} U.
Arguments cauchy_proper {_ _} F {_}.

Class CompletionReflect@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} (ι:X ⇾ Y)
  := completion_reflect_initial `{@UniformlyInitial X Z Φ Ξ f} `{!Dense f} : Z ⇾ Y.
Arguments completion_reflect_initial {X Y Φ Ψ} ι {_ Z Ξ} f {_ _}.

Definition CompleteInverse@{u} (X:set@{u}) {Φ:Uniformity X} := CompletionReflect (id_fun X).
Existing Class CompleteInverse.
Identity Coercion CompleteInverse_Reflect : CompleteInverse >-> CompletionReflect.
#[global] Hint Extern 4 (@CompletionReflect ?X _ ?Φ _ (id_fun _)) => change (@CompleteInverse X Φ) : typeclass_instances.

Class Completion@{u} `{@CompletionReflect@{u} X Y Φ Ψ ι} : SProp :=
{ completion_separated : SeparatedUniformSpace Y
; completion_initial : UniformlyInitial ι
; completion_dense   : Dense ι
; completion_reflect_initial_ufm_cont `{@UniformlyInitial X Z Φ Ξ f} `{!Dense f}
  : UniformlyContinuous (completion_reflect_initial ι f)
; completion_reflect_initial_spec `{@UniformlyInitial X Z Φ Ξ f} `{!Dense f}
    : completion_reflect_initial ι f ∘ f = ι
}.
Arguments Completion {X Y Φ Ψ} ι {_}.
Arguments completion_reflect_initial_spec {X Y Φ Ψ} ι {_ _} {Z Ξ} f {_ _}.
Coercion completion_separated : Completion >-> SeparatedUniformSpace.
Coercion completion_initial : Completion >-> UniformlyInitial.
Coercion completion_dense : Completion >-> Dense.
#[global] Hint Extern 2 (UniformlyContinuous (completion_reflect_initial _ _)) => simple notypeclasses refine completion_reflect_initial_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (completion_reflect_initial _ _)) => simple notypeclasses refine completion_reflect_initial_ufm_cont : typeclass_instances.

Definition CompleteUniformSpace `{Ci:@CompleteInverse X Φ} := Completion (id_fun X).
Existing Class CompleteUniformSpace.
Arguments CompleteUniformSpace X {Φ Ci}.


#[global] Hint Extern 10 (Topology ?Y) =>
  match goal with
  | H : UniformlyContinuous (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UniformlyInitial (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UniformlyEmbedding (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UniformlyReflecting (Y:=Y) _ |- _ => exact (ufm_reflecting_Y _ H)
  | H : Completion (X:=Y) ?f |- _ => exact (ufm_cont_X f H)
  end : typeclass_instances.

#[global] Hint Extern 10 (UniformSpace ?Y) =>
  match goal with
  | H : UniformlyContinuous (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UniformlyInitial (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UniformlyEmbedding (Y:=Y) _ |- _ => exact (ufm_cont_Y _ H)
  | H : UniformlyReflecting (Y:=Y) _ |- _ => exact (ufm_reflecting_Y _ H)
  | H : Completion (X:=Y) ?f |- _ => exact (ufm_cont_X f H)
  end : typeclass_instances.
