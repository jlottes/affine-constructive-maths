Require Export interfaces.set algebra_notation.
Require Import logic.aprop relations.
Require Import set_lambda.
Require Export interfaces.orders interfaces.subset.

Import image_notation.

(** Topology *)

Set Typeclasses Unique Instances.

Declare Scope topology_scope.
Delimit Scope topology_scope with top.
Local Open Scope topology_scope.

Class Neighborhood@{u} (X:set@{u}) : Type@{u} := nbrhood : X ⊗ 𝒫 X ⇾ Ω.
Notation "x ⪽ U" := (func_op nbrhood (x, U)) (at level 70, no associativity) : topology_scope.
Global Hint Mode Neighborhood + : typeclass_instances.

Unset Typeclasses Unique Instances.

Class Topology X {XN:Neighborhood X} : SProp :=
{ top_refl (x:X) U : x ⪽ U ⊸ x ∊ U
; top_isotony (x:X) U V : x ⪽ U ⊠ U ⊆ V ⊸ x ⪽ V
; top_nullary_additivity (x:X) : x ⪽ full_subset X
; top_binary_additivity (x:X) U V : x ⪽ U ⊠ x ⪽ V ⊸ x ⪽ U ⊓ V
; top_trans (x:X) U : x ⪽ U ⊸ x ⪽ { y : X | y ⪽ U }
}.

Class Separation_T₀ X {XN:Neighborhood X} : SProp :=
  separation_T₀ (x y : X) : (∏ U, x ⪽ U ⧟ y ⪽ U) ⊸ x = y .

Class Hausdorff X {XN:Neighborhood X} : SProp :=
  hausdorff (x y : X) : (∏ U V, of_course (x ⪽ U ⊠ y ⪽ V) ⊸ ∐ z, z ∊ U ⊠ z ∊ V) ⊸ x = y .

Definition interior `{XN:Neighborhood X} : 𝒫 X ⇾ 𝒫 X := ap2 nbrhood.
Definition closure `{XN:Neighborhood X} : 𝒫 X ⇾ 𝒫 X := complement ∘ interior ∘ complement.

Definition open `{XN:Neighborhood X} (U: 𝒫 X) : Ω := interior U = U.
Definition closed `{XN:Neighborhood X} (U: 𝒫 X) : Ω := closure U = U.
Definition dense `{XN:Neighborhood X} := { U : 𝒫 X | closure U = ⊤ }.

Definition NeighborhoodBasis@{u} `{XN:Neighborhood@{u} X} {Λ:Type@{u}} (β:Λ → 𝒫 X) : SProp :=
  ∀ x N, x ⪽ N ⧟ ∐ i, x ∊ β i ⊠ β i ⊆ N.
Existing Class NeighborhoodBasis.

Record Continuous@{u} {X Y:set@{u}} {XN:Neighborhood X} {YN:Neighborhood Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] cont_top_X :> Topology X
; cont_top_Y : Topology Y
; continuity x N : f x ⪽ N ⊸ x ⪽ f* N
}.
Existing Class Continuous.
Arguments continuity {X Y _ _} f {_} x N.

Class ContinuousReflection@{u} {X Y:set@{u}} {XN:Neighborhood X} {YN:Neighborhood Y} (f:X ⇾ Y) : SProp :=
  cont_reflection x U : x ⪽ U ⊸ ∐ V, f x ⪽ V ⊠ f* V ⊆ U.
Arguments cont_reflection {X Y _ _} f {_} x U.

Record ContinuouslyReflecting@{u} {X Y:set@{u}} {XN:Neighborhood X} {YN:Neighborhood Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] cont_reflecting_X :> Topology X
; cont_reflecting_Y : Topology Y
; #[canonical=no, reversible=no] cont_reflecting :> ContinuousReflection f
}.
Existing Class ContinuouslyReflecting.

Record ContinuouslyInitial@{u} {X Y:set@{u}} {XN:Neighborhood X} {YN:Neighborhood Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] cont_initial_cont :> Continuous f
; #[canonical=no, reversible=no] cont_initial_refl :> ContinuouslyReflecting f
}.
Existing Class ContinuouslyInitial.

Record ContinuouslyEmbedding@{u} {X Y:set@{u}} {XN:Neighborhood X} {YN:Neighborhood Y} (f:X ⇾ Y) : SProp :=
{ #[canonical=no, reversible=no] cont_embedding_initial :> ContinuouslyInitial f
; #[canonical=no, reversible=no] cont_embedding_inj :> Injective f
}.
Existing Class ContinuouslyEmbedding.

Class Dense@{u} {A:Type@{u}} {Y:set@{u}} {YN:Neighborhood Y} (f:A → Y) : SProp :=
{ #[canonical=no, reversible=no] Dense_Y :> Topology Y
; dense_range : dense (range f)
}.

(** Discrete and indiscrete topologies.  A neighborhood structure is discrete
    when neighborhood is membership (the finest topology, by [top_refl]), and
    indiscrete when every point neighbors only the full subsets (the coarsest). *)
Class Discrete@{u} {X:set@{u}} (XN:Neighborhood@{u} X) : SProp
  := is_discrete_nbrhood : @nbrhood _ XN = element.

Definition indiscrete_nbrhood {X:set} : X ⊗ 𝒫 X ⇾ Ω
  := set:(λ '(x, U) : X ⊗ 𝒫 X, ∏ y, y ∊ U).

Class Indiscrete@{u} {X:set@{u}} (XN:Neighborhood@{u} X) : SProp
  := is_indiscrete_nbrhood : @nbrhood _ XN = indiscrete_nbrhood.

(** Initial/Terminal objects: the default neighborhood structure on 𝟏 is discrete. *)
#[global] Hint Extern 20 (Neighborhood 𝟏) => refine element : typeclass_instances.

(** Product topology *)
Section product_neighborhoods.
  Universes u.
  Context {X Y:set@{u}} {NX:Neighborhood@{u} X} {NY:Neighborhood@{u} Y}.

  Definition tensor_product_neighborhood_basis
    := set:(λ '(N, M):𝒫 X ⊗ 𝒫 Y, { '(x, y) : X ⊗ Y | x ⪽ N ⊠ y ⪽ M}).

  SubClass TensorProductNeighborhood    (XYN:Neighborhood@{u} (X ⊗ Y)) :=
    NeighborhoodBasis tensor_product_neighborhood_basis.

  Record CartesianProductTopology (XYN:Neighborhood@{u} (X × Y)) : SProp :=
  { prod_proj1_cont :> Continuous (prod_proj1 X Y)
  ; prod_proj2_cont :> Continuous (prod_proj2 X Y)
  ; cart_prod_initial `{@Topology@{u} Z NZ} (f:Z ⇾ X × Y)
     : Continuous (prod_proj1 _ _ ∘ f) → Continuous (prod_proj2 _ _ ∘ f) →
       Continuous f
  }.
End product_neighborhoods.
Arguments tensor_product_neighborhood_basis    {X Y} NX NY.
Arguments TensorProductNeighborhood    {X Y} NX NY XYN.
Existing Class TensorProductNeighborhood.
Existing Class CartesianProductTopology.

(** Continuity of the projections out of a cartesian product. *)
#[global] Hint Extern 2 (Continuous (prod_proj1 _ _)) => simple notypeclasses refine (prod_proj1_cont _ _) : typeclass_instances.
#[global] Hint Extern 2 (Continuous (prod_proj2 _ _)) => simple notypeclasses refine (prod_proj2_cont _ _) : typeclass_instances.

(** [CartesianProductTopology] coerces to [Topology (X × Y)] (the product
    itself) via [prod_proj1_cont]'s domain; the component topologies [Topology X]
    and [Topology Y] are the codomains of the two projections and are recovered
    here. *)
#[global] Hint Extern 10 (Topology ?Y) =>
  match goal with
  | H : Continuous (Y:=Y) _ |- _ => exact (cont_top_Y _ H)
  | H : ContinuouslyInitial (Y:=Y) _ |- _ => exact (cont_top_Y _ H)
  | H : ContinuouslyEmbedding (Y:=Y) _ |- _ => exact (cont_top_Y _ H)
  | H : ContinuouslyReflecting (Y:=Y) _ |- _ => exact (cont_reflecting_Y _ H)
  | H : CartesianProductTopology (X:=Y) _ |- _ => exact (cont_top_Y _ (prod_proj1_cont _ H))
  | H : CartesianProductTopology (Y:=Y) _ |- _ => exact (cont_top_Y _ (prod_proj2_cont _ H))
  end : typeclass_instances.
