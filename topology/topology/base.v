Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology.
Require Import theory.set orders.orders orders.maps orders.subset theory.lattices orders.lattices.
Require Import orders.subset_images.
Require Import easy rewrite simplify.

Import image_notation.
Local Open Scope topology_scope.


#[global] Hint Extern 2 (apos (_ ⪽ full_subset _)) => simple notypeclasses refine (top_nullary_additivity _) : typeclass_instances.


Import of_course_set_notation.

Lemma Continuous_proper_impl@{u} {X Y:set@{u}} {NX:Neighborhood X} {NY:Neighborhood Y} (f g : X ⇾ Y)
  : f = g → impl (Continuous f, Continuous g).
Proof. intros E [???]; split; try exact _. now rew <-E. Qed.
Canonical Structure Continuous_fun {X Y} {NX:Neighborhood X} {NY:Neighborhood Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@Continuous X Y NX NY) Continuous_proper_impl.

Lemma ContinuouslyReflecting_proper_impl@{u} {X Y:set@{u}} {NX:Neighborhood X} {NY:Neighborhood Y} (f g : X ⇾ Y)
  : f = g → impl (ContinuouslyReflecting f, ContinuouslyReflecting g).
Proof. intros E [???]; split; try exact _. red. now rew <-E. Qed.
Canonical Structure ContinuouslyReflecting_fun {X Y} {NX:Neighborhood X} {NY:Neighborhood Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@ContinuouslyReflecting X Y NX NY) ContinuouslyReflecting_proper_impl.

Lemma ContinuouslyInitial_proper_impl@{u} {X Y:set@{u}} {NX:Neighborhood X} {NY:Neighborhood Y} (f g : X ⇾ Y)
  : f = g → impl (ContinuouslyInitial f, ContinuouslyInitial g).
Proof. intros E [??]; split; now rew <-E. Qed.
Canonical Structure ContinuouslyInitial_fun {X Y} {NX:Neighborhood X} {NY:Neighborhood Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@ContinuouslyInitial X Y NX NY) ContinuouslyInitial_proper_impl.

Lemma ContinuouslyEmbedding_proper_impl@{u} {X Y:set@{u}} {NX:Neighborhood X} {NY:Neighborhood Y} (f g : X ⇾ Y)
  : f = g → impl (ContinuouslyEmbedding f, ContinuouslyEmbedding g).
Proof. intros E ?; split; now rew <-E. Qed.
Canonical Structure ContinuouslyEmbedding_fun {X Y} {NX:Neighborhood X} {NY:Neighborhood Y} : !(X ⇾ Y) ⇾ SProp
  := make_weak_spred (@ContinuouslyEmbedding X Y NX NY) ContinuouslyEmbedding_proper_impl.


Lemma Dense_proper_impl@{u} {A:Type@{u}} {Y:set@{u}} {NY:Neighborhood Y} (f g : A → Y)
  : f = g → impl (Dense f, Dense g).
Proof. intros E [??]; split; try exact _; now rew <-E. Qed.
Canonical Structure Dense_fun {A Y} {NY:Neighborhood Y} : !(A → Y) ⇾ SProp
  := make_weak_spred (@Dense A Y NY) Dense_proper_impl.


Lemma id_emb `{@Topology X XN} : ContinuouslyEmbedding (id_fun X).
Proof. do 3 (split; try exact _).
+ intros x N. now change (x ⪽ N ⊸ x ⪽ N).
+ intros x N. rew <-(aex_ub _ N). change (x ⪽ N ⊸ x ⪽ N ⊠ N ⊆ N). now simplify.
Qed.
#[global] Hint Extern 2 (ContinuouslyEmbedding (id_fun _)) => simple notypeclasses refine id_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (id_fun _)) => simple notypeclasses refine id_emb : typeclass_instances.
#[global] Hint Extern 2 (Continuous (id_fun _)) => simple notypeclasses refine id_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (id_fun _)) => simple notypeclasses refine id_emb : typeclass_instances.


Lemma compose_cont@{u} {X Y Z:set@{u}} `{@Continuous X Y NX NY f} `{@Continuous Y Z NY NZ g} : Continuous (g ∘ f).
Proof. split; try exact _.
  intros x N. change (g (f x) ⪽ N ⊸ x ⪽ f* (g* N)).
  rew (continuity g _ _). exact (continuity f _ _).
Qed.
#[global] Hint Extern 2 (Continuous (_ ∘ _)) => simple notypeclasses refine compose_cont : typeclass_instances.

Lemma compose_cont_reflect@{u} {X Y Z:set@{u}}
  `{@ContinuousReflection X Y NX NY f} `{@ContinuousReflection Y Z NY NZ g}
  : ContinuousReflection (g ∘ f).
Proof. intros x U.
  rew (cont_reflection f x U).
  rew <-aex_adj; intros V.
  rew (cont_reflection g (f x) V).
  rew aex_frob_r, <-aex_adj; intros W.
  rew <-(aex_ub _ W). rew (aprod_assoc _ _ _).
  refine (aprod_proper_aimpl _ _); [ easy |].
  change ((g ∘ f)* W) with (f* (g* W)).
  rew (order_preserving f* (g* W) V).
  now apply transitivity.
Qed.
#[global] Hint Extern 2 (ContinuousReflection (_ ∘ _)) => simple notypeclasses refine compose_cont_reflect : typeclass_instances.

Lemma compose_cont_reflecting@{u} {X Y Z:set@{u}}
  `{@ContinuouslyReflecting X Y NX NY f} `{@ContinuouslyReflecting Y Z NY NZ g}
  : ContinuouslyReflecting (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (ContinuouslyReflecting (_ ∘ _)) => simple notypeclasses refine compose_cont_reflecting : typeclass_instances.

Lemma compose_cont_initial@{u} {X Y Z:set@{u}}
  `{@ContinuouslyInitial X Y NX NY f} `{@ContinuouslyInitial Y Z NY NZ g}
  : ContinuouslyInitial (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (ContinuouslyInitial (_ ∘ _)) => simple notypeclasses refine compose_cont_initial : typeclass_instances.

Lemma compose_cont_embedding@{u} {X Y Z:set@{u}}
  `{@ContinuouslyEmbedding X Y NX NY f} `{@ContinuouslyEmbedding Y Z NY NZ g}
  : ContinuouslyEmbedding (g ∘ f).
Proof. now split. Qed.
#[global] Hint Extern 2 (ContinuouslyEmbedding (_ ∘ _)) => simple notypeclasses refine compose_cont_embedding : typeclass_instances.

Lemma Dense_alt@{u} {A:Type@{u}} `{@Topology@{u} X XN} (f:A → X)
  : Dense f ↔ dense (range f).
Proof. split; [ now intros [??] | intros; now split ]. Qed.

Lemma Hausdorff_T₀ `{@Topology X XN} : Hausdorff X → Separation_T₀ X.
Proof.
  intros HH x y. rew <-(hausdorff x y).
  rew <-all_adj; intros U. rew <-all_adj; intros V.
  rew <-(aex_ub _ x). rew (all_lb _ V).
  rew <-(aprod_adj _ _ _).
  rew <-(top_refl x U), <-(top_refl x V).
  tautological.
Qed.

Lemma hausdorff_iff  `{@Topology X XN} `{!Hausdorff X} (x y : X) :
   (∏ U V, of_course (x ⪽ U ⊠ y ⪽ V) ⊸ ∐ z, z ∊ U ⊠ z ∊ V) ⧟ x = y.
Proof. split.
+ exact (hausdorff _ _).
+ rew <-all_adj; intros U; rew <-all_adj; intros V. rew <-(aex_ub _ y).
  rew [(top_refl x U) | (top_refl y V)].
  change (x = y ⊸ of_course (x ∊ U ⊠ y ∊ V) ⊸ y ∊ U ⊠ y ∊ V).
  rew <-(equal_element U x y). tautological.
Qed.


Lemma cont_initial_embedding `{@ContinuouslyInitial X Y NX NY f}
  `{!Separation_T₀ X} : ContinuouslyEmbedding f.
Proof. split; trivial. intros x y.
  rew <-(separation_T₀ x y).
  enough (∀ x y (U : 𝒫 X), f x = f y ⊸ x ⪽ U ⊸ y ⪽ U) as P.
  + rew <-all_adj; intros U. apply aand_intro; [ apply P |].
    rew (symmetry_iff (=) _ _). apply P.
  + clear x y; intros x y U.
    rew (cont_reflection f x U).
    rew <-(aprod_adj _ _ _), aex_frob_l, <-aex_adj; intros V.
    rew <-(top_isotony y (preimage f V) U).
    rew <-(continuity f y V).
    rew (aprod_adj _ _ _), (is_fun (set:(λ a:Y, a ⪽ V)) (f x) (f y)).
    full_tautological.
Qed.


(** A continuous map into a Hausdorff space identifies points whose
    neighborhoods meet.  Hausdorff is reflected by any point-separating family
    of continuous maps; the two cases used are an injective map
    ([reflects_hausdorff]) and the projections of a cartesian product
    ([cartesian_product_hausdorff]). *)
Lemma cont_hausdorff_meet `{@Continuous X Y NX NY f} `{!Hausdorff Y} (x y : X)
  : (∏ U V, of_course (x ⪽ U ⊠ y ⪽ V) ⊸ ∐ z, z ∊ U ⊠ z ∊ V) ⊸ f x = f y.
Proof. rew <-(hausdorff_iff (f x) (f y)).
  rew <-all_adj; intros U; rew <-all_adj; intros V.
  rew (continuity f _ _). rew (all_lb _ (f* U)), (all_lb _ (f* V)).
  refine ((tautology : ∀ P Q R, (Q ⊸ R) → (P ⊸ Q) ⊸ P ⊸ R) _ _ _ _).
  rew <-aex_adj; intros z. now rew <-(aex_ub _ (f z)).
Qed.
Arguments cont_hausdorff_meet {_ _ _ _} f {_ _} x y.


Lemma reflects_hausdorff `{@Continuous X Y NX NY f} `{!Injective f} `{!Hausdorff Y} : Hausdorff X.
Proof. intros x y. rew (injective_iff f x y). exact (cont_hausdorff_meet f x y). Qed.
Arguments reflects_hausdorff {_ _ _ _} f {_ _ _}.

(** Initial object *)

Section empty.
  Universes u.
  Context {NE:Neighborhood@{u} 𝟎}.
  
  Local Instance empty_topology : @Topology@{u} _ NE.
  Proof. tautological. Qed.

  Lemma from_empty_cont `{@Topology X NX} : @Continuous  _ X NE NX (from_Empty X).
  Proof. split; try exact _. intros []. Qed.
End empty.
#[global] Hint Extern 2 (Topology 𝟎) => simple notypeclasses refine empty_topology : typeclass_instances.
#[global] Hint Extern 2 (Continuous (from_Empty _)) => simple notypeclasses refine from_empty_cont : typeclass_instances.

(** Discrete topologies: neighborhood is membership.  This is the finest
    topology; every map out of a discrete space is continuous. *)

Lemma element_discrete@{u} {X:set@{u}} : Discrete@{u} (X:=X) element.
Proof. now red. Qed.
#[global] Hint Extern 2 (Discrete element) => simple notypeclasses refine element_discrete : typeclass_instances.

Lemma const_nbrhood@{u} `{@Topology@{u} X NX} {x:X} {P:Ω}
  : x ⪽ { y:X | P } ⧟ P.
Proof. split.
+ now rew (top_refl x _).
+ rew <-(top_isotony x ⊤ _).
  rew (aprod_true_l (top_nullary_additivity x)).
  change (P ⊸ ∏ (x:X), 𝐓 ⊸ P). full_tautological.
Qed.

Section discrete.
  Universes u.
  Context {X:set@{u}} {NX} {DX:Discrete@{u} (X:=X) NX}.

  Local Instance discrete_topology : @Topology@{u} _ NX.
  Proof. split; rew is_discrete_nbrhood.
  + tautological.
  + intros. apply subset_apply.
  + tautological.
  + tautological.
  + intros x U. change (x ∊ U ⊸ x ⪽ U). now rew is_discrete_nbrhood.
  Qed.

  (** Every map out of a discrete space is continuous. *)
  Lemma discrete_cont `{@Topology@{u} Y NY} (f:X ⇾ Y) : Continuous f.
  Proof. split; try exact _. intros x N. rew is_discrete_nbrhood.
    change (f x ⪽ N ⊸ f x ∊ N). apply top_refl.
  Qed.
End discrete.

(** Indiscrete topologies: every point neighbors only the full subsets.  This
    is the coarsest topology; every map into an indiscrete space is continuous. *)

Lemma indiscrete_nbrhood_correct@{u} {X:set@{u}} : Indiscrete@{u} (X:=X) indiscrete_nbrhood.
Proof. now red. Qed.
#[global] Hint Extern 2 (Indiscrete indiscrete_nbrhood) => simple notypeclasses refine indiscrete_nbrhood_correct : typeclass_instances.

Section indiscrete.
  Universes u.
  Context {X:set@{u}} {NX} {IX:Indiscrete@{u} (X:=X) NX}.

  Local Instance indiscrete_topology : @Topology@{u} _ NX.
  Proof. split; rew is_indiscrete_nbrhood.
  + tautological.
  + tautological.
  + tautological.
  + tautological.
  + intros x U. change (indiscrete_nbrhood (x, U) ⊸ ∏ z:X, z ⪽ U).
    rew <-all_adj; intros z. rew is_indiscrete_nbrhood. full_tautological.
  Qed.

  (** Every map into an indiscrete space is continuous. *)
  Lemma indiscrete_cont `{@Topology@{u} W NW} (f:W ⇾ X) : Continuous f.
  Proof. split; try exact _. intros x N. rew is_indiscrete_nbrhood.
    rew <-(top_isotony x ⊤ _).
    rew (aprod_true_l (top_nullary_additivity x)).
    change ((∏ y, y ∊ N) ⊸ ∏ w:W, w ∊ ⊤ ⊸ w ∊ f* N).
    rew <-all_adj; intros w; rew (all_lb _ (f w)). now simplify.
  Qed.
End indiscrete.

(** The canonical structures, and the default structure on 𝟏, are topologies. *)
#[global] Hint Extern 2 (Topology 𝟏) => simple notypeclasses refine discrete_topology : typeclass_instances.
#[global] Hint Extern 2 (@Topology _ element) => simple notypeclasses refine discrete_topology : typeclass_instances.
#[global] Hint Extern 2 (@Topology _ indiscrete_nbrhood) => simple notypeclasses refine indiscrete_topology : typeclass_instances.

(** Terminal object *)

Section unit.
  Universes u.
  Context {NU : Neighborhood@{u} 𝟏} {UN:Discrete@{u} NU}.

  Lemma to_unit_cont `{@Topology X NX} : @Continuous  X _ NX NU (to_Unit X).
  Proof. split; try exact _. rew is_discrete_nbrhood. intros x N.
    change (to_Unit X x) with tt.
    change (N tt ⊸ x ⪽ { y:X | N tt }).
    now rew const_nbrhood.
  Qed.
End unit.
#[global] Hint Extern 2 (Continuous (to_Unit _)) => simple notypeclasses refine to_unit_cont : typeclass_instances.



(** Constant maps — in particular global points [𝟏 ⇾ X] — are continuous. *)

Lemma const_cont@{u} `{@Topology@{u} X NX, @Topology@{u} Y NY} (y:Y)
  : Continuous (const (X:=X) y).
Proof. split; try exact _. intros x N.
  change ( y ⪽ N ⊸ x ⪽ { x' : X | y ∊ N } ).
  rew const_nbrhood. exact (top_refl y N).
Qed.
#[global] Hint Extern 2 (Continuous (func_op const _)) => simple notypeclasses refine const_cont : typeclass_instances.


