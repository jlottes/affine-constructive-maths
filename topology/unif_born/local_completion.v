(** Instantiating the completion kit at (𝐖𝐂𝐔𝐧𝐢𝐟, 𝒯): the WCUnif counterpart
    of uniform/completion2.v, delegating to reflection_pair/completion.v.

    The bridge direction is [LocalCompletion] ⟹ [PairCompletion] (with hints,
    so the abstract theorems apply whenever a concrete local completion is in
    context); the converse is left to direct invocation.  Unlike at 𝐔𝐧𝐢𝐟, the
    data-class bridge is not a definitional identity: the 𝐖𝐂𝐔𝐧𝐢𝐟 fiber packs
    (Uniformity ∗ Bornology), so the two directions are pack/unpack wrappers —
    definitionally mutually inverse by tprod eta. *)
Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform interfaces.bornology interfaces.unif_born.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import topology.topology topology.uniform.base uniform.basis uniform.product topology.uniform.cauchy_completion.
Require Import topology.maps.
Require Import bornology.base.
Require Import unif_born.base unif_born.local_maps unif_born.localization.
Require Import unif_born.trapped_cauchy unif_born.trapped_wc.
Require Import interfaces.reflection_pair reflection_pair.base topology.reflection_pair.completion.
Require Import easy rewrite.

Local Open Scope fun_inv_scope.

Local Abbreviation id := (id_fun _).
Local Abbreviation ℒ := localization.
Local Abbreviation ε := from_localization.
Local Abbreviation η := to_localization.
Local Abbreviation κ := to_cauchy.
Local Abbreviation 𝒞 := cauchy_filter_set.
Local Abbreviation 𝒞₁ := cauchy_map.

Local Abbreviation 𝒯 := trapped_cauchy_filter_set.
Local Abbreviation τ := to_trapped.
Local Abbreviation ρ := from_trapped.
Local Abbreviation 𝒯₁ := wc_trapped_map.
Local Abbreviation R := wc_trapped_reflect.

#[local] Hint Extern 8 (Uniformity ?X) => match goal with
| H : Fib 𝐔𝐧𝐢𝐟 X |- _ => exact H
| H : Fib 𝐖𝐂𝐔𝐧𝐢𝐟 X |- _ => exact (proj1 H)
end : typeclass_instances.

#[local] Hint Extern 8 (Bornology ?X) => match goal with
| H : Fib 𝐖𝐂𝐔𝐧𝐢𝐟 X |- _ => exact (proj2 H)
end : typeclass_instances.

(** * The bridge: concrete completions instantiate the pair-level API. *)

Definition wcunif_pair_completion_reflect `{H:@LocalCompletionReflect X Y Φ Ψ 𝒜 ℬ ι} : PairCompletionReflect 𝐖𝐂𝐔𝐧𝐢𝐟 ι
  := λ Z '(Ξ, 𝒵), @local_completion_reflect_initial X Y Φ Ψ 𝒜 ℬ ι _ Z Ξ 𝒵.
#[global] Hint Extern 0 (@PairCompletionReflect 𝐖𝐂𝐔𝐧𝐢𝐟 _ _ _ ?X ?Y (?Φ, ?𝒜) (?Ψ, ?ℬ) ?ι)
  => simple notypeclasses refine (@wcunif_pair_completion_reflect X Y Φ Ψ 𝒜 ℬ ι _) : typeclass_instances.

Definition wcunif_pair_complete_inverse `{H:@LocalCompleteInverse X Φ 𝒜} : PairCompleteInverse 𝐖𝐂𝐔𝐧𝐢𝐟 X
  := wcunif_pair_completion_reflect (H:=H).
#[global] Hint Extern 0 (@PairCompleteInverse 𝐖𝐂𝐔𝐧𝐢𝐟 _ _ _ ?X (?Φ, ?𝒜))
  => simple notypeclasses refine (@wcunif_pair_complete_inverse X Φ 𝒜 _) : typeclass_instances.

Lemma wcunif_pair_completion `{H:@LocalCompletion X Y Φ Ψ 𝒜 ℬ ι Ci} : PairCompletion 𝐖𝐂𝐔𝐧𝐢𝐟 ι.
Proof. split; try exact _.
+ intros Z [Ξ 𝒵] f ??. apply H.
+ intros Z [Ξ 𝒵] f ??. exact (local_completion_reflect_initial_spec ι f).
Qed.

Lemma wcunif_complete_obj `{H:@LocallyComplete X Φ 𝒜 Ci} : CompleteObj 𝐖𝐂𝐔𝐧𝐢𝐟 X.
Proof. exact wcunif_pair_completion. Qed.

#[global] Hint Extern 2 (PairCompletion 𝐖𝐂𝐔𝐧𝐢𝐟 _) => simple notypeclasses refine wcunif_pair_completion : typeclass_instances.
#[global] Hint Extern 2 (CompleteObj 𝐖𝐂𝐔𝐧𝐢𝐟 _) => simple notypeclasses refine wcunif_complete_obj : typeclass_instances.

(** The converse bridge, for direct invocation. *)
Definition wcunif_completion_reflect@{u} {X Y:set@{u}} {Φ:Uniformity X} {Ψ:Uniformity Y} {𝒜:Bornology X} {ℬ:Bornology Y}
  {ι:X ⇾ Y} (H:PairCompletionReflect@{u} 𝐖𝐂𝐔𝐧𝐢𝐟 ι) : LocalCompletionReflect ι
  := λ Z Ξ 𝒵, @pair_completion_reflect_initial 𝐖𝐂𝐔𝐧𝐢𝐟 _ _ _ X Y _ _ ι _ Z _.

Definition wcunif_complete_inverse@{u} {X:set@{u}} {Φ:Uniformity X} {𝒜:Bornology X}
  (H:PairCompleteInverse@{u} 𝐖𝐂𝐔𝐧𝐢𝐟 X) : LocalCompleteInverse X
  := wcunif_completion_reflect H.

Lemma wcunif_completion `{Ci:@LocalCompletionReflect X Y Φ Ψ 𝒜 ℬ ι} : PairCompletion 𝐖𝐂𝐔𝐧𝐢𝐟 ι → LocalCompletion ι.
Proof. intros H. split.
+ pose proof (pair_completion_obj_Y 𝐖𝐂𝐔𝐧𝐢𝐟 (H:=H)) as HY. change (WCUnifSpace Y) in HY.
  apply uniform_T₀_separated, Hausdorff_T₀. exact H.
+ exact (pair_completion_initial 𝐖𝐂𝐔𝐧𝐢𝐟 (PairCompletion:=H)).
+ exact (pair_completion_dense 𝐖𝐂𝐔𝐧𝐢𝐟 (PairCompletion:=H)).
+ intros Z Ξ 𝒵 f ??. exact (pair_completion_reflect_initial_mor 𝐖𝐂𝐔𝐧𝐢𝐟 (PairCompletion:=H) f).
+ intros Z Ξ 𝒵 f ??. exact (pair_completion_reflect_initial_spec 𝐖𝐂𝐔𝐧𝐢𝐟 ι (PairCompletion:=H) f).
Qed.

Lemma wcunif_complete `{Ci:@LocalCompleteInverse X Φ 𝒜} : CompleteObj 𝐖𝐂𝐔𝐧𝐢𝐟 X → LocallyComplete X.
Proof. exact wcunif_completion. Qed.

(** * The canonical completion: (𝒯, τ, wc_trapped_map, wc_trapped_reflect). *)

Definition wcunif_canonical_completor@{u} : CanonicalCompletor@{u} 𝐖𝐂𝐔𝐧𝐢𝐟 (U:=λ (X:set@{u}) '(Φ, 𝒜), @UniformNeighborhood@{u} X Φ).
Proof. unshelve esplit.
+ intros X [Φ 𝒜] HX. exact (𝒯 X).
+ intros X [Φ 𝒜] HX. now split.
+ intros X [Φ 𝒜] HX. exact (τ X).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f Hf. exact (𝒯₁ f).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX f Hf1 Hf2. exact (R f).
Defined.
#[global] Hint Extern 2 (CanonicalCompletor 𝐖𝐂𝐔𝐧𝐢𝐟) => exact wcunif_canonical_completor : typeclass_instances.

Lemma wcunif_canonical_completion : CanonicalCompletion 𝐖𝐂𝐔𝐧𝐢𝐟.
Proof. split.
+ intros X [Φ 𝒜] HX. now change (Hausdorff (𝒯 X)).
+ intros X [Φ 𝒜] HX. now change (WCUnifInitial (τ X)).
+ intros X [Φ 𝒜] HX. now change (Dense (τ X)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f Hf. now change (WCUnifMorphism (𝒯₁ f)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f Hf. exact (wc_trapped_map_unit f).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f HR HD. now change (WCUnifMorphism (R f)).
+ intros X Y [Φ 𝒜] [Ψ ℬ] HX HY f HD HR. exact (wc_trapped_reflect_spec f).
Qed.
#[global] Hint Extern 2 (CanonicalCompletion 𝐖𝐂𝐔𝐧𝐢𝐟) => simple notypeclasses refine wcunif_canonical_completion : typeclass_instances.

(** (K3), by the dense-initial descent law. *)
Lemma wcunif_canonical_map_initial : CanonicalCompletionMapInitial 𝐖𝐂𝐔𝐧𝐢𝐟.
Proof. apply (dense_initial_descent_map_ini 𝐖𝐂𝐔𝐧𝐢𝐟).
  intros S T V [??] [??] [??] f g HD Hf Hg HR.
  change (WCUnifMorphism g) in Hg.
  enough (LocallyUnifBornInitial g) by (repeat (split; try exact _)).
  exact (dense_locally_initial f g).
Qed.
#[global] Hint Extern 2 (CanonicalCompletionMapInitial 𝐖𝐂𝐔𝐧𝐢𝐟) => simple notypeclasses refine wcunif_canonical_map_initial : typeclass_instances.


(** * The theory of uniform/completion.v, by delegation. *)

Section completion_reflect_initial.
  Universes u.
  Context `{@LocalCompletion@{u} X Y Φ Ψ 𝒜 ℬ ι HC, @WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}.

  Local Abbreviation g := (local_completion_reflect_initial ι f).

  Lemma local_completion_reflect_initial_dense : Dense g.
  Proof. now pose proof (pair_completion_reflect_initial_dense 𝐖𝐂𝐔𝐧𝐢𝐟 (ι:=ι) (f:=f)). Qed.

  Lemma local_completion_reflect_initial_initial : WCUnifInitial g.
  Proof. now pose proof (pair_completion_reflect_initial_initial 𝐖𝐂𝐔𝐧𝐢𝐟 (ι:=ι) f). Qed.
End completion_reflect_initial.
#[global] Hint Extern 2 (Dense (func_op (local_completion_reflect_initial _ _)))  => simple notypeclasses refine local_completion_reflect_initial_dense : typeclass_instances.
#[global] Hint Extern 2 (WCUnifInitial              (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial           (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting        (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting     (local_completion_reflect_initial _ _))  => simple notypeclasses refine local_completion_reflect_initial_initial : typeclass_instances.


(** Completions are complete. *)
Coercion local_completion_inverse@{u} {X Y:set@{u}} `{H:@LocalCompletion@{u} X Y Φ Ψ 𝒜 ℬ ι U}
  : LocalCompleteInverse@{u} Y
  := wcunif_complete_inverse (pair_completion_inverse 𝐖𝐂𝐔𝐧𝐢𝐟 (ι:=ι)).
#[global] Hint Extern 4 (LocalCompleteInverse ?Y) =>
  match goal with H : LocalCompletion (Y:=Y) _ |- _ => exact H end : typeclass_instances.

Coercion local_completion_complete@{u} {X Y:set@{u}} `{H:@LocalCompletion@{u} X Y Φ Ψ 𝒜 ℬ ι U}
  : LocallyComplete@{u} Y.
Proof. apply wcunif_completion. exact (pair_completion_complete 𝐖𝐂𝐔𝐧𝐢𝐟 (ι:=ι)). Qed.

Definition trapped_complete_inverse@{u} `{@WCUnifSpace@{u} X Φ 𝒜} : LocalCompleteInverse@{u} (𝒯 X)
  := local_completion_inverse (ι:=τ _).
#[global] Hint Extern 2 (LocalCompleteInverse (𝒯 ?X)) => simple notypeclasses refine (trapped_complete_inverse (X:=X)) : typeclass_instances.
Lemma trapped_complete@{u} `{@WCUnifSpace@{u} X Φ 𝒜} : LocallyComplete@{u} (𝒯 X).
Proof. exact local_completion_complete. Qed.
#[global] Hint Extern 2 (LocallyComplete (𝒯 ?X)) => simple notypeclasses refine (trapped_complete (X:=X)) : typeclass_instances.

(** The UP extends to any WCUnifReflecting Dense map. *)
Section completion_reflect.
  Universes u.
  Context `{@LocalCompletion@{u} X Y Φ Ψ 𝒜 ℬ ι HC, @WCUnifReflecting@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}.

  Definition local_completion_reflect : Z ⇾ Y := pair_completion_reflect 𝐖𝐂𝐔𝐧𝐢𝐟 ι f.

  Local Instance local_completion_reflect_mor : WCUnifMorphism local_completion_reflect.
  Proof. exact (pair_completion_reflect_mor 𝐖𝐂𝐔𝐧𝐢𝐟 ι f). Qed.

  Lemma local_completion_reflect_spec : local_completion_reflect ∘ f = ι.
  Proof. exact (pair_completion_reflect_spec 𝐖𝐂𝐔𝐧𝐢𝐟 (ι:=ι) f). Qed.

  Lemma local_completion_reflect_dense : Dense local_completion_reflect.
  Proof. exact (pair_completion_reflect_dense 𝐖𝐂𝐔𝐧𝐢𝐟 ι f). Qed.
End completion_reflect.
Arguments local_completion_reflect {_ _ _ _ _ _} ι {_ _ _ _ _} f {_ _}.
Arguments local_completion_reflect_spec {_ _ _ _ _ _} ι {_ _ _ _ _} f {_ _}.
#[global] Hint Extern 2 (WCUnifMorphism             (local_completion_reflect _ _)) => simple notypeclasses refine local_completion_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (local_completion_reflect _ _)) => simple notypeclasses refine local_completion_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (local_completion_reflect _ _)) => simple notypeclasses refine local_completion_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (local_completion_reflect _ _)) => simple notypeclasses refine local_completion_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (local_completion_reflect _ _)) => simple notypeclasses refine local_completion_reflect_mor : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (local_completion_reflect _ _))) => simple notypeclasses refine local_completion_reflect_dense : typeclass_instances.

Lemma local_completion_reflect_equal@{u} `{@LocalCompletion@{u} X Y Φ Ψ 𝒜 ℬ ι HC, @WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}
  : local_completion_reflect ι f = local_completion_reflect_initial ι f.
Proof. exact (pair_completion_reflect_equal 𝐖𝐂𝐔𝐧𝐢𝐟 (ι:=ι) f). Qed.

Lemma local_completion_reflect_is_initial@{u} `{@LocalCompletion@{u} X Y Φ Ψ 𝒜 ℬ ι HC, @WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}
  : WCUnifInitial (local_completion_reflect ι f).
Proof. exact (pair_completion_reflect_is_initial 𝐖𝐂𝐔𝐧𝐢𝐟 (ι:=ι) f). Qed.
#[global] Hint Extern 2 (WCUnifInitial              (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial           (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting        (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting     (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_is_initial : typeclass_instances.

Lemma local_completion_reflect_emb@{u} `{@LocalCompletion@{u} X Y Φ Ψ 𝒜 ℬ ι HC, @WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f, !SeparatedUniformSpace Z}
  : WCUnifEmbedding (local_completion_reflect ι f).
Proof. exact wcunif_initial_embedding. Qed.
#[global] Hint Extern 2 (WCUnifEmbedding (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_emb : typeclass_instances.
#[global] Hint Extern 2 (Injective (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (local_completion_reflect _ _))  => simple notypeclasses refine local_completion_reflect_emb : typeclass_instances.

(** UP for a complete space *)
Section complete_inverse.
  Universes u.
  Context `{@LocallyComplete@{u} X Φ 𝒜 Ci, @WCUnifReflecting@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}.

  Definition local_complete_inverse := local_completion_reflect (id_fun X) f.
  #[local] Hint Extern 2 (Inverse local_complete_inverse) => exact f : typeclass_instances.

  Lemma local_complete_inverse_mor : WCUnifMorphism local_complete_inverse.
  Proof. now unfold local_complete_inverse. Qed.

  Lemma local_complete_inverse_spec : local_complete_inverse ∘ f = id.
  Proof. exact (local_completion_reflect_spec id f). Qed.

  Lemma local_complete_inverse_surjective : Surjective local_complete_inverse.
  Proof. exact local_complete_inverse_spec. Qed.

  Lemma local_complete_inverse_dense : Dense local_complete_inverse.
  Proof. apply (Dense_factor_right f). now rew (local_complete_inverse_spec). Qed.
End complete_inverse.
Arguments local_complete_inverse {_ _ _ _ _ _ _ _} f {_ _}.
Arguments local_complete_inverse_spec {_ _ _ _ _ _ _ _} f {_ _}.
#[global] Hint Extern 2 (WCUnifMorphism             (local_complete_inverse _)) => simple notypeclasses refine local_complete_inverse_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (local_complete_inverse _)) => simple notypeclasses refine local_complete_inverse_mor : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (local_complete_inverse _)) => simple notypeclasses refine local_complete_inverse_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (local_complete_inverse _)) => simple notypeclasses refine local_complete_inverse_mor : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (local_complete_inverse _)) => simple notypeclasses refine local_complete_inverse_mor : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (local_complete_inverse _))) => simple notypeclasses refine local_complete_inverse_dense : typeclass_instances.

#[global] Hint Extern 2 (Inverse (local_complete_inverse ?f)) => exact f : typeclass_instances.
#[global] Hint Extern 2 (Surjective (local_complete_inverse _)) => simple notypeclasses refine local_complete_inverse_surjective : typeclass_instances.

Section complete_inverse.
  Universes u.
  Context `{@LocallyComplete@{u} X Φ 𝒜 Ci, @WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f}.

  Local Instance local_complete_inverse_initial : WCUnifInitial (local_complete_inverse f).
  Proof. exact (pair_completion_reflect_is_initial 𝐖𝐂𝐔𝐧𝐢𝐟 (ι:=id_fun X) f). Qed.

  Context `{!SeparatedUniformSpace Z}.

  Local Instance local_complete_inverse_bij : Bijective (local_complete_inverse f).
  Proof. exact (complete_obj_inverse_bij 𝐖𝐂𝐔𝐧𝐢𝐟 f). Qed.

  Lemma local_complete_inverse_bij_back : Bijective f (inv:=local_complete_inverse f).
  Proof. exact (complete_obj_inverse_bij_back 𝐖𝐂𝐔𝐧𝐢𝐟 f). Qed.
End complete_inverse.
#[global] Hint Extern 2 (WCUnifInitial              (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial           (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting        (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting     (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_initial : typeclass_instances.

#[global] Hint Extern 2 (Bijective (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_bij : typeclass_instances.
#[global] Hint Extern 2 (Injective (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_bij : typeclass_instances.
#[global] Hint Extern 2 (Bijective _ (inv:=local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_bij_back : typeclass_instances.
#[global] Hint Extern 2 (Surjective _ (inv:=local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_bij_back : typeclass_instances.

Lemma local_complete_inverse_emb@{u} `{@LocallyComplete@{u} X Φ 𝒜 Ci, @WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, !Dense f, !SeparatedUniformSpace Z}
  : WCUnifEmbedding (local_complete_inverse f).
Proof. exact wcunif_initial_embedding. Qed.
#[global] Hint Extern 2 (WCUnifEmbedding          (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding    (local_complete_inverse _))  => simple notypeclasses refine local_complete_inverse_emb : typeclass_instances.


#[global] Hint Extern 8 (Inverse (@to_trapped ?X ?Φ ?𝒜 ?H)) => simple notypeclasses refine (local_complete_inverse (Ξ:=@trapped_uniformity X Φ 𝒜 H) (𝒵:=@trapped_bornology X Φ 𝒜 H) (@to_trapped X Φ 𝒜 H)) : typeclass_instances.

(** For CompleteUniformSpace, the Separated axiom is redundant. *)
Lemma alt_Build_LocallyComplete@{u} `{@WCUnifSpace@{u} X Φ 𝒜} {Ci:LocalCompleteInverse X}
  : (∀ Y Ψ ℬ (f:X ⇾ Y) `{@WCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ f} `{!Dense f},
       (WCUnifMorphism (local_completion_reflect_initial (id_fun X) f) ∧
                 local_completion_reflect_initial (id_fun X) f ∘ f = id_fun X)%sprop
       ) → LocallyComplete X.
Proof. intros P. apply wcunif_complete. refine (alt_Build_CompleteObj 𝐖𝐂𝐔𝐧𝐢𝐟 _).
  intros Y [Ψ ℬ]. exact (P _ _ _).
Qed.

(** Completeness extends along dense uniformly-initial maps out of a complete
    space: a separated space with a dense complete subspace is complete.
    Injectivity of [f] is automatic ([uniform_initial_embedding]); separation
    of [Y] is a genuine hypothesis. *)
Section dense_initial_complete.
  Universes u.
  Context `{@LocallyComplete@{u} X Φ 𝒜 Ci} `{@WCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ f, !Dense f, !SeparatedUniformSpace Y}.

  Local Instance dense_initial_local_complete_inverse : LocalCompleteInverse@{u} Y
    := wcunif_complete_inverse (dense_initial_complete_inverse 𝐖𝐂𝐔𝐧𝐢𝐟 f).

  Lemma dense_initial_locally_complete : LocallyComplete Y.
  Proof. apply wcunif_complete. exact (dense_initial_complete 𝐖𝐂𝐔𝐧𝐢𝐟 _). Qed.
End dense_initial_complete.
Arguments dense_initial_local_complete_inverse {_ _ _ _ _ _ _} f {_ _}.
Arguments dense_initial_locally_complete {_ _ _ _ _ _ _ _} f {_ _}.

(** A space whose completion unit is a bijection is complete. *)
Section to_trapped_bijective.
  Universes u.
  Context `{@WCUnifSpace@{u} X Φ 𝒜} `{!Inverse (τ X), !Bijective (τ X)}.

  Local Instance to_trapped_bijective_complete_inverse : LocalCompleteInverse X
    := wcunif_complete_inverse (unit_bijective_complete_inverse 𝐖𝐂𝐔𝐧𝐢𝐟 (X:=X)).

  Lemma to_trapped_bijective_complete : LocallyComplete X.
  Proof. apply wcunif_complete. exact (unit_bijective_complete 𝐖𝐂𝐔𝐧𝐢𝐟). Qed.
End to_trapped_bijective.

(** A continuous retraction of (τ X) suffices. *)
Section to_trapped_retract.
  Universes u.
  Context `{@WCUnifSpace@{u} X Φ 𝒜} (r:𝒯 X ⇾ X) `{!Continuous r} (Er:r ∘ τ X = id).

  Local Instance to_trapped_retract_complete_inverse : LocalCompleteInverse X
    := wcunif_complete_inverse (unit_retract_complete_inverse 𝐖𝐂𝐔𝐧𝐢𝐟 (X:=X) r Er).

  Lemma to_trapped_retract_complete : LocallyComplete X.
  Proof. apply wcunif_complete. exact (unit_retract_complete 𝐖𝐂𝐔𝐧𝐢𝐟 (X:=X) r Er). Qed.
End to_trapped_retract.

(** A locally uniformly continuous extension construction subsuming the UP. *)
Section complete_ext.
  Universes u.
  Context `{@WCUnifReflecting@{u} X Y Φ Ψ 𝒜 ℬ ι, !Dense ι}.
  Context `{@WCUnifMorphism@{u} X Z Φ Ξ 𝒜 𝒵 f, @LocallyComplete Z Ξ 𝒵 Ci}.

  Definition wc_cont_ext : Y ⇾ Z := (τ Z)⁻¹ ∘ 𝒯₁ f ∘ R ι.

  Lemma wc_cont_ext_mor : WCUnifMorphism wc_cont_ext.
  Proof. now pose proof canonical_completion_ext_mor 𝐖𝐂𝐔𝐧𝐢𝐟 ι f. Qed.

  Lemma wc_cont_ext_spec : wc_cont_ext ∘ ι = f.
  Proof. now pose proof canonical_completion_ext_spec 𝐖𝐂𝐔𝐧𝐢𝐟 ι f. Qed.

  Lemma wc_cont_ext_dense `{!Dense f} : Dense wc_cont_ext.
  Proof. now pose proof canonical_completion_ext_dense 𝐖𝐂𝐔𝐧𝐢𝐟 ι f. Qed.
End complete_ext.
Arguments wc_cont_ext {_ _ _ _ _ _} ι {_ _ _ _ _} f {_ _ _}.
Arguments wc_cont_ext_spec {_ _ _ _ _ _} ι {_ _ _ _ _} f {_ _ _}.
#[global] Hint Extern 2 (WCUnifMorphism             (wc_cont_ext _ _)) => simple notypeclasses refine wc_cont_ext_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBorn            (wc_cont_ext _ _)) => simple notypeclasses refine wc_cont_ext_mor : typeclass_instances.
#[global] Hint Extern 2 (Bornological               (wc_cont_ext _ _)) => simple notypeclasses refine wc_cont_ext_mor : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyContinuous (wc_cont_ext _ _)) => simple notypeclasses refine wc_cont_ext_mor : typeclass_instances.
#[global] Hint Extern 2 (Continuous                 (wc_cont_ext _ _)) => simple notypeclasses refine wc_cont_ext_mor : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (wc_cont_ext _ _))) => simple notypeclasses refine wc_cont_ext_dense : typeclass_instances.

Lemma wc_cont_ext_initial@{u}
  `{@WCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ ι, !Dense ι}
  `{@WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, @LocallyComplete Z Ξ 𝒵 Ci}
  : WCUnifInitial (wc_cont_ext ι f).
Proof. now pose proof canonical_completion_ext_initial 𝐖𝐂𝐔𝐧𝐢𝐟 ι f. Qed.
#[global] Hint Extern 2 (WCUnifInitial              (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornInitial     (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyInitial           (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial        (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (WCUnifReflecting           (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornReflecting  (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (BornologyReflecting        (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (LocallyUniformlyReflecting (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting     (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_initial : typeclass_instances.

Lemma wc_cont_ext_emb@{u}
  `{@WCUnifInitial@{u} X Y Φ Ψ 𝒜 ℬ ι, !Dense ι}
  `{@WCUnifInitial@{u} X Z Φ Ξ 𝒜 𝒵 f, @LocallyComplete Z Ξ 𝒵 Ci, !SeparatedUniformSpace Y}
  : WCUnifEmbedding (wc_cont_ext ι f).
Proof. exact wcunif_initial_embedding. Qed.
#[global] Hint Extern 2 (WCUnifEmbedding          (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_emb : typeclass_instances.
#[global] Hint Extern 2 (LocallyUnifBornEmbedding (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_emb : typeclass_instances.
#[global] Hint Extern 2 (Injective                (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_emb : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding    (wc_cont_ext _ _))  => simple notypeclasses refine wc_cont_ext_emb : typeclass_instances.

(** Theory specific to WCUnif. *)
(** A complete space is locally complete *)
Section complete_locally_complete.
  Local Open Scope fun_inv_scope.
  Context `{@WCUnifSpace X Φ 𝒜} `{!CompleteUniformSpace X (Ci:=Ci)}.
  
  Lemma complete_locally_complete_spec : ((κ X)⁻¹ ∘ ρ X) ∘ τ X = id.
  Proof. change ((κ X)⁻¹ ∘ (ρ X ∘ τ X) = id). rew (from_trapped_spec _). exact (bijective _). Qed.
  Local Abbreviation Er := complete_locally_complete_spec.
  
  Local Instance complete_locally_inverse : LocalCompleteInverse X := to_trapped_retract_complete_inverse _ Er.
  Lemma complete_locally_complete : LocallyComplete X.
  Proof. exact (to_trapped_retract_complete _ Er). Qed.
End complete_locally_complete.
#[global] Hint Extern 2 (LocallyComplete _ (Li:=complete_locally_inverse)) => simple notypeclasses refine complete_locally_complete : typeclass_instances.
#[global] Hint Extern 10 (LocalCompleteInverse _) => simple notypeclasses refine complete_locally_inverse : typeclass_instances.


