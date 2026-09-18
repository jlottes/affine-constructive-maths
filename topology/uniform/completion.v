(** Instantiating the completion kit at (𝐔𝐧𝐢𝐟, 𝒞): a reworking of
    uniform/completion.v that delegates to reflection_pair/completion.v.

    The bridge direction is [Completion] ⟹ [PairCompletion] (with hints, so
    the abstract theorems apply whenever a concrete completion is in
    context); the converse is left to direct invocation. *)
Require Import interfaces.set algebra_notation.
Require Import interfaces.sprop logic.aprop relations.
Require Import interfaces.common_props theory.common_props.
Require Import set_lambda.
Require Import interfaces.orders interfaces.subset.
Require Import interfaces.topology interfaces.uniform.
Require Import theory.set orders.orders orders.maps orders.subset orders.closure orders.filters.
Require Import topology.topology topology.uniform.base uniform.basis uniform.product topology.uniform.cauchy_completion.
Require Import topology.maps.
Require Import interfaces.reflection_pair reflection_pair.base topology.reflection_pair.completion topology.reflection_pair.products.
Require Import easy rewrite.

Local Open Scope fun_inv_scope.

Local Abbreviation id := (id_fun _).
Local Abbreviation η := to_cauchy.
Local Abbreviation 𝒞 := cauchy_filter_set.
Local Abbreviation 𝒞₁ := cauchy_map.
Local Abbreviation R := cauchy_reflect.

#[local] Hint Extern 8 (Uniformity ?X) => match goal with H : Fib 𝐔𝐧𝐢𝐟 X |- _ => exact H end : typeclass_instances.

(** * The bridge: concrete completions instantiate the pair-level API. *)

#[global] Hint Extern 0 (@PairCompletionReflect 𝐔𝐧𝐢𝐟 _ _ _ ?X ?Y ?FX ?FY ?ι) => change (@CompletionReflect X Y FX FY ι) : typeclass_instances.
#[global] Hint Extern 0 (@PairCompleteInverse 𝐔𝐧𝐢𝐟 _ _ _ ?X ?FX) => change (@CompleteInverse X FX) : typeclass_instances.

Lemma unif_pair_completion `{H:@Completion X Y Φ Ψ ι Ci} : PairCompletion 𝐔𝐧𝐢𝐟 ι.
Proof. split; try exact _; apply H. Qed.

Lemma unif_complete_obj `{H:@CompleteUniformSpace X Φ Ci} : CompleteObj 𝐔𝐧𝐢𝐟 X.
Proof. exact unif_pair_completion. Qed.

#[global] Hint Extern 2 (PairCompletion 𝐔𝐧𝐢𝐟 _) => simple notypeclasses refine unif_pair_completion : typeclass_instances.
#[global] Hint Extern 2 (CompleteObj 𝐔𝐧𝐢𝐟 _) => simple notypeclasses refine unif_complete_obj : typeclass_instances.

(** The converse record bridge, for direct invocation. *)
Lemma unif_completion `{Ci:@CompletionReflect X Y Φ Ψ ι} : PairCompletion 𝐔𝐧𝐢𝐟 ι → Completion ι.
Proof. intros H. split.
+ pose proof (pair_completion_obj_Y 𝐔𝐧𝐢𝐟 (H:=H)) as HY. change (UniformSpace Y) in HY.
  apply uniform_T₀_separated, Hausdorff_T₀. exact H.
+ exact (pair_completion_initial 𝐔𝐧𝐢𝐟 (PairCompletion:=H)). 
+ exact (pair_completion_dense 𝐔𝐧𝐢𝐟 (PairCompletion:=H)).
+ intros Z Ξ f ??. exact (pair_completion_reflect_initial_mor 𝐔𝐧𝐢𝐟 (PairCompletion:=H) f).
+ intros Z Ξ f ??. exact (pair_completion_reflect_initial_spec 𝐔𝐧𝐢𝐟 ι (PairCompletion:=H) f).
Qed.

Lemma unif_complete `{Ci:@CompleteInverse X Φ} : CompleteObj 𝐔𝐧𝐢𝐟 X → CompleteUniformSpace X.
Proof. exact unif_completion. Qed.

(** * The canonical completion: (𝒞, η, cauchy_map, cauchy_reflect). *)

Definition unif_canonical_completor@{u} : CanonicalCompletor@{u} 𝐔𝐧𝐢𝐟 (U:=@UniformNeighborhood@{u}).
Proof. unshelve esplit.
+ exact @cauchy_filter_set.
+ exact @cauchy_uniformity.
+ exact @to_cauchy.
+ intros X Y Φ Ψ HX HY f Hf. exact (𝒞₁ f).
+ intros X Y Φ Ψ HX f ??. exact (R f).
Defined.
#[global] Hint Extern 2 (CanonicalCompletor 𝐔𝐧𝐢𝐟) => exact unif_canonical_completor : typeclass_instances.

Lemma unif_canonical_completion : CanonicalCompletion 𝐔𝐧𝐢𝐟.
Proof. split.
+ intros X Φ HX. now change (Hausdorff (𝒞 X)).
+ intros X Φ HX. now change (UniformlyInitial (η X)).
+ intros X Φ HX. now change (Dense (η X)).
+ intros X Y Φ Ψ HX HY f Hf. now change (UniformlyContinuous (𝒞₁ f)).
+ intros X Y Φ Ψ HX HY f Hf. exact (cauchy_map_spec f).
+ intros X Y Φ Ψ HX HY f HR HD. now change (UniformlyContinuous (cauchy_reflect f)).
+ intros X Y Φ Ψ HX HY f HD HR. exact (cauchy_reflect_spec f).
Qed.
#[global] Hint Extern 2 (CanonicalCompletion 𝐔𝐧𝐢𝐟) => simple notypeclasses refine unif_canonical_completion : typeclass_instances.

(** (K3), by the dense-initial descent law. *)
Lemma unif_canonical_map_initial : CanonicalCompletionMapInitial 𝐔𝐧𝐢𝐟.
Proof. apply (dense_initial_descent_map_ini 𝐔𝐧𝐢𝐟).
  intros S T V FS FT FV f g HD Hf Hg HR. exact (ufm_dense_initial f g).
Qed.
#[global] Hint Extern 2 (CanonicalCompletionMapInitial 𝐔𝐧𝐢𝐟) => simple notypeclasses refine unif_canonical_map_initial : typeclass_instances.


(** * The theory of uniform/completion.v, by delegation. *)

Section completion_reflect_initial.
  Universes u.
  Context `{@Completion@{u} X Y Φ Ψ ι HC, @UniformlyInitial@{u} X Z Φ Ξ f, !Dense f}.

  Local Abbreviation g := (completion_reflect_initial ι f).

  Lemma completion_reflect_initial_dense : Dense g.
  Proof. exact (pair_completion_reflect_initial_dense 𝐔𝐧𝐢𝐟 (ι:=ι)). Qed.

  Lemma completion_reflect_initial_initial : UniformlyInitial g.
  Proof. exact (pair_completion_reflect_initial_initial 𝐔𝐧𝐢𝐟 (ι:=ι) f). Qed.
End completion_reflect_initial.
#[global] Hint Extern 2 (Dense (func_op (completion_reflect_initial _ _)))  => simple notypeclasses refine completion_reflect_initial_dense : typeclass_instances.
#[global] Hint Extern 2 (UniformlyInitial (completion_reflect_initial _ _))  => simple notypeclasses refine completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (completion_reflect_initial _ _))  => simple notypeclasses refine completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (completion_reflect_initial _ _))  => simple notypeclasses refine completion_reflect_initial_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (completion_reflect_initial _ _))  => simple notypeclasses refine completion_reflect_initial_initial : typeclass_instances.


(** Completions are complete. *)
Coercion completion_inverse@{u} {X Y:set@{u}} `{H:@Completion@{u} X Y Φ Ψ ι U}
  : CompleteInverse@{u} Y
  := pair_completion_inverse 𝐔𝐧𝐢𝐟 (ι:=ι) (H:=unif_pair_completion (H:=H)).
#[global] Hint Extern 4 (CompleteInverse ?Y) =>
  match goal with H : Completion (Y:=Y) _ |- _ => exact H end : typeclass_instances.

Coercion completion_complete@{u} {X Y:set@{u}} `{H:@Completion@{u} X Y Φ Ψ ι U}
  : CompleteUniformSpace@{u} Y.
Proof. apply unif_completion. exact (pair_completion_complete 𝐔𝐧𝐢𝐟 (ι:=ι) (H:=unif_pair_completion (H:=H))). Qed.

Definition cauchy_complete_inverse@{u} `{@UniformSpace@{u} X Φ} : CompleteInverse@{u} (𝒞 X)
  := completion_inverse (ι:=η _).
#[global] Hint Extern 2 (CompleteInverse (cauchy_filter_set ?X)) => simple notypeclasses refine (cauchy_complete_inverse (X:=X)) : typeclass_instances.
Lemma cauchy_complete@{u} `{@UniformSpace@{u} X Φ} : CompleteUniformSpace@{u} (𝒞 X).
Proof. exact completion_complete. Qed.
#[global] Hint Extern 2 (CompleteUniformSpace (cauchy_filter_set ?X)) => simple notypeclasses refine (cauchy_complete (X:=X)) : typeclass_instances.

(** The UP extends to any UniformlyReflecting Dense map. *)
Section completion_reflect.
  Universes u.
  Context `{@Completion@{u} X Y Φ Ψ ι HC, @UniformlyReflecting@{u} X Z Φ Ξ f, !Dense f}.

  Definition completion_reflect : Z ⇾ Y := pair_completion_reflect 𝐔𝐧𝐢𝐟 ι f.

  Local Instance completion_reflect_ufm_cont : UniformlyContinuous completion_reflect.
  Proof. exact (pair_completion_reflect_mor 𝐔𝐧𝐢𝐟 ι f). Qed.

  Lemma completion_reflect_spec : completion_reflect ∘ f = ι.
  Proof. exact (pair_completion_reflect_spec 𝐔𝐧𝐢𝐟 (ι:=ι) f). Qed.

  Lemma completion_reflect_dense : Dense completion_reflect.
  Proof. exact (pair_completion_reflect_dense 𝐔𝐧𝐢𝐟 ι f). Qed.
End completion_reflect.
Arguments completion_reflect {_ _ _ _} ι {_ _ _ _} f {_ _}.
Arguments completion_reflect_spec {_ _ _ _} ι {_ _ _ _} f {_ _}.
#[global] Hint Extern 2 (UniformlyContinuous (completion_reflect _ _)) => simple notypeclasses refine completion_reflect_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (completion_reflect _ _)) => simple notypeclasses refine completion_reflect_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (completion_reflect _ _))) => simple notypeclasses refine completion_reflect_dense : typeclass_instances.

Lemma completion_reflect_equal@{u} `{@Completion@{u} X Y Φ Ψ ι HC, @UniformlyInitial@{u} X Z Φ Ξ f, !Dense f}
  : completion_reflect ι f = completion_reflect_initial ι f.
Proof. exact (pair_completion_reflect_equal 𝐔𝐧𝐢𝐟 (ι:=ι) f). Qed.

Lemma completion_reflect_is_initial@{u} `{@Completion@{u} X Y Φ Ψ ι HC, @UniformlyInitial@{u} X Z Φ Ξ f, !Dense f}
  : UniformlyInitial (completion_reflect ι f).
Proof. exact (pair_completion_reflect_is_initial 𝐔𝐧𝐢𝐟 (ι:=ι) f). Qed.
#[global] Hint Extern 2 (UniformlyInitial (completion_reflect _ _))  => simple notypeclasses refine completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (completion_reflect _ _))  => simple notypeclasses refine completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (completion_reflect _ _))  => simple notypeclasses refine completion_reflect_is_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (completion_reflect _ _))  => simple notypeclasses refine completion_reflect_is_initial : typeclass_instances.

#[global] Hint Extern 2 (UniformlyEmbedding (completion_reflect _ _))  => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (Injective (completion_reflect _ _))  => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (completion_reflect _ _))  => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.

(** UP for a complete space *)
Section complete_inverse.
  Universes u.
  Context `{@CompleteUniformSpace@{u} X Φ Ci, @UniformlyReflecting@{u} X Z Φ Ξ f, !Dense f}.

  Definition complete_inverse := completion_reflect (id_fun X) f.
  #[local] Hint Extern 2 (Inverse complete_inverse) => exact f : typeclass_instances.

  Lemma complete_inverse_ufm_cont : UniformlyContinuous complete_inverse.
  Proof. now unfold complete_inverse. Qed.

  Lemma complete_inverse_spec : complete_inverse ∘ f = id.
  Proof. exact (completion_reflect_spec id f). Qed.

  Lemma complete_inverse_surjective : Surjective complete_inverse.
  Proof. exact complete_inverse_spec. Qed.

  Lemma complete_inverse_dense : Dense complete_inverse.
  Proof. apply (Dense_factor_right f). now rew (complete_inverse_spec). Qed.
End complete_inverse.
Arguments complete_inverse {_ _ _ _ _ _} f {_ _}.
Arguments complete_inverse_spec {_ _ _ _ _ _} f {_ _}.
#[global] Hint Extern 2 (UniformlyContinuous (complete_inverse _)) => simple notypeclasses refine complete_inverse_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (complete_inverse _)) => simple notypeclasses refine complete_inverse_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (complete_inverse _))) => simple notypeclasses refine complete_inverse_dense : typeclass_instances.

#[global] Hint Extern 2 (Inverse (complete_inverse ?f)) => exact f : typeclass_instances.
#[global] Hint Extern 2 (Surjective (complete_inverse _)) => simple notypeclasses refine complete_inverse_surjective : typeclass_instances.

Section complete_inverse.
  Universes u.
  Context `{@CompleteUniformSpace@{u} X Φ Ci, @UniformlyInitial@{u} X Z Φ Ξ f, !Dense f}.

  Local Instance complete_inverse_ufm_init : UniformlyInitial (complete_inverse f).
  Proof. exact (pair_completion_reflect_is_initial 𝐔𝐧𝐢𝐟 (ι:=id_fun X) f). Qed.

  Context `{!SeparatedUniformSpace Z}.

  Local Instance complete_inverse_bij : Bijective (complete_inverse f).
  Proof. exact (complete_obj_inverse_bij 𝐔𝐧𝐢𝐟 f). Qed.

  Lemma complete_inverse_bij_back : Bijective f (inv:=complete_inverse f).
  Proof. exact (complete_obj_inverse_bij_back 𝐔𝐧𝐢𝐟 f). Qed.
End complete_inverse.
#[global] Hint Extern 2 (UniformlyInitial (complete_inverse _))  => simple notypeclasses refine complete_inverse_ufm_init : typeclass_instances.
#[global] Hint Extern 2 (Bijective (complete_inverse _))  => simple notypeclasses refine complete_inverse_bij : typeclass_instances.
#[global] Hint Extern 2 (Bijective _ (inv:=complete_inverse _))  => simple notypeclasses refine complete_inverse_bij_back : typeclass_instances.
#[global] Hint Extern 2 (Surjective (complete_inverse _))  => simple notypeclasses refine complete_inverse_bij : typeclass_instances.
#[global] Hint Extern 2 (Surjective _ (inv:=complete_inverse _))  => simple notypeclasses refine complete_inverse_bij_back : typeclass_instances.

#[global] Hint Extern 2 (UniformlyEmbedding (complete_inverse _))  => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (Injective (complete_inverse _))  => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (complete_inverse _))  => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.


#[global] Hint Extern 8 (Inverse (@to_cauchy ?X ?Φ ?H)) => simple notypeclasses refine (complete_inverse (Ξ:=@cauchy_uniformity X Φ H) (@to_cauchy X Φ H)) : typeclass_instances.

(** For CompleteUniformSpace, the Separated axiom is redundant. *)
Lemma alt_Build_CompleteUniformSpace@{u} `{@UniformSpace@{u} X Φ} {Ci:CompleteInverse X}
  : (∀ Y Ψ (f:X ⇾ Y) `{@UniformlyInitial@{u} X Y Φ Ψ f} `{!Dense f},
       (UniformlyContinuous (completion_reflect_initial (id_fun X) f) ∧
                 completion_reflect_initial (id_fun X) f ∘ f = id_fun X)%sprop
       ) → CompleteUniformSpace X.
Proof. intros P. apply unif_complete. refine (alt_Build_CompleteObj 𝐔𝐧𝐢𝐟 _). exact P. Qed.

(** Completeness extends along dense uniformly-initial maps out of a complete
    space: a separated space with a dense complete subspace is complete.
    Injectivity of [f] is automatic ([uniform_initial_embedding]); separation
    of [Y] is a genuine hypothesis. *)
Section dense_initial_complete.
  Universes u.
  Context `{@CompleteUniformSpace@{u} X Φ Ci} `{@SeparatedUniformSpace@{u} Y Ψ}
          (f:X ⇾ Y) `{!UniformlyInitial f, !Dense f}.

  Local Instance unif_dense_initial_complete_inverse : CompleteInverse@{u} Y
    := dense_initial_complete_inverse 𝐔𝐧𝐢𝐟 f.

  Lemma unif_dense_initial_complete : CompleteUniformSpace@{u} Y.
  Proof. apply unif_complete. exact (dense_initial_complete 𝐔𝐧𝐢𝐟 _). Qed.
End dense_initial_complete.

(** A space whose completion unit is a bijection is complete. *)
Section to_cauchy_bijective.
  Universes u.
  Context `{@UniformSpace@{u} X Φ} `{!Inverse (η X), !Bijective (η X)}.

  Local Instance to_cauchy_bijective_complete_inverse : CompleteInverse X
    := unit_bijective_complete_inverse 𝐔𝐧𝐢𝐟 (X:=X).

  Lemma to_cauchy_bijective_complete : CompleteUniformSpace X.
  Proof. apply unif_complete. exact (unit_bijective_complete 𝐔𝐧𝐢𝐟). Qed.
End to_cauchy_bijective.

(** A continuous retraction of (η X) suffices. *)
Section to_cauchy_retract.
  Universes u.
  Context `{@UniformSpace@{u} X Φ} (r:𝒞 X ⇾ X) `{!Continuous r} (Er:r ∘ η X = id).

  Local Instance to_cauchy_retract_complete_inverse : CompleteInverse X
    := unit_retract_complete_inverse 𝐔𝐧𝐢𝐟 (X:=X) r Er.

  Lemma to_cauchy_retract_complete : CompleteUniformSpace X.
  Proof. apply unif_complete. exact (unit_retract_complete 𝐔𝐧𝐢𝐟 (X:=X) r Er). Qed.
End to_cauchy_retract.

(** A uniformly continuous extension construction subsuming the UP. *)
Section complete_ext.
  Universes u.
  Context `{@UniformlyReflecting@{u} X Y Φ Ψ ι, !Dense ι}.
  Context `{@UniformlyContinuous@{u} X Z Φ Ξ f, @CompleteUniformSpace Z Ξ Ci}.

  Local Open Scope fun_inv_scope.

  Definition ufm_cont_ext : Y ⇾ Z := (η Z)⁻¹ ∘ cauchy_map f ∘ cauchy_reflect ι.

  Lemma ufm_cont_ext_ufm_cont : UniformlyContinuous ufm_cont_ext.
  Proof. exact (canonical_completion_ext_mor 𝐔𝐧𝐢𝐟 ι f). Qed.

  Lemma ufm_cont_ext_spec : ufm_cont_ext ∘ ι = f.
  Proof. exact (canonical_completion_ext_spec 𝐔𝐧𝐢𝐟 ι f). Qed.

  Lemma ufm_cont_ext_dense `{!Dense f} : Dense ufm_cont_ext.
  Proof. exact (canonical_completion_ext_dense 𝐔𝐧𝐢𝐟 ι f). Qed.
End complete_ext.
Arguments ufm_cont_ext {_ _ _ _} ι {_ _ _ _} f {_ _ _}.
Arguments ufm_cont_ext_spec {_ _ _ _} ι {_ _ _ _} f {_ _ _}.
#[global] Hint Extern 2 (UniformlyContinuous (ufm_cont_ext _ _)) => simple notypeclasses refine ufm_cont_ext_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Continuous (ufm_cont_ext _ _)) => simple notypeclasses refine ufm_cont_ext_ufm_cont : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (ufm_cont_ext _ _))) => simple notypeclasses refine ufm_cont_ext_dense : typeclass_instances.

Lemma ufm_cont_ext_initial@{u}
  `{@UniformlyInitial@{u} X Y Φ Ψ ι, !Dense ι}
  `{@UniformlyInitial@{u} X Z Φ Ξ f, @CompleteUniformSpace Z Ξ Ci}
  : UniformlyInitial@{u} (ufm_cont_ext@{u} ι f).
Proof. exact (canonical_completion_ext_initial 𝐔𝐧𝐢𝐟 ι f). Qed.
#[global] Hint Extern 2 (UniformlyInitial (ufm_cont_ext _ _))  => simple notypeclasses refine ufm_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (UniformlyReflecting (ufm_cont_ext _ _))  => simple notypeclasses refine ufm_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyInitial (ufm_cont_ext _ _))  => simple notypeclasses refine ufm_cont_ext_initial : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyReflecting (ufm_cont_ext _ _))  => simple notypeclasses refine ufm_cont_ext_initial : typeclass_instances.

#[global] Hint Extern 2 (UniformlyEmbedding (ufm_cont_ext _ _))     => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (Injective (ufm_cont_ext _ _))              => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.
#[global] Hint Extern 2 (ContinuouslyEmbedding (ufm_cont_ext _ _))  => simple notypeclasses refine uniform_initial_embedding : typeclass_instances.


(** Products. *)

(** The cartesian product uniformity is a product in the pair sense
    ([reflection_pair/products.v]): with it, [prod_map_ufm_refl] and the two
    product theorems below are instances of the abstract ones. *)
Lemma unif_pair_product `{@UniformSpace X Φ} `{@UniformSpace Y Ψ}
  `{@CartesianProductUniformity X Y Φ Ψ Θ} : PairProduct 𝐔𝐧𝐢𝐟 X Y Θ.
Proof. split; try exact _.
+ exact prod_proj1_ufm_cont.
+ exact prod_proj2_ufm_cont.
+ intros Z Ξ f g Hf Hg. change (UniformlyContinuous f) in Hf. change (UniformlyContinuous g) in Hg.
  apply cartesian_product_uniformity_initial; [ exact Hf | exact Hg ].
Qed.
#[global] Hint Extern 2 (PairProduct 𝐔𝐧𝐢𝐟 _ _ _) => simple notypeclasses refine unif_pair_product : typeclass_instances.

Definition cartesian_completion_reflect@{u}
  `{@Completion@{u} X₁ Y₁ Φ₁ Ψ₁ ι₁ HC₁, @Completion@{u} X₂ Y₂ Φ₂ Ψ₂ ι₂ HC₂}
  `{@CartesianProductUniformity X₁ X₂ Φ₁ Φ₂ Φ}
  `{@CartesianProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  : CompletionReflect@{u} (prod_map (ι₁, ι₂))
:= λ Z Ξ f Hf1 Hf2,
   to_prod (completion_reflect_initial ι₁ (η _) ∘ cauchy_map (prod_proj1 _ _),
            completion_reflect_initial ι₂ (η _) ∘ cauchy_map (prod_proj2 _ _)) ∘ cauchy_reflect f.
#[global] Hint Extern 2 (CompletionReflect (func_op prod_map _)) => notypeclasses refine cartesian_completion_reflect : typeclass_instances.

Lemma cartesian_product_completion@{u}
  `{@Completion@{u} X₁ Y₁ Φ₁ Ψ₁ ι₁ HC₁, @Completion@{u} X₂ Y₂ Φ₂ Ψ₂ ι₂ HC₂}
  `{@CartesianProductUniformity X₁ X₂ Φ₁ Φ₂ Φ}
  `{@CartesianProductUniformity Y₁ Y₂ Ψ₁ Ψ₂ Ψ}
  :  Completion@{u} (prod_map (ι₁, ι₂)) .
Proof. split; try exact _; intros Z Ξ f Hf1 Hf2.
+ now unfold completion_reflect_initial, cartesian_completion_reflect.
+ change (to_prod
    (completion_reflect_initial ι₁ (η _) ∘ (cauchy_map (prod_proj1 X₁ X₂) ∘ (cauchy_reflect f ∘ f)),
     completion_reflect_initial ι₂ (η _) ∘ (cauchy_map (prod_proj2 X₁ X₂) ∘ (cauchy_reflect f ∘ f)))
    = prod_map (ι₁, ι₂) ).
  rew (cauchy_reflect_spec f).
  rew [(cauchy_map_spec (prod_proj1 _ _))|(cauchy_map_spec (prod_proj2 _ _))].
  change (to_prod ((completion_reflect_initial ι₁ (η _) ∘ η _) ∘ prod_proj1 X₁ X₂,
                   (completion_reflect_initial ι₂ (η _) ∘ η _) ∘ prod_proj2 X₁ X₂) =
          prod_map (ι₁, ι₂)).
  now rew (completion_reflect_initial_spec _ _).
Qed.
#[global] Hint Extern 2 (Completion (func_op prod_map _)) => simple notypeclasses refine cartesian_product_completion : typeclass_instances.

(** Products of complete spaces are complete. *)

Definition cartesian_complete_inverse@{u}
  `{@CompleteUniformSpace@{u} X Φ CiX, @CompleteUniformSpace@{u} Y Ψ CiY}
  `{@CartesianProductUniformity X Y Φ Ψ Θ}
  : CompleteInverse@{u} (X × Y)
  := completion_inverse (ι:=prod_map (id, id)).
#[global] Hint Extern 2 (CompleteInverse (_ × _)) => simple notypeclasses refine cartesian_complete_inverse : typeclass_instances.

Lemma cartesian_product_complete@{u}
  `{@CompleteUniformSpace@{u} X Φ CiX, @CompleteUniformSpace@{u} Y Ψ CiY}
  `{@CartesianProductUniformity X Y Φ Ψ Θ}
  : CompleteUniformSpace@{u} (X × Y).
Proof. exact completion_complete. Qed.
#[global] Hint Extern 2 (CompleteUniformSpace (_ × _)) => simple notypeclasses refine cartesian_product_complete : typeclass_instances.
