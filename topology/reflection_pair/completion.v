(** Prototype: the completion API of doc/completion_abstract.md §3–§5, abstract
    over a completion context — a full reflection pair concrete over the 𝐀𝐓𝐨𝐩
    pair (doc §3).  Density and separation of objects and morphisms are
    *defined* through the leg, and the dense-epi engine applies to abstract
    hom-classes via [hom_map].  Mirrors [interfaces/uniform.v : Completion]
    field for field. *)
Require Import sprop srelations.
Require Import logic.aprop relations.
Require Import set_lambda.
Require Import interfaces.topology.
Require Import topology.base topology.interior topology.maps topology.product.
Require Import reflection_pair.base reflection_pair.products.
Require Import easy rewrite.

Local Open Scope fun_inv_scope.

#[local] Hint Extern 2 (Neighborhood ?X) => refine (@fmap _ 𝐀𝐓𝐨𝐩 _ _ _ X _) : typeclass_instances.

Section data.
  Universes u.
  Context C `{HM:!PairMorphism@{u} C 𝐀𝐓𝐨𝐩 (CD:=CD) (U:=U)}.

  Class PairCompletionReflect@{} {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} (ι:X ⇾ Y)
    := pair_completion_reflect_initial (Z:set@{u}) {FZ:Fib C Z} (f:X ⇾ Z) `{!Ini C f, !Dense f} : Z ⇾ Y.
  #[global] Arguments pair_completion_reflect_initial {X Y FX FY} ι {_ Z FZ} f {_ _}.

  Definition PairCompleteInverse@{} (X:set@{u}) {FX:Fib C X} := PairCompletionReflect (id_fun X).
  Existing Class PairCompleteInverse.
  #[global] Identity Coercion PairCompleteInverse_Reflect : PairCompleteInverse >-> PairCompletionReflect.
End data.
#[global] Hint Extern 4 (@PairCompletionReflect ?C ?CD ?U ?HM ?X _ ?FX _ (id_fun _))
  => change (@PairCompleteInverse C CD U HM X FX) : typeclass_instances.

Section prop.
  Universes u.
  Context C `{HM:!PairMorphism@{u} C 𝐀𝐓𝐨𝐩 (CD:=CD) (U:=U)}.
  
  Class PairCompletion@{} `{@PairCompletionReflect@{u} C _ _ HM X Y FX FY ι} : SProp :=
  { pair_completion_hausdorff : Hausdorff Y
  ; pair_completion_initial : Ini C ι
  ; pair_completion_dense   : Dense ι
  ; pair_completion_reflect_initial_mor {Z:set@{u}} {FZ:Fib C Z} (f:X ⇾ Z) `{!Ini C f, !Dense f}
    : Hom C (pair_completion_reflect_initial C ι f)
  ; pair_completion_reflect_initial_spec {Z:set@{u}} {FZ:Fib C Z} (f:X ⇾ Z) `{!Ini C f, !Dense f}
    : pair_completion_reflect_initial C ι f ∘ f = ι
  }.

  Definition CompleteObj `{Ci:@PairCompleteInverse C _ _ HM X FX} := PairCompletion (ι:=id_fun X).
  Existing Class CompleteObj.
End prop.
Arguments PairCompletion C {_ _ _ X Y FX FY} ι {_}.
Arguments pair_completion_reflect_initial_spec C {_ _ _ X Y FX FY} ι {_ _} {Z FZ} f {_ _}.
Coercion pair_completion_hausdorff : PairCompletion >-> Hausdorff.
Coercion pair_completion_initial : PairCompletion >-> Ini.
Coercion pair_completion_dense : PairCompletion >-> Dense.
#[global] Hint Extern 2 (Hom _ (pair_completion_reflect_initial _ _ _)) => simple notypeclasses refine (pair_completion_reflect_initial_mor _ _) : typeclass_instances.
  
Arguments CompleteObj C {_ _ _} X {_ _}.

Section canonical_completor.
  Universes u.
  Context C `{HM:!PairMorphism@{u} C 𝐀𝐓𝐨𝐩 (CD:=CD) (U:=U)}.

  Record CanonicalCompletor :=
  { canonical_completion (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : set@{u}
  ; canonical_completion_fib (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : Fib C (canonical_completion X)
  ; canonical_completion_unit (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : X ⇾ (canonical_completion X)
  ; canonical_completion_map {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {HX:Obj C X} {HY:Obj C Y} (f:X ⇾ Y) {Hf:Hom C f}
    : canonical_completion X ⇾ canonical_completion Y
  ; canonical_completion_reflect {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {HX:Obj C X} (f:X ⇾ Y) {Hf₁:Rfl C f} {Hf₂:Dense f}
    : Y ⇾ canonical_completion X
  }.
  Existing Class CanonicalCompletor.
End canonical_completor.
Arguments canonical_completion C {_ _ _} X {_ _}.
Arguments canonical_completion_fib C {_ _ _} X {_ _}.
Arguments canonical_completion_unit C {_ _ _} X {_ _}.
Arguments canonical_completion_map C {_ _ _ X Y _ _ _ _} f {_}.
Arguments canonical_completion_reflect C {_ _ _ X Y _ _ _} f {_ _}.
#[global] Hint Extern 0 (Fib ?C (@canonical_completion ?C _ _ ?c ?X ?FX ?HX)) => exact (c.(canonical_completion_fib _) X (FX:=FX) (HX:=HX)) : typeclass_instances.
#[global] Hint Extern 0 (PairCompletionReflect ?C (@canonical_completion_unit ?C _ _ ?c ?X ?FX ?HX))
  => exact (λ Z FZ f HI HD, canonical_completion_reflect C (c:=c) f (Hf₁:=HI) (Hf₂:=HD)) : typeclass_instances.

Section canonical_completion.
  Universes u.
  Context C `{HM:!PairMorphism@{u} C 𝐀𝐓𝐨𝐩 (CD:=CD) (U:=U)}.
  
  Context {Ccomp:CanonicalCompletor C}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Local Abbreviation 𝒞₁ := (canonical_completion_map _ (c:=Ccomp)).
  Local Abbreviation R := (canonical_completion_reflect _ (c:=Ccomp)).

  Record CanonicalCompletion : SProp :=
  { canonical_completion_hausdorff (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : Hausdorff (𝒞 X)
  ; canonical_completion_unit_ini (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : Ini C (η X)
  ; canonical_completion_unit_dense (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : Dense (η X)
  ; canonical_completion_map_mor {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {HX:Obj C X} {HY:Obj C Y} (f:X ⇾ Y) {Hf:Hom C f}
    : Hom C (𝒞₁ f)
  ; canonical_completion_unit_natural {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {HX:Obj C X} {HY:Obj C Y} (f:X ⇾ Y) {Hf:Hom C f}
    : 𝒞₁ f ∘ η X = η Y ∘ f
  ; canonical_completion_reflect_mor {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {HX:Obj C X} {HY:Obj C Y} (f:X ⇾ Y) {Hf₁:Rfl C f} {Hf₂:Dense f}
    : Hom C (R f)
  ; canonical_completion_reflect_spec {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {HX:Obj C X} {HY:Obj C Y} (f:X ⇾ Y) {Hf₁:Rfl C f} {Hf₂:Dense f}
    : R f ∘ f = η X
  }.
  Existing Class CanonicalCompletion.

  (** (K3) 𝓜-preservation — a separate kit item, deliberately not a field of
      the record: the completion functor preserves initial maps with no
      density side condition.  Enters as its own hypothesis where needed. *)
  Class CanonicalCompletionMapInitial : SProp :=
  { canonical_completion_map_ini {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {HX:Obj C X} {HY:Obj C Y} (f:X ⇾ Y) `{!Ini C f}
      : Ini C (𝒞₁ f) }.
End canonical_completion.
Arguments canonical_completion_hausdorff C {_ _ _ _ _} X {_ _}.
Arguments canonical_completion_unit_ini C {_ _ _ _ _} X {_ _}.
Arguments canonical_completion_unit_dense C {_ _ _ _ _} X {_ _}.
Arguments canonical_completion_map_mor C {_ _ _ _ _ X Y FX FY _ _} f {_}.
Arguments canonical_completion_unit_natural C {_ _ _ _ _ X Y FX FY _ _} f {_}.
Arguments canonical_completion_reflect_mor C {_ _ _ _ _ X Y FX FY _ _} f {_ _}.
Arguments canonical_completion_reflect_spec C {_ _ _ _ _ X Y FX FY _ _} f {_ _}.
Arguments canonical_completion_map_ini C {_ _ _ _ _ X Y FX FY _ _} f {_}.
#[global] Hint Extern 2 (Ini ?C (canonical_completion_map ?C (c:=?c) ?f)) => simple notypeclasses refine (canonical_completion_map_ini C (Ccomp:=c) f) : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (canonical_completion_map ?C (c:=?c) ?f)) => simple notypeclasses refine (initial_rfl (Hf:=canonical_completion_map_ini C (Ccomp:=c) f)) : typeclass_instances.
#[global] Hint Extern 0 (Hausdorff (canonical_completion ?C (c:=?c) ?X)) => simple notypeclasses refine (canonical_completion_hausdorff C (Ccomp:=c) X) : typeclass_instances.
#[global] Hint Extern 0 (Ini ?C (canonical_completion_unit ?C (c:=?c) ?X)) => simple notypeclasses refine (canonical_completion_unit_ini C (Ccomp:=c) X) : typeclass_instances.
#[global] Hint Extern 0 (Hom ?C (canonical_completion_unit ?C (c:=?c) ?X)) => simple notypeclasses refine (initial_hom (Hf:=canonical_completion_unit_ini C (Ccomp:=c) X)) : typeclass_instances.
#[global] Hint Extern 0 (Rfl ?C (canonical_completion_unit ?C (c:=?c) ?X)) => simple notypeclasses refine (initial_rfl (Hf:=canonical_completion_unit_ini C (Ccomp:=c) X)) : typeclass_instances.
#[global] Hint Extern 0 (Dense (func_op (canonical_completion_unit ?C (c:=?c) ?X))) => simple notypeclasses refine (canonical_completion_unit_dense C (Ccomp:=c) X) : typeclass_instances.

#[global] Hint Extern 0 (Hom ?C (canonical_completion_map ?C (c:=?c) ?f)) => simple notypeclasses refine (canonical_completion_map_mor C (Ccomp:=c) f) : typeclass_instances.

#[global] Hint Extern 0 (Hom ?C (canonical_completion_reflect ?C (c:=?c) ?f)) => simple notypeclasses refine (canonical_completion_reflect_mor C (Ccomp:=c) f) : typeclass_instances.

(** The instances' proof of (K3): a dense-initial descent law — the
    [ufm_dense_initial] / [dense_locally_initial] cancellation — applied to
    the naturality square of the unit yields 𝓜-preservation. *)
Lemma dense_initial_descent_map_ini@{u} C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}
  : (∀ (S T V:set@{u}) (FS:Fib C S) (FT:Fib C T) (FV:Fib C V) (f:S ⇾ T) (g:T ⇾ V),
       Dense f → Hom C f → Hom C g → Rfl C (g ∘ f) → Ini C g)
  → CanonicalCompletionMapInitial C (Ccomp:=Ccomp).
Proof. intros descent. split.
  intros X Y FX FY HX HY f Ini0.
  apply (descent _ _ _ _ _ _ (canonical_completion_unit C (c:=Ccomp) X)); try exact _.
  now rew (canonical_completion_unit_natural C f).
Qed.

(** The canonical unit is a pair completion — the Ini-test record, with the
    reflect datum the Rfl-strength field restricted along [initial_rfl]. *)
Lemma canonical_completion_pair_compl@{u} C `{H:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}
  (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : PairCompletion C (canonical_completion_unit C X).
Proof. split.
+ exact (canonical_completion_hausdorff C X).
+ exact (canonical_completion_unit_ini C X).
+ exact (canonical_completion_unit_dense C X).
+ intros Z FZ f HD HI. exact (canonical_completion_reflect_mor C f).
+ intros Z FZ f HD HI. exact (canonical_completion_reflect_spec C f).
Qed.
#[global] Hint Extern 0 (PairCompletion ?C (canonical_completion_unit ?C (c:=?c) ?X)) => simple notypeclasses refine (canonical_completion_pair_compl C (Ccomp:=c) X) : typeclass_instances.


#[global] Hint Extern 4 (Continuous             (XN:=fmap ?C 𝐀𝐓𝐨𝐩 ?FX) (YN:=fmap ?C 𝐀𝐓𝐨𝐩 ?FY) ?f) => simple notypeclasses refine (hom_map C 𝐀𝐓𝐨𝐩 (FX:=FX) (FY:=FY) f) : typeclass_instances.
#[global] Hint Extern 4 (ContinuouslyReflecting (XN:=fmap ?C 𝐀𝐓𝐨𝐩 ?FX) (YN:=fmap ?C 𝐀𝐓𝐨𝐩 ?FY) ?f) => simple notypeclasses refine (rfl_map C 𝐀𝐓𝐨𝐩 (FX:=FX) (FY:=FY) f) : typeclass_instances.
#[global] Hint Extern 4 (ContinuouslyInitial    (XN:=fmap ?C 𝐀𝐓𝐨𝐩 ?FX) (YN:=fmap ?C 𝐀𝐓𝐨𝐩 ?FY) ?f) => simple notypeclasses refine (ini_map C 𝐀𝐓𝐨𝐩 (FX:=FX) (FY:=FY) f) : typeclass_instances.
#[global] Hint Extern 4 (ContinuouslyEmbedding  (XN:=fmap ?C 𝐀𝐓𝐨𝐩 ?FX) (YN:=fmap ?C 𝐀𝐓𝐨𝐩 ?FY) ?f) => simple notypeclasses refine (emb_map C 𝐀𝐓𝐨𝐩 (FX:=FX) (FY:=FY) f) : typeclass_instances.
#[global] Hint Extern 4 (@Topology ?X (fmap ?C 𝐀𝐓𝐨𝐩 ?FX)) => simple notypeclasses refine (pmap_obj (D:=𝐀𝐓𝐨𝐩) (DD:=atop_classes) (FX:=FX) _) : typeclass_instances.


Section theory.
  Universes u.
  Context C `{HM:!PairMorphism@{u} C 𝐀𝐓𝐨𝐩 (CD:=CD) (U:=U)}.

  Context `{H:@PairCompletion C _ _ HM X Y FX FY ι PCR}.

  Local Instance pair_completion_obj_X : Obj C X.  Proof. now pose proof _ : Ini C ι. Qed.
  Local Instance pair_completion_obj_Y : Obj C Y.  Proof. now pose proof _ : Ini C ι. Qed.

  (** The universal extension arrow is automatically dense and unique. *)  
  Section reflect_map_dense.
    Context {Z:set@{u}} {FZ:Fib C Z} {f:X ⇾ Z} `{!Dense f, !Ini C f}.

    Local Abbreviation g := (pair_completion_reflect_initial C ι f).

    Lemma pair_completion_reflect_initial_dense : Dense g.
    Proof. apply (Dense_factor_right f). now rew (pair_completion_reflect_initial_spec C _ _). Qed.

    Lemma pair_completion_reflect_initial_unique (h:Z ⇾ Y) `{!Hom C h} : h ∘ f = ι ⊸ h = g.
    Proof. now rew <-(cont_dense_epi h g f), (pair_completion_reflect_initial_spec C _ _). Qed.
  End reflect_map_dense.

  (** Completions are complete. *)
  Local Instance pair_completion_inverse : PairCompleteInverse C Y
    := λ Z FZ f Hf1 Hf2, pair_completion_reflect_initial C ι (f ∘ ι).

  Lemma pair_completion_complete : CompleteObj C Y.
  Proof. split; try exact _; intros Z FZ f Hf1 Hf2;
    unfold pair_completion_reflect_initial, pair_completion_inverse.
  + exact _.
  + apply (cont_dense_epi _ _ ι). exact (pair_completion_reflect_initial_spec C ι (f ∘ ι)).
  Qed.
End theory.
#[global] Hint Extern 11 (Obj ?C ?X) =>
  match goal with
  | H : PairCompletion C (X:=X) _ |- _ => simple notypeclasses refine (pair_completion_obj_X C (H:=H))
  | H : PairCompletion C (Y:=X) _ |- _ => simple notypeclasses refine (pair_completion_obj_Y C (H:=H))
  end : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (pair_completion_reflect_initial ?C _ _))) => simple notypeclasses refine (pair_completion_reflect_initial_dense C) : typeclass_instances.

Coercion pair_completion_inverse : PairCompletion >-> PairCompleteInverse.
#[global] Hint Extern 4 (PairCompleteInverse ?C ?Y) =>
  match goal with H : PairCompletion C (Y:=Y) _ |- _ => exact H end : typeclass_instances.
Coercion pair_completion_complete : PairCompletion >-> CompleteObj.

Coercion complete_obj_obj `{H:CompleteObj C (X:=X)} : Obj C X.  Proof. refine (pair_completion_obj_X C (H:=H)). Qed.

(** For CompleteObj, the Hausdorff axiom is redundant. *)
Section alt_Build_CompleteObj.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  
  Context {X:set@{u}} {FX:Fib C X} {HX:Obj C X} {Ci:PairCompleteInverse C X}.
  #[local] Hint Extern 0 (Inverse ?f) => exact (pair_completion_reflect_initial C (id_fun X) f) : typeclass_instances.
  
  Context (P:∀ Y (FY:Fib C Y) (f:X ⇾ Y) `{!Ini C f} `{!Dense f}, (Hom C f⁻¹ ∧ f⁻¹ ∘ f = id_fun X)%sprop).
  
  Lemma alt_Build_CompleteObj : CompleteObj C X.
  Proof. enough (Hausdorff X) by (split; try exact _; apply P).
    refine (reflects_hausdorff (canonical_completion_unit C X)); try exact _; try exact _.
    pose proof P _ _ (η X) _ _ as [Hf1 Hf2].
    apply (injective_factor _ (η X)⁻¹). now rew Hf2.
  Qed.
End alt_Build_CompleteObj.


(** Completeness transfers along dense initial maps out of a complete object:
    invert a test [g : Y ⇾ Z] by pulling it back along [f], inverting at [X],
    and returning through [f]. *)
Section dense_initial_complete.
  Universes u.
  Context C `{HM:!PairMorphism@{u} C 𝐀𝐓𝐨𝐩 (CD:=CD) (U:=U)}.
  Context {X:set@{u}} {FX:Fib C X} {Ci:PairCompleteInverse C X} {HX:CompleteObj C X}.
  Context {Y:set@{u}} {FY:Fib C Y} `{!Hausdorff Y}.
  Context (f:X ⇾ Y) `{!Dense f, !Ini C f}.

  Definition dense_initial_complete_inverse : PairCompleteInverse@{u} C Y
    := λ Z FZ g H₁ H₂, f ∘ pair_completion_reflect_initial C (id_fun X) (g ∘ f).

  Lemma dense_initial_complete : CompleteObj C Y (Ci:=dense_initial_complete_inverse).
  Proof. split; try exact _; intros Z FZ g H₁ H₂;
    unfold pair_completion_reflect_initial, dense_initial_complete_inverse; [ exact _ |].
    rew <-(cont_dense_epi _ _ f).
    change ( f ∘ (pair_completion_reflect_initial C (id_fun X) (g ∘ f) ∘ (g ∘ f)) = f ).
    now rew (pair_completion_reflect_initial_spec C (id_fun X) (g ∘ f)).
  Qed.
End dense_initial_complete.

#[global] Hint Extern 0 (PairCompleteInverse ?C (canonical_completion ?C (c:=?c) ?X)) => simple notypeclasses refine (canonical_completion_pair_compl C (Ccomp:=c) X) : typeclass_instances.
Lemma canonical_completion_complete@{u} `{H:CanonicalCompletion@{u} C (Ccomp:=Ccomp)} {X:set@{u}} {FX:Fib C X} {HX:Obj C X}
  : CompleteObj C (canonical_completion C X).
Proof. exact (pair_completion_complete C). Qed.
#[global] Hint Extern 0 (CompleteObj ?C (canonical_completion ?C _)) => simple notypeclasses refine canonical_completion_complete : typeclass_instances.
#[global] Hint Extern 0 (Obj ?C (canonical_completion ?C _)) => simple notypeclasses refine canonical_completion_complete : typeclass_instances.

Lemma canonical_completion_reflect_dense@{u} `{H:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}
  {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {f:X ⇾ Y} `{!Dense f, !Rfl C f} : Dense (canonical_completion_reflect C f).
Proof. apply (Dense_factor_right f). now rew (canonical_completion_reflect_spec C f). Qed.
#[global] Hint Extern 2 (Dense (func_op (canonical_completion_reflect _ _))) => simple notypeclasses refine canonical_completion_reflect_dense : typeclass_instances.

(** Firmness, μ-free: 𝒞 inverts tests, with inverse the reflect of the
    composite test [η Z ∘ f].  Initiality of [𝒞₁ f] and of the reflect then
    follows by the inversion duality — no 𝓜-preservation kit item and no
    dense-initial descent side condition.  (T6 for the canonical completion.) *)
Section canonical_invert_tests.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Local Abbreviation 𝒞₁ := (canonical_completion_map _ (c:=Ccomp)).
  Local Abbreviation R := (canonical_completion_reflect _ (c:=Ccomp)).
  Local Abbreviation unit_natural := (canonical_completion_unit_natural C _).
  Local Abbreviation reflect_spec := (canonical_completion_reflect_spec C _).

  Context {X Z:set@{u}} {FX:Fib C X} {FZ:Fib C Z} (f:X ⇾ Z) `{!Dense f, !Ini C f}.

  Local Instance canonical_completion_test_inverse : Inverse (𝒞₁ f) := R (η Z ∘ f).
  Local Instance canonical_completion_test_inverse_inverse : Inverse (R (η Z ∘ f)) := 𝒞₁ f.

  Local Instance canonical_completion_test_bijective : Bijective (𝒞₁ f).
  Proof. apply alt_Build_Bijective; unfold inverse, canonical_completion_test_inverse.
  + apply (cont_dense_epi _ _ (η X)). change (R (η Z ∘ f) ∘ (𝒞₁ f ∘ η X) = η X).
    rew unit_natural. exact reflect_spec.
  + apply (cont_dense_epi _ _ (η Z ∘ f)). change ( 𝒞₁ f ∘ (R (η Z ∘ f) ∘ (η Z ∘ f)) = η Z ∘ f ).
    rew reflect_spec. exact unit_natural.
  Qed.

  Local Instance canonical_completion_test_inverse_bijective : Bijective (R (η Z ∘ f)).
  Proof. now change (Bijective (𝒞₁ f)⁻¹). Qed.

  Local Instance canonical_completion_map_rfl : Rfl C (𝒞₁ f).
  Proof. now change (Rfl C (R (η Z ∘ f))⁻¹). Qed.

  Local Instance canonical_completion_map_emb : Emb C (𝒞₁ f).
  Proof. pose proof canonical_completion_test_bijective.
    rew (embed_split_iff _). split; [| exact _ ].
    rew (initial_split_iff (𝒞₁ f)). now split.
  Qed.

  Local Instance canonical_completion_test_inverse_emb : Emb C (R (η Z ∘ f)).
  Proof. pose proof canonical_completion_map_emb. now change (Emb C (𝒞₁ f)⁻¹). Qed.

  Lemma canonical_completion_reflect_alt : R (η Z ∘ f) ∘ η Z = R f.
  Proof. apply (cont_dense_epi _ _ f). change (R (η Z ∘ f) ∘ (η Z ∘ f) = R f ∘ f).
    now rew reflect_spec.
  Qed.

  Lemma canonical_completion_reflect_initial : Ini C (R f).
  Proof. pose proof canonical_completion_test_inverse_emb. now rew <-canonical_completion_reflect_alt. Qed.
End canonical_invert_tests.
#[global] Hint Extern 2 (Ini ?C (canonical_completion_reflect ?C (c:=?c) ?f)) => simple notypeclasses refine (canonical_completion_reflect_initial C f) : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (canonical_completion_reflect ?C (c:=?c) ?f)) => simple notypeclasses refine (initial_rfl (Hf:=canonical_completion_reflect_initial C f)) : typeclass_instances.

(** A bijective section of the unit makes X complete. *)
Section unit_bijective.
  Universes u.
  Context C `{H:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Context {X:set@{u}} {FX:Fib C X} {HX:Obj C X} `{!Inverse (η X), !Bijective (η X)}.

  Local Instance unit_bijective_hausdorff : Hausdorff X.
  Proof. exact (reflects_hausdorff (Y:=𝒞 X) (η X)). Qed.

  Local Instance unit_bijective_inverse_dense : Dense (η X)⁻¹.
  Proof. exact (weakly_surjective_dense _). Qed.

  Local Instance unit_bijective_complete_inverse : PairCompleteInverse@{u} C X
    := dense_initial_complete_inverse C (η X)⁻¹.

  Lemma unit_bijective_complete : CompleteObj C X.
  Proof. exact (dense_initial_complete C _). Qed.
End unit_bijective.

(** A merely *continuous* retraction of the unit suffices. *)
Section unit_retract.
  Universes u.
  Context C `{H:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Context {X:set@{u}} {FX:Fib C X} {HX:Obj C X} (r:𝒞 X ⇾ X) `{!Continuous r} (Er:r ∘ η X = id_fun X).

  #[local] Hint Extern 0 (Inverse (η X)) => exact r : typeclass_instances.

  Local Instance unit_retract_bij : Bijective (η X).
  Proof. apply alt_Build_Bijective.
  + exact Er.
  + apply (cont_dense_epi _ _ (η X)).
    change (η X ∘ (r ∘ η X) = η X). now rew Er.
  Qed.

  Local Instance unit_retract_complete_inverse : PairCompleteInverse C X := unit_bijective_complete_inverse C.
  Lemma unit_retract_complete : CompleteObj C X.
  Proof. exact (unit_bijective_complete C). Qed.
End unit_retract.

(** T5 (essential uniqueness): any completion of X is isomorphic to the
    canonical one by an initial comparison iso, and T6 follows: reflects of
    initial tests are initial. *)
Section completion_compare.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Context `{H:@PairCompletion C _ _ _ X Y FX FY ι RPC}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Local Abbreviation R := (canonical_completion_reflect _ (c:=Ccomp)).

  Local Abbreviation p := (pair_completion_reflect_initial C ι (η X)).

  #[local] Hint Extern 0 (Inverse p) => exact (R ι) : typeclass_instances.
  #[local] Hint Extern 0 (Inverse (R ι)) => exact p : typeclass_instances.

  Local Instance completion_compare_bijective : Bijective p.
  Proof. apply alt_Build_Bijective; unfold inverse.
  + apply (cont_dense_epi _ _ (η X)). change (R ι ∘ (p ∘ η X) = η X).
    rew (pair_completion_reflect_initial_spec C _ _).
    exact (canonical_completion_reflect_spec _ _).
  + apply (cont_dense_epi _ _ ι). change (p ∘ (R ι ∘ ι) = ι).
    rew (canonical_completion_reflect_spec _ _).
    exact (pair_completion_reflect_initial_spec C _ _).
  Qed.

  Local Instance completion_compare_bijective_back : Bijective (R ι).
  Proof. now change (Bijective p⁻¹). Qed.

  Local Instance completion_compare_emb : Emb C p.
  Proof. pose proof completion_compare_bijective.
    rew (embed_split_iff _); split; [| exact _].
    rew (initial_split_iff _); split; try exact _.
    now change (Rfl C (R ι)⁻¹).
  Qed.

  Lemma pair_completion_reflect_initial_alt {Z:set@{u}} {FZ:Fib C Z} (f:X ⇾ Z) `{!Dense f, !Ini C f}
    : p ∘ R f = pair_completion_reflect_initial C ι f.
  Proof. apply (cont_dense_epi _ _ f). change ( p ∘ R f ∘ f) with (p ∘ (R f ∘ f)).
    rew [ (canonical_completion_reflect_spec C f) | (pair_completion_reflect_initial_spec C ι f) ].
    exact (pair_completion_reflect_initial_spec C ι (η X)).
  Qed.

  Lemma pair_completion_reflect_initial_initial {Z:set@{u}} {FZ:Fib C Z} (f:X ⇾ Z) `{!Dense f, !Ini C f}
    : Ini C (pair_completion_reflect_initial C ι f).
  Proof. pose proof completion_compare_emb. now rew <-(pair_completion_reflect_initial_alt f). Qed.
End completion_compare.
#[global] Hint Extern 2 (Ini ?C (pair_completion_reflect_initial ?C ?ι ?f)) => simple notypeclasses refine (pair_completion_reflect_initial_initial C (ι:=ι) f) : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (pair_completion_reflect_initial ?C ?ι ?f)) => simple notypeclasses refine (initial_rfl (Hf:=pair_completion_reflect_initial_initial C (ι:=ι) f)) : typeclass_instances.

(** The UP extends to Rfl Dense tests: the canonical completion serves
    reflecting tests natively, and re-fibering routes an arbitrary pair
    completion through it — mirror of [completion_reflect] /
    [local_completion_reflect]. *)
Section pair_completion_reflect.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Context `{H:@PairCompletion C _ _ _ X Y FX FY ι RPC}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Local Abbreviation 𝒞₁ := (canonical_completion_map _ (c:=Ccomp)).
  Local Abbreviation R := (canonical_completion_reflect _ (c:=Ccomp)).
  Context {Z:set@{u}} {FZ:Fib C Z} (f:X ⇾ Z) `{!Dense f, !Rfl C f}.

  Definition pair_completion_reflect : Z ⇾ Y
    := pair_completion_reflect_initial C ι (η Y ∘ ι) ∘ 𝒞₁ ι ∘ R f.
  Local Abbreviation g := pair_completion_reflect.

  Lemma pair_completion_reflect_mor : Hom C g.
  Proof. now unfold g. Qed.

  Lemma pair_completion_reflect_spec : pair_completion_reflect ∘ f = ι.
  Proof.
    change ( pair_completion_reflect_initial C ι (η Y ∘ ι) ∘ (𝒞₁ ι ∘ (R f ∘ f)) = ι ).
    rew (canonical_completion_reflect_spec C f), (canonical_completion_unit_natural C ι).
    exact (pair_completion_reflect_initial_spec C _ _).
  Qed.

  Lemma pair_completion_reflect_dense : Dense g.
  Proof. apply (Dense_factor_right f). now rew pair_completion_reflect_spec. Qed.
End pair_completion_reflect.
Arguments pair_completion_reflect C {CD U HM Ccomp Hc X Y FX FY} ι {RPC H Z FZ} f {Dense0 Rfl0}.
Arguments pair_completion_reflect_mor C {CD U HM Ccomp Hc X Y FX FY} ι {RPC H Z FZ} f {Dense0 Rfl0}.
Arguments pair_completion_reflect_dense C {CD U HM Ccomp Hc X Y FX FY} ι {RPC H Z FZ} f {Dense0 Rfl0}.
#[global] Hint Extern 2 (Hom ?C (pair_completion_reflect ?C ?ι ?f)) => simple notypeclasses refine (pair_completion_reflect_mor C ι f) : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (pair_completion_reflect ?C ?ι ?f))) => simple notypeclasses refine (pair_completion_reflect_dense C ι f) : typeclass_instances.

(** At an initial test the two reflects agree, and the Rfl-reflect is
    initial — mirrors [completion_reflect_equal] / [completion_reflect_is_initial]. *)
Section pair_completion_reflect_initial_tests.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Context `{H:@PairCompletion C _ _ _ X Y FX FY ι RPC}.
  Context {Z:set@{u}} {FZ:Fib C Z} (f:X ⇾ Z) `{!Dense f, !Ini C f}.

  Lemma pair_completion_reflect_equal : pair_completion_reflect C ι f = pair_completion_reflect_initial C ι f.
  Proof. apply (cont_dense_epi _ _ f).
    now rew [ (pair_completion_reflect_spec C (ι:=ι) f) | (pair_completion_reflect_initial_spec C ι f) ].
  Qed.

  Lemma pair_completion_reflect_is_initial : Ini C (pair_completion_reflect C ι f).
  Proof. now rew pair_completion_reflect_equal. Qed.
End pair_completion_reflect_initial_tests.
#[global] Hint Extern 2 (Ini ?C (pair_completion_reflect ?C ?ι ?f)) => simple notypeclasses refine (pair_completion_reflect_is_initial C (ι:=ι) f) : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (pair_completion_reflect ?C ?ι ?f)) => simple notypeclasses refine (initial_rfl (Hf:=pair_completion_reflect_is_initial C (ι:=ι) f)) : typeclass_instances.

(** The UP of a complete object, at Rfl Dense tests: the complete-inverse
    kit — mirror of [complete_inverse] / [local_complete_inverse]. *)
Section complete_obj_theory.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Context {W:set@{u}} {FW:Fib C W} {Ci:PairCompleteInverse C W} {HW:CompleteObj C W}.

  Section invert_tests.
    Context {Z:set@{u}} {FZ:Fib C Z} (u:W ⇾ Z) `{!Dense u, !Rfl C u}.

    Definition complete_obj_inverse : Z ⇾ W := pair_completion_reflect C (id_fun W) u.
    #[local] Hint Extern 2 (Inverse complete_obj_inverse) => exact u : typeclass_instances.

    Lemma complete_obj_inverse_hom : Hom C complete_obj_inverse.
    Proof. now unfold complete_obj_inverse. Qed.

    Lemma complete_obj_inverse_spec : complete_obj_inverse ∘ u = id_fun W.
    Proof. exact (pair_completion_reflect_spec C (ι:=id_fun W) u). Qed.

    Lemma complete_obj_inverse_surjective : Surjective complete_obj_inverse.
    Proof. exact complete_obj_inverse_spec. Qed.

    Lemma complete_obj_inverse_dense : Dense complete_obj_inverse.
    Proof. apply (Dense_factor_right u). now rew complete_obj_inverse_spec. Qed.
  End invert_tests.

  (** At an initial test with Hausdorff codomain the inverse is two-sided. *)
  Section invert_tests_initial.
    Context {Z:set@{u}} {FZ:Fib C Z} (u:W ⇾ Z) `{!Dense u, !Ini C u} `{!Hausdorff Z}.

    #[local] Hint Extern 2 (Inverse (complete_obj_inverse u)) => exact u : typeclass_instances.
    #[local] Hint Extern 2 (Hom _ (complete_obj_inverse u)) => simple notypeclasses refine (complete_obj_inverse_hom u) : typeclass_instances.

    Lemma complete_obj_inverse_section : u ∘ complete_obj_inverse u = id_fun Z.
    Proof. apply (cont_dense_epi _ _ u).
      change (u ∘ (complete_obj_inverse u ∘ u) = u).
      now rew (complete_obj_inverse_spec u).
    Qed.

    Local Instance complete_obj_inverse_bij : Bijective (complete_obj_inverse u).
    Proof. apply alt_Build_Bijective; unfold inverse.
    + exact complete_obj_inverse_section.
    + exact (complete_obj_inverse_spec u).
    Qed.

    Lemma complete_obj_inverse_bij_back : Bijective u (inv:=complete_obj_inverse u).
    Proof. now apply flip_bijection. Qed.

    Local Instance complete_obj_inverse_emb : Emb C (complete_obj_inverse u).
    Proof. pose proof complete_obj_inverse_bij.
      rew (embed_split_iff _). split; [| exact _ ].
      exact (pair_completion_reflect_is_initial C (ι:=id_fun W) u).
    Qed.
  End invert_tests_initial.
End complete_obj_theory.
#[global] Hint Extern 2 (Hom ?C (complete_obj_inverse ?C ?u)) => simple notypeclasses refine (complete_obj_inverse_hom C u) : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (complete_obj_inverse ?C ?u))) => simple notypeclasses refine (complete_obj_inverse_dense C u) : typeclass_instances.
#[global] Hint Extern 2 (Inverse (complete_obj_inverse ?C ?u)) => exact u : typeclass_instances.
#[global] Hint Extern 2 (Surjective (complete_obj_inverse ?C ?u)) => simple notypeclasses refine (complete_obj_inverse_surjective C u) : typeclass_instances.
#[global] Hint Extern 2 (Bijective (complete_obj_inverse ?C ?u)) => simple notypeclasses refine (complete_obj_inverse_bij C u) : typeclass_instances.
#[global] Hint Extern 2 (Bijective _ (inv:=complete_obj_inverse ?C ?u)) => simple notypeclasses refine (complete_obj_inverse_bij_back C u) : typeclass_instances.
#[global] Hint Extern 2 (Surjective _ (inv:=complete_obj_inverse ?C ?u)) => simple notypeclasses refine (complete_obj_inverse_bij_back C u) : typeclass_instances.
#[global] Hint Extern 2 (Emb ?C (complete_obj_inverse ?C ?u)) => simple notypeclasses refine (complete_obj_inverse_emb C u) : typeclass_instances.
#[global] Hint Extern 2 (Ini ?C (complete_obj_inverse ?C ?u)) => simple notypeclasses refine (complete_obj_inverse_emb C u) : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (complete_obj_inverse ?C ?u)) => simple notypeclasses refine (complete_obj_inverse_emb C u) : typeclass_instances.

(** (η X)⁻¹ for complete X: the unit is a test out of X, inverted by
    completeness.  Low priority, so the μ-form wins at η (𝒞 X). *)
#[global] Hint Extern 8 (Inverse (canonical_completion_unit ?C (c:=?c) ?X)) => simple notypeclasses refine (complete_obj_inverse C (canonical_completion_unit C (c:=c) X)) : typeclass_instances.

(** T11: the extension operator — extend a Hom morphism on a dense reflecting
    subobject to a complete codomain; mirror of [ufm_cont_ext] / [wc_cont_ext]. *)
Section canonical_completion_ext.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Local Abbreviation 𝒞₁ := (canonical_completion_map _ (c:=Ccomp)).
  Local Abbreviation R := (canonical_completion_reflect _ (c:=Ccomp)).

  Context {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} (ι:X ⇾ Y) `{!Dense ι, !Rfl C ι}.
  Context {Z:set@{u}} {FZ:Fib C Z} (f:X ⇾ Z) `{!Hom C f} {Ci:PairCompleteInverse C Z} {HZ:CompleteObj C Z}.

  Definition canonical_completion_ext : Y ⇾ Z := (η Z)⁻¹ ∘ 𝒞₁ f ∘ R ι.
  Local Abbreviation g := canonical_completion_ext.

  Lemma canonical_completion_ext_mor : Hom C g.
  Proof. now unfold canonical_completion_ext. Qed.
  #[local] Hint Extern 2 (Hom _ canonical_completion_ext) => simple notypeclasses refine canonical_completion_ext_mor : typeclass_instances.

  Lemma canonical_completion_ext_spec : g ∘ ι = f.
  Proof.
    change ( (η Z)⁻¹ ∘ (𝒞₁ f ∘ (R ι ∘ ι)) = f ).
    rew (canonical_completion_reflect_spec C ι).
    rew (canonical_completion_unit_natural C f).
    change ( ((η Z)⁻¹ ∘ η Z) ∘ f = f ).
    now rew (bijective (η Z)).
  Qed.

  Lemma canonical_completion_ext_dense `{!Dense f} : Dense g.
  Proof. apply (Dense_factor_right ι). now rew canonical_completion_ext_spec. Qed.

  (** Together with [_mor] and [_spec], at [ι := η X] this is the
      universal-arrow property of the unit: the canonical completion is
      (object-wise) left adjoint to the inclusion of complete objects. *)
  Lemma canonical_completion_ext_unique (h:Y ⇾ Z) `{!Hom C h} : h ∘ ι = f ⊸ h = g.
  Proof. now rew <-(cont_dense_epi h g ι), canonical_completion_ext_spec. Qed.
End canonical_completion_ext.
Arguments canonical_completion_ext C {CD U HM Ccomp Hc X Y FX FY} ι {Dense0 Rfl0 Z FZ} f {Hom0 Ci HZ}.
Arguments canonical_completion_ext_spec C {CD U HM Ccomp Hc X Y FX FY} ι {Dense0 Rfl0 Z FZ} f {Hom0 Ci HZ}.
#[global] Hint Extern 2 (Hom ?C (canonical_completion_ext ?C ?ι ?f)) => simple notypeclasses refine (canonical_completion_ext_mor C ι f) : typeclass_instances.
#[global] Hint Extern 2 (Dense (func_op (canonical_completion_ext ?C ?ι ?f))) => simple notypeclasses refine (canonical_completion_ext_dense C ι f) : typeclass_instances.

(** With initial data and (K3), the extension is initial. *)
Section canonical_completion_ext_initial.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)} `{Hk:!CanonicalCompletionMapInitial C}.
  Context {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} (ι:X ⇾ Y) `{!Dense ι, !Ini C ι}.
  Context {Z:set@{u}} {FZ:Fib C Z} (f:X ⇾ Z) `{!Ini C f} {Ci:PairCompleteInverse C Z} {HZ:CompleteObj C Z}.

  Lemma canonical_completion_ext_initial : Ini C (canonical_completion_ext C ι f).
  Proof. now unfold canonical_completion_ext. Qed.
End canonical_completion_ext_initial.
#[global] Hint Extern 2 (Ini ?C (canonical_completion_ext ?C ?ι ?f)) => simple notypeclasses refine (canonical_completion_ext_initial C ι f) : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (canonical_completion_ext ?C ?ι ?f)) => simple notypeclasses refine (initial_rfl (Hf:=canonical_completion_ext_initial C ι f)) : typeclass_instances.

(** The canonical completion is an idempotent monad (𝒞, η, μ) *)
Section canonical_completion_theory.
  Universes u.
  Context C `{H:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Local Abbreviation 𝒞₁ := (canonical_completion_map _ (c:=Ccomp)).
  Local Abbreviation R := (canonical_completion_reflect _ (c:=Ccomp)).

  Definition canonical_completion_multiply (X:set@{u}) {FX:Fib C X} {HX:Obj C X}
    : 𝒞 (𝒞 X) ⇾ 𝒞 X := R (η (𝒞 X) ∘ η X).
  Local Abbreviation μ := canonical_completion_multiply.

  Lemma canonical_completion_multiply_spec (X:set@{u}) {FX:Fib C X} {HX:Obj C X}
    : μ X ∘ (η (𝒞 X) ∘ η X) = η X.
  Proof. exact (canonical_completion_reflect_spec C (η (𝒞 X) ∘ η X)). Qed.

  Local Instance canonical_completion_multiply_hom (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : Hom C (μ X).  Proof. now unfold μ. Qed.
  Local Instance canonical_completion_multiply_dense (X:set@{u}) {FX:Fib C X} {HX:Obj C X} : Dense (μ X).  Proof. now unfold μ. Qed.

  Local Abbreviation unit_natural := (canonical_completion_unit_natural C _).

  (** 𝒞 is a functor. *)  
  Lemma canonical_completion_map_id (X:set@{u}) {FX:Fib C X} {HX:Obj C X}
    : 𝒞₁ (id_fun X) = id_fun (𝒞 X).
  Proof. apply (cont_dense_epi _ _ (η X)). exact unit_natural. Qed.

  Lemma canonical_completion_map_compose {X Y Z:set@{u}} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z}
    (f:X ⇾ Y) (g:Y ⇾ Z) `{!Hom C f} `{!Hom C g} : 𝒞₁ (g ∘ f) = 𝒞₁ g ∘ 𝒞₁ f.
  Proof. apply (cont_dense_epi _ _ (η X)). change (𝒞₁ g ∘ 𝒞₁ f ∘ η X) with (𝒞₁ g ∘ (𝒞₁ f ∘ η X)).
    rew unit_natural. change (𝒞₁ g ∘ (η Y ∘ f)) with ( (𝒞₁ g ∘ η Y) ∘ f).
    now rew unit_natural.
  Qed.

  (** Monad laws *)
  Section monad_laws.
    Context (X:set@{u}) {FX:Fib C X} {HX:Obj C X}.

    Lemma canonical_completion_left_unit : μ X ∘ η (𝒞 X) = id_fun _.
    Proof. apply (cont_dense_epi _ _ (η X)). exact (canonical_completion_multiply_spec X). Qed.

    Lemma canonical_completion_unit_comparison : η (𝒞 X) = 𝒞₁ (η X).
    Proof. apply (cont_dense_epi _ _ (η X)). now rew unit_natural. Qed.

    Lemma canonical_completion_right_unit : μ X ∘ 𝒞₁ (η X) = id_fun _.
    Proof. rew <-canonical_completion_unit_comparison. exact canonical_completion_left_unit. Qed.
  End monad_laws.

  Lemma canonical_completion_multiply_natural {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y) `{!Hom C f}
    : μ Y ∘ 𝒞₁ (𝒞₁ f) = 𝒞₁ f ∘ μ X.
  Proof. apply (cont_dense_epi _ _ (η (𝒞 X))).
    change ( μ Y ∘ (𝒞₁ (𝒞₁ f) ∘ η (𝒞 X)) = 𝒞₁ f ∘ (μ X ∘ η (𝒞 X)) ).
    rew unit_natural, (canonical_completion_left_unit _).
    change ( (μ Y ∘ η (𝒞 Y)) ∘ 𝒞₁ f = 𝒞₁ f ).
    now rew (canonical_completion_left_unit _).
  Qed.

  Section monad_laws.
    Context (X:set@{u}) {FX:Fib C X} {HX:Obj C X}.

    Lemma canonical_completion_multiply_assoc : μ X ∘ 𝒞₁ (μ X) = μ X ∘ μ (𝒞 X).
    Proof. apply (cont_dense_epi _ _ (η (𝒞 (𝒞 X)))).
      change ( μ X ∘ (𝒞₁ (μ X) ∘ η (𝒞 (𝒞 X))) = μ X ∘ (μ (𝒞 X) ∘ η (𝒞 (𝒞 X))) ).
      rew unit_natural, (canonical_completion_left_unit _).
      change ( (μ X ∘ η (𝒞 X)) ∘ μ X = μ X ).
      now rew (canonical_completion_left_unit _).
    Qed.

    Lemma canonical_completion_idempotent : η (𝒞 X) ∘ μ X = id_fun (𝒞 (𝒞 X)).
    Proof. apply (cont_dense_epi _ _ (η (𝒞 X))).
      change ( η (𝒞 X) ∘ (μ X ∘ η (𝒞 X)) = η (𝒞 X) ).
      now rew (canonical_completion_left_unit _).
    Qed.
  End monad_laws.

  #[local] Hint Extern 0 (Inverse (μ ?X)) => exact (η (𝒞 X)) : typeclass_instances.
  #[local] Hint Extern 0 (Inverse (η (𝒞 ?X))) => exact (μ X) : typeclass_instances.

  Section idempotent_monad.
    Context {X:set@{u}} {FX:Fib C X} {HX:Obj C X}.

    Local Instance canonical_completion_multiply_bij : Bijective (μ X).
    Proof. apply alt_Build_Bijective; unfold inverse.
    + exact (canonical_completion_idempotent _).
    + exact (canonical_completion_left_unit _).
    Qed.

    Local Instance canonical_completion_multiply_bij_back : Bijective (η (𝒞 X)).
    Proof. now change (Bijective (μ X)⁻¹). Qed.

    Lemma canonical_completion_multiply_emb : Emb C (μ X).
    Proof. now change (Emb C (η (𝒞 X))⁻¹). Qed.
  End idempotent_monad.

  (** Firmness, functor form: 𝒞 inverts tests.  The inverse of 𝒞₁ u is the
      Kleisli extension of the reflect, μ ∘ 𝒞₁ (R u). *)
  Section invert_tests.
    Context {X Z:set@{u}} {FX:Fib C X} {FZ:Fib C Z} (u:X ⇾ Z) `{!Dense u, !Ini C u}.

    Lemma canonical_completion_map_reflect : 𝒞₁ u ∘ R u = η Z.
    Proof. apply (cont_dense_epi _ _ u).
      change (𝒞₁ u ∘ (R u ∘ u) = η Z ∘ u).
      rew (canonical_completion_reflect_spec C u).
      exact unit_natural.
    Qed.

    Lemma canonical_completion_map_inverse_l : (μ X ∘ 𝒞₁ (R u)) ∘ 𝒞₁ u = id_fun (𝒞 X).
    Proof. apply (cont_dense_epi _ _ (η X)).
      change ( μ X ∘ 𝒞₁ (R u) ∘ (𝒞₁ u ∘ η X) = id_fun (𝒞 X) ∘ η X ).
      rew unit_natural.
      change ( μ X ∘ (𝒞₁ (R u) ∘ η Z) ∘ u = id_fun (𝒞 X) ∘ η X ).
      rew unit_natural.
      change ( (μ X ∘ η (𝒞 X)) ∘ (R u ∘ u) = id_fun (𝒞 X) ∘ η X ).
      now rew [ (canonical_completion_left_unit _) | (canonical_completion_reflect_spec C u) ].
    Qed.

    Lemma canonical_completion_map_inverse_r : 𝒞₁ u ∘ (μ X ∘ 𝒞₁ (R u)) = id_fun (𝒞 Z).
    Proof. apply (cont_dense_epi _ _ (η Z)).
      change ( 𝒞₁ u ∘ μ X ∘ (𝒞₁ (R u) ∘ η Z) = id_fun (𝒞 Z) ∘ η Z ).
      rew unit_natural.
      change ( 𝒞₁ u ∘ (μ X ∘ η (𝒞 X)) ∘ R u = id_fun (𝒞 Z) ∘ η Z ).
      rew (canonical_completion_left_unit _).
      change ( 𝒞₁ u ∘ R u = id_fun (𝒞 Z) ∘ η Z ).
      now rew canonical_completion_map_reflect.
    Qed.

    Local Instance canonical_completion_map_inverse : Inverse (𝒞₁ u) := μ X ∘ 𝒞₁ (R u).

    Lemma canonical_completion_map_bijective : Bijective (𝒞₁ u).
    Proof. apply alt_Build_Bijective; unfold inverse.
    + exact canonical_completion_map_inverse_l.
    + exact canonical_completion_map_inverse_r.
    Qed.
  End invert_tests.
End canonical_completion_theory.

(** Post-section battery for μ: the section's Local Instances re-exported as
    global hints, plus the coercion targets (Ini, Rfl) of the Emb fact, which
    hint-derived instances do not reach on their own. *)
#[global] Hint Extern 0 (Hom ?C (canonical_completion_multiply ?C (Ccomp:=?c) ?X)) => simple notypeclasses refine (canonical_completion_multiply_hom C (Ccomp:=c) X) : typeclass_instances.
#[global] Hint Extern 0 (Dense (func_op (canonical_completion_multiply ?C (Ccomp:=?c) ?X))) => simple notypeclasses refine (canonical_completion_multiply_dense C (Ccomp:=c) X) : typeclass_instances.
#[global] Hint Extern 0 (Inverse (canonical_completion_multiply ?C (Ccomp:=?c) ?X)) => exact (canonical_completion_unit C (c:=c) (canonical_completion C (c:=c) X)) : typeclass_instances.
#[global] Hint Extern 0 (Inverse (canonical_completion_unit ?C (c:=?c) (canonical_completion ?C (c:=?c) ?X))) => exact (canonical_completion_multiply C (Ccomp:=c) X) : typeclass_instances.
#[global] Hint Extern 0 (Bijective (canonical_completion_multiply ?C (Ccomp:=?c) ?X)) => simple notypeclasses refine (canonical_completion_multiply_bij C (Ccomp:=c)) : typeclass_instances.
#[global] Hint Extern 0 (Bijective (canonical_completion_unit ?C (c:=?c) (canonical_completion ?C (c:=?c) ?X))) => simple notypeclasses refine (canonical_completion_multiply_bij_back C (Ccomp:=c)) : typeclass_instances.
#[global] Hint Extern 2 (Emb ?C (canonical_completion_multiply ?C (Ccomp:=?c) ?X)) => simple notypeclasses refine (canonical_completion_multiply_emb C (Ccomp:=c)) : typeclass_instances.
#[global] Hint Extern 2 (Ini ?C (canonical_completion_multiply ?C (Ccomp:=?c) ?X)) => simple notypeclasses refine (emb_ini (Hf:=canonical_completion_multiply_emb C (Ccomp:=c))) : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (canonical_completion_multiply ?C (Ccomp:=?c) ?X)) => simple notypeclasses refine (initial_rfl (Hf:=emb_ini (Hf:=canonical_completion_multiply_emb C (Ccomp:=c)))) : typeclass_instances.

(** (K3) is equivalent to the descent law: with 𝓜-preservation, initiality
    descends along dense forward maps — the converse of
    [dense_initial_descent_map_ini].  Firmness makes 𝒞₁ f invertible for the
    dense initial f, so 𝒞₁ g = 𝒞₁ (g ∘ f) ∘ (𝒞₁ f)⁻¹ is initial, and the
    unit's naturality square brings the conclusion back to g. *)
Section map_ini_descent.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)} `{Hk:!CanonicalCompletionMapInitial C}.
  Local Abbreviation 𝒞 := (canonical_completion _ (c:=Ccomp)).
  Local Abbreviation η := (canonical_completion_unit _ (c:=Ccomp)).
  Local Abbreviation 𝒞₁ := (canonical_completion_map _ (c:=Ccomp)).
  Context {X Y Z:set@{u}} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z} {HX:Obj C X} {HY:Obj C Y} {HZ:Obj C Z}.
  Context (f:X ⇾ Y) (g:Y ⇾ Z) `{!Dense f, !Hom C f, !Hom C g, !Rfl C (g ∘ f)}.

  Lemma map_ini_dense_descent : Ini C g.
  Proof.
    assert (Ini C (g ∘ f)) as Hgf.
    { rew (initial_split_iff _). split; exact _. }
    assert (Ini C f) as Hf.
    { rew (initial_split_iff f). split; [ exact _ | exact (rp_cancel_rfl g _) ]. }
    pose (inv := canonical_completion_map_inverse C f (Ini0:=Hf)).
    pose proof (canonical_completion_map_bijective C f (Ini0:=Hf)) as Hbij.
    assert (Ini C (𝒞₁ g)) as Hg.
    { assert (𝒞₁ g = 𝒞₁ (g ∘ f) ∘ (𝒞₁ f)⁻¹) as E.
      { rew (canonical_completion_map_compose C f g).
        change (𝒞₁ g = 𝒞₁ g ∘ (𝒞₁ f ∘ (𝒞₁ f)⁻¹)).
        now rew (surjective (𝒞₁ f)). }
      rew E. exact _. }
    rew (initial_split_iff g). split; [ exact _ |].
    apply (rp_cancel_rfl (η Z)).
    rew <-(canonical_completion_unit_natural C g).
    exact _.
  Qed.
End map_ini_descent.

(** The two directions together: (K3) is exactly the descent law. *)
Lemma map_ini_descent_iff@{u} C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}
  : CanonicalCompletionMapInitial C (Ccomp:=Ccomp) ↔
    (∀ (S T V:set@{u}) (FS:Fib C S) (FT:Fib C T) (FV:Fib C V) (f:S ⇾ T) (g:T ⇾ V),
       Dense f → Hom C f → Hom C g → Rfl C (g ∘ f) → Ini C g).
Proof. split.
+ intros Hk S T V FS FT FV f g Hd Hf Hg Hgf.
  pose proof (construct_hom_X Hf). pose proof (construct_hom_Y Hf). pose proof (construct_hom_Y Hg).
  exact (map_ini_dense_descent C f g).
+ exact (dense_initial_descent_map_ini C).
Qed.

(** * Products and completion.

    With the 𝐀𝐓𝐨𝐩 leg sending the product fiber to a cartesian product
    topology, products of completions are completions and products of complete
    objects are complete: Hausdorff and density are 𝐀𝐓𝐨𝐩 facts, initiality is
    the product rule of [reflection_pair/products.v] ([pair_prod_map_ini]), and
    the reflect datum is the pairing of two extensions. *)

Local Abbreviation π₁ := (prod_proj1 _ _).
Local Abbreviation π₂ := (prod_proj2 _ _).

Section product_completion.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Context {HS:SaturatedPair@{u} C (CD:=CD)}.
  Local Abbreviation ext := (canonical_completion_ext C).

  Context {X₁ X₂ Y₁ Y₂:set@{u}} {FX₁:Fib C X₁} {FX₂:Fib C X₂} {FY₁:Fib C Y₁} {FY₂:Fib C Y₂}.
  Context {FP:Fib C (X₁ × X₂)} {HP:PairProduct C X₁ X₂ FP}.
  Context {FQ:Fib C (Y₁ × Y₂)} {HQ:PairProduct C Y₁ Y₂ FQ}.
  Context {HT:CartesianProductTopology (NX:=fmap C 𝐀𝐓𝐨𝐩 FY₁) (NY:=fmap C 𝐀𝐓𝐨𝐩 FY₂) (fmap C 𝐀𝐓𝐨𝐩 FQ)}.
  Context (ι₁:X₁ ⇾ Y₁) (ι₂:X₂ ⇾ Y₂)
    `{H₁:@PairCompletion C _ _ HM X₁ Y₁ FX₁ FY₁ ι₁ PCR₁} `{H₂:@PairCompletion C _ _ HM X₂ Y₂ FX₂ FY₂ ι₂ PCR₂}.

  Local Instance pair_product_completion_reflect : PairCompletionReflect C (prod_map (ι₁, ι₂))
    := λ Z FZ h Hini Hdense, to_prod (ext h (ι₁ ∘ π₁), ext h (ι₂ ∘ π₂)).

  Lemma pair_product_completion : PairCompletion C (prod_map (ι₁, ι₂)).
  Proof. split; try exact _; intros Z FZ h Hini Hdense;
    unfold pair_completion_reflect_initial, pair_product_completion_reflect.
  + exact _.
  + change (to_prod (ext h (ι₁ ∘ π₁) ∘ h, ext h (ι₂ ∘ π₂) ∘ h) = to_prod (ι₁ ∘ π₁, ι₂ ∘ π₂)).
    now rew [(canonical_completion_ext_spec C h (ι₁ ∘ π₁))
            |(canonical_completion_ext_spec C h (ι₂ ∘ π₂))].
  Qed.
End product_completion.

Section product_complete.
  Universes u.
  Context C `{Hc:CanonicalCompletion@{u} C (Ccomp:=Ccomp)}.
  Context {HS:SaturatedPair@{u} C (CD:=CD)}.
  Local Abbreviation ext := (canonical_completion_ext C).

  Context {X Y:set@{u}} {FX:Fib C X} {FY:Fib C Y} {FP:Fib C (X × Y)} {HP:PairProduct C X Y FP}.
  Context {HT:CartesianProductTopology (NX:=fmap C 𝐀𝐓𝐨𝐩 FX) (NY:=fmap C 𝐀𝐓𝐨𝐩 FY) (fmap C 𝐀𝐓𝐨𝐩 FP)}.
  Context `{HX:!CompleteObj C X (Ci:=CiX)} `{HY:!CompleteObj C Y (Ci:=CiY)}.

  Local Instance pair_product_complete_inverse : PairCompleteInverse C (X × Y)
    := λ Z FZ h Hini Hdense, to_prod (ext h π₁, ext h π₂).

  Lemma pair_product_complete : CompleteObj C (X × Y).
  Proof. split; try exact _; intros Z FZ h Hini Hdense;
    unfold pair_completion_reflect_initial, pair_product_complete_inverse.
  + exact _.
  + change (to_prod (ext h π₁ ∘ h, ext h π₂ ∘ h) = to_prod (π₁, π₂)).
    now rew [(canonical_completion_ext_spec C h π₁)|(canonical_completion_ext_spec C h π₂)].
  Qed.
End product_complete.
#[global] Hint Extern 2 (PairCompletionReflect ?C (func_op prod_map (?ι₁, ?ι₂))) => simple notypeclasses refine (pair_product_completion_reflect C ι₁ ι₂) : typeclass_instances.
#[global] Hint Extern 2 (PairCompletion ?C (func_op prod_map (?ι₁, ?ι₂))) => simple notypeclasses refine (pair_product_completion C ι₁ ι₂) : typeclass_instances.
#[global] Hint Extern 2 (PairCompleteInverse ?C (_ × _)) => simple notypeclasses refine (pair_product_complete_inverse C) : typeclass_instances.
#[global] Hint Extern 2 (CompleteObj ?C (_ × _)) => simple notypeclasses refine (pair_product_complete C) : typeclass_instances.
