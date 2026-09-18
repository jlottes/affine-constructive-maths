(** * Products in a reflection pair.

    A binary product in the forward construct, concretely over the product of
    sets: a fiber on [X × Y] making the projections forward and the pairing of
    forward morphisms forward.  Nothing is asked of the reflecting construct.
    In a fibered pair the forward product is the join of the two pullback
    structures, and a product in the reflecting construct would be their meet,
    which degenerates in the instances (for uniformities it is the indiscrete
    uniformity).  The reflecting class contributes only the one-way rule that
    [f × g] reflects when [f] and [g] do, and in a saturated pair that is a
    theorem ([pair_prod_map_rfl]): the maps detecting forward maps under
    precomposition are closed under products by the universal property alone,
    and saturation identifies them with the reflecting maps. *)
Require Import sprop srelations.
Require Import logic.aprop relations.
Require Import set_lambda.
Require Import interfaces.topology.
Require Import topology.base topology.interior topology.maps.
Require Import reflection_pair.base.
Require Import easy rewrite.

Local Open Scope sprop_scope.

Local Abbreviation π₁ := (prod_proj1 _ _).
Local Abbreviation π₂ := (prod_proj2 _ _).

Lemma pair_product_obj@{u} `{HP:@PairProduct@{u} C CD X Y FX FY FP} : Obj C (X × Y).
Proof. exact (construct_hom_X pair_product_proj1). Qed.
#[global] Hint Extern 10 (@Obj ?C _ _ (?X × ?Y) ?FP) =>
  match goal with H : PairProduct C X Y FP |- _ => simple notypeclasses refine (pair_product_obj (HP:=H)) end : typeclass_instances.

(** Products of morphisms.  Forward is the universal property; reflecting is
    detection through the projections; initial and embedding split. *)
Section prod_map.
  Universes u.
  Context C `{HS:@SaturatedPair@{u} C CD}.
  Context {X₁ X₂ Y₁ Y₂:set@{u}} {FX₁:Fib C X₁} {FX₂:Fib C X₂} {FY₁:Fib C Y₁} {FY₂:Fib C Y₂}.
  Context {FP:Fib C (X₁ × X₂)} {HP:PairProduct C X₁ X₂ FP}.
  Context {FQ:Fib C (Y₁ × Y₂)} {HQ:PairProduct C Y₁ Y₂ FQ}.
  Context (f:X₁ ⇾ Y₁) (g:X₂ ⇾ Y₂).

  Lemma pair_prod_map_hom `{!Hom C f, !Hom C g} : Hom C (FX:=FP) (FY:=FQ) (prod_map (f, g)).
  Proof. change (prod_map (f, g)) with (to_prod (f ∘ π₁, g ∘ π₂)).
    now apply pair_product_pairing.
  Qed.

  Lemma pair_prod_map_rfl `{!Rfl C f, !Rfl C g} : Rfl C (FX:=FP) (FY:=FQ) (prod_map (f, g)).
  Proof. apply rp_rfl_detect. intros S FS h Hh.
    change (Hom C (to_prod (π₁ ∘ h, π₂ ∘ h))).
    apply pair_product_pairing.
    + apply (rp_cancel_fwd f). now change (Hom C (π₁ ∘ (prod_map (f, g) ∘ h))).
    + apply (rp_cancel_fwd g). now change (Hom C (π₂ ∘ (prod_map (f, g) ∘ h))).
  Qed.

  Lemma pair_prod_map_ini `{!Ini C f, !Ini C g} : Ini C (FX:=FP) (FY:=FQ) (prod_map (f, g)).
  Proof. apply (initial_split_iff _). split; [ exact pair_prod_map_hom | exact pair_prod_map_rfl ]. Qed.

  Lemma pair_prod_map_emb `{!Emb C f, !Emb C g} : Emb C (FX:=FP) (FY:=FQ) (prod_map (f, g)).
  Proof. apply (embed_split_iff _). split; [ exact pair_prod_map_ini | exact _ ]. Qed.
End prod_map.
#[global] Hint Extern 2 (Hom ?C (func_op prod_map (?f, ?g))) => simple notypeclasses refine (pair_prod_map_hom C f g) : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (func_op prod_map (?f, ?g))) => simple notypeclasses refine (pair_prod_map_rfl C f g) : typeclass_instances.
#[global] Hint Extern 2 (Ini ?C (func_op prod_map (?f, ?g))) => simple notypeclasses refine (pair_prod_map_ini C f g) : typeclass_instances.
#[global] Hint Extern 2 (Emb ?C (func_op prod_map (?f, ?g))) => simple notypeclasses refine (pair_prod_map_emb C f g) : typeclass_instances.

