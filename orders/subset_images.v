Require Import abstract_algebra theory.groups theory.lattices theory.common_props.
Require Import interfaces.orders orders.orders orders.lattices orders.maps orders.suborders.
Require Import set_lambda sprop srelations logic.aprop logic.relations.
Require Export orders.subset_relations.
Require Import tactics.misc easy rewrite simplify.

Local Abbreviation id := (id_fun _).

Local Open Scope subset_scope.

(** Image and preimage *)

Import image_notation.

Lemma image_el@{u} {X Y:set@{u}} (f:X → Y) (x:X) (U:𝒫 X) : x ∊ U ⊸ f x ∊ f⁎ U.
Proof. change (x ∊ U ⊸ ∐ x', f x' = f x ⊠ x' ∊ U). rew <-(aex_ub _ x). now simplify. Qed.

Lemma image_el_alt@{u} {X Y:set@{u}} {f:X → Y} {x:X} {U:𝒫 X} : x ∊ U → f x ∊ f⁎ U.
Proof. now rew <-(image_el _ _ _). Qed.
#[global] Hint Extern 2 (apos (?f _ ∊ func_op2 image ?g _)) =>
  match f with g => simple notypeclasses refine (image_el_alt _) end : typeclass_instances.

Lemma range_el@{u} {A:Type@{u}} {Y:set@{u}} {f:A → Y} {a:A} : f a ∊ range f.
Proof. now exists a. Qed.
#[global] Hint Extern 2 (apos (?f _ ∊ func_op range ?g)) =>
  match f with g => simple notypeclasses refine range_el end : typeclass_instances.

Lemma aex_image@{u} {X Y:set@{u}} (f:X → Y) (U:𝒫 X) (P:Y ⇾ Ω)
  : (∐ y, y ∊ f⁎ U ⊠ P y) ⧟ (∐ x, x ∊ U ⊠ P (f x)).
Proof. split.
+ rew <-aex_adj; intros y. unfold_image.
  rew aex_frob_r, <-aex_adj; intros x. rew <-(aex_ub _ x).
  rew (is_fun P (f x) y : f x = y ⊸ P (f x) ⧟ P y).
  tautological.
+ rew <-aex_adj; intros x. now rew <-(aex_ub _ (f x)), <-(image_el f _ _).
Qed.

Lemma all_image@{u} {X Y:set@{u}} (f:X → Y) (U:𝒫 X) (P:Y ⇾ Ω)
  : (∏ y, y ∊ f⁎ U ⊸ P y) ⧟ (∏ x, x ∊ U ⊸ P (f x)).
Proof. apply by_contrapositive_iff. exact (aex_image f U (anot_fun ∘ P)). Qed.

Lemma image_inhabited@{u} {X Y:set@{u}} (f:X → Y) (U:𝒫 X)
  : (∐ y, y ∊ f⁎ U) ⧟ (∐ x, x ∊ U).
Proof. rew <-(aprod_unit_r (aex _)), aex_frob_r.
  exact (aex_image f U set:(λ y:Y, 𝐓)).
Qed.

Lemma image_preimage_adj@{u} {X Y:set@{u}} (f:X ⇾ Y) U V : f⁎ U ⊆ V ⧟ U ⊆ f* V.
Proof. change ( (∏ y, (∐ z, f z = y ⊠ z ∊ U) ⊸ y ∊ V) ⧟ (∏ x, x ∊ U ⊸ f x ∊ V)); split.
+ rew <-all_adj; intros x. rew (all_lb _ (f x)). rew <-(aex_ub _ x). now simplify.
+ rew <-all_adj; intros y. rew <-(aprod_adj _ _ _), (aprod_com _ _), (aprod_adj _ _ _).
  rew <-aex_adj; intros z. rew (all_lb _ z). rew <-(equal_element V (f z) y). tautological.
Qed.

Lemma preimage_image_unit@{u} {X Y:set@{u}} (f:X ⇾ Y) U : U ⊆ f* (f⁎ U).
Proof. now rew <-(image_preimage_adj _ _ _). Qed.
#[global] Hint Extern 2 (apos (?U ≤ func_op2 preimage ?f (func_op2 image (func_op ?f) ?U))) =>
  simple notypeclasses refine (preimage_image_unit _ _) : typeclass_instances.

Lemma image_preimage_counit@{u} {X Y:set@{u}} (f:X ⇾ Y) V : f⁎ (f* V) ⊆ V.
Proof. now rew (image_preimage_adj _ _ _). Qed.
#[global] Hint Extern 2 (apos (func_op2 image (func_op ?f) (func_op2 preimage ?f ?U) ≤ ?U)) =>
  simple notypeclasses refine (image_preimage_counit _ _) : typeclass_instances.

Lemma preimage_universal_image_adj@{u} {X Y:set@{u}} (f:X ⇾ Y) U V
  : f* V ⊆ U ⧟ V ⊆ ∀.[f] U.
Proof.
  rew (order_embedding_flip complement (f* V) U).
  change ((U ᗮ ⊆ f* (V ᗮ)) ⧟ (V ⊆ ∀.[f] U)).
  rew <-(image_preimage_adj f (U ᗮ) (V ᗮ)).
  rew (order_embedding_flip complement V (∀.[f] U)).
  now change ((f⁎ (U ᗮ) ⊆ V ᗮ) ⧟ (f⁎ (U ᗮ) ⊆ V ᗮ)).
Qed.

Lemma universal_image_unit@{u} {X Y:set@{u}} (f:X ⇾ Y) V : V ⊆ ∀.[f] (f* V).
Proof. now rew <-(preimage_universal_image_adj _ _ _). Qed.
#[global] Hint Extern 2 (apos (?V ≤ func_op2 universal_image (func_op ?f) (func_op2 preimage ?f ?V))) =>
  simple notypeclasses refine (universal_image_unit _ _) : typeclass_instances.

Lemma universal_image_counit@{u} {X Y:set@{u}} (f:X ⇾ Y) U : f* (∀.[f] U) ⊆ U.
Proof. now rew (preimage_universal_image_adj _ _ _). Qed.
#[global] Hint Extern 2 (apos (func_op2 preimage ?f (func_op2 universal_image (func_op ?f) ?U) ≤ ?U)) =>
  simple notypeclasses refine (universal_image_counit _ _) : typeclass_instances.

Lemma preimage_bounded_lattice_mor `{f:X ⇾ Y} : BoundedLattice_Morphism f*.
Proof. apply alt_Build_BoundedLattice_Morphism; full_tautological. Qed.
#[global] Hint Extern 2 (BoundedLattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_bounded_lattice_mor : typeclass_instances.
#[global] Hint Extern 2 (Lattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_bounded_lattice_mor : typeclass_instances.
#[global] Hint Extern 2 (MeetSemiLattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_bounded_lattice_mor : typeclass_instances.
#[global] Hint Extern 2 (JoinSemiLattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_bounded_lattice_mor : typeclass_instances.
#[global] Hint Extern 2 (BoundedJoinSemiLattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_bounded_lattice_mor : typeclass_instances.
#[global] Hint Extern 2 (Bottom_Pointed_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_bounded_lattice_mor : typeclass_instances.
#[global] Hint Extern 2 (BoundedMeetSemiLattice_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_bounded_lattice_mor : typeclass_instances.
#[global] Hint Extern 2 (Top_Pointed_Morphism (func_op preimage _)) => simple notypeclasses refine preimage_bounded_lattice_mor : typeclass_instances.

Definition preimage_order_preserving `{f:X ⇾ Y} : OrderPreserving f*.
Proof. exact (join_sl_mor_preserving _). Qed.
Global Hint Extern 2 (OrderPreserving (func_op preimage _)) => simple notypeclasses refine preimage_order_preserving : typeclass_instances.

Lemma image_join_sl_mor@{u} {X Y:set@{u}} {f:X → Y} : BoundedJoinSemiLattice_Morphism f⁎.
Proof. apply alt_Build_BoundedJoinSemiLattice_Morphism; [| full_tautological ].
  intros U V y.
  change ((∐ x, f x = y ⊠ (x ∊ U ∨ x ∊ V)) ⧟ (∐ x, f x = y ⊠ x ∊ U) ∨ (∐ x, f x = y ⊠ x ∊ V)). split.
+ rew <-aex_adj. intros x. rew (aprod_com (f x = y) _), (aprod_adj _ _ _). apply aor_elim.
  * rew <-(aorl _ _), <-(aex_ub _ x), <-(aprod_adj _ _ _). apply aprod_com.
  * rew <-(aorr _ _), <-(aex_ub _ x), <-(aprod_adj _ _ _). apply aprod_com.
+ apply aor_elim; rew <-aex_adj; intros x; rew <-(aex_ub _ x); tautological.
Qed.
Global Hint Extern 2 (BoundedJoinSemiLattice_Morphism (func_op image _)) => simple notypeclasses refine image_join_sl_mor : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Morphism (func_op image _)) => simple notypeclasses refine image_join_sl_mor : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism (func_op image _)) => simple notypeclasses refine image_join_sl_mor : typeclass_instances.

Definition image_order_preserving@{u} {X Y:set@{u}} {f:X → Y} : OrderPreserving f⁎.
Proof. exact (join_sl_mor_preserving _). Qed.
Global Hint Extern 2 (OrderPreserving (func_op image _)) => simple notypeclasses refine image_order_preserving : typeclass_instances.

Lemma range_image@{u} {X Y:set@{u}} (f:X → Y) : range f = f⁎ ⊤.
Proof. intros y. change ((∐ x, f x = y) ⧟ ∐ x, f x = y ⊠ 𝐓). now simplify. Qed.

Lemma weakly_surjective_alt@{u} {A:Type@{u}} {Y:set@{u}} (f:A → Y) `{!WeaklySurjective f} : range f = ⊤.
Proof. rew <-(above_top _). intros y.
  change (𝐓 ⊸ ∐ x, f x = y). simplify. exact (weakly_surjective f y).
Qed.

Lemma image_top@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!WeaklySurjective@{u} f}
  : f⁎ ⊤ = ⊤.
Proof. rew <-(range_image f). exact (weakly_surjective_alt f). Qed.

Lemma universal_image_meet_sl_mor@{u} {X Y:set@{u}} {f:X → Y} : BoundedMeetSemiLattice_Morphism ∀.[f].
Proof. now change (∀.[f]) with (complement ∘ f⁎ ∘ complement). Qed.
#[global] Hint Extern 2 (BoundedMeetSemiLattice_Morphism ∀.[_]) => simple notypeclasses refine universal_image_meet_sl_mor : typeclass_instances.
#[global] Hint Extern 2 (MeetSemiLattice_Morphism ∀.[_]) => simple notypeclasses refine universal_image_meet_sl_mor : typeclass_instances.
#[global] Hint Extern 2 (Top_Pointed_Morphism ∀.[_]) => simple notypeclasses refine universal_image_meet_sl_mor : typeclass_instances.

Lemma universal_image_mono@{u} {X Y:set@{u}} {f:X → Y} : OrderPreserving ∀.[f].
Proof. exact (meet_sl_mor_preserving _). Qed.
#[global] Hint Extern 2 (OrderPreserving ∀.[_]) => simple notypeclasses refine universal_image_mono : typeclass_instances.

Lemma universal_image_bot@{u} {X Y:set@{u}} (f:X → Y) : ∀.[f] ⊥ = (range f)ᗮ.
Proof. change ((f⁎ ⊤)ᗮ = (range f)ᗮ). now rew <-(range_image f). Qed.

Lemma universal_image_bot_ws@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!WeaklySurjective@{u} f}
  : ∀.[f] ⊥ = ⊥.
Proof. change ((f⁎ ⊤)ᗮ = ⊥). now rew (image_top f). Qed.

(** The projection ("Frobenius") laws hold laxly.  The converse inclusions'
    negative components would need a single disjunct chosen uniformly across
    the fiber, which the additive connectives do not supply. *)
Lemma image_meet_preimage_le@{u} {X Y:set@{u}} (f:X ⇾ Y) U V : f⁎ (U ⊓ f* V) ⊆ f⁎ U ⊓ V.
Proof. intros y.
  change ((∐ x, f x = y ⊠ (x ∊ U ∧ f x ∊ V)) ⊸ (∐ x, f x = y ⊠ x ∊ U) ∧ y ∊ V).
  rew <-aex_adj; intros x. apply aand_intro.
  + rew <-(aex_ub _ x), (aandl _ _). easy.
  + rew (aandr _ _). exact (equal_element V (f x) y).
Qed.

Lemma universal_image_join_preimage_le@{u} {X Y:set@{u}} (f:X ⇾ Y) U V : ∀.[f] U ⊔ V ⊆ ∀.[f] (U ⊔ f* V).
Proof.
  rew (order_embedding_flip complement (∀.[f] U ⊔ V) (∀.[f] (U ⊔ f* V))).
  change (f⁎ ((U ᗮ) ⊓ f* (V ᗮ)) ⊆ f⁎ (U ᗮ) ⊓ V ᗮ).
  exact (image_meet_preimage_le f (U ᗮ) (V ᗮ)).
Qed.


Import tensor_map_notation.
Import projection_notation.

Lemma weakly_surjective_id_rel@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!WeaklySurjective@{u} f}
  : id_rel Y ⊆ ⟨f,f⟩⁎ (id_rel X).
Proof. intros [y₁ y₂].
  pose proof (weakly_surjective f y₁) as [x Hx].
  change ((y₁, y₂) ∊ ⟨f,f⟩⁎ (id_rel X)) with (∐ p, ⟨f,f⟩ p = (y₁,y₂) ⊠ p ∊ id_rel X).
  rew <-(aex_ub _ (x, x)), (aprod_true_r (ltac:(now change (x=x)):(x,x) ∊ id_rel X)).
  change (y₁ = y₂ ⊸ f x = y₁ ⊠ f x = y₂). rew Hx; now simplify.
Qed.

Lemma preimage_compose@{u} {X Y Z:set@{u}} (f:X⇾Y) (g:Y⇾Z) : (g ∘ f)* = f* ∘ g*.
Proof. refl. Qed.

Lemma preimage_compose_alt@{u} {X Y Z:set@{u}} (f:X⇾Y) (g:Y⇾Z) (U:𝒫 Z) : (g ∘ f)* U = f* (g* U).
Proof. refl. Qed.

Lemma preimage_id@{u} {X:set@{u}} : (id_fun X)* = id.
Proof. refl. Qed.

Lemma preimage_id_alt@{u} {X:set@{u}} (U:𝒫 X) : id* U = U.
Proof. refl. Qed.

Lemma image_id@{u} {X:set@{u}} : (id_fun X)⁎ = id.
Proof. intros U y. change ((∐ x, x = y ⊠ x ∊ U) ⧟ y ∊ U); split.
+ rew <-aex_adj; intros x. apply equal_element.
+ rew <-(aex_ub _ y). now simplify.
Qed.
Definition image_id_alt@{u} {X:set@{u}} (U:𝒫 X) : id⁎ U = U := image_id U.

Lemma image_compose@{u} {X Y Z:set@{u}} (f:X⇾Y) (g:Y⇾Z) : (g ∘ f)⁎ = g⁎ ∘ f⁎.
Proof. intros U z.
  change ((∐ x, g (f x) = z ⊠ x ∊ U) ⧟ (∐ y, g y = z ⊠ (∐ x, f x = y ⊠ x ∊ U))).
  split.
+ rew <-aex_adj; intros x. rew <-(aex_ub _ (f x)). rew <-(aex_ub _ x). now simplify.
+ rew <-aex_adj; intros y.
  rew aex_frob_l, <-aex_adj; intros x.
  rew <-(aex_ub _ x). rew <-(aprod_assoc _ _ _).
  rew (is_fun g _ _ : f x = y ⊸ g (f x) = g y).
  now rew (aprod_com (g y = z) _), (transitivity (=) _ _ _).
Qed.
Definition image_compose_alt@{u} {X Y Z:set@{u}} (f:X⇾Y) (g:Y⇾Z) (U:𝒫 X) : (g ∘ f)⁎ U = g⁎ (f⁎ U) := image_compose _ _ _.

Lemma universal_image_id@{u} {X:set@{u}} : ∀.[id_fun X] = id.
Proof. intros U. change ((id⁎ (U ᗮ))ᗮ = U). now rew (image_id_alt (U ᗮ)). Qed.
Definition universal_image_id_alt@{u} {X:set@{u}} (U:𝒫 X) : ∀.[id] U = U := universal_image_id U.

Lemma universal_image_compose@{u} {X Y Z:set@{u}} (f:X⇾Y) (g:Y⇾Z) : ∀.[g ∘ f] = ∀.[g] ∘ ∀.[f].
Proof. intros U. change (((g ∘ f)⁎ (U ᗮ))ᗮ = (g⁎ (f⁎ (U ᗮ)))ᗮ).
  now rew (image_compose_alt f g (U ᗮ)).
Qed.
Definition universal_image_compose_alt@{u} {X Y Z:set@{u}} (f:X⇾Y) (g:Y⇾Z) (U:𝒫 X) : ∀.[g ∘ f] U = ∀.[g] (∀.[f] U) := universal_image_compose _ _ _.


Lemma image_tensor_map@{u} {X Y Z W:set@{u}} (f:X⇾Y) (g:Z⇾W) A B : ⟨f, g⟩⁎ (A ⊗ B) = f⁎ A ⊗ g⁎ B.
Proof. intros [a b].
  change ((∐ p, (f (π₁ p), g (π₂ p)) = (a, b) ⊠ p ∊ A ⊗ B) ⧟ (∐ x, f x = a ⊠ x ∊ A) ⊠ (∐ z, g z = b ⊠ z ∊ B)); split.
+ rew <-aex_adj; intros [x y]. rew [<-(aex_ub _ x) | <-(aex_ub _ y)]. full_tautological.
+ rew <-aex_adj2; intros x y. rew <-(aex_ub _ (x, y)). full_tautological.
Qed.

(** Only an inclusion: off the range of [f] the left factor holds vacuously,
    but the right factor still constrains the second coordinate. *)
Lemma universal_image_tensor_map@{u} {X Y Z W:set@{u}} (f:X⇾Y) (g:Z⇾W) A B : ∀.[f] A ⊗ ∀.[g] B ⊆ ∀.[⟨f, g⟩] (A ⊗ B).
Proof. rew <-(preimage_universal_image_adj _ _ _).
  change (f* (∀.[f] A) ⊗ g* (∀.[g] B) ⊆ A ⊗ B).
  now rew [(universal_image_counit f A)|(universal_image_counit g B)].
Qed.

Lemma image_prod_map_ub@{u} {X Y Z W:set@{u}} (f:X⇾Y) (g:Z⇾W) A B : (prod_map (f, g))⁎ (A × B) ⊆ f⁎ A × g⁎ B.
Proof. intros [a b].
  change ((∐ p:(X × Z)%set, (f (π₁ p), g (π₂ p)) = (a, b) :> (Y × W)%set ⊠ p ∊ A × B) ⊸ (∐ x, f x = a ⊠ x ∊ A) ∧ (∐ z, g z = b ⊠ z ∊ B)).
  rew <-aex_adj; intros [x y]. rew [<-(aex_ub _ x) | <-(aex_ub _ y)]. full_tautological.
Qed.

Lemma image_singleton@{u} {X Y:set@{u}} (f:X ⇾ Y) : f⁎ ∘ singleton = singleton ∘ f.
Proof. intros x y. change ( (∐ x', f x' = y ⊠ x = x') ⧟ f x = y). split.
+ rew <-aex_adj; intros x'. rew (aprod_com _ _), (aprod_adj _ _ _).
  rew ( is_fun set:(λ x, f x = y) x x' : x = x' ⊸ f x = y ⧟ f x' = y ). tautological.
+ rew <-(aex_ub _ x). now simplify.
Qed.
Definition image_singleton_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) (x:X) : f⁎ (singleton x) = singleton (f x) := image_singleton _ _.

Lemma sub_proj_image_prod@{u} {X Y:set@{u}} (U:𝒫 (X × Y)) : U ⊆ (prod_proj1 _ _)⁎ U × (prod_proj2 _ _)⁎ U.
Proof. intros p; apply aand_intro; apply image_el. Qed.


Lemma flip_image_tensor_map@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W)
  : flip ∘ ⟨f, g⟩⁎ = ⟨g, f⟩⁎ ∘ flip.
Proof. intros U [w y].
 change ( (∐ p, ⟨f, g⟩ p = (y,w) ⊠ p ∊ U) ⧟ (∐ p, ⟨g, f⟩ p = (w,y) ⊠ p ∊ flip U) ).
 split.
+ rew <-aex_adj; intros [x z]. rew <-(aex_ub _ (z, x)). full_tautological.
+ rew <-aex_adj; intros [z x]. rew <-(aex_ub _ (x, z)). full_tautological.
Qed.
Definition flip_image_tensor_map_alt@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W) A
  : flip (⟨f, g⟩⁎ A) = ⟨g, f⟩⁎ (flip A)
  := flip_image_tensor_map _ _ _.

Lemma flip_universal_image_tensor_map@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W)
  : flip ∘ ∀.[⟨f, g⟩] = ∀.[⟨g, f⟩] ∘ flip.
Proof. intros U.
  change (complement (flip (⟨f, g⟩⁎ (complement U))) = complement (⟨g, f⟩⁎ (complement (flip U)))).
  now rew (flip_image_tensor_map_alt f g (complement U)).
Qed.
Definition flip_universal_image_tensor_map_alt@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W) A
  : flip (∀.[⟨f, g⟩] A) = ∀.[⟨g, f⟩] (flip A)
  := flip_universal_image_tensor_map _ _ _.

Lemma image_preimage_pair_commute@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W)
  : ⟨id, g⟩⁎ ∘ ⟨f, id⟩* = ⟨f, id⟩* ∘ ⟨id, g⟩⁎.
Proof. intros U [x w].
  change ( (∐ p, ⟨id, g⟩ p = (x, w) ⊠ p ∊ ⟨f, id⟩* U)
          ⧟ (∐ p, ⟨id, g⟩ p = (f x, w) ⊠ p ∊ U) ). split.
+ rew <-aex_adj; intros [x' z]. rew <-(aex_ub _ (f x', z)).
  change ( (x' = x ⊠ g z = w) ⊠ (f x', z) ∊ U
            ⊸ (f x' = f x ⊠ g z = w) ⊠ (f x', z) ∊ U ).
  now rew <-(is_fun f x' x).
+ rew <-aex_adj; intros [y z]. rew <-(aex_ub _ (x, z)).
  change ( (y = f x ⊠ g z = w) ⊠ (y, z) ∊ U
            ⊸ (x = x ⊠ g z = w) ⊠ (f x, z) ∊ U ).
  rew <-(equal_element U (y, z) (f x, z) : (y = f x ⊠ z = z) ⊠ _  ⊸ _).
  simplify; tautological.
Qed.

Lemma image_preimage_pair_commute_alt@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W)
  : ⟨f, id⟩⁎ ∘ ⟨id, g⟩* = ⟨id, g⟩* ∘ ⟨f, id⟩⁎.
Proof. intros U. simplify. apply (injective flip).
  change ( flip (⟨ f, id ⟩⁎ (⟨ id, g ⟩* U)) = ⟨ g, id ⟩* (flip (⟨ f, id ⟩⁎ U)) ).
  rew (flip_image_tensor_map_alt _ _ _).
  now pose proof (image_preimage_pair_commute g f (flip U)).
Qed.

Lemma image_preimage_pair_split_l@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W)
  : ⟨f, g⟩⁎ ∘ ⟨f, g⟩* = ⟨f, id⟩⁎ ∘ ⟨f, id⟩* ∘ ⟨id, g⟩⁎  ∘ ⟨id, g⟩*.
Proof. change (⟨f, g⟩⁎ ∘ ⟨f, g⟩* = ⟨f, id⟩⁎ ∘ (⟨f, id⟩* ∘ ⟨id, g⟩⁎)  ∘ ⟨id, g⟩*).
  rew <-(image_preimage_pair_commute f g).
  change (⟨ f, g ⟩⁎ ∘ ⟨ f, g ⟩* = (⟨ f, id ⟩⁎ ∘ ⟨ id, g ⟩⁎) ∘ ⟨ f, g ⟩*).
  now rew <-(image_compose _ _).
Qed.
Definition image_preimage_pair_split_l_alt@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W) U
  : ⟨f, g⟩⁎ (⟨f, g⟩* U) = ⟨f, id⟩⁎ (⟨f, id⟩* (⟨id, g⟩⁎ (⟨id, g⟩* U)))
  := image_preimage_pair_split_l f g U.

Lemma image_preimage_pair_split_r@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W)
  : ⟨f, g⟩⁎ ∘ ⟨f, g⟩* = ⟨id, g⟩⁎  ∘ ⟨id, g⟩* ∘ ⟨f, id⟩⁎ ∘ ⟨f, id⟩*.
Proof. change (⟨f, g⟩⁎ ∘ ⟨f, g⟩* = ⟨id, g⟩⁎  ∘ (⟨id, g⟩* ∘ ⟨f, id⟩⁎) ∘ ⟨f, id⟩*).
  rew <-(image_preimage_pair_commute_alt f g).
  change (⟨ f, g ⟩⁎ ∘ ⟨ f, g ⟩* = (⟨ id, g ⟩⁎ ∘ ⟨ f, id ⟩⁎) ∘ ⟨ f, g ⟩*).
  now rew <-(image_compose _ _).
Qed.
Definition image_preimage_pair_split_r_alt@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (g:Z ⇾ W) U
  : ⟨f, g⟩⁎ (⟨f, g⟩* U) = ⟨id, g⟩⁎ (⟨id, g⟩* (⟨f, id⟩⁎ (⟨f, id⟩* U)))
  := image_preimage_pair_split_r f g U.

Lemma preimage_id_compose_distr_l@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (A:𝒫(Y ⊗ Z)) (B:𝒫(Z ⊗ W))
  : ⟨f, id⟩* (A ⋄ B) = ⟨f, id⟩* A ⋄ B .
Proof. refl. Qed.

Lemma image_id_compose_distr_l@{u} {X Y Z W:set@{u}} (f:X ⇾ Y) (A:𝒫(X ⊗ Z)) (B:𝒫(Z ⊗ W))
  : ⟨f, id⟩⁎ (A ⋄ B) = ⟨f, id⟩⁎ A ⋄ B .
Proof. intros [y w].
  change ( (∐ p, ⟨f, id⟩ p = (y, w) ⊠ (∐ z, (π₁ p, z) ∊ A ⊠ (z, π₂ p) ∊ B) )
         ⧟ (∐ z, (∐ p, ⟨ f, id ⟩ p = (y, z) ⊠ p ∊ A) ⊠ (z, w) ∊ B) ). split.
+ rew <-aex_adj; intros [x w']. rew aex_frob_l. apply aex_aimpl; intros z.
  rew <-(aex_ub _ (x, z)).
  change (  ( f x = y ⊠ w' = w ) ⊠ ((x, z) ∊ A ⊠ (z, w') ∊ B)
          ⊸ ((f x = y ⊠ z = z) ⊠ (x, z) ∊ A ) ⊠ (z, w) ∊ B ) .
  rew <-(equal_element B (z, w') (z, w)). unfold_pair_eq.
  let t := constr:(ltac:(refl):z = z) in rew [ (aprod_true_l t) | (aprod_true_r t) ].
  tautological.
+ rew <-aex_adj; intros z. rew aex_frob_r, <-aex_adj. intros [x z'].
  rew <-(aex_ub _ (x, w)), <-(aex_ub _ z').
  change (⟨ f, id ⟩ (?a, ?b)) with ( (f a, b) ).
  change ( ((f x = y ⊠ z' = z) ⊠ (x, z') ∊ A) ⊠ (z, w) ∊ B ⊸ (f x = y ⊠ w = w) ⊠ (x, z') ∊ A ⊠ (z', w) ∊ B ).
  rew <-(equal_element B (z, w) (z', w)). unfold_pair_eq.
  let t := constr:(ltac:(refl):w = w) in rew (aprod_true_r t).
  rew (symmetry_iff (=) z z'). tautological.
Qed.

Lemma preimage_id_compose_distr_r@{u} {X Y Z W:set@{u}} (f:Z ⇾ W) (A:𝒫(X ⊗ Y)) (B:𝒫(Y ⊗ W))
  : ⟨id, f⟩* (A ⋄ B) = A ⋄ ⟨id, f⟩* B.
Proof. refl. Qed.

Lemma image_id_compose_distr_r@{u} {X Y Z W:set@{u}} (f:Z ⇾ W) (A:𝒫(X ⊗ Y)) (B:𝒫(Y ⊗ Z))
  : ⟨id, f⟩⁎ (A ⋄ B) = A ⋄ ⟨id, f⟩⁎ B.
Proof. apply (injective flip).
  rew (flip_image_tensor_map_alt id f (A ⋄ B)), (flip_compose_rel_distr A B).
  rew (flip_compose_rel_distr A _), (flip_image_tensor_map_alt id f B).
  exact (image_id_compose_distr_l f (flip B) (flip A)).
Qed.

(** Moving a map across [⋄]: an image on the inner boundary of a composite
    is a preimage on the other factor. *)
Lemma image_compose_pin_l@{u} {X Y Z W:set@{u}} (f:Y ⇾ Z) (A:𝒫(X ⊗ Y)) (B:𝒫(Z ⊗ W))
  : ⟨id, f⟩⁎ A ⋄ B = A ⋄ ⟨f, id⟩* B.
Proof. intros [x w].
  change ( (∐ z, (∐ p, ⟨id, f⟩ p = (x, z) ⊠ p ∊ A) ⊠ (z, w) ∊ B)
         ⧟ (∐ y, (x, y) ∊ A ⊠ (f y, w) ∊ B) ).
  split.
+ rew <-aex_adj; intros z. rew aex_frob_r, <-aex_adj; intros [x' y].
  rew <-(aex_ub _ y).
  change (⟨ id, f ⟩ (?a, ?b)) with ( (a, f b) ). unfold_pair_eq.
  change ((x', f y) = (x, z)) with (x' = x ⊠ f y = z).
  rew <-(equal_element A (x', y) (x, y)), <-(equal_element B (z, w) (f y, w)). unfold_pair_eq.
  let t := constr:(ltac:(refl):y = y) in rew (aprod_true_r t).
  let t := constr:(ltac:(refl):w = w) in rew (aprod_true_r t).
  rew (symmetry_iff (=) z (f y)). tautological.
+ rew <-aex_adj; intros y. rew <-(aex_ub _ (f y)), <-(aex_ub _ (x, y)).
  change (⟨ id, f ⟩ (?a, ?b)) with ( (a, f b) ).
  change ((x, f y) = (x, f y)) with (x = x ⊠ f y = f y).
  let t := constr:(ltac:(refl):x = x) in rew (aprod_true_l t).
  let t := constr:(ltac:(refl):f y = f y) in rew (aprod_true_l t).
  tautological.
Qed.

Lemma image_compose_pin_r@{u} {X Y Z W:set@{u}} (f:Y ⇾ Z) (A:𝒫(X ⊗ Z)) (B:𝒫(Y ⊗ W))
  : A ⋄ ⟨f, id⟩⁎ B = ⟨id, f⟩* A ⋄ B.
Proof. apply (injective flip).
  rew [(flip_compose_rel_distr A _) | (flip_compose_rel_distr _ B)].
  rew (flip_image_tensor_map_alt f id B).
  exact (image_compose_pin_l f (flip B) (flip A)).
Qed.

Lemma preimage_compose_rel_lax@{u} {X Y Z W U V:set@{u}}
  (f:X ⇾ Y) (g:Z ⇾ W) (h:U ⇾ V) (R:𝒫 (Y ⊗ W)) (S:𝒫 (W ⊗ V))
  : ⟨f, g⟩* R ⋄ ⟨g, h⟩* S ⊆ ⟨f, h⟩* (R ⋄ S).
Proof. intros [a c].
  change ( (∐ b, (f a, g b) ∊ R ⊠ (g b, h c) ∊ S) ⊸ (∐ b', (f a, b') ∊ R ⊠ (b', h c) ∊ S) ).
  rew <-aex_adj; intros b. rew <-(aex_ub _ (g b)). tautological.
Qed.

Lemma image_compose_rel_lax@{u} {X Y Z W U V:set@{u}}
  (f:X ⇾ Y) (g:Z ⇾ W) (h:U ⇾ V) (R:𝒫 (X ⊗ Z)) (S:𝒫 (Z ⊗ U))
  : ⟨f, h⟩⁎ (R ⋄ S) ⊆ ⟨f, g⟩⁎ R ⋄ ⟨g, h⟩⁎ S.
Proof. rew (image_preimage_adj _ _ _). intros [a c].
  change ( (∐ b, (a, b) ∊ R ⊠ (b, c) ∊ S) ⊸ ∐ y, (f a, y) ∊ ⟨f, g⟩⁎ R ⊠ (y, h c) ∊ ⟨g, h⟩⁎ S ).
  rew <-aex_adj; intros b. rew <-(aex_ub _ (g b)).
  now rew [(image_el ⟨f,g⟩ _ _)|(image_el ⟨g,h⟩ _ _)].
Qed.

(** Image is not lax for [⋄] — the shared middle points of a composite of
    images need only be identified after applying the map — but the two-sided
    conjugation form is exact: the outer images pin the boundary points of the
    middle composition into the range, letting the middle factor pull back.
    The projection formula of the image ⊣ preimage adjunction against [⋄]. *)
Lemma image_compose_middle@{u} {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃:set@{u}}
  (f₀:X₀ ⇾ Y₀) (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂) (f₃:X₃ ⇾ Y₃)
  (A:𝒫 (X₀ ⊗ X₁)) (Z:𝒫 (Y₁ ⊗ Y₂)) (C:𝒫 (X₂ ⊗ X₃))
  : ⟨f₀,f₁⟩⁎ A ⋄ Z ⋄ ⟨f₂,f₃⟩⁎ C = ⟨f₀,f₃⟩⁎ (A ⋄ ⟨f₁,f₂⟩* Z ⋄ C).
Proof. change ((⟨f₀,id⟩ ∘ ⟨id,f₁⟩)⁎ A ⋄ Z ⋄ (⟨id,f₃⟩ ∘ ⟨f₂,id⟩)⁎ C
        = (⟨id,f₃⟩ ∘ ⟨f₀,id⟩)⁎ (A ⋄ ⟨id,f₂⟩* (⟨f₁,id⟩* Z) ⋄ C)).
  rew [(image_compose_alt ⟨id,f₁⟩ ⟨f₀,id⟩ A) | (image_compose_alt ⟨f₂,id⟩ ⟨id,f₃⟩ C) | (image_compose_alt ⟨f₀,id⟩ ⟨id,f₃⟩ _)].
  rew <-(image_id_compose_distr_l f₀ _ Z).
  rew <-(image_id_compose_distr_r f₃ _ _).
  rew <-(image_id_compose_distr_l f₀ _ _).
  rew (image_compose_pin_l f₁ A Z).
  rew (image_compose_pin_r f₂ _ C).
  refl. 
Qed.

(** The right-adjoint companion of the projection formula, inclusion only:
    universal images pin nothing by themselves (a point outside the range
    belongs to every universal image), so the inner factor must be an image,
    which supplies preimages of the middle points for the universal ends to
    consume.  Without the middle image, [∀.[⟨f,f⟩]] has no law for [⋄]. *)
Lemma universal_image_compose_middle@{u} {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃:set@{u}}
  (f₀:X₀ ⇾ Y₀) (f₁:X₁ ⇾ Y₁) (f₂:X₂ ⇾ Y₂) (f₃:X₃ ⇾ Y₃)
  (A:𝒫 (X₀ ⊗ X₁)) (W:𝒫 (X₁ ⊗ X₂)) (C:𝒫 (X₂ ⊗ X₃))
  : ∀.[⟨f₀,f₁⟩] A ⋄ ⟨f₁,f₂⟩⁎ W ⋄ ∀.[⟨f₂,f₃⟩] C ⊆ ∀.[⟨f₀,f₃⟩] (A ⋄ W ⋄ C).
Proof. rew <-(preimage_universal_image_adj _ _ _).
  change (⟨f₀,id⟩* (∀.[⟨f₀,f₁⟩] A) ⋄ (⟨f₁,id⟩ ∘ ⟨id,f₂⟩)⁎ W ⋄ ⟨id,f₃⟩* (∀.[⟨f₂,f₃⟩] C) ⊆ A ⋄ W ⋄ C).
  rew (image_compose_alt ⟨id,f₂⟩ ⟨f₁,id⟩ W).
  rew (image_compose_pin_r f₁ _ _).
  change (⟨id,f₁⟩* (⟨f₀,id⟩* (∀.[⟨f₀,f₁⟩] A))) with (⟨f₀,f₁⟩* (∀.[⟨f₀,f₁⟩] A)).
  rew (universal_image_counit ⟨f₀,f₁⟩ A).
  rew <-(compose_rel_assoc A _ _).
  rew (image_compose_pin_l f₂ W _).
  change (⟨f₂,id⟩* (⟨id,f₃⟩* (∀.[⟨f₂,f₃⟩] C))) with (⟨f₂,f₃⟩* (∀.[⟨f₂,f₃⟩] C)).
  rew (universal_image_counit ⟨f₂,f₃⟩ C).
  now rew (compose_rel_assoc A W C).
Qed.

Local Open Scope sg_op_scope.
Lemma preimage_compose_rel_lax_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) (R S:𝒫 (Y ⊗ Y))
  : ⟨f, f⟩* R ∙ ⟨f, f⟩* S ⊆ ⟨f, f⟩* (R ∙ S).
Proof. exact (preimage_compose_rel_lax _ _ _ _ _). Qed.

Lemma image_compose_rel_lax_alt@{u} {X Y:set@{u}}
  (f:X ⇾ Y) (R:𝒫 (X ⊗ X)) (S:𝒫 (X ⊗ X))
  : ⟨f, f⟩⁎ (R ∙ S) ⊆ ⟨f, f⟩⁎ R ∙ ⟨f, f⟩⁎ S.
Proof. exact (image_compose_rel_lax _ _ _ _ _). Qed.

Lemma image_compose_middle_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) (A:𝒫 (X ⊗ X)) (Z:𝒫 (Y ⊗ Y)) (C:𝒫 (X ⊗ X))
  : ⟨f, f⟩⁎ A ∙ Z ∙ ⟨f, f⟩⁎ C = ⟨f, f⟩⁎ (A ∙ ⟨f, f⟩* Z ∙ C).
Proof. exact (image_compose_middle _ _ _ _ _ _ _). Qed.

Lemma universal_image_compose_middle_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) (A W C:𝒫 (X ⊗ X))
  : ∀.[⟨f, f⟩] A ∙ ⟨f, f⟩⁎ W ∙ ∀.[⟨f, f⟩] C ⊆ ∀.[⟨f, f⟩] (A ∙ W ∙ C).
Proof. exact (universal_image_compose_middle _ _ _ _ _ _ _). Qed.

Local Abbreviation m := (tensor_medial _ _ _ _).

Lemma medial_preimage_compose@{u} {X₁ Y₁ Z₁ X₂ Y₂ Z₂:set@{u}} (R:𝒫(X₁ ⊗ Y₁)) (S:𝒫(Y₁ ⊗ Z₁)) (T:𝒫(X₂ ⊗ Y₂)) (U:𝒫(Y₂ ⊗ Z₂))
  : m* ((R ⋄ S) ⊗ (T ⋄ U)) = m* (R ⊗ T) ⋄ m* (S ⊗ U).
Proof. intros [[x₁ x₂][z₁ z₂]].
  change ( ( (∐ y₁, (x₁,y₁) ∊ R ⊠ (y₁,z₁) ∊ S) ⊠ (∐ y₂, (x₂,y₂) ∊ T ⊠ (y₂,z₂) ∊ U) )
           ⧟ (∐ p, ((x₁,x₂),p) ∊ m* (R ⊗ T) ⊠ (p,(z₁,z₂)) ∊ m* (S ⊗ U)) ).
  split.
+ rew <-aex_adj2; intros y₁ y₂. rew <-(aex_ub _ (y₁,y₂)). now rew (aprod_medial _ _ _ _).
+ rew <-aex_adj; intros [y₁ y₂]. rew [<-(aex_ub _ y₁)|<-(aex_ub _ y₂)]. now rew (aprod_medial _ _ _ _).
Qed.  

Lemma medial_preimage_compose_alt@{u} {X Y:set@{u}} (R S:𝒫(X ⊗ X)) (T U:𝒫(Y ⊗ Y))
  : m* ((R ∙ S) ⊗ (T ∙ U)) = m* (R ⊗ T) ∙ m* (S ⊗ U).
Proof. exact (medial_preimage_compose R S T U). Qed.

Local Close Scope sg_op_scope.

Local Open Scope fun_inv_scope.

Lemma surjective_image_preimage@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Inverse f, !Surjective f}
  : f⁎ ∘ f* = id.
Proof. intros V. change (f⁎ (f* V) = V). apply le_antisym. split; [ exact _ |].
  intros y. change (y ∊ V ⊸ ∐ x, f x = y ⊠ f x ∊ V).
  rew <-(aex_ub _ (f⁻¹ y)), (surjective_applied f y). now simplify.
Qed.
Definition surjective_image_preimage_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Inverse f, !Surjective f} V
  : f⁎ (f* V) = V := surjective_image_preimage f V.

Lemma surjective_preimage_injective@{u} {X Y:set@{u}} {f:X ⇾ Y} `{!Inverse f, !Surjective f}
  : Injective f*.
Proof. apply (alt_Build_Injective _). exact (surjective_image_preimage _). Qed.
#[global] Hint Extern 2 (Injective _*) => simple notypeclasses refine surjective_preimage_injective : typeclass_instances. 

Lemma surjective_image_surjective@{u} {X Y:set@{u}} {f:X ⇾ Y} `{!Inverse f, !Surjective f}
  : Surjective f⁎.
Proof. exact (surjective_image_preimage _). Qed.
#[global] Hint Extern 2 (Surjective _⁎) => simple notypeclasses refine surjective_image_surjective : typeclass_instances.

Lemma surjective_universal_image_preimage@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Inverse f, !Surjective f}
  : ∀.[f] ∘ f* = id.
Proof. intros V. change ((f⁎ (f* (V ᗮ)))ᗮ = V). now rew (surjective_image_preimage_alt f (V ᗮ)). Qed.
Definition surjective_universal_image_preimage_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Inverse f, !Surjective f} V
  : ∀.[f] (f* V) = V := surjective_universal_image_preimage f V.

Lemma surjective_universal_image_surjective@{u} {X Y:set@{u}} {f:X ⇾ Y} `{!Inverse f, !Surjective f}
  : Surjective ∀.[f].
Proof. exact (surjective_universal_image_preimage _). Qed.
#[global] Hint Extern 2 (Surjective ∀.[_]) => simple notypeclasses refine surjective_universal_image_surjective : typeclass_instances. 


Lemma injective_preimage_image@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Injective f}
  : f* ∘ f⁎ = id.
Proof. intros U; simplify. apply le_antisym. split; [| exact _].
  intros x. change ((∐ x', f x' = f x ⊠ x' ∊ U) ⊸ x ∊ U).
  rew <-aex_adj; intros x'. rew (injective f x' x).
  exact (equal_element U x' x).
Qed.
Definition injective_preimage_image_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Injective f} U
  : f* (f⁎ U) = U := injective_preimage_image _ _.

Lemma injective_preimage_surjective@{u} {X Y:set@{u}} {f:X ⇾ Y} `{!Injective f}
  : Surjective f*.
Proof. exact (injective_preimage_image _). Qed.
#[global] Hint Extern 2 (Surjective _*) => simple notypeclasses refine injective_preimage_surjective : typeclass_instances.

Lemma injective_preimage_universal_image@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Injective f}
  : f* ∘ ∀.[f] = id.
Proof. intros U. change ((f* (f⁎ (U ᗮ)))ᗮ = U). now rew (injective_preimage_image_alt f (U ᗮ)). Qed.
Definition injective_preimage_universal_image_alt@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Injective f} U
  : f* (∀.[f] U) = U := injective_preimage_universal_image f U.

Lemma injective_universal_image_injective@{u} {X Y:set@{u}} {f:X ⇾ Y} `{!Injective f}
  : Injective ∀.[f].
Proof. apply (alt_Build_Injective _). exact (injective_preimage_universal_image _). Qed.
#[global] Hint Extern 2 (Injective ∀.[_]) => simple notypeclasses refine injective_universal_image_injective : typeclass_instances.

Lemma injective_image_sub_universal@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Injective f} U
  : f⁎ U ⊆ ∀.[f] U.
Proof.
  now rew <-(preimage_universal_image_adj f U (f⁎ U)), (injective_preimage_image_alt f U).
Qed.

(** Dually, weak surjectivity compares the adjoints the other way (an
    unwitnessed preimage suffices — both components spend it once). *)
Lemma weakly_surjective_universal_sub_image@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!WeaklySurjective@{u} f} U
  : ∀.[f] U ⊆ f⁎ U.
Proof. intros y.
  change ((∏ x, f x = y ⊸ x ∊ U) ⊸ ∐ x, f x = y ⊠ x ∊ U).
  pose proof (weakly_surjective f y) as [x Hx].
  rew [(all_lb _ x) | <-(aex_ub _ x)].
  rew (aiff_is_true Hx). now simplify.
Qed.

Lemma injective_image_injective@{u} {X Y:set@{u}} {f:X ⇾ Y} `{!Injective f}
  : Injective f⁎.
Proof. apply (alt_Build_Injective _). exact (injective_preimage_image _). Qed.
#[global] Hint Extern 2 (Injective _⁎) => simple notypeclasses refine injective_image_injective : typeclass_instances. 

Lemma bijective_preimage_bijective@{u} {X Y:set@{u}} {f:X ⇾ Y} `{!Inverse f, !Bijective f}
  : Bijective f*.
Proof. now split. Qed.
#[global] Hint Extern 2 (Bijective _*) => simple notypeclasses refine bijective_preimage_bijective : typeclass_instances. 

Lemma bijective_image_bijective@{u} {X Y:set@{u}} {f:X ⇾ Y} `{!Inverse f, !Bijective f}
  : Bijective f⁎.
Proof. now split. Qed.
#[global] Hint Extern 2 (Bijective _⁎) => simple notypeclasses refine bijective_image_bijective : typeclass_instances. 


Lemma bijective_preimage_inverse@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Inverse f, !Bijective f}
  : (f⁻¹)* = f⁎.
Proof. intros V. rew <-(injective_preimage_image_alt f V) at 1.
  change ( (f ∘ f⁻¹)* (f⁎ V) = f⁎ V ).
  now rew (surjective f).
Qed.

Lemma bijective_image_inverse@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Inverse f, !Bijective f}
  : (f⁻¹)⁎ = f*.
Proof. intros V. rew <-(surjective_image_preimage_alt f V) at 1.
  change ( ((f⁻¹)⁎ ∘ f⁎) (f* V) = f* V ).
  now rew <-(image_compose _ _), (bijective f ), image_id.
Qed.

Lemma preimage_image_adj@{u} {X Y:set@{u}} (f:X ⇾ Y) `{!Inverse f, !Bijective f} U V
  : f* U ⊆ V ⧟ U ⊆ f⁎ V .
Proof. rew [<-(bijective_image_inverse f) | <-(bijective_preimage_inverse f)].
  exact (image_preimage_adj _ _ _).
Qed.


(** Projection preimages (cylinders) and the tensor. *)

Local Abbreviation π₁ := (tensor_proj1 _ _).
Local Abbreviation π₂ := (tensor_proj2 _ _).

Lemma proj1_preimage_tensor_top@{u} {X Y:set@{u}} (A:𝒫 X) : π₁* A = A ⊗ ⊤ :> 𝒫(X ⊗ Y).
Proof. intros [a b]. change (a ∊ A ⧟ a ∊ A ⊠ 𝐓). now simplify. Qed.

Lemma compose_proj1_preimage@{u} {X Y Z:set@{u}} (A:𝒫 X) (R:𝒫(Y ⊗ Z)) :
   (π₁* A) ⋄ R = A ⊗ π₂⁎ R.
Proof. intros [x z].
  change ( (∐ y, x ∊ A ⊠ (y, z) ∊ R) ⧟ x ∊ A ⊠ z ∊ π₂⁎ R).
  rew <-aex_frob_l. apply aprod_proper_aiff; [ easy |]. split.
+ rew <-aex_adj; intros y. exact (image_el π₂ (y, z) R).
+ unfold_image. rew <-aex_adj; intros [y z']. rew <-(aex_ub _ y).
  change (z' = z ⊠ (y, z') ∊ R ⊸ (y, z) ∊ R).
  rew (is_fun set:(λ z, (y, z) ∊ R) z' z).
  change ( ((y, z') ∊ R ⧟ (y, z) ∊ R ) ⊠ (y, z') ∊ R ⊸ (y, z) ∊ R ).
  tautological.
Qed.

