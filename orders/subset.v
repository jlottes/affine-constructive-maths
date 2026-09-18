Require Import abstract_algebra theory.groups theory.lattices theory.common_props.
Require Import interfaces.orders orders.orders orders.lattices orders.maps orders.suborders.
Require Import set_lambda sprop srelations logic.aprop logic.relations.
Require Export interfaces.subset.
Require Import tactics.misc easy rewrite simplify.

Local Abbreviation id := (id_fun _).

Local Ltac unfold_subset :=
  try change (?U ≤ ?W) with (∏ x, x ∊ U ⊸ x ∊ W);
  try change (?U = ?W) with (∏ x, x ∊ U ⧟ x ∊ W).

Lemma subset_poset {X} : Poset (𝒫 X).
Proof. split; [ split | .. ].
+ tautological.
+ tautological.
+ tautological.
+ hnf; intros U V; unfold_subset. rew <-all_adj. intros x. now rew (all_lb _ x).
Qed.

Global Hint Extern 2 (Poset (subset_set _)) => simple notypeclasses refine subset_poset : typeclass_instances.
Global Hint Extern 2 (WeakPoset (subset_set _)) => simple notypeclasses refine subset_poset : typeclass_instances.
Global Hint Extern 2 (PreOrder (subset _)) => simple notypeclasses refine subset_poset : typeclass_instances.
Global Hint Extern 2 (PreOrder (set_T (subset_set _))) => simple notypeclasses refine subset_poset : typeclass_instances.

Lemma element_proper_aimpl {X:set} {x y:X} {U V : 𝒫 X} : x = y → U ⊆ V → (x ∊ U ⊸ y ∊ V).
Proof. intros E H. rew (H x). apply (is_fun element (x,V) (y,V)). now split. Qed.
Global Hint Extern 2 (apos (aimpl (_ ∊ _, _))) => sapply_2 element_proper_aimpl : proper.

Lemma element_proper_le_aimpl {X:set} {Xle:Le X} {x y:X} {U V : 𝒫 X} {H:UpSet V} :
  x ≤ y → U ⊆ V → (x ∊ U ⊸ y ∊ V).
Proof. intros E HUV. rew (HUV x). exact (aimpl_impl_pos (up_closed V x y) E). Qed.

Lemma element_proper_le_flip_aimpl {X:set} {Xle:Le X} {x y:X} {U V : 𝒫 X} {H:DownSet V} :
  y ≤ x → U ⊆ V → (x ∊ U ⊸ y ∊ V).
Proof. intros E HUV. rew (HUV x). exact (aimpl_impl_pos (down_closed V y x) E). Qed.

(** Order rewriting in the point position of [∊]: fires only when a tag
    carrying an order relation is syntactically present in the point terms,
    so equality rewrites never spawn the [UpSet]/[DownSet] search. *)
Ltac element_le_proper x y V :=
  lazymatch constr:((x, y)) with
  | context [ @arewrite_tag_l _ (@le _ _) _ _ _ ] => idtac
  | context [ @arewrite_tag_r _ (@le _ _) _ _ _ ] => idtac
  end;
  (  (let H := get_instance (UpSet V) in sapply_2 (element_proper_le_aimpl (H:=H)))
   + (let H := get_instance (DownSet V) in sapply_2 (element_proper_le_flip_aimpl (H:=H))) ).

Global Hint Extern 1 (apos (aimpl (?x ∊ _, ?y ∊ ?V))) => element_le_proper x y V : proper.

(*
Section test_element_le_rewrite.
  Context `{WeakPoset X} (U D W : 𝒫 X) {HU:UpSet U} {HD:DownSet D} (x y : X) (E : x ≤ y).

  Example test_hyp_upset (m : x ∊ U) : y ∊ U.
  Proof. rew E in m. exact m. Qed.

  Example test_goal_downset (m : y ∊ D) : x ∊ D.
  Proof. rew E. exact m. Qed.

  Example test_goal_rev_upset (m : x ∊ U) : y ∊ U.
  Proof. rew <-E. exact m. Qed.

  Example test_hyp_rev_downset (m : y ∊ D) : x ∊ D.
  Proof. rew <-E in m. exact m. Qed.

  Example test_eq_regression (Ee : x = y) (m : x ∊ W) : y ∊ W.
  Proof. rew <-Ee. exact m. Qed.

  Example test_subset_position (A B : 𝒫 X) (HAB : A ⊆ B) (m : x ∊ A) : x ∊ B.
  Proof. rew <-HAB. exact m. Qed.
End test_element_le_rewrite.
*)


Lemma subset_bounded_lattice_order {X} : BoundedLatticeOrder (𝒫 X).
Proof. split.
+ split; [ split|..]; [ exact _ | tautological.. ].
+ simple notypeclasses refine (Build_BoundedJoinSemiLatticeOrder _);
  [ apply Build_JoinSemiLatticeOrder |]; tautological.
Qed.

Global Hint Extern 2 (BoundedLatticeOrder (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (LatticeOrder (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLatticeOrder (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (MeetSemiLatticeOrder (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLatticeOrder (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (JoinSemiLatticeOrder (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (BoundedLattice (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (Lattice (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice (subset_set _)) => simple notypeclasses refine subset_bounded_lattice_order : typeclass_instances.

Lemma subset_distr_lattice {X} : DistributiveLattice (𝒫 X).
Proof. apply Build_DistributiveLatticeOrder. tautological. Qed.
Global Hint Extern 2 (DistributiveLattice (subset_set _)) => simple notypeclasses refine subset_distr_lattice : typeclass_instances.

Lemma nonempty_alt {X} {U : 𝒫 X} : U ≠ ∅ ⧟ ∐ x, x ∊ U.
Proof. full_tautological. Qed.

Lemma complement_involutive {X:set} : Involutive (@complement X).
Proof. full_tautological. Qed.
Global Hint Extern 2 (Involutive complement) => simple notypeclasses refine complement_involutive : typeclass_instances.
Global Hint Extern 2 (Bijective complement) => simple notypeclasses refine complement_involutive : typeclass_instances.
Global Hint Extern 2 (Injective complement) => simple notypeclasses refine complement_involutive : typeclass_instances.
Global Hint Extern 2 (Surjective complement) => simple notypeclasses refine complement_involutive : typeclass_instances.

Lemma complement_latmor_flip {X:set} : BoundedLattice_Flip_Morphism (@complement X).
Proof. apply Build_BoundedLattice_Flip_Morphism; full_tautological. Qed.
Global Hint Extern 2 (BoundedLattice_Flip_Morphism complement) => simple notypeclasses refine complement_latmor_flip : typeclass_instances.
Global Hint Extern 2 (Lattice_Flip_Morphism complement) => simple notypeclasses refine complement_latmor_flip : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice_Flip_Morphism complement) => simple notypeclasses refine complement_latmor_flip : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice_Flip_Morphism complement) => simple notypeclasses refine complement_latmor_flip : typeclass_instances.
Global Hint Extern 2 (MeetSemiLattice_Flip_Morphism complement) => simple notypeclasses refine complement_latmor_flip : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Flip_Morphism complement) => simple notypeclasses refine complement_latmor_flip : typeclass_instances.

Lemma complement_order_embedding_flip {X:set} : OrderEmbeddingFlip (@complement X).
Proof. exact (join_sl_mor_embedding_flip _). Qed.
Global Hint Extern 2 (OrderEmbeddingFlip complement) => simple notypeclasses refine complement_order_embedding_flip : typeclass_instances.
Global Hint Extern 2 (OrderPreservingFlip complement) => simple notypeclasses refine complement_order_embedding_flip : typeclass_instances.
Global Hint Extern 2 (OrderReflectingFlip complement) => simple notypeclasses refine complement_order_embedding_flip : typeclass_instances.

Lemma powerset_pt_fun_order_embedding `{F: 𝒫² X} : OrderEmbedding (powerset_pt_fun F).
Proof. exact from_subset_order_embedding. Qed.
Global Hint Extern 2 (OrderEmbedding  (powerset_pt_fun _)) => simple notypeclasses refine powerset_pt_fun_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (powerset_pt_fun _)) => simple notypeclasses refine powerset_pt_fun_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (powerset_pt_fun _)) => simple notypeclasses refine powerset_pt_fun_order_embedding : typeclass_instances.

(** Multiplicative intersection *)

Local Open Scope subset_scope.

Lemma mult_intersection_commutative {X:set} : Commutative (@mult_intersection X).
Proof. tautological. Qed.
#[global] Hint Extern 2 (Commutative mult_intersection) => simple notypeclasses refine mult_intersection_commutative : typeclass_instances.

(*
Lemma mult_intersection_associative {X:set} : Associative (@mult_intersection X).
Proof. tautological. Qed.
#[global] Hint Extern 2 (Associative mult_intersection) => simple notypeclasses refine mult_intersection_associative : typeclass_instances.
*)

(*
Lemma mult_intersection_commutative {X:set} : Commutative (@mult_intersection X).
Proof. tautological. Qed.
#[global] Hint Extern 2 (Commutative mult_intersection) => simple notypeclasses refine mult_intersection_commutative : typeclass_instances.

Lemma mult_intersection_apos {X:set} {U V : 𝒫 X} {x} : x ∊ U ⨶ V ↔ x ∊ U ∧ x ∊ V.
Proof. split.
+ intros [y[E[??]]]. change (apos (x=y)) in E. now rew E.
+ intros [??]. exists x. now change (x = x ⊠ x ∊ U ⊠ x ∊ V).
Qed.

Lemma mult_intersection_aneg {X:set} {U V : 𝒫 X} {x} : x ∊̸ U ⨶ V ↔ (x ∊̸ U ⊞ x ∊̸ V) ∧ (∀ y, y ∊ U ⨶ V → x ≠ y).
Proof. split.
+ intros P. split.
  - specialize (P x); change (apos (x = x ⊠ x ∊ U ⊠ x ∊ V)ᗮ) in P. revert P; now simplify.
  - intros y. rew mult_intersection_apos. intros [??]. now apply (P y).
+ intros [H1 P]. intros y. change ( anot (x = y ⊠ y ∊ U ⊠ y ∊ V) ). split.
  - intros E. change (anot (y ∊ U ⊠ y ∊ V)). now rew <-E.
  - intros [??]. apply (P y). now apply (@mult_intersection_apos _ U V y).
Qed.


Lemma mult_intersection_inhabited_alt {X:set} (U V : 𝒫 X) :
  (∐ x, x ∊ U ⨶ V) ⧟ (∐ x, x ∊ U ⊠ x ∊ V).
Proof. change  (∐ x, x ∊ U ⨶ V) with (∐ x, ∐ y, x = y ⊠ y ∊ U ⊠ y ∊ V); split.
+ rew <-aex_adj; intros x. rew <-aex_adj; intros y.
  rew <-(aex_ub _ y). tautological.
+ rew <-aex_adj; intros x.
  rew <-(aex_ub _ x), <-(aex_ub _ x). 
  now simplify.
Qed.

Lemma mult_disjoint_subset_complement_l {X:set} (U V : 𝒫 X) :
  U ⨶ V = ∅ ⧟ U ⊆ V ᗮ.
Proof. apply by_contrapositive_iff.
  now rew (nonempty_alt (U:= U ⨶ V)), (mult_intersection_inhabited_alt _ _).
Qed.

Lemma mult_disjoint_subset_complement_r {X:set} (U V : 𝒫 X) :
  U ⨶ V = ∅ ⧟ V ⊆ U ᗮ.
Proof. rew (commutativity _ _ _). exact (mult_disjoint_subset_complement_l _ _). Qed.
*)

Lemma mult_empty_subset_complement_l {X:set} (U V : 𝒫 X) :
  anot (∐ x, x ∊ U ⊠ x ∊ V) ⧟ U ⊆ V ᗮ.
Proof. refl. Qed.

Lemma mult_empty_subset_complement_r {X:set} (U V : 𝒫 X) :
  anot (∐ x, x ∊ U ⊠ x ∊ V) ⧟ V ⊆ U ᗮ.
Proof. rew <-(mult_empty_subset_complement_l _ _).
  apply anot_proper_aiff, aex_proper_aiff. intros x. exact (aprod_com _ _).
Qed.

Lemma mult_disjoint_subset_complement_l {X:set} (U V : 𝒫 X) :
  (∏ x, x ∊̸ U ⊞ x ∊̸ V) ⧟ U ⊆ V ᗮ.
Proof. refl. Qed.

(*
Lemma mult_disjoint_subset_complement_r {X:set} (U V : 𝒫 X) :
  (∏ x, x ∊̸ U ⊞ x ∊̸ V) ⧟ V ⊆ U ᗮ.
Proof. exact (mult_empty_subset_complement_r _ _). Qed.
*)

(** Singleton *)

Lemma tensor_singleton@{u} {X Y:set@{u}} (x:X) (y:Y) : @singleton (X ⊗ Y) (x, y) = singleton x ⊗ singleton y.
Proof. refl. Qed.

Lemma singleton_subset {X:set} (x:X) (U:𝒫 X) : singleton x ⊆ U ⧟ x ∊ U.
Proof. change ((∏ y, x = y ⊸ y ∊ U) ⧟ x ∊ U). split.
+ rew (all_lb _ x). now simplify.
+ rew <-all_adj; intros y. rew <-(aprod_adj _ _ _), (aprod_com _ _). apply equal_element.
Qed.

(** of_course_subset *)

Definition of_course_subset {X:set} `(U:𝒫 X) := range (from_subset U).

Import of_course_set_notation.
Lemma of_course_subset_is_fun {X:set} : @IsFun !(𝒫 X) (𝒫 X) of_course_subset.
Proof. intros U V. apply affirmative_aimpl. intros E. change (𝒫 X) in U,V.
  change (apos (U = V)) in E. intros x.
  change ( (∐ a : U, subset_pt a = x) ⧟ ∐ a : V, subset_pt a = x).
  split; rew <-aex_adj; intros [a Ha]; unfold subset_pt, pt.
* assert (a ∊ V) by now rew <-E. exact (aex_ub _ (to_subset a)).
* assert (a ∊ U) by now rew   E. exact (aex_ub _ (to_subset a)).
Qed.

Canonical Structure of_course_subset_fun (X:set) : _ ⇾ _ := @func_make _ _ _ (@of_course_subset_is_fun X).

Lemma of_course_subset_subset `(U:𝒫 X) : of_course_subset U ⊆ U.
Proof.
  intros x. change ((∐ u:U, from_subset U u = x) ⊸ x ∊ U).
  rew <-aex_adj; intros u. rew <-(equal_element U (from_subset U u) x). now simplify.
Qed.

Lemma of_course_subset_order_preserving {X:set} : OrderPreserving (@of_course_subset_fun X).
Proof. apply alt_Build_OrderPreserving.
  intros U V. apply affirmative_aimpl. intros E. change (𝒫 X) in U,V. intros x.
  change ( (∐ a : U, subset_pt a = x) ⊸ ∐ a : V, subset_pt a = x).
  rew <-aex_adj; intros [a Ha]; unfold subset_pt, pt.
  assert (a ∊ V) by now rew <-(E:U ⊆ V). exact (aex_ub _ (to_subset a)).
Qed.
#[global] Hint Extern 2 (OrderPreserving (of_course_subset_fun _)) => simple notypeclasses refine of_course_subset_order_preserving : typeclass_instances.

Lemma of_course_singleton {X:set} (x:X) : of_course_subset (singleton x) = singleton x.
Proof. intros y. change ((∐ u:subset_to_set (singleton x), from_subset (singleton x) u = y) ⧟ x = y). split.
+ rew <-aex_adj; intros [a Ha]. change (apos (x = a)) in Ha. change (a = y ⊸ x = y). now rew <-Ha.
+ now rew <-(aex_ub _ (to_subset x)).
Qed.

(** subset_to_set *)
Lemma aex_subset {X:set} {S:𝒫 X} {P:X → Ω} : (∐ x:S, P x) ↔ (∐ x:X, x ∊ S ⊠ P x).
Proof. split.
+ intros [x Hx]. now exists x.
+ intros [x [Hx1 Hx2]]. now exists (to_subset x).
Qed.

(** Congruence for quantifiers over a subset-as-type binder. In [rew]-generated
    properness goals both bodies are one context instantiated at [S] resp. [T],
    and the pointwise premise closes by conversion: [to_subset] witnesses are
    strict, and [subset_pt (to_subset x)] reduces to [x]. *)
Lemma aex_subset_proper_aimpl {X:set} {S T:𝒫 X} {P:S → Ω} {Q:T → Ω}
  : S ⊆ T → (∀ (x:X) (hs : x ∊ S) (ht : x ∊ T), P (@to_subset X S x hs) ⊸ Q (@to_subset X T x ht))
  → ((∐ a:S, P a) ⊸ (∐ b:T, Q b)).
Proof. intros E HPQ.
  rew <-aex_adj. intros a.
  assert (subset_pt a ∊ T) as ht by (rew <-E; exact (subset_pt_is_el a)).
  rew <-(aex_ub _ (@to_subset X T (subset_pt a) ht)).
  exact (HPQ (subset_pt a) (subset_pt_is_el a) ht).
Qed.

Lemma all_subset_proper_aimpl {X:set} {S T:𝒫 X} {P:S → Ω} {Q:T → Ω}
  : T ⊆ S → (∀ (x:X) (hs : x ∊ S) (ht : x ∊ T), P (@to_subset X S x hs) ⊸ Q (@to_subset X T x ht))
  → ((∏ a:S, P a) ⊸ (∏ b:T, Q b)).
Proof. intros E HPQ.
  rew <-all_adj. intros b.
  assert (subset_pt b ∊ S) as hs by (rew <-E; exact (subset_pt_is_el b)).
  rew (all_lb _ (@to_subset X S (subset_pt b) hs)).
  exact (HPQ (subset_pt b) hs (subset_pt_is_el b)).
Qed.

Lemma aex_subset_proper_aiff {X:set} {S T:𝒫 X} {P:S → Ω} {Q:T → Ω}
  : S = T → (∀ (x:X) (hs : x ∊ S) (ht : x ∊ T), P (@to_subset X S x hs) ⧟ Q (@to_subset X T x ht))
  → ((∐ a:S, P a) ⧟ (∐ b:T, Q b)).
Proof. intros E HPQ. split.
+ apply (aex_subset_proper_aimpl (aimpl_impl_pos (eq_le _ _) E)).
  intros x hs ht. exact (andl (HPQ x hs ht)).
+ apply (aex_subset_proper_aimpl (aimpl_impl_pos (eq_le_flip _ _) E)).
  intros x ht hs. exact (andr (HPQ x hs ht)).
Qed.

Lemma all_subset_proper_aiff {X:set} {S T:𝒫 X} {P:S → Ω} {Q:T → Ω}
  : S = T → (∀ (x:X) (hs : x ∊ S) (ht : x ∊ T), P (@to_subset X S x hs) ⧟ Q (@to_subset X T x ht))
  → ((∏ a:S, P a) ⧟ (∏ b:T, Q b)).
Proof. intros E HPQ. split.
+ apply (all_subset_proper_aimpl (aimpl_impl_pos (eq_le_flip _ _) E)).
  intros x hs ht. exact (andl (HPQ x hs ht)).
+ apply (all_subset_proper_aimpl (aimpl_impl_pos (eq_le _ _) E)).
  intros x ht hs. exact (andr (HPQ x hs ht)).
Qed.

Global Hint Extern 3 (apos (aex _ ⊸ aex _)) =>
  simple notypeclasses refine (aex_subset_proper_aimpl _ _); [ | intros ? ? ?; refl ] : proper.
Global Hint Extern 3 (apos (all _ ⊸ all _)) =>
  simple notypeclasses refine (all_subset_proper_aimpl _ _); [ | intros ? ? ?; refl ] : proper.
Global Hint Extern 3 (apos (aex _ ⧟ aex _)) =>
  simple notypeclasses refine (aex_subset_proper_aiff _ _); [ | intros ? ? ?; refl ] : proper.
Global Hint Extern 3 (apos (all _ ⧟ all _)) =>
  simple notypeclasses refine (all_subset_proper_aiff _ _); [ | intros ? ? ?; refl ] : proper.

(** SProp-level twin, for record fields quantifying over a subset carrier
    ([∀ U:Φ, …] : SProp). The pointwise premise is left to the proper search,
    so tagged structure inside the body (e.g. an inner [∐ V:Φ]) recurses into
    the hints above. *)
Lemma sall_subset_proper_impl {X:set} {S T:𝒫 X} {P:S → SProp} {Q:T → SProp}
  : T ⊆ S → (∀ (x:X) (hs : x ∊ S) (ht : x ∊ T), sprop.impl (P (@to_subset X S x hs), Q (@to_subset X T x ht)))
  → sprop.impl (∀ a:S, P a, ∀ b:T, Q b).
Proof. intros E HPQ H b.
  assert (subset_pt b ∊ S) as hs by (rew <-E; exact (subset_pt_is_el b)).
  exact (HPQ (subset_pt b) hs (subset_pt_is_el b) (H (@to_subset X S (subset_pt b) hs))).
Qed.

Lemma sall_subset_proper_iff {X:set} {S T:𝒫 X} {P:S → SProp} {Q:T → SProp}
  : S = T → (∀ (x:X) (hs : x ∊ S) (ht : x ∊ T), sprop.iff (P (@to_subset X S x hs), Q (@to_subset X T x ht)))
  → sprop.iff (∀ a:S, P a, ∀ b:T, Q b).
Proof. intros E HPQ. split.
+ apply (sall_subset_proper_impl (aimpl_impl_pos (eq_le_flip _ _) E)).
  intros x hs ht. exact (andl (HPQ x hs ht)).
+ apply (sall_subset_proper_impl (aimpl_impl_pos (eq_le _ _) E)).
  intros x ht hs. exact (andr (HPQ x hs ht)).
Qed.

Global Hint Extern 3 (sprop.impl ((∀ x, _), (∀ y, _))) =>
  simple notypeclasses refine (sall_subset_proper_impl _ _); [ | intros ? ? ?; cbv beta ] : proper.
Global Hint Extern 3 (sprop.iff ((∀ x, _), (∀ y, _))) =>
  simple notypeclasses refine (sall_subset_proper_iff _ _); [ | intros ? ? ?; cbv beta ] : proper.
