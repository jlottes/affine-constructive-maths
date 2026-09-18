Require Import abstract_algebra orders.orders orders.maps.
Require Import easy rewrite interfaces.sprop logic.aprop logic.relations tactics.misc.

Local Notation "X 'ᵒᵖ'" := (order_op X) (at level 1, format "X 'ᵒᵖ'").

Lemma Build_DownDirected `{PreOrder X} `{Inhabited X} :
  (∀ x y : X, ∐ z, z ≤ x ⊠ z ≤ y ) →
  DownDirected X.
Proof. now split. Qed.


Definition DownDirected_preorder `{H:DownDirected X} : PreOrder X := PreOrder_op (X:=X ᵒᵖ).
Coercion DownDirected_preorder : DownDirected >-> PreOrder.

Definition UpDirected_op `{H:DownDirected X} : UpDirected (X ᵒᵖ) := H.
Definition DownDirected_op `{H:UpDirected X} : DownDirected (X ᵒᵖ) := H.
Global Hint Extern 2 (UpDirected (_ ᵒᵖ)) => simple notypeclasses refine UpDirected_op : typeclass_instances.
Global Hint Extern 2 (DownDirected (_ ᵒᵖ)) => simple notypeclasses refine DownDirected_op : typeclass_instances.
Global Hint Extern 2 (UpDirected (set_T (Order_op _))) => simple notypeclasses refine UpDirected_op : typeclass_instances.
Global Hint Extern 2 (DownDirected (set_T (Order_op _))) => simple notypeclasses refine DownDirected_op : typeclass_instances.

Lemma unit_up_directed   : UpDirected   𝟏. Proof. full_tautological. Qed.
Lemma unit_down_directed : DownDirected 𝟏. Proof. full_tautological. Qed.
#[global] Hint Extern 2 (UpDirected   unit     ) => simple notypeclasses refine unit_up_directed   : typeclass_instances.
#[global] Hint Extern 2 (DownDirected unit     ) => simple notypeclasses refine unit_down_directed : typeclass_instances.
#[global] Hint Extern 2 (UpDirected   (set_T 𝟏)) => simple notypeclasses refine unit_up_directed   : typeclass_instances.
#[global] Hint Extern 2 (DownDirected (set_T 𝟏)) => simple notypeclasses refine unit_down_directed : typeclass_instances.

Lemma tensor_up_directed@{u} {X Y:set@{u}} `{@UpDirected X Xle, @UpDirected Y Yle} : UpDirected (X ⊗ Y).
Proof. split; try exact _. intros [x₁ y₁][x₂ y₂].
  pose proof up_directed x₁ x₂ as [x Hx].
  pose proof up_directed y₁ y₂ as [y Hy].
  exists (x, y). unfold_pair_le.
  rew (aprod_medial _ _ _ _); now split.
Qed.
#[global] Hint Extern 2 (UpDirected (set_T (_ ⊗ _))) => simple notypeclasses refine tensor_up_directed : typeclass_instances.

Lemma tensor_down_directed@{u} {X Y:set@{u}} `{@DownDirected X Xle, @DownDirected Y Yle} : DownDirected (X ⊗ Y).
Proof. exact (tensor_up_directed (X:=X ᵒᵖ) (Y:=Y ᵒᵖ)). Qed.
#[global] Hint Extern 2 (DownDirected (set_T (_ ⊗ _))) => simple notypeclasses refine tensor_down_directed : typeclass_instances.

