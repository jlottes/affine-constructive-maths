Require Import interfaces.sprop.
Require Import orders.orders interfaces.common_props theory.common_props.
Require Import relations easy rewrite simplify tactics.misc.

Local Notation "X 'ᵒᵖ'" := (Order_op X) (at level 1, format "X 'ᵒᵖ'").

Section alt_Build.
  Universes u.
  Context `{WeakPoset@{u} X} `{WeakPoset@{u} Y} {f:X ⇾ Y}.

  Lemma alt_Build_OrderPreserving : (∀ x y : X, x ≤ y ⊸ f x ≤ f y) → OrderPreserving f.  Proof. now split. Qed.
  Lemma alt_Build_OrderReflecting : (∀ x y : X, f x ≤ f y ⊸ x ≤ y) → OrderReflecting f.  Proof. now split. Qed.
  Lemma alt_Build_OrderEmbedding  : (∀ x y : X, x ≤ y ⧟ f x ≤ f y) → OrderEmbedding f.
  Proof. intros P. split; [ apply alt_Build_OrderPreserving, P | apply alt_Build_OrderReflecting, P ]. Qed.
End alt_Build.
  
Section alt_Build_Flip.
  Universes u.
  Context `{WeakPoset@{u} X} `{WeakPoset@{u} Y} {f:X ⇾ Y}.
  Definition alt_Build_OrderPreservingFlip (H : ∀ x y : X, x ≤ y ⊸ f y ≤ f x) : OrderPreservingFlip f := alt_Build_OrderPreserving H.
  Definition alt_Build_OrderReflectingFlip (H : ∀ x y : X, f y ≤ f x ⊸ x ≤ y) : OrderReflectingFlip f := alt_Build_OrderReflecting H.
  Definition alt_Build_OrderEmbeddingFlip  (H : ∀ x y : X, x ≤ y ⧟ f y ≤ f x) : OrderEmbeddingFlip f := alt_Build_OrderEmbedding H.
End alt_Build_Flip.

Definition Build_OrderEmbeddingFlip@{u}  {X:set@{u}} `{Le X} {Y:set@{u}} `{Le Y} {f:X ⇾ Y} :
  OrderPreservingFlip f → OrderReflectingFlip f → OrderEmbeddingFlip f.
Proof. now split. Defined.

Definition strictly_order_preserving `{OrderReflecting (f:=f)} x y : x < y ⊸ f x < f y := acontra (order_reflecting f _ _).
Definition strictly_order_reflecting `{OrderPreserving (f:=f)} x y : f x < f y ⊸ x < y := acontra (order_preserving f _ _).
Definition strictly_order_embedding  `{OrderEmbedding  (f:=f)} x y : x < y ⧟ f x < f y := acontra_iff (order_embedding f _ _).
Arguments strictly_order_preserving {_ _ _ _} f {_} _ _.
Arguments strictly_order_reflecting {_ _ _ _} f {_} _ _.
Arguments strictly_order_embedding {_ _ _ _} f {_} _ _.

Definition strictly_order_preserving_flip `{OrderReflectingFlip (f:=f)} x y : x < y ⊸ f y < f x := acontra (order_reflecting_flip f _ _).
Definition strictly_order_reflecting_flip `{OrderPreservingFlip (f:=f)} x y : f y < f x ⊸ x < y := acontra (order_preserving_flip f _ _).
Definition strictly_order_embedding_flip  `{OrderEmbeddingFlip  (f:=f)} x y : x < y ⧟ f y < f x := acontra_iff (order_embedding_flip f _ _).
Arguments strictly_order_preserving_flip {_ _ _ _} f {_} _ _.
Arguments strictly_order_reflecting_flip {_ _ _ _} f {_} _ _.
Arguments strictly_order_embedding_flip {_ _ _ _} f {_} _ _.


Lemma right_order_preserving_from_left `{!@Commutative X X f} {Xle:Le X} `{!WeakPoset X}
  : (∀ z, OrderPreserving (ap1 f z)) → (∀ z, OrderPreserving (ap2 f z)).
Proof. intros ? z. apply alt_Build_OrderPreserving. intros x y.
  change (x ≤ y ⊸ f (x, z) ≤ f (y, z)).
  rew [ (commutativity f x z) | (commutativity f y z) ].
  exact (order_preserving (ap1 f z) x y).
Qed.

Lemma right_order_reflecting_from_left `{!@Commutative X X f} {Xle:Le X} `{!WeakPoset X}
  : (∀ z, OrderReflecting (ap1 f z)) → (∀ z, OrderReflecting (ap2 f z)).
Proof. intros ? z. apply alt_Build_OrderReflecting. intros x y.
  change (f (x, z) ≤ f (y, z) ⊸ x ≤ y).
  rew [ (commutativity f x z) | (commutativity f y z) ].
  exact (order_reflecting (ap1 f z) x y).
Qed.

Lemma right_order_embedding_from_left `{!@Commutative X X f} {Xle:Le X} `{!WeakPoset X}
  : (∀ z, OrderEmbedding (ap1 f z)) → (∀ z, OrderEmbedding (ap2 f z)).
Proof. intros ? z. apply alt_Build_OrderEmbedding. split.
* now apply right_order_preserving_from_left.
* now apply right_order_reflecting_from_left.
Qed.

Lemma order_morphism_flip@{u} {X Y : set@{u}} {Xle:Le X} {Yle:Le Y} : OrderMorphism X (Y ᵒᵖ) → OrderMorphism X Y.
Proof. split. exact H. change (WeakPoset ((Y ᵒᵖ)ᵒᵖ)). refine WeakPoset_op. apply H. Qed.

Definition order_preserving_flip_mor `{H:OrderPreservingFlip (X:=X) (Y:=Y) (f:=f)} : OrderMorphism X Y := order_morphism_flip H.
Definition order_reflecting_flip_mor `{H:OrderReflectingFlip (X:=X) (Y:=Y) (f:=f)} : OrderMorphism X Y := order_morphism_flip H.
Coercion order_preserving_flip_mor : OrderPreservingFlip >-> OrderMorphism.
Coercion order_reflecting_flip_mor : OrderReflectingFlip >-> OrderMorphism.

Global Hint Extern 10 (WeakPoset ?X) =>
  match goal with
  | H : OrderMorphism _ X |- _ => exact (order_mor_Y _ _ H)
  | H : OrderPreserving (Y:=X) _ |- _ => exact (order_mor_Y _ _ H)
  | H : OrderReflecting (Y:=X) _ |- _ => exact (order_mor_Y _ _ H)
  | H : OrderEmbedding  (Y:=X) _ |- _ => exact (order_mor_Y _ _ H)
  | H : OrderPreservingFlip (Y:=X) _ |- _ => exact (order_mor_Y _ _ H)
  | H : OrderReflectingFlip (Y:=X) _ |- _ => exact (order_mor_Y _ _ H)
  | H : OrderEmbeddingFlip  (Y:=X) _ |- _ => exact (order_mor_Y _ _ H)
  end : typeclass_instances.


Lemma OrderPreserving_proper_impl@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} {f g : X ⇾ Y}
  : f = g → impl (OrderPreserving f, OrderPreserving g).
Proof. intros E P. apply alt_Build_OrderPreserving. rew <-E. apply P. Qed.
Canonical Structure OrderPreserving_fun@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} :=
  make_weak_spred (@OrderPreserving X Y Xle Yle) (@OrderPreserving_proper_impl X Y Xle Yle).

Lemma OrderReflecting_proper_impl@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} {f g : X ⇾ Y}
  : f = g → impl (OrderReflecting f, OrderReflecting g).
Proof. intros E P. apply alt_Build_OrderReflecting. rew <-E. apply P. Qed.
Canonical Structure OrderReflecting_fun@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} :=
  make_weak_spred (@OrderReflecting X Y Xle Yle) (@OrderReflecting_proper_impl X Y Xle Yle).

Lemma OrderEmbedding_proper_impl@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} {f g : X ⇾ Y}
  : f = g → impl (OrderEmbedding f, OrderEmbedding g).
Proof. intros E P. split; now rew <-E. Qed.
Canonical Structure OrderEmbedding_fun@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} :=
  make_weak_spred (@OrderEmbedding X Y Xle Yle) (@OrderEmbedding_proper_impl X Y Xle Yle).


Lemma OrderPreservingFlip_proper_impl@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} {f g : X ⇾ Y}
  : f = g → impl (OrderPreservingFlip f, OrderPreservingFlip g).
Proof. intros E P. apply alt_Build_OrderPreservingFlip. rew <-E. apply P. Qed.
Canonical Structure OrderPreservingFlip_fun@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} :=
  make_weak_spred (@OrderPreservingFlip X Y Xle Yle) (@OrderPreservingFlip_proper_impl X Y Xle Yle).

Lemma OrderReflectingFlip_proper_impl@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} {f g : X ⇾ Y}
  : f = g → impl (OrderReflectingFlip f, OrderReflectingFlip g).
Proof. intros E P. apply alt_Build_OrderReflectingFlip. rew <-E. apply P. Qed.
Canonical Structure OrderReflectingFlip_fun@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} :=
  make_weak_spred (@OrderReflectingFlip X Y Xle Yle) (@OrderReflectingFlip_proper_impl X Y Xle Yle).

Lemma OrderEmbeddingFlip_proper_impl@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} {f g : X ⇾ Y}
  : f = g → impl (OrderEmbeddingFlip f, OrderEmbeddingFlip g).
Proof. intros E P. split; now rew <-E. Qed.
Canonical Structure OrderEmbeddingFlip_fun@{u} {X Y:set@{u}} {Xle:Le X} {Yle:Le Y} :=
  make_weak_spred (@OrderEmbeddingFlip X Y Xle Yle) (@OrderEmbeddingFlip_proper_impl X Y Xle Yle).


Lemma ap1_order_preserving@{u} {X Y Z:set@{u}} `{Le X} `{Le Y} `{Le Z} {f:X ⊗ Y ⇾ Z}
  `{!WeakPoset X, !WeakPoset Y, !OrderPreserving f} {x} : OrderPreserving (ap1 f x).
Proof. apply alt_Build_OrderPreserving; intros y₁ y₂. change (y₁ ≤ y₂ ⊸ f (x, y₁) ≤ f (x, y₂)).
  rew <-(order_preserving f _ _). unfold_pair_le; now simplify.
Qed.
#[global] Hint Extern 4 (OrderPreserving (func_op2 ap1 _ _)) => simple notypeclasses refine ap1_order_preserving : typeclass_instances.

Lemma ap2_order_preserving@{u} {X Y Z:set@{u}} `{Le X} `{Le Y} `{Le Z} {f:X ⊗ Y ⇾ Z}
  `{!WeakPoset X, !WeakPoset Y, !OrderPreserving f} {y} : OrderPreserving (ap2 f y).
Proof. apply alt_Build_OrderPreserving; intros x₁ x₂. change (x₁ ≤ x₂ ⊸ f (x₁, y) ≤ f (x₂, y)).
  rew <-(order_preserving f _ _). unfold_pair_le; now simplify.
Qed.
#[global] Hint Extern 4 (OrderPreserving (func_op2 ap2 _ _)) => simple notypeclasses refine ap2_order_preserving : typeclass_instances.

Lemma tensor_to_prod_order_preserving@{u} {X Y:set@{u}} `{Le X, Le Y, !WeakPoset X, !WeakPoset Y}
  : OrderPreserving (tensor_to_prod X Y).
Proof. apply alt_Build_OrderPreserving. intros [a b][c d].
  change (a ≤ c ⊠ b ≤ d ⊸ a ≤ c ∧ b ≤ d); tautological.
Qed.
#[global] Hint Extern 2 (OrderPreserving (tensor_to_prod _ _)) => simple notypeclasses refine tensor_to_prod_order_preserving : typeclass_instances.

Section simplify_variants.
  Universes u.
  Context {X Y:set@{u}} (f:X ⇾ Y).

  Lemma order_preserving_simp {Xle:Le X} {Yle:Le Y} {H:OrderPreserving f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : x ≤ y ⊸ fx ≤ fy.
  Proof. rew (order_preserving f _ _). now simplify. Qed.
  
  Lemma order_reflecting_simp {Xle:Le X} {Yle:Le Y} {H:OrderReflecting f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : fx ≤ fy ⊸ x ≤ y.
  Proof. rew <-(order_reflecting f x y). now simplify. Qed.
  
  Lemma order_embedding_simp {Xle:Le X} {Yle:Le Y} {H:OrderEmbedding f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : x ≤ y ⧟ fx ≤ fy.
  Proof. rew (order_embedding f _ _). now simplify. Qed.
  
  Lemma strictly_order_preserving_simp {Xle:Le X} {Yle:Le Y} {H:OrderReflecting f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : x < y ⊸ fx < fy.
  Proof. rew (strictly_order_preserving f _ _). now simplify. Qed.
  
  Lemma strictly_order_reflecting_simp {Xle:Le X} {Yle:Le Y} {H:OrderPreserving f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : fx < fy ⊸ x < y.
  Proof. rew <-(strictly_order_reflecting f x y). now simplify. Qed.
  
  Lemma strictly_order_embedding_simp {Xle:Le X} {Yle:Le Y} {H:OrderEmbedding f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : x < y ⧟ fx < fy.
  Proof. rew (strictly_order_embedding f _ _). now simplify. Qed.
  
  Lemma order_preserving_flip_simp {Xle:Le X} {Yle:Le Y} {H:OrderPreservingFlip f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : x ≤ y ⊸ fy ≤ fx.
  Proof. rew (order_preserving_flip f _ _). now simplify. Qed.
  
  Lemma order_reflecting_flip_simp {Xle:Le X} {Yle:Le Y} {H:OrderReflectingFlip f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : fy ≤ fx ⊸ x ≤ y.
  Proof. rew <-(order_reflecting_flip f x y). now simplify. Qed.
  
  Lemma order_embedding_flip_simp {Xle:Le X} {Yle:Le Y} {H:OrderEmbeddingFlip f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : x ≤ y ⧟ fy ≤ fx.
  Proof. rew (order_embedding_flip f _ _). now simplify. Qed.
  
  Lemma strictly_order_preserving_flip_simp {Xle:Le X} {Yle:Le Y} {H:OrderReflectingFlip f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : x < y ⊸ fy < fx.
  Proof. rew (strictly_order_preserving_flip f _ _). now simplify. Qed.
  
  Lemma strictly_order_reflecting_flip_simp {Xle:Le X} {Yle:Le Y} {H:OrderPreservingFlip f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : fy < fx ⊸ x < y.
  Proof. rew <-(strictly_order_reflecting_flip f x y). now simplify. Qed.
  
  Lemma strictly_order_embedding_flip_simp {Xle:Le X} {Yle:Le Y} {H:OrderEmbeddingFlip f} (x y : X)
    {fx fy} `{!SimplifiesTo (f x) fx, !SimplifiesTo (f y) fy}
    : x < y ⧟ fy < fx.
  Proof. rew (strictly_order_embedding_flip f _ _). now simplify. Qed.
End simplify_variants.


Lemma order_reflecting_injective@{u} {X Y:set@{u}} `{Poset X} `{Poset Y} {f:X ⇾ Y} `{!OrderReflecting f} : Injective f.
Proof. intros x y. rew [<-(le_antisym_iff _ y) | <-(le_antisym_iff _ (f y))].
  now rew (order_reflecting f _ _).
Qed.
Global Hint Extern 20 (Injective _) => simple notypeclasses refine order_reflecting_injective : typeclass_instances.
(* Coercion order_reflecting_injective : OrderReflecting >-> Injective. *)


Lemma linear_order_reflecting_embedding@{u} {X Y:set@{u}}
  `{Poset X} `{LinearOrder Y} `{!RefutativeOrder Y} {f:X ⇾ Y}
  : OrderReflecting f → OrderEmbedding f.
Proof. split; trivial. apply alt_Build_OrderPreserving. intros x y.
  rew (le_lt_par_eq x y). apply by_contrapositive.
  rew [(lt_iff_le_prod_ne _ (f x)) | (symmetry (=) x y)].
  now rew [(order_reflecting f _ _) | (contrapositive (is_fun f y x))].
Qed.

Lemma involutive_order_embedding@{u} {X:set@{u}} {Xle:Le X} (f:X ⇾ X) `{!Involutive f}
  : OrderPreserving f → OrderEmbedding f.
Proof. intro. split; try exact _. apply alt_Build_OrderReflecting. intros x y.
  rew <-(involutive_alt f x) at 2.
  rew <-(involutive_alt f y) at 2.
  now apply order_preserving.
Qed.

Lemma involutive_order_embedding_flip@{u} {X:set@{u}} {Xle:Le X} (f:X ⇾ X) `{!Involutive f}
  : OrderPreservingFlip f → OrderEmbeddingFlip f.
Proof. intro. split; try exact _. apply alt_Build_OrderReflectingFlip. intros x y.
  rew <-(involutive_alt f x) at 2.
  rew <-(involutive_alt f y) at 2.
  now apply order_preserving_flip.
Qed.


Lemma id_order_embedding `{Poset X} : OrderEmbedding (id_fun X).
Proof. now apply alt_Build_OrderEmbedding. Qed.
Global Hint Extern 2 (OrderEmbedding (id_fun _)) => simple notypeclasses refine id_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (id_fun _)) => simple notypeclasses refine id_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (id_fun _)) => simple notypeclasses refine id_order_embedding : typeclass_instances.

Section compose.
  Universes u.
  Context (X Y Z:set@{u}) {Xle:Le X} {Yle:Le Y} {Zle:Le Z} (g : Y ⇾ Z) (f : X ⇾ Y).

  Ltac go :=
    match goal with
    | |- OrderPreserving _ => apply alt_Build_OrderPreserving
    | |- OrderReflecting _ => apply alt_Build_OrderReflecting
    | |- OrderPreservingFlip _ => apply alt_Build_OrderPreservingFlip
    | |- OrderReflectingFlip _ => apply alt_Build_OrderReflectingFlip
    | _ => idtac
    end;
    intros x y; change (func_op (g ∘ f) ?x) with (g (f x));
    match goal with
    | _ : OrderPreserving g |- _ => rew <-(order_preserving g _ _)
    | _ : OrderReflecting g |- _ => rew (order_reflecting g _ _)
    | _ : OrderPreservingFlip g |- _ => rew <-(order_preserving_flip g _ _)
    | _ : OrderReflectingFlip g |- _ => rew (order_reflecting_flip g _ _)
    end;
    match goal with
    | _ : OrderPreserving f |- _ => exact (order_preserving f _ _)
    | _ : OrderReflecting f |- _ => exact (order_reflecting f _ _)
    | _ : OrderPreservingFlip f |- _ => exact (order_preserving_flip f _ _)
    | _ : OrderReflectingFlip f |- _ => exact (order_reflecting_flip f _ _)
    end.

  Instance OrderPreserving_compose `{!OrderPreserving f, !OrderPreserving g} : OrderPreserving (g ∘ f).  Proof. go. Qed.
  Instance OrderReflecting_compose `{!OrderReflecting f, !OrderReflecting g} : OrderReflecting (g ∘ f).  Proof. go. Qed.
  Instance OrderPreserving_compose_flip `{!OrderPreservingFlip f, !OrderPreservingFlip g} : OrderPreserving (g ∘ f).  Proof. go. Qed.
  Instance OrderReflecting_compose_flip `{!OrderReflectingFlip f, !OrderReflectingFlip g} : OrderReflecting (g ∘ f).  Proof. go. Qed.
  Instance OrderPreservingFlip_compose_l `{!OrderPreserving f, !OrderPreservingFlip g} : OrderPreservingFlip (g ∘ f).  Proof. go. Qed.
  Instance OrderReflectingFlip_compose_l `{!OrderReflecting f, !OrderReflectingFlip g} : OrderReflectingFlip (g ∘ f).  Proof. go. Qed.
  Instance OrderPreservingFlip_compose_r `{!OrderPreservingFlip f, !OrderPreserving g} : OrderPreservingFlip (g ∘ f).  Proof. go. Qed.
  Instance OrderReflectingFlip_compose_r `{!OrderReflectingFlip f, !OrderReflecting g} : OrderReflectingFlip (g ∘ f).  Proof. go. Qed.

  Instance OrderEmbedding_compose `{!OrderEmbedding f, !OrderEmbedding g} : OrderEmbedding (g ∘ f).  Proof. now split. Qed.
  Instance OrderEmbedding_compose_flip `{!OrderEmbeddingFlip f, !OrderEmbeddingFlip g} : OrderEmbedding (g ∘ f).  Proof. now split. Qed.
  Instance OrderEmbeddingFlip_compose_l `{!OrderEmbedding f, !OrderEmbeddingFlip g} : OrderEmbeddingFlip (g ∘ f).  Proof. now apply Build_OrderEmbeddingFlip. Qed.
  Instance OrderEmbeddingFlip_compose_r `{!OrderEmbeddingFlip f, !OrderEmbedding g} : OrderEmbeddingFlip (g ∘ f).  Proof. now apply Build_OrderEmbeddingFlip. Qed.
End compose.
Arguments OrderPreserving_compose {X Y Z _ _ _ g f} _ _.
Arguments OrderReflecting_compose {X Y Z _ _ _ g f} _ _.
Arguments OrderEmbedding_compose  {X Y Z _ _ _ g f} _ _.
Arguments OrderPreserving_compose_flip {X Y Z _ _ _ g f} _ _.
Arguments OrderReflecting_compose_flip {X Y Z _ _ _ g f} _ _.
Arguments OrderEmbedding_compose_flip  {X Y Z _ _ _ g f} _ _.
Arguments OrderPreservingFlip_compose_l {X Y Z _ _ _ g f} _ _.
Arguments OrderReflectingFlip_compose_l {X Y Z _ _ _ g f} _ _.
Arguments OrderEmbeddingFlip_compose_l  {X Y Z _ _ _ g f} _ _.
Arguments OrderPreservingFlip_compose_r {X Y Z _ _ _ g f} _ _.
Arguments OrderReflectingFlip_compose_r {X Y Z _ _ _ g f} _ _.
Arguments OrderEmbeddingFlip_compose_r  {X Y Z _ _ _ g f} _ _.


Section find_order_morphism_pack.
  Universes i.
  Local Definition find_order_preserving_pack :=
    let P := @OrderPreserving@{i} in
    let Pf := @OrderPreservingFlip@{i} in
    let c := @OrderPreserving_compose@{i} in
    let cf := @OrderPreserving_compose_flip@{i} in
    let cl := @OrderPreservingFlip_compose_l@{i} in
    let cr := @OrderPreservingFlip_compose_r@{i} in
    Type@{i}.
  Local Definition find_order_reflecting_pack :=
    let P := @OrderReflecting@{i} in
    let Pf := @OrderReflectingFlip@{i} in
    let c := @OrderReflecting_compose@{i} in
    let cf := @OrderReflecting_compose_flip@{i} in
    let cl := @OrderReflectingFlip_compose_l@{i} in
    let cr := @OrderReflectingFlip_compose_r@{i} in
    Type@{i}.
  Local Definition find_order_embedding_pack :=
    let P := @OrderEmbedding@{i} in
    let Pf := @OrderEmbeddingFlip@{i} in
    let c := @OrderEmbedding_compose@{i} in
    let cf := @OrderEmbedding_compose_flip@{i} in
    let cl := @OrderEmbeddingFlip_compose_l@{i} in
    let cr := @OrderEmbeddingFlip_compose_r@{i} in
    Type@{i}.
End find_order_morphism_pack.

Ltac find_order_morphism pack f :=
  lazymatch eval red in pack with let _ := ?P in let _ := ?Pf in let _ := ?c in let _ := ?cf in let _ := ?cl in let _ := ?cr in _ =>
    let rec aux f :=
      match f with
      | id_fun _ => constr:(_ : P _ _ _ _ f)
      | ?h ∘ ?g =>
         let Hg := aux g in
         let Hh := aux h in
         lazymatch type of Hg with
         | P _ _ _ _ _ => lazymatch type of Hh with
           | P _ _ _ _ _ => constr:(c _ _ _ _ _ _ _ _ Hg Hh)
           | Pf _ _ _ _ _ => constr:(cl _ _ _ _ _ _ _ _ Hg Hh)
           end
         | Pf _ _ _ _ _ => lazymatch type of Hh with
           | P _ _ _ _ _ => constr:(cr _ _ _ _ _ _ _ _ Hg Hh)
           | Pf _ _ _ _ _ => constr:(cf _ _ _ _ _ _ _ _ Hg Hh)
           end
         end
      | _ => constr:(_ : P _ _ _ _ f)
      | _ => constr:(_ : Pf _ _ _ _ f)
      end
    in aux f
  end.

Ltac find_compose_order_morphism pack f :=
  lazymatch eval red in pack with let _ := ?P in let _ := ?Pf in let _ := ?c in let _ := ?cf in let _ := ?cl in let _ := ?cr in _ =>
    let H := find_order_morphism pack f in lazymatch type of H with
    | P _ _ _ _ _ => simple notypeclasses refine (c _ _ _ _ _ _ _ _ H _)
    | Pf _ _ _ _ _ => simple notypeclasses refine (cf _ _ _ _ _ _ _ _ H _)
    end
  end.

Ltac find_compose_order_morphism_flip pack f :=
  lazymatch eval red in pack with let _ := ?P in let _ := ?Pf in let _ := ?c in let _ := ?cf in let _ := ?cl in let _ := ?cr in _ =>
    let H := find_order_morphism pack f in lazymatch type of H with
    | P _ _ _ _ _ => simple notypeclasses refine (cl _ _ _ _ _ _ _ _ H _)
    | Pf _ _ _ _ _ => simple notypeclasses refine (cr _ _ _ _ _ _ _ _ H _)
    end
  end.

Ltac find_order_preserving f := find_order_morphism find_order_preserving_pack f.
Ltac find_order_reflecting f := find_order_morphism find_order_reflecting_pack f.
Ltac find_order_embedding f := find_order_morphism find_order_embedding_pack f.
Ltac find_compose_order_preserving f := find_compose_order_morphism find_order_preserving_pack f.
Ltac find_compose_order_reflecting f := find_compose_order_morphism find_order_reflecting_pack f.
Ltac find_compose_order_embedding f := find_compose_order_morphism find_order_embedding_pack f.
Ltac find_compose_order_preserving_flip f := find_compose_order_morphism_flip find_order_preserving_pack f.
Ltac find_compose_order_reflecting_flip f := find_compose_order_morphism_flip find_order_reflecting_pack f.
Ltac find_compose_order_embedding_flip f := find_compose_order_morphism_flip find_order_embedding_pack f.

Global Hint Extern 2 (OrderPreserving (?g ∘ ?f)) => find_compose_order_preserving f : typeclass_instances.
Global Hint Extern 2 (OrderPreservingFlip (?g ∘ ?f)) => find_compose_order_preserving_flip f : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (?g ∘ ?f)) => find_compose_order_reflecting f : typeclass_instances.
Global Hint Extern 2 (OrderReflectingFlip (?g ∘ ?f)) => find_compose_order_reflecting_flip f : typeclass_instances.
Global Hint Extern 2 (OrderEmbedding (?g ∘ ?f)) => find_compose_order_embedding f : typeclass_instances.
Global Hint Extern 2 (OrderEmbeddingFlip (?g ∘ ?f)) => find_compose_order_embedding_flip f : typeclass_instances.

(* The two sides' function terms can differ in universe instances (e.g. when
   the rewrite engine re-elaborates one side), so a nonlinear pattern
   [?f _ ≤ ?f _] silently never matches.  House style: match both sides
   linearly and guard with [lazymatch f with g] — Ltac term matching against
   a bound variable ignores universes; the tactic body then collapses the
   universes by unification. *)
#[global] Hint Extern 4 (apos (func_op ?f _ ≤ func_op ?g _)) =>
  lazymatch f with g =>
  let H := find_order_preserving f in lazymatch type of H with
  | OrderPreserving _     => simple notypeclasses refine (sprop.andl ( order_preserving      _ (o:=H) _ _) (_ : _ ≤ _))
  | OrderPreservingFlip _ => simple notypeclasses refine (sprop.andl ( order_preserving_flip _ (H:=H) _ _) (_ : _ ≤ _))
  end end
: proper.

#[global] Hint Extern 10 (apos (?f ?x₁ ?x₂ ?x₃ ≤ ?g ?y₁ ?y₂ ?y₃ :> ?A)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) (eval_tuncurry3 f)) in
  change (f' (x₁, x₂, x₃) ≤ f' (y₁, y₂, y₃) :> A) end : proper.
#[global] Hint Extern 11 (apos (?f ?x₁ ?x₂ ≤ ?g ?y₁ ?y₂ :> ?A)) =>
  lazymatch f with g =>
  let f' := eval red in (@id (func _ _) (tuncurry f)) in
  change (f' (x₁, x₂) ≤ f' (y₁, y₂) :> A) end : proper.
#[global] Hint Extern 12 (apos (?f ?x ≤ ?g ?y :> ?A)) =>
  lazymatch f with g =>
    let f' := eval red in (@id (func _ _) f) in
    real_progress ltac:(fun _ => change (f' x ≤ f' y :> A)) end : proper.
  

Lemma op_order_morphism `{H:@OrderMorphism X Y Xle Yle} : OrderMorphism (X ᵒᵖ) (Y ᵒᵖ).
Proof. now split. Qed.
Global Hint Extern 2 (OrderMorphism (_ ᵒᵖ) (_ ᵒᵖ)) => simple notypeclasses refine op_order_morphism : typeclass_instances.

Lemma op_order_preserving `{H:OrderPreserving (X:=X) (Y:=Y) (f:=f)} : OrderPreserving (f:X ᵒᵖ ⇾ Y ᵒᵖ).
Proof. split; [ exact _ |]. intros x y. exact (order_preserving f y x). Qed.
Global Hint Extern 2 (OrderPreserving (X:=_ ᵒᵖ) (Y:=_ ᵒᵖ) _) => simple notypeclasses refine op_order_preserving : typeclass_instances.

Lemma op_order_preserving_iff { X Y Xle Yle} f : @OrderPreserving X Y Xle Yle f ↔ OrderPreserving (f:X ᵒᵖ ⇾ Y ᵒᵖ).
Proof. split. exact _. intro. now pose proof (_ : OrderPreserving (f:X ᵒᵖ ᵒᵖ ⇾ Y ᵒᵖ ᵒᵖ)). Qed.

Lemma op_order_reflecting `{H:OrderReflecting (X:=X) (Y:=Y) (f:=f)} : OrderReflecting (f:X ᵒᵖ ⇾ Y ᵒᵖ).
Proof. split; [ exact _ |]. intros x y. exact (order_reflecting f y x). Qed.
Global Hint Extern 2 (OrderReflecting (X:=_ ᵒᵖ) (Y:=_ ᵒᵖ) _) => simple notypeclasses refine op_order_reflecting : typeclass_instances.

Lemma op_order_reflecting_iff { X Y Xle Yle} f : @OrderReflecting X Y Xle Yle f ↔ OrderReflecting (f:X ᵒᵖ ⇾ Y ᵒᵖ).
Proof. split. exact _. intro. now pose proof (_ : OrderReflecting (f:X ᵒᵖ ᵒᵖ ⇾ Y ᵒᵖ ᵒᵖ)). Qed.

Lemma op_order_embedding `{H:OrderEmbedding (X:=X) (Y:=Y) (f:=f)} : OrderEmbedding (f:X ᵒᵖ ⇾ Y ᵒᵖ).
Proof. now split. Qed.
Global Hint Extern 2 (OrderEmbedding (X:=_ ᵒᵖ) (Y:=_ ᵒᵖ) _) => simple notypeclasses refine op_order_embedding : typeclass_instances.

Lemma op_order_embedding_iff { X Y Xle Yle} f : @OrderEmbedding X Y Xle Yle f ↔ OrderEmbedding (f:X ᵒᵖ ⇾ Y ᵒᵖ).
Proof. split. exact _. intro. now pose proof (_ : OrderEmbedding (f:X ᵒᵖ ᵒᵖ ⇾ Y ᵒᵖ ᵒᵖ)). Qed.

(** tensor map *)

Import tensor_map_notation.
Lemma tensor_map_applied_order_preserving `{@OrderPreserving X₁ Y₁ Xle₁ Yle₁ f₁} `{@OrderPreserving X₂ Y₂ Xle₂ Yle₂ f₂}
  : OrderPreserving ⟨f₁, f₂⟩.
Proof. apply alt_Build_OrderPreserving. intros [a b][c d].
  change (  a ≤ c ⊠ b ≤ d ⊸ f₁ a ≤ f₁ c ⊠ f₂ b ≤ f₂ d ).
  now rew [<-(order_preserving f₁ _ _)|<-(order_preserving f₂ _ _)].
Qed.
#[global] Hint Extern 2 (OrderPreserving ⟨_,_⟩) => simple notypeclasses refine tensor_map_applied_order_preserving : typeclass_instances.

Lemma tensor_map_applied_order_preserving_flip `{@OrderPreservingFlip X₁ Y₁ Xle₁ Yle₁ f₁} `{@OrderPreservingFlip X₂ Y₂ Xle₂ Yle₂ f₂}
  : OrderPreservingFlip ⟨f₁, f₂⟩.
Proof. apply alt_Build_OrderPreservingFlip. intros [a b][c d].
  change (  a ≤ c ⊠ b ≤ d ⊸ f₁ c ≤ f₁ a ⊠ f₂ d ≤ f₂ b ).
  now rew [<-(order_preserving_flip f₁ _ _)|<-(order_preserving_flip f₂ _ _)].
Qed.
#[global] Hint Extern 2 (OrderPreservingFlip ⟨_,_⟩) => simple notypeclasses refine tensor_map_applied_order_preserving_flip : typeclass_instances.

Lemma tensor_map_applied_order_reflecting `{@OrderReflecting X₁ Y₁ Xle₁ Yle₁ f₁} `{@OrderReflecting X₂ Y₂ Xle₂ Yle₂ f₂}
  : OrderReflecting ⟨f₁, f₂⟩.
Proof. apply alt_Build_OrderReflecting. intros [a b][c d].
  change (  f₁ a ≤ f₁ c ⊠ f₂ b ≤ f₂ d ⊸ a ≤ c ⊠ b ≤ d ).
  now rew [(order_reflecting f₁ _ _)|(order_reflecting f₂ _ _)].
Qed.
#[global] Hint Extern 2 (OrderReflecting ⟨_,_⟩) => simple notypeclasses refine tensor_map_applied_order_reflecting : typeclass_instances.

Lemma tensor_map_applied_order_reflecting_flip `{@OrderReflectingFlip X₁ Y₁ Xle₁ Yle₁ f₁} `{@OrderReflectingFlip X₂ Y₂ Xle₂ Yle₂ f₂}
  : OrderReflectingFlip ⟨f₁, f₂⟩.
Proof. apply alt_Build_OrderReflectingFlip. intros [a b][c d].
  change (  f₁ c ≤ f₁ a ⊠ f₂ d ≤ f₂ b ⊸ a ≤ c ⊠ b ≤ d ).
  now rew [(order_reflecting_flip f₁ _ _)|(order_reflecting_flip f₂ _ _)].
Qed.
#[global] Hint Extern 2 (OrderReflectingFlip ⟨_,_⟩) => simple notypeclasses refine tensor_map_applied_order_reflecting_flip : typeclass_instances.

Lemma tensor_map_applied_order_embedding `{@OrderEmbedding X₁ Y₁ Xle₁ Yle₁ f₁} `{@OrderEmbedding X₂ Y₂ Xle₂ Yle₂ f₂}
  : OrderEmbedding ⟨f₁, f₂⟩.
Proof. now split. Qed.
#[global] Hint Extern 2 (OrderEmbedding ⟨_,_⟩) => simple notypeclasses refine tensor_map_applied_order_embedding : typeclass_instances.

Lemma tensor_map_applied_order_embedding_flip `{@OrderEmbeddingFlip X₁ Y₁ Xle₁ Yle₁ f₁} `{@OrderEmbeddingFlip X₂ Y₂ Xle₂ Yle₂ f₂}
  : OrderEmbeddingFlip ⟨f₁, f₂⟩.
Proof. now apply Build_OrderEmbeddingFlip. Qed.
#[global] Hint Extern 2 (OrderEmbeddingFlip ⟨_,_⟩) => simple notypeclasses refine tensor_map_applied_order_embedding_flip : typeclass_instances.

