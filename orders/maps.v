Require Import orders.orders interfaces.common_props.
Require Import relations easy rewrite.

Local Notation "X 'ᵒᵖ'" := (order_op X) (at level 1, format "X 'ᵒᵖ'").

Lemma alt_Build_OrderPreserving `{WeakPoset X} `{WeakPoset Y} {f:X ⇾ Y} : (∀ x y : X, x ≤ y ⊸ f x ≤ f y) → OrderPreserving f.  Proof. now split. Qed.
Lemma alt_Build_OrderReflecting `{WeakPoset X} `{WeakPoset Y} {f:X ⇾ Y} : (∀ x y : X, f x ≤ f y ⊸ x ≤ y) → OrderReflecting f.  Proof. now split. Qed.
Lemma alt_Build_OrderEmbedding  `{WeakPoset X} `{WeakPoset Y} {f:X ⇾ Y} : (∀ x y : X, x ≤ y ⧟ f x ≤ f y) → OrderEmbedding f.
Proof. intros P. split; [ apply alt_Build_OrderPreserving, P | apply alt_Build_OrderReflecting, P ]. Qed.

Definition alt_Build_OrderPreservingFlip `{WeakPoset X} `{WeakPoset Y} {f:X ⇾ Y} (H : ∀ x y : X, x ≤ y ⊸ f y ≤ f x) : OrderPreservingFlip f := alt_Build_OrderPreserving H.
Definition alt_Build_OrderReflectingFlip `{WeakPoset X} `{WeakPoset Y} {f:X ⇾ Y} (H : ∀ x y : X, f y ≤ f x ⊸ x ≤ y) : OrderReflectingFlip f := alt_Build_OrderReflecting H.
Definition alt_Build_OrderEmbeddingFlip  `{WeakPoset X} `{WeakPoset Y} {f:X ⇾ Y} (H : ∀ x y : X, x ≤ y ⧟ f y ≤ f x) : OrderEmbeddingFlip f := alt_Build_OrderEmbedding H.
Definition Build_OrderEmbeddingFlip  {X:set} `{Le X} {Y:set} `{Le Y} {f:X ⇾ Y} :
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

Lemma order_morphism_flip {X Y : set} {Xle:Le X} {Yle:Le Y} : OrderMorphism X (Y ᵒᵖ) → OrderMorphism X Y.
Proof. split. exact H. refine WeakPoset_op. apply H. Qed.

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

Lemma order_reflecting_injective `{Poset X} `{Poset Y} {f:X ⇾ Y} `{!OrderReflecting f} : Injective f.
Proof. intros x y. rew [<-(le_antisym_iff _ y) | <-(le_antisym_iff _ (f y))].
  now rew !2(order_reflecting f _ _).
Qed.
Global Hint Extern 20 (Injective _) => simple notypeclasses refine order_reflecting_injective : typeclass_instances.
(* Coercion order_reflecting_injective : OrderReflecting >-> Injective. *)


Lemma linear_order_reflecting_embedding
  `{Poset X} `{LinearOrder Y} `{!RefutativeOrder Y} {f:X ⇾ Y}
  : OrderReflecting f → OrderEmbedding f.
Proof. split; trivial. apply alt_Build_OrderPreserving. intros x y.
  rew (le_lt_par_eq x y). apply by_contrapositive.
  rew [(lt_iff_le_prod_ne _ (f x)) | (symmetry (=) x y)].
  now rew [(order_reflecting f _ _) | (contrapositive (is_fun f y x))].
Qed.



Lemma id_order_embedding `{Poset X} : OrderEmbedding (id_fun X).
Proof. now apply alt_Build_OrderEmbedding. Qed.
Global Hint Extern 2 (OrderEmbedding (id_fun _)) => simple notypeclasses refine id_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (id_fun _)) => simple notypeclasses refine id_order_embedding : typeclass_instances.
Global Hint Extern 2 (OrderReflecting (id_fun _)) => simple notypeclasses refine id_order_embedding : typeclass_instances.

Section compose.
  Universes i.
  Context (X Y Z:set@{i}) {Xle:Le X} {Yle:Le Y} {Zle:Le Z} (g : Y ⇾ Z) (f : X ⇾ Y).

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

  Instance OrderPreserving_compose `{!OrderPreserving f} `{!OrderPreserving g} : OrderPreserving (g ∘ f).  Proof. go. Qed.
  Instance OrderReflecting_compose `{!OrderReflecting f} `{!OrderReflecting g} : OrderReflecting (g ∘ f).  Proof. go. Qed.
  Instance OrderPreserving_compose_flip `{!OrderPreservingFlip f} `{!OrderPreservingFlip g} : OrderPreserving (g ∘ f).  Proof. go. Qed.
  Instance OrderReflecting_compose_flip `{!OrderReflectingFlip f} `{!OrderReflectingFlip g} : OrderReflecting (g ∘ f).  Proof. go. Qed.
  Instance OrderPreservingFlip_compose_l `{!OrderPreserving f} `{!OrderPreservingFlip g} : OrderPreservingFlip (g ∘ f).  Proof. go. Qed.
  Instance OrderReflectingFlip_compose_l `{!OrderReflecting f} `{!OrderReflectingFlip g} : OrderReflectingFlip (g ∘ f).  Proof. go. Qed.
  Instance OrderPreservingFlip_compose_r `{!OrderPreservingFlip f} `{!OrderPreserving g} : OrderPreservingFlip (g ∘ f).  Proof. go. Qed.
  Instance OrderReflectingFlip_compose_r `{!OrderReflectingFlip f} `{!OrderReflecting g} : OrderReflectingFlip (g ∘ f).  Proof. go. Qed.

  Instance OrderEmbedding_compose `{!OrderEmbedding f} `{!OrderEmbedding g} : OrderEmbedding (g ∘ f).  Proof. now split. Qed.
  Instance OrderEmbedding_compose_flip `{!OrderEmbeddingFlip f} `{!OrderEmbeddingFlip g} : OrderEmbedding (g ∘ f).  Proof. now split. Qed.
  Instance OrderEmbeddingFlip_compose_l `{!OrderEmbedding f} `{!OrderEmbeddingFlip g} : OrderEmbeddingFlip (g ∘ f).  Proof. now apply Build_OrderEmbeddingFlip. Qed.
  Instance OrderEmbeddingFlip_compose_r `{!OrderEmbeddingFlip f} `{!OrderEmbedding g} : OrderEmbeddingFlip (g ∘ f).  Proof. now apply Build_OrderEmbeddingFlip. Qed.
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

Global Hint Extern 4 (apos (func_op ?f _ ≤ func_op ?f _)) =>
  let H := find_order_preserving f in lazymatch type of H with
  | OrderPreserving _     => refine (sprop.andl ( order_preserving      _ (o:=H) _ _) _)
  | OrderPreservingFlip _ => refine (sprop.andl ( order_preserving_flip _ (H:=H) _ _) _)
  end
: proper.


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

