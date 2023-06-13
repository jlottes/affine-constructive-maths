Require Import abstract_algebra theory.lattices orders.orders orders.maps.
Require Import easy rewrite logic.aprop logic.relations refutative tactics.misc.

Local Notation "X 'ᵒᵖ'" := (order_op X) (at level 1, format "X 'ᵒᵖ'").

Lemma Build_JoinSemiLatticeOrder `{Poset L} `{Join L} :
  (∀ x y : L, x ≤ x ⊔ y) →
  (∀ x y : L, y ≤ x ⊔ y) →
  (∀ x y z : L, x ≤ z ⊠ y ≤ z ⊸ x ⊔ y ≤ z) →
  JoinSemiLatticeOrder L.
Proof. now split. Qed.

Definition JoinSemiLatticeOrder_poset `{H:JoinSemiLatticeOrder L} : Poset L := Poset_op.
Coercion JoinSemiLatticeOrder_poset : JoinSemiLatticeOrder >-> Poset.

Definition MeetSemiLatticeOrder_op `{H:JoinSemiLatticeOrder L} : MeetSemiLatticeOrder (L ᵒᵖ) := H.
Definition JoinSemiLatticeOrder_op `{H:MeetSemiLatticeOrder L} : JoinSemiLatticeOrder (L ᵒᵖ) := H.
Global Hint Extern 2 (MeetSemiLatticeOrder (_ ᵒᵖ)) => simple notypeclasses refine MeetSemiLatticeOrder_op : typeclass_instances.
Global Hint Extern 2 (JoinSemiLatticeOrder (_ ᵒᵖ)) => simple notypeclasses refine JoinSemiLatticeOrder_op : typeclass_instances.
Lemma LatticeOrder_op `{LatticeOrder L} : LatticeOrder (L ᵒᵖ).  Proof. now split. Qed.
Global Hint Extern 2 (LatticeOrder (_ ᵒᵖ)) => simple notypeclasses refine LatticeOrder_op : typeclass_instances.


(** A join or meet operation satisfying the semilattice order axioms is
    automatically a function (respects equality). *)
Section join_from_op.
  Universes i.
  Context `{Poset@{i} L} (jn:L → L → L).
  Context (ub_l : ∀ x y, x ≤ jn x y)
          (ub_r : ∀ x y, y ≤ jn x y)
          (lub : ∀ x y z, x ≤ z ⊠ y ≤ z ⊸ jn x y ≤ z).

  Local Instance jn_is_fun : @IsFun@{i} (L ⊗ L) L (λ '(x, y), jn x y).
  Proof. intros [x₁ y₁][x₂ y₂].
    change (x₁ = x₂ ⊠ y₁ = y₂ ⊸ jn x₁ y₁ = jn x₂ y₂).
    rew <-(antisymmetry (≤) (jn _ _) _).
    apply aand_intro; rew <-(lub _ _ _);
    refine (aprod_proper_aimpl _ _);
    [ rew <-(ub_l _ _) | rew <-(ub_r _ _)
    | rew <-(ub_l _ _) | rew <-(ub_r _ _) ];
    try match goal with |- apos (?a = ?b ⊸ le ?b ?a) => change (a = b ⊸ flip le a b) end;
    now apply subrelation.
  Qed.

  Instance join_from_op : Join L := @func_make (L ⊗ L) L (λ '(x, y), jn x y) _.
  Lemma join_from_op_sl_order : JoinSemiLatticeOrder L.
  Proof. now apply Build_JoinSemiLatticeOrder. Qed.
End join_from_op.
Global Hint Extern 2 (@JoinSemiLatticeOrder _ (join_from_op _ _ _ _)) =>
  simple notypeclasses refine (join_from_op_sl_order _ _ _ _) : typeclass_instances.

Section meet_from_op.
  Universes i.
  Context `{Poset@{i} L} (mt:L → L → L).
  Context (lb_l : ∀ x y, mt x y ≤ x)
          (lb_r : ∀ x y, mt x y ≤ y)
          (glb : ∀ x y z, z ≤ x ⊠ z ≤ y ⊸ z ≤ mt x y).

  Instance meet_from_op : Meet L := join_from_op (L:=L ᵒᵖ) mt lb_l lb_r glb.
  Definition meet_from_op_sl_order : MeetSemiLatticeOrder L := join_from_op_sl_order (L:=L ᵒᵖ) _ _ _ _.
End meet_from_op.
Global Hint Extern 2 (@MeetSemiLatticeOrder _ (meet_from_op _ _ _ _)) =>
  simple notypeclasses refine (meet_from_op_sl_order _ _ _ _) : typeclass_instances.

Section join_ub_3.
  Universes i.
  Context `{JoinSemiLatticeOrder@{i} L}.

  Local Ltac join_ub :=
    match goal with
      | |- apos (?x ≤ ?y ⊔ ?z) =>
        match x with
        | y => apply join_ub_l
        | z => apply join_ub_r
        end
    end.

  Lemma join_ub_3_r (x y z : L) : z ≤ x ⊔ y ⊔ z.  Proof join_ub_r _ _.
  Lemma join_ub_3_m (x y z : L) : y ≤ x ⊔ y ⊔ z.  Proof. trans (x ⊔ y); join_ub. Qed.
  Lemma join_ub_3_l (x y z : L) : x ≤ x ⊔ y ⊔ z.  Proof. trans (x ⊔ y); join_ub. Qed.

  Lemma join_ub_3_assoc_l (x y z : L) : x ≤ x ⊔ (y ⊔ z).  Proof join_ub_l _ _.
  Lemma join_ub_3_assoc_m (x y z : L) : y ≤ x ⊔ (y ⊔ z).  Proof. trans (y ⊔ z); join_ub. Qed.
  Lemma join_ub_3_assoc_r (x y z : L) : z ≤ x ⊔ (y ⊔ z).  Proof. trans (y ⊔ z); join_ub. Qed.
End join_ub_3.

Section meet_lb_3.
  Universes i.
  Context `{MeetSemiLatticeOrder@{i} L}.

  Lemma meet_lb_3_r (x y z : L) : x ⊓ y ⊓ z ≤ z.  Proof meet_lb_r _ _.
  Definition meet_lb_3_m : ∀ (x y z : L), x ⊓ y ⊓ z ≤ y := exact:(join_ub_3_m (L:=L ᵒᵖ)).
  Definition meet_lb_3_l : ∀ (x y z : L), x ⊓ y ⊓ z ≤ x := exact:(join_ub_3_l (L:=L ᵒᵖ)).

  Lemma meet_lb_3_assoc_l (x y z : L) : x ⊓ (y ⊓ z) ≤ x.  Proof meet_lb_l _ _.
  Definition meet_lb_3_assoc_m : ∀ (x y z : L), x ⊓ (y ⊓ z) ≤ y := exact:(join_ub_3_assoc_m (L:=L ᵒᵖ)).
  Definition meet_lb_3_assoc_r : ∀ (x y z : L), x ⊓ (y ⊓ z) ≤ z := exact:(join_ub_3_assoc_r (L:=L ᵒᵖ)).
End meet_lb_3.

(** A (very) simple tactic for solving / simplifying inequalities involving lattice ops *)
Ltac lattice_order_tac :=
    repeat match goal with
      | |- apos (?x ≤ ?x) => refl
      | |- apos (?x ⊓ _ ≤ ?x) => apply meet_lb_l
      | |- apos (_ ⊓ ?x ≤ ?x) => apply meet_lb_r
      | |- apos (?x ⊓ _ ⊓ _ ≤ ?x) => apply meet_lb_3_l
      | |- apos (_ ⊓ ?x ⊓ _ ≤ ?x) => apply meet_lb_3_m
      | |- apos (_ ⊓ (?x ⊓ _) ≤ ?x) => apply meet_lb_3_assoc_m
      | |- apos (_ ⊓ (_ ⊓ ?x) ≤ ?x) => apply meet_lb_3_assoc_r
      | |- apos (?x ≤ ?x ⊔ _) => apply join_ub_l
      | |- apos (?x ≤ _ ⊔ ?x) => apply join_ub_r
      | |- apos (?x ≤ ?x ⊔ _ ⊔ _) => apply join_ub_3_l
      | |- apos (?x ≤ _ ⊔ ?x ⊔ _) => apply join_ub_3_m
      | |- apos (?x ≤ _ ⊔ (?x ⊔ _)) => apply join_ub_3_assoc_m
      | |- apos (?x ≤ _ ⊔ (_ ⊔ ?x)) => apply join_ub_3_assoc_r
      | |- apos (?x ⊔ _ ≤ ?x) => rew <-(join_lub x _ x); split
      | |- apos (_ ⊔ ?x ≤ ?x) => rew <-(join_lub _ x x); split
      | |- apos (?x ≤ ?x ⊓ _) => rew <-(meet_glb x _ x); split
      | |- apos (?x ≤ _ ⊓ ?x) => rew <-(meet_glb _ x x); split
    end.

(** The order-theoretic semilattice structures are instances of the algebraic ones *)
Lemma join_sl_order_join_sl `{JoinSemiLatticeOrder L} : JoinSemiLattice L.
Proof. apply alt_Build_JoinSemiLattice.
+ intros x y z. rew <-(antisymmetry (≤) _ _); split.
  * rew <-(join_lub _ _ _); split; [| rew <-(join_lub (L:=L) _ _ _); split ]; lattice_order_tac.
  * rew <-(join_lub _ _ _); split; [ rew <-(join_lub (L:=L) _ _ _); split |]; lattice_order_tac.
+ intros x y. rew <-(antisymmetry (≤) _ _); split;
    rew <-(join_lub (L:=L) _ _ _); split; lattice_order_tac.
+ intros x. rew <-(antisymmetry (≤) _ _); split;
  [ rew <-(join_lub (L:=L) _ _ _); now split | lattice_order_tac ].
Qed.
Coercion join_sl_order_join_sl : JoinSemiLatticeOrder >-> JoinSemiLattice.
Global Hint Extern 4 (JoinSemiLattice _) => simple notypeclasses refine join_sl_order_join_sl : typeclass_instances.

Coercion meet_sl_order_meet_sl `{MeetSemiLatticeOrder L} : MeetSemiLattice L := _ : JoinSemiLattice L ᵒᵖ.
Global Hint Extern 4 (MeetSemiLattice _) => simple notypeclasses refine meet_sl_order_meet_sl : typeclass_instances.

Section join_sl.
  Universes i.
  Context `{JoinSemiLatticeOrder@{i} L}.

  (*Lemma join_le_compat_r (x y z : L) : z ≤ x ⊸ z ≤ x ⊔ y.  Proof. now rew <-(join_ub_l _ _). Qed.
  Lemma join_le_compat_l (x y z : L) : z ≤ y ⊸ z ≤ x ⊔ y.  Proof. now rew <-(join_ub_r _ _). Qed.*)

  Lemma join_l_iff (x y : L) : y ≤ x ⧟ x ⊔ y = x.
  Proof. rew <-(le_antisym_iff (P:=L) _ _).
    rew (aand_true_r (join_ub_l _ _)).
    split.
    + rew <-(join_lub (L:=L) _ _ _).
      now rew (aprod_true_l (_ : x ≤ x)).
    + now rew (join_ub_r x y) at 2.
  Qed.
  Lemma join_l {x y : L} : y ≤ x → x ⊔ y = x.  Proof. apply join_l_iff. Qed.

  Lemma join_r_iff (x y : L) : x ≤ y ⧟ x ⊔ y = y.
  Proof. rew (commutativity (⊔) x y). apply join_l_iff. Qed.
  Lemma join_r {x y : L} : x ≤ y → x ⊔ y = y.  Proof. apply join_r_iff. Qed.

  Definition join_ne_l_iff (x y : L) : x < y ⧟ x ⊔ y ≠ x := acontra_iff (join_l_iff _ _).
  Definition join_ne_r_iff (x y : L) : y < x ⧟ x ⊔ y ≠ y := acontra_iff (join_r_iff _ _).

  Lemma join_order_preserving : OrderPreserving (@join L _).
  Proof. split; [ now split |].
    intros [x₁ y₁][x₂ y₂]. change (x₁ ≤ x₂ ⊠ y₁ ≤ y₂ ⊸ x₁ ⊔ y₁ ≤ x₂ ⊔ y₂).
    rew <-(join_lub (L:=L) _ _ _).
    rew <-(join_ub_l x₂ y₂) at 1.
    rew <-(join_ub_r x₂ y₂).
    refl.
  Qed.

(*
  Lemma join_le_compat (x₁ x₂ y₁ y₂ : L) : x₁ ≤ x₂ ⊠ y₁ ≤ y₂ ⊸ x₁ ⊔ y₁ ≤ x₂ ⊔ y₂.
  Proof.
    rew <-(join_lub (L:=L) _ _ _).
    rew <-(join_ub_l x₂ y₂) at 1.
    rew <-(join_ub_r x₂ y₂).
    refl.
  Qed.

  Lemma join_proper_le {x₁:L} {x₂ y₁ y₂} : (x₁ ≤ x₂) → (y₁ ≤ y₂) → x₁ ⊔ y₁ ≤ x₂ ⊔ y₂.
  Proof. intros. rew <-(join_le_compat _ _ _ _). now split. Qed.

  Instance join_l_order_preserving (z:L) : OrderPreserving (z ⊔).
  Proof. apply alt_Build_OrderPreserving. intros x y. change ( x ≤ y ⊸ z ⊔ x ≤ z ⊔ y ).
    rew <-(join_le_compat _ _ _ _).
    now rew (aprod_true_l (_ : z ≤ z)).
  Qed.

  Instance join_r_order_preserving (z:L) : OrderPreserving (⊔ z).
  Proof. apply alt_Build_OrderPreserving. intros x y. change ( x ≤ y ⊸ x ⊔ z ≤ y ⊔ z ).
    rew <-(join_le_compat _ _ _ _).
    now rew (aprod_true_r (_ : z ≤ z)).
  Qed.
*)
End join_sl.
(*
Global Hint Extern 2 (OrderPreserving (_ ⊔)) => simple notypeclasses refine (join_l_order_preserving _) : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (⊔ _)) => simple notypeclasses refine (join_r_order_preserving _) : typeclass_instances.
*)
Global Hint Extern 2 (OrderPreserving (⊔)) => simple notypeclasses refine join_order_preserving : typeclass_instances.

Section meet_sl.
  Universes i.
  Context `{MeetSemiLatticeOrder@{i} L}.

  Definition meet_l_iff : ∀ (x y : L), x ≤ y ⧟ x ⊓ y = x := join_l_iff (L:=L ᵒᵖ).
  Definition meet_r_iff : ∀ (x y : L), y ≤ x ⧟ x ⊓ y = y := join_r_iff (L:=L ᵒᵖ).
  Definition meet_l {x : L} {y} : x ≤ y → x ⊓ y = x := join_l (L:=L ᵒᵖ).
  Definition meet_r {x : L} {y} : y ≤ x → x ⊓ y = y := join_r (L:=L ᵒᵖ).

  Definition meet_ne_l_iff (x y : L) : y < x ⧟ x ⊓ y ≠ x := acontra_iff (meet_l_iff _ _).
  Definition meet_ne_r_iff (x y : L) : x < y ⧟ x ⊓ y ≠ y := acontra_iff (meet_r_iff _ _).

  Lemma meet_order_preserving : OrderPreserving (@meet L _).
  Proof. apply alt_Build_OrderPreserving. intros [x₁ y₁][x₂ y₂]. unfold_pair_le.
    pose proof (order_preserving ((⊔) : L ᵒᵖ ⊗ L ᵒᵖ ⇾ L ᵒᵖ)) as P.
    exact ( P (x₂, y₂) (x₁, y₁) ).
  Qed.
(*
  Lemma meet_le_compat (x₁ x₂ y₁ y₂ : L) : x₁ ≤ x₂ ⊠ y₁ ≤ y₂ ⊸ x₁ ⊓ y₁ ≤ x₂ ⊓ y₂.
  Proof. apply exact:(join_le_compat (L:=L ᵒᵖ)). Qed.

  Lemma meet_proper_le {x₁:L} {x₂ y₁ y₂} : (x₁ ≤ x₂) → (y₁ ≤ y₂) → x₁ ⊓ y₁ ≤ x₂ ⊓ y₂.
  Proof. apply exact:(@join_proper_le (L ᵒᵖ) _ _ _). Qed.

  Lemma meet_l_order_preserving (z:L) : OrderPreserving (z ⊓).
  Proof. apply alt_Build_OrderPreserving. intros. apply exact:(order_preserving (((z:L ᵒᵖ) ⊔) : L ᵒᵖ ⇾ L ᵒᵖ)). Qed.

  Lemma meet_r_order_preserving (z:L) : OrderPreserving (⊓ z).
  Proof. apply alt_Build_OrderPreserving. intros. apply exact:(order_preserving ((⊔ (z:L ᵒᵖ)) : L ᵒᵖ ⇾ L ᵒᵖ)). Qed.
*)
End meet_sl.
(*
Global Hint Extern 2 (OrderPreserving (_ ⊓)) => simple notypeclasses refine (meet_l_order_preserving _) : typeclass_instances.
Global Hint Extern 2 (OrderPreserving (⊓ _)) => simple notypeclasses refine (meet_r_order_preserving _) : typeclass_instances.
*)
Global Hint Extern 2 (OrderPreserving (⊓)) => simple notypeclasses refine meet_order_preserving : typeclass_instances.

(*Global Hint Extern 2 (apos ((_ ⊔ _) ≤ _)) => proper 2 join_proper_le : proper.
Global Hint Extern 2 (apos ((_ ⊓ _) ≤ _)) => proper 2 meet_proper_le : proper.*)

Section bounded_join_semilattice.
  Universes i.
  Context `{JoinSemiLatticeOrder@{i} L} `{Bottom L} `{!BoundedJoinSemiLattice L}.

  Lemma above_bottom (x : L) : ⊥ ≤ x.
  Proof. rew (join_l_iff (L:=L) _ _). exact (join_bot_r _). Qed.

  Lemma below_bottom (x:L) : x ≤ ⊥ ⧟ x = ⊥.
  Proof. now rew (join_l_iff (L:=L) _ _), (join_bot_l _). Qed.
End bounded_join_semilattice.

Section bounded_meet_semilattice.
  Universes i.
  Context `{MeetSemiLatticeOrder@{i} L} `{Top L} `{!BoundedMeetSemiLattice L}.

  Definition below_top : ∀ x:L, x ≤ ⊤ := exact:(above_bottom (L:=L ᵒᵖ)).
  Definition above_top : ∀ x:L, ⊤ ≤ x ⧟ x = ⊤ := exact:(below_bottom (L:=L ᵒᵖ)).
End bounded_meet_semilattice.

Section lattice_order.
  (** The order-theoretic lattice structure is an instance of the algebraic one *)
  Instance lattice_order_lattice `{LatticeOrder L} : Lattice L.
  Proof. split; try exact _; intros x y; rew <-(le_antisym_iff _ x); split; lattice_order_tac. Qed.

  (** One direction of the distributivity laws is always satisfied. *)
  Lemma meet_join_distr_l_le `{LatticeOrder L}
    (x y z : L) : (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z).
  Proof.
    rew <-(meet_glb (L:=L) _ _ _); split; rew <-(join_lub (L:=L) _ _ _); split; lattice_order_tac.
    trans y; lattice_order_tac.
    trans z; lattice_order_tac.
  Qed.

  Lemma join_meet_distr_l_le `{LatticeOrder L} :
    ∀ x y z : L, x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ (x ⊔ z).
  Proof exact:(meet_join_distr_l_le (L:=L ᵒᵖ)).


  Lemma Build_DistributiveLatticeOrder `{LatticeOrder L} :
    (∀ x y z : L, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z) → DistributiveLattice L.
  Proof. intro. apply alt_Build_DistributiveLattice.
    intros x y z. rew <-(le_antisym_iff (P:=L) _ _); split; [ apply join_meet_distr_l_le | trivial ].
  Qed.

  (** A lattice order that is linear and refutative is distributive. *)
  Lemma lattice_order_distr `{LatticeOrder L} `{!LinearOrder L} `{!RefutativeOrder L} : DistributiveLattice L.
  Proof. apply Build_DistributiveLatticeOrder. intros x y z.
    apply (refutative_by_aff_cases (x ≤ y)); intros [Ey|Ey];
      [ rew (join_r Ey) | rew (lt_le y x) in Ey; rew (join_l Ey) ];
    apply (refutative_by_aff_cases (x ≤ z)); (intros [Ez|Ez];
      [ rew (join_r Ez) | rew (lt_le z x) in Ez; rew (join_l Ez) ]).
  + lattice_order_tac.
  + rew (meet_r Ey). lattice_order_tac.
  + rew (meet_l Ez). lattice_order_tac.
  + rew (binary_idempotency (⊓) _). lattice_order_tac.
  Qed.
End lattice_order.
Coercion lattice_order_lattice : LatticeOrder >-> Lattice.
Global Hint Extern 4 (DistributiveLattice _) => simple notypeclasses refine lattice_order_distr : typeclass_instances.

(** In the other direction, a strong partial order can be recovered from
    a strong (algebraic) meet or join semilattice. *)
Section from_meet_semilattice.
  Universes i.
  Context `{MeetSemiLattice@{i} L} `{!StrongSet L} `{Le L}.
  Context (le_correct : ∀ x y : L, x ≤ y ⧟ x ⊓ y = x).

  Let inst: @StronglyTransitive@{i} L (≤).
  Proof. intros x y z; rew ?(le_correct _ _).
    rew <-(strong_transitivity (=) (x ⊓ z) (x ⊓ y) x).
    apply aand_intro; [| exact _ ].
    rew (is_fun (⊓ z) (x ⊓ y) x : _ ⊸ x ⊓ y ⊓ z = x ⊓ z), (symmetry_iff (=) _ (x ⊓ z)).
    rew (is_fun (x ⊓) (y ⊓ z) y : _ ⊸ x ⊓ (y ⊓ z) = x ⊓ y), (associativity _ _ _ _).
    exact (strong_transitivity (=) _ _ _).
  Qed.

  Instance: PreOrder L.
  Proof. split; [| exact _].
    intro x. rew (le_correct _ _).
    now apply binary_idempotency.
  Qed.

  Instance: Poset L.
  Proof. apply alt_Build_Poset; try exact _; hnf; intros x y.
  + rew (is_fun (x ⊓) _ _ : _ ⊸ x ⊓ _ = x ⊓ _).
    rew [ (binary_idempotency (⊓) _) | (le_correct _ _) ].
    now apply symmetry.
  + rew ?(le_correct _ _).
    rew [(symmetry_iff (=) _ x) | (commutativity (⊓) y x) ].
    exact (strong_transitivity (=) x (x ⊓ y) y).
  Qed.

  Lemma from_meet_sl_strong : StrongPoset L.
  Proof. now split. Qed.

  Instance from_meet_sl_meet_order : MeetSemiLatticeOrder L.
  Proof. apply Build_MeetSemiLatticeOrder.
  + exact _.
  + intros x y.
    now rew (le_correct _ _), (commutativity (⊓) x y), <-(associativity _ _ _ _), (binary_idempotency _ _).
  + intros x y. now rew (le_correct _ _), <-(associativity _ x _ _), (binary_idempotency _ _).
  + intros x y z. rew ?(le_correct _ _).
    rew (associativity _ z _ _). rew <-(transitivity (=) (z ⊓ x ⊓ y) (z ⊓ y) z).
    refine (aprod_proper_aimpl _ _).
    exact (is_fun (⊓ y) _ _).
  Qed.
End from_meet_semilattice.

Section from_join_semilattice.
  Universes i.
  Context `{jn:Join@{i} L} `{!JoinSemiLattice L} `{!StrongSet L} {Lle: Le L}.
  Context (le_correct : ∀ x y : L, y ≤ x ⧟ x ⊔ y = x).

  Lemma from_join_sl_strong : StrongPoset L.
  Proof. refine StrongPoset_op. refine (from_meet_sl_strong le_correct). Qed.
  Lemma from_join_sl_join_order : JoinSemiLatticeOrder L.
  Proof. refine JoinSemiLatticeOrder_op. refine (from_meet_sl_meet_order _). Qed.
End from_join_semilattice.


Section from_lattice_meet.
  Universes i.
  Context `{Lattice@{i} L} `{!StrongSet L} `{Le L}.
  Context (le_correct : ∀ x y : L, x ≤ y ⧟ x ⊓ y = x).

  Let inst : MeetSemiLatticeOrder L := from_meet_sl_meet_order le_correct.

  Lemma from_lattice_meet_order : LatticeOrder L.
  Proof. split; [exact _ |].
    enough (∀ x y : L, y ≤ x ⧟ x ⊔ y = x) as le_jn by now pose proof from_join_sl_join_order le_jn.
    intros x y. rew (le_correct _ _). split.
  + rew (commutativity (⊓) _ _), (is_fun (x ⊔) (x ⊓ y) y : _ ⊸ x ⊔ _ = x ⊔ _), (join_meet_absorption x y).
    now apply symmetry.
  + rew (commutativity (⊔) _ _), (is_fun (y ⊓) (y ⊔ x) x : _ ⊸ y ⊓ _ = y ⊓ _), (meet_join_absorption y x).
    now apply symmetry.
  Qed.
End from_lattice_meet.


Section from_lattice_join.
  Universes i.
  Context `{Lattice@{i} L} `{!StrongSet L} `{Le L}.
  Context (le_correct : ∀ x y : L, y ≤ x ⧟ x ⊔ y = x).

  Lemma from_lattice_join_order : LatticeOrder L.
  Proof. refine LatticeOrder_op. refine (from_lattice_meet_order (L:=L ᵒᵖ) le_correct). Qed.
End from_lattice_join.

(** Morphisms *)

Section join_order_preserving.
  Universes i.
  Context `{JoinSemiLatticeOrder@{i} (L:=L)} `{JoinSemiLatticeOrder (L:=K)}
    (f : L ⇾ K) {mor:JoinSemiLattice_Morphism f}.

  Local Instance join_sl_mor_preserving: OrderPreserving f.
  Proof. apply alt_Build_OrderPreserving. intros x y.
    rew [ (join_r_iff _ _) | (join_r_iff _ _) ].
    rew <-(preserves_join f _ _).
    exact (is_fun f _ _).
  Qed.

  Lemma join_sl_mor_embedding `{!Injective f}: OrderEmbedding f.
  Proof. split; [ exact _ |]. apply alt_Build_OrderReflecting. intros x y.
    rew [ (join_r_iff _ _) | (join_r_iff _ _) ].
    rew <-(preserves_join f _ _).
    exact (injective f _ _).
  Qed.
End join_order_preserving.

Section meet_order_preserving.
  Universes i.
  Context `{MeetSemiLatticeOrder (L:=L)} `{MeetSemiLatticeOrder (L:=K)}
    (f : L ⇾ K) `{!MeetSemiLattice_Morphism f}.

  Lemma meet_sl_mor_preserving: OrderPreserving f.
  Proof. apply op_order_preserving_iff. exact (join_sl_mor_preserving (f:L ᵒᵖ ⇾ K ᵒᵖ) ). Qed.

  Lemma meet_sl_mor_reflecting `{!Injective f}: OrderEmbedding f.
  Proof. apply op_order_embedding_iff. exact (join_sl_mor_embedding (f:L ᵒᵖ ⇾ K ᵒᵖ) ). Qed.
End meet_order_preserving.


Section order_preserving_join_sl_mor.
  Context `{JoinSemiLatticeOrder (L:=L)} `{JoinSemiLatticeOrder (L:=K)}
    `{!LinearOrder L} `{!RefutativeEquality L} `{!RefutativeOrder K} (f: L ⇾ K) `{!OrderPreserving f}.

  Lemma order_preserving_join_sl_mor: JoinSemiLattice_Morphism f.
  Proof. apply Build_JoinSemiLattice_Morphism. intros x y.
    apply le_antisym; split.
    * apply ( refutative_by_aff_cases (x = y) ); intros [E|E].
      + rew E. now rew [ (binary_idempotency (⊔) _) | (binary_idempotency (⊔) _) ].
      + rew (ne_iff_lt _ _) in E. destruct E as [E|E];
          rew E at 1; rew (binary_idempotency _ _); lattice_order_tac.
    * apply join_lub; split; apply (order_preserving f); lattice_order_tac.
  Qed.
End order_preserving_join_sl_mor.
Local Hint Extern 20 (JoinSemiLattice_Morphism _) => simple notypeclasses refine (order_preserving_join_sl_mor _) : typeclass_instances.

Section order_preserving_meet_sl_mor.
  Context `{MeetSemiLatticeOrder (L:=L)} `{MeetSemiLatticeOrder (L:=K)}
    `{!LinearOrder L} `{!RefutativeEquality L} `{!RefutativeOrder K} (f: L ⇾ K) `{!OrderPreserving f}.

  Lemma order_preserving_meet_sl_mor: MeetSemiLattice_Morphism f.
  Proof _ : JoinSemiLattice_Morphism (f:L ᵒᵖ ⇾ K ᵒᵖ).
End order_preserving_meet_sl_mor.
Local Hint Extern 20 (MeetSemiLattice_Morphism _) => simple notypeclasses refine (order_preserving_meet_sl_mor _) : typeclass_instances.

Lemma order_preserving_lat_mor `{LatticeOrder (L:=L)} `{LatticeOrder (L:=K)}
  `{!LinearOrder L} `{!RefutativeEquality L} `{!RefutativeOrder K} (f: L ⇾ K) `{!OrderPreserving f}
  : Lattice_Morphism f.
Proof. now split. Qed.
(* Global Hint Extern 20 (Lattice_Morphism _) => simple notypeclasses refine (order_preserving_lat_mor _) : typeclass_instances. *)

