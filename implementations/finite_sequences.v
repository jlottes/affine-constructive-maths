Require Import interfaces.set abstract_algebra bundled_algebra interfaces.free_monoid.
Require Import interfaces.sprop logic.aprop relations theory.set theory.projected_set theory.default_equality.
Require Import theory.groups theory.bundled_groups theory.additive_groups theory.nno.
Require Import easy rewrite tactics.misc.
Require Import set_lambda.

Require Import list nat.
Local Notation ℕ := Nat.

Local Notation e := mon_unit.
Local Open Scope grp_scope.

Definition ProdList_index_or_zero X {z:Zero X} := set:(λ s, ProdList_fold_right (X:=X) (Y:=ℕ ⇾ X) Nat_destruct (s, const 0)).

Definition FinSeq X {z:Zero X} := projected_set (ProdList_index_or_zero X).
Global Hint Extern 1 (Zero (FinSeq _)) => refine nil : typeclass_instances.

Lemma FinSeq_is_projected X {z:Zero X} : IsProjectedSet (FinSeq X) (f:=ProdList_index_or_zero X).
Proof. now unfold FinSeq. Qed.
Global Hint Extern 2 (IsProjectedSet (set_T (FinSeq _))) => notypeclasses refine (FinSeq_is_projected _) : typeclass_instances.

Local Notation "X *" := (FinSeq X) (at level 1, format "X *").

Section props.
  Universes i.
  Context {X} {z:Zero@{i} X}.
  Definition FinSeq_sequence : X* ⇾ ℕ ⇾ X := projected_set_project (FinSeq X).
  Lemma FinSeq_sequence_inj : Injective FinSeq_sequence.  Proof. now unfold FinSeq_sequence. Qed.

  Definition FinSeq_index : ℕ ⇾ X* ⇾ X := set:(λ n s, FinSeq_sequence s n).

  Definition FinSeq_strong `{!StrongSet X} : StrongSet X* := projected_set_strong.
  Definition FinSeq_ref_eq `{!RefutativeEquality X} : RefutativeEquality X* := projected_set_ref_eq.

  Definition ProdList_to_FinSeq : ProdList X ⇾ X* := projected_quotient_map _.

  Definition FinSeq_unit : X ⇾ X* := ProdList_to_FinSeq ∘ ProdList_unit.

  Local Notation "[ x ]_ i" := (func_op (func_op FinSeq_index i) x) (at level 1, format "[ x ]_ i").
  Lemma FinSeq_cons_is_fun : @IsFun (X × X*) X* ProdCons.
  Proof. intros [x s][y t]. change (x = y ∧ s = t ⊸ ∏ n, [ ProdCons (x, s) ]_n = [ ProdCons (y, t) ]_n).
    rew <-all_adj. intros [| m].
  + exact (aandl _ _).
  + rew (aandr _ _). change (s = t ⊸ [s]_m = [t]_m).
    revert m. now rew all_adj.
  Qed.
  Definition FinSeq_cons : X × X* ⇾ X* := @make_fun _ _ _ FinSeq_cons_is_fun.
  Local Notation "x :: y" := (func_op FinSeq_cons (x, y)) (at level 60, right associativity).

  Definition FinSeq_induction (P : X* → Ω) : (∏ x₀ x, P x ⊸ P (x₀ :: x)) → (P 0 ⊸ all P) := list_induction P.
  Definition FinSeq_sinduction (P:X* → SProp) : P 0 → (∀ x₀ x, P x → P (x₀ :: x)) → ∀ x, P x := list_sinduction P.
  Definition FinSeq_destruct (P : X* → Ω) : (P 0 ∧ ∏ x₀ x, P (x₀ :: x)) ⊸ all P := list_destruct P.
  Definition FinSeq_sdestruct (P:X* → SProp) : P 0 → (∀ x₀ x, P (x₀ :: x)) → ∀ x, P x := list_sdestruct P.
End props.
Global Hint Extern 2 (StrongSet (FinSeq _)) => simple notypeclasses refine FinSeq_strong : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality (FinSeq _)) => simple notypeclasses refine FinSeq_ref_eq : typeclass_instances.

Module index_notation.
  Notation "[ x ]_ i" := (func_op (func_op FinSeq_index i) x) (at level 1, format "[ x ]_ i") : op_scope.
End index_notation.

Local Notation "x :: y" := (func_op FinSeq_cons (x, y)) (at level 60, right associativity).

Section dec.
  Universes i.
  Context {X} {z:Zero@{i} X}.
  Local Notation ϕ := FinSeq_sequence.

  Lemma FinSeq_dec_is_zero `{!DecidableEquality X} : ∀ (s : X*), Decidable (s = 0).
  Proof. refine (FinSeq_sinduction _ _ _).
  + now rew (aiff_is_true (_ : 0 = 0)).
  + intros x s IH. change (Decidable (∏ n, ϕ (x :: s) n = 0)).
    apply decidable_by_dual.
    pose proof (_ : Decidable (x = 0)) as [Ex|Ex].
    * destruct (decidable_dual (∏ n, ϕ s n = 0)) as [Es|[m Es]].
      - left. intros [| m]; [ exact Ex | exact (Es m) ].
      - right. now exists (nat_S m).
    * right. now exists nat_0.
  Qed.

  Lemma FinSeq_dec_eq `{!DecidableEquality X} : DecidableEquality X*.
  Proof. refine (FinSeq_sinduction _ _ _).
  + intros y. rew (symmetry_iff (=) 0 y). apply FinSeq_dec_is_zero.
  + intros x s IH. refine (FinSeq_sdestruct _ _ _).
    * apply FinSeq_dec_is_zero.
    * intros y t. change (Decidable (∏ n, ϕ (x :: s) n = ϕ (y :: t) n)).
      apply decidable_by_dual.
      pose proof (_ : Decidable (x = y)) as [Ex|Ex].
      - specialize (IH t). destruct (decidable_dual (∏ n, ϕ s n = ϕ t n)) as [Es|[m Es]].
        ++ left. intros [| m]; [ exact Ex | exact (Es m) ].
        ++ right. now exists (nat_S m).
      - right. now exists nat_0.
  Qed.

  Definition FinSeq_zero_dec {d:Dec (A:=X) (=)} : X* → bool :=
    fix F s := match s with
    | nil => true
    | cons s₀ s' => if dec (=) s₀ 0 then F s' else false
    end.

  Lemma FinSeq_zero_is_dec `{!IsDecEq X (d:=d)} : ∀ s, if FinSeq_zero_dec s then s = 0 else s ≠ 0.
  Proof. intro s. change (s ≠ 0) with (∐ n, ϕ s n ≠ 0). revert s. refine (FinSeq_sinduction _ _ _).
  + now change (0 = 0 :> X*).
  + intros x s IH. change (FinSeq_zero_dec (x :: s)) with (if dec (=) x 0 then FinSeq_zero_dec s else false).
    generalize (dec_spec (=) x 0); destruct (dec (=) x 0); intro Ex.
    * revert IH. destruct (FinSeq_zero_dec s); [ intros Es | intros [ m Es ]].
      - intros [| m]; [ exact Ex | exact (Es m) ].
      - now exists (nat_S m).
    * now exists nat_0.
  Qed.

  Instance FinSeq_eq_dec {d:Dec (A:=X) (=)} : Dec (A:=X*) (=) := fix F s t :=
    match s with
    | nil => FinSeq_zero_dec t
    | cons s₀ s' =>
      match t with
      | nil => FinSeq_zero_dec s
      | cons t₀ t' => if dec (=) s₀ t₀ then F s' t' else false
      end
    end.

  Lemma FinSeq_eq_is_dec `{!IsDecEq X (d:=d)} : IsDecEq X*.
  Proof. refine (FinSeq_sinduction _ _ _).
  + intros t. change (dec (=) 0 t) with (FinSeq_zero_dec t).
    generalize (FinSeq_zero_is_dec t). destruct (FinSeq_zero_dec t);
      apply aimpl_impl_pos; [| apply by_contrapositive]; now apply symmetry.
  + intros x s IH. refine (FinSeq_sdestruct _ (FinSeq_zero_is_dec _) _).
    intros y t. change (dec (=) (x :: s) (y :: t)) with (if dec (=) x y then dec (=) s t else false).
    generalize (dec_spec (=) x y); destruct (dec (=) x y); intro Ex.
    * specialize (IH t). revert IH. change (?s ≠ ?t) with (∐ n, ϕ s n ≠ ϕ t n).
      destruct (dec (=) s t); [ intros Es | intros [m Es] ].
      - intros [| m]; [ exact Ex | exact (Es m) ].
      - now exists (nat_S m).
    * now exists nat_0.
  Qed.
End dec.
Global Hint Extern 2 (DecidableEquality _*) => simple notypeclasses refine FinSeq_dec_eq : typeclass_instances.

Global Hint Extern 2 (Dec (A:=set_T _*) (=)) => refine FinSeq_eq_dec : typeclass_instances.
Global Hint Extern 2 (IsDecEq _*) => simple notypeclasses refine FinSeq_eq_is_dec : typeclass_instances.

Section tail.
  Import index_notation.
  Definition tail_op {X:set} : ProdList X ⇾ ProdList X := ProdList_match (e, prod_proj2 _ _).
  Lemma tail_is_fun {X:set} {zX:Zero X} : @IsFun X* X* tail_op.
  Proof. refine (ProdList_sdestruct _ _ _).
  + refine (ProdList_sdestruct _ _ _); [ refl |].
    intros x s. change ((∏ i, 0 = [ ProdList_unit x ∙ s ]_i) ⊸ (∏ i, 0 = [s]_i)).
    rew <-all_adj. intros i. exact (all_lb _ (nat_S i)).
  + intros x s. refine (ProdList_sdestruct _ _ _).
    * change ((∏ i, [ ProdList_unit x ∙ s ]_i = 0) ⊸ (∏ i, [s]_i = 0)).
      rew <-all_adj. intros i. exact (all_lb _ (nat_S i)).
    * intros y t. change ((∏ i, [ ProdList_unit x ∙ s ]_i = [ ProdList_unit y ∙ t ]_i) ⊸ (∏ i, [s]_i = [t]_i)).
      rew <-all_adj. intros i. exact (all_lb _ (nat_S i)).
  Qed.
  Definition FinSeq_tail `{zX:Zero X} := @make_fun _ _ _ (@tail_is_fun X _).

  Definition FinSeq_tail_spec `{zX:Zero X} : ∏ s:X*, s = [s]_0 :: FinSeq_tail s.
  Proof. refine (ProdList_sdestruct _ _ _); [| intros ??]; now intros [| m]. Qed.
End tail.

Section map.
  Context `(f:X ⇾ Y) {zX:Zero X} {zY:Zero Y} {H:Zero_Pointed_Morphism f}.

  Local Notation ϕ := (ProdList_index_or_zero _).
  Local Notation "[ x ]" := (func_op ProdList_unit x).

  Lemma FinSeq_map_spec' : ∀ (s:X*), ϕ (ProdList_map f s) = f ∘ ϕ s.
  Proof. refine (ProdList_sinduction_alt _ _ _); [ now intro | intros x₀ x IHx ].
    rew (preserves_sg_op (ProdList_map f) _ _).
    change (ProdList_map f [x₀]) with ([f x₀]). intros [| i]; [ refl | exact (IHx _) ].
  Qed.

  Local Instance: @IsFun X* Y* (ProdList_map f).
  Proof. intros s t. change (s = t ⊸ ϕ (ProdList_map f s) = ϕ (ProdList_map f t)).
    rew [ (FinSeq_map_spec' _) | ( FinSeq_map_spec' _) ]. exact (is_fun (f ∘) _ _).
  Qed.

  Definition FinSeq_map := @make_fun X* Y* (ProdList_map f) _.

  Import index_notation.
  Definition FinSeq_map_spec : ∀ (s:X*) n, [FinSeq_map s]_n = f [s]_n := FinSeq_map_spec'.
End map.

Import projection_notation.

Section map2.
  Local Notation ϕ := (ProdList_index_or_zero _).
  Local Notation "[ x ]" := (func_op ProdList_unit x).

  Universes i.
  Context {X Y Z: set@{i}} {zX : Zero X} {zY : Zero Y} {zZ : Zero Z}.
  Local Hint Extern 2 (Zero (X ⊗ Y)) => exact (0, 0) : typeclass_instances.
  Context (f:X ⊗ Y ⇾ Z) {H:Zero_Pointed_Morphism f}.

  Local Instance: Zero_Pointed_Morphism (ap1 f 0) := preserves_0 f.
  Local Instance: Zero_Pointed_Morphism (ap2 f 0) := preserves_0 f.

  Definition map2_zero_l := ProdList_map (ap1 f 0).
  Definition map2_zero_r := ProdList_map (ap2 f 0).
  Definition map2_zero_l_spec (s:ProdList Y) n : ϕ (map2_zero_l s) n = f (0, ϕ s n) := FinSeq_map_spec' _ s n.
  Definition map2_zero_r_spec (s:ProdList X) n : ϕ (map2_zero_r s) n = f (ϕ s n, 0) := FinSeq_map_spec' _ s n.

  Definition map2_aux : X × ProdList X × (ProdList Y ⇾ ProdList Z) → (ProdList Y ⇾ ProdList Z)
  := set:(λ p : X × ProdList X × (ProdList Y ⇾ ProdList Z),
    ProdList_match (X:=Y) (
      ProdCons (f (π₁ (π₁ p), 0), map2_zero_r (π₂ (π₁ p))) ,
      set:(λ yl' : Y × ProdList Y,  ProdCons (f (π₁ (π₁ p), π₁ yl'), (π₂ p) (π₂ yl')) )
    )).

  Definition map2 : ProdList X ⇾ ProdList Y ⇾ ProdList Z
  := set:(λ l, ProdList_elim map2_aux (map2_zero_l : _ ⇾ _, l)).

  Lemma map2_spec' : ∀ l l' n, ϕ (map2 l l') n = f (ϕ l n, ϕ l' n).
  Proof. refine (ProdList_sinduction_alt _ _ _).
  + exact map2_zero_l_spec.
  + intros x l IH. refine (ProdList_sdestruct _ _ _).
    * intros [| m]; [ refl |].
      revert m. exact (map2_zero_r_spec l).
    * intros y l' [| m]; [ refl |].
      exact (IH l' m).
  Qed.

  Local Instance: @IsFun (X* ⊗ Y*) Z* (uncurry map2).
  Proof. intros [s₁ t₁][s₂ t₂]. change (s₁ = s₂ ⊠ t₁ = t₂ ⊸ ∏ n, ϕ (map2 s₁ t₁) n = ϕ (map2 s₂ t₂) n).
    rew <-all_adj. intros n. rew [ (map2_spec' _ _ _) | (map2_spec' _ _ _) ].
    rew <-(is_fun f _ _); unfold_pair_eq.
    refine (aprod_proper_aimpl _ _); exact (all_lb _ _).
  Qed.

  Definition FinSeq_map2 := @make_fun (X* ⊗ Y*) Z* (uncurry map2) _.

  Import index_notation.
  Definition FinSeq_map2_spec : ∀ s t n, [FinSeq_map2 (s, t)]_n = f ([s]_n, [t]_n) := map2_spec'.
End map2.

Import index_notation.

Section add_mon.
  Universes i.
  Context `{AdditiveMonoid@{i} M}.

  Local Instance FinSeq_plus : Plus M* := FinSeq_map2 (X:=M) plus (H:=plus_0_l _).
  Lemma FinSeq_plus_spec (x y : M*) i : [x + y]_i = [x]_i + [y]_i.
  Proof FinSeq_map2_spec _ x y i.

  Local Instance FinSeq_add_mon: AdditiveMonoid M*.
  Proof. apply alt_Build_AdditiveMonoid; hnf; intros; change (?s = ?t) with (∏ i, [s]_i = [t]_i); intro i;
    rew ?(FinSeq_plus_spec _ _ _).
  + now apply associativity.
  + now apply commutativity.
  + now apply plus_0_l.
  Qed.

  Local Instance: AdditiveNonComMonoid M* := FinSeq_add_mon.

  Lemma FinSeq_index_addmon_mor {n} : AdditiveMonoid_Morphism (FinSeq_index (X:=M) n).
  Proof. simple refine (alt_Build_AdditiveMonoid_Morphism _ _).
  + intros. apply FinSeq_plus_spec.
  + refl.
  Qed.

  Lemma FinSeq_tail_addmon_mor : AdditiveMonoid_Morphism (FinSeq_tail (X:=M)).
  Proof. apply alt_Build_AdditiveMonoid_Morphism.
  + intros s t. now rew [ (FinSeq_tail_spec s) | (FinSeq_tail_spec t) ].
  + refl.
  Qed.
End add_mon.
Global Hint Extern 1 (Plus _*) => notypeclasses refine FinSeq_plus : typeclass_instances.
Global Hint Extern 1 (AdditiveMonoid _*) => simple notypeclasses refine FinSeq_add_mon : typeclass_instances.
Global Hint Extern 1 (AdditiveNonComMonoid _*) => simple notypeclasses refine FinSeq_add_mon : typeclass_instances.
Global Hint Extern 1 (AdditiveNonComSemiGroup _*) => simple notypeclasses refine FinSeq_add_mon : typeclass_instances.
Global Hint Extern 1 (AdditiveSemiGroup _*) => simple notypeclasses refine FinSeq_add_mon : typeclass_instances.

Global Hint Extern 1 (AdditiveMonoid_Morphism (func_op FinSeq_index _)) => simple notypeclasses refine FinSeq_index_addmon_mor : typeclass_instances.
Global Hint Extern 1 (AdditiveSemiGroup_Morphism (func_op FinSeq_index _)) => simple notypeclasses refine FinSeq_index_addmon_mor : typeclass_instances.
Global Hint Extern 1 (Zero_Pointed_Morphism (func_op FinSeq_index _)) => simple notypeclasses refine FinSeq_index_addmon_mor : typeclass_instances.

Global Hint Extern 1 (AdditiveMonoid_Morphism FinSeq_tail) => simple notypeclasses refine FinSeq_tail_addmon_mor : typeclass_instances.
Global Hint Extern 1 (AdditiveSemiGroup_Morphism FinSeq_tail) => simple notypeclasses refine FinSeq_tail_addmon_mor : typeclass_instances.
Global Hint Extern 1 (Zero_Pointed_Morphism FinSeq_tail) => simple notypeclasses refine FinSeq_tail_addmon_mor : typeclass_instances.

Section addgroup.
  Universes i.
  Context `{AdditiveGroup@{i} G}.

  Instance FinSeq_negate : Negate G* := FinSeq_map (X:=G) negate (H:=negate_0).
  Lemma FinSeq_negate_spec (x : G*) i : [-x]_i = -[x]_i.
  Proof FinSeq_map_spec _ _ _.

  Lemma FinSeq_add_grp: AdditiveGroup G*.
  Proof. apply alt_Build_AdditiveGroup; try exact _.
    hnf. intros s. change (?s = ?t) with (∏ i, [s]_i = [t]_i); intro i.
    rew ?(FinSeq_plus_spec _ _ _). rew (FinSeq_negate_spec _ _).
    exact (plus_negate_l _).
  Qed.
End addgroup.
Global Hint Extern 1 (Negate _*) => notypeclasses refine FinSeq_negate : typeclass_instances.
Global Hint Extern 1 (AdditiveGroup _*) => simple notypeclasses refine FinSeq_add_grp : typeclass_instances.
Global Hint Extern 1 (AdditiveNonComGroup _*) => simple notypeclasses refine FinSeq_add_grp : typeclass_instances.

