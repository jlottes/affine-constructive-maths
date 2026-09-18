Require Import abstract_algebra interfaces.naturals interfaces.integers
  logic.aprop logic.relations logic.dec theory.set
  theory.default_equality theory.projected_set theory.rings orders.rings
  theory.subgroups theory.subrings orders.suborders
  theory.naturals theory.integers orders.naturals orders.integers
  theory.group_completion.
Require Import implementations.bool implementations.z2 implementations.nat implementations.signed_naturals_integers.
Require Import implementations.list.
Require Import easy replc simplify rewrite_preserves tactics.misc tactics.algebra.ab_groups.
Require Import set_lambda.

Local Open Scope mult_scope.
Local Open Scope list_scope.

Local Notation "bs :: b" := (cons b bs) (at level 60, left associativity).
Import projection_notation.

Local Hint Extern 2 (SimplifiesTo (notb 0) ?out) => change (SimplifiesTo (@one ℤ₂ _) out) : typeclass_instances.
Local Hint Extern 2 (SimplifiesTo (notb 1) ?out) => change (SimplifiesTo (@zero ℤ₂ _) out) : typeclass_instances.

Module bin_int.
  Section with_ref.
    Universes u.

    (** Bits *)
    Definition bit_to_ℤ (ℤ:integers@{u}) : ℤ₂ ⇾ ℤ := default_eq_func (λ b:bool, if b then 1 else 0).
    Local Abbreviation ϕ := (bit_to_ℤ _).
    Local Hint Extern 2 (SimplifiesTo (func_op (bit_to_ℤ ?ℤ) 1) ?out) => change (SimplifiesTo (@one ℤ _) out) : typeclass_instances.
    Local Hint Extern 2 (SimplifiesTo (func_op (bit_to_ℤ ?ℤ) 0) ?out) => change (SimplifiesTo (@zero ℤ _) out) : typeclass_instances.
    Local Hint Extern 2 (SimplifiesTo (func_op (bit_to_ℤ ?ℤ) true) ?out) => change (SimplifiesTo (@one ℤ _) out) : typeclass_instances.
    Local Hint Extern 2 (SimplifiesTo (func_op (bit_to_ℤ ?ℤ) false) ?out) => change (SimplifiesTo (@zero ℤ _) out) : typeclass_instances.

    Abbreviation parity := (integers_to_group (ring_car (ints_ring _)) ℤ₂).
    Local Hint Extern 2 (SimplifiesTo (func_op parity 0) _) => solve_simplify (preserves_0 _) : typeclass_instances.
    Local Hint Extern 2 (SimplifiesTo (func_op parity 1) _) => solve_simplify (preserves_1 _) : typeclass_instances.

    Lemma parity_negate {ℤ:integers@{u}} (z:ℤ) : parity (-z) = parity z.
    Proof. now rewrite_preserves (integers_to_group ℤ ℤ₂). Qed.
    Local Hint Extern 2 (SimplifiesTo (func_op parity (- ?z)) _) => solve_simplify (parity_negate z) : typeclass_instances.

    Lemma parity_two {ℤ:integers@{u}} : integers_to_group ℤ ℤ₂ 2 = 0.
    Proof. now rewrite_preserves (integers_to_group ℤ ℤ₂). Qed.
    Local Hint Extern 2 (SimplifiesTo (func_op parity 2) _) => solve_simplify parity_two : typeclass_instances.

    Lemma parity_even {ℤ:integers@{u}} (z:ℤ) : parity (2·z) = 0.
    Proof. rew (preserves_mult parity _ _); now simplify. Qed.
    Local Hint Extern 2 (SimplifiesTo (func_op parity (2·?z)) _) => solve_simplify (parity_even z) : typeclass_instances.

    Local Hint Extern 2 (Inverse parity) => refine ϕ : typeclass_instances.

    Lemma parity_surj {ℤ:integers@{u}} : Surjective (integers_to_group ℤ ℤ₂).
    Proof. intros x. unfold inverse. simplify. revert x. ℤ₂_induction; now simplify. Qed.
    Local Hint Extern 2 (Surjective parity) => simple notypeclasses refine parity_surj : typeclass_instances.

    Local Hint Extern 2 (SimplifiesTo (func_op parity (func_op ϕ ?z)) _) => solve_simplify (surjective_applied parity z) : typeclass_instances.

    Local Instance bit_to_ℤ_inj {ℤ:integers@{u}} : Injective (bit_to_ℤ ℤ).
    Proof. exact (alt_Build_Injective _ parity_surj). Qed.

    Definition to_ints_op (ℤ:integers@{u}) (l : ℤ₂) : list ℤ₂ → ℤ := fix F n :=
      match n with
      | nil => -(ϕ l)
      | m :: b => 2 · F m + (ϕ b)
      end.

    Lemma to_ints_coherent (Z₁ Z₂ : integers@{u}) (x : ℤ₂ ∗ list ℤ₂)
      : tuncurry (to_ints_op Z₂) x = integers_to_group Z₁ Z₂ (tuncurry (to_ints_op Z₁) x).
    Proof. destruct x as [l n]. revert n. refine (list_sinduction _ _ _).
    + simplify. cbn [ to_ints_op ]. rewrite_preserves (integers_to_group Z₁ Z₂).
      revert l. ℤ₂_induction; simplify; rewrite_preserves (integers_to_group Z₁ Z₂); now simplify.
    + intros b m. simplify. intro IH. cbn [ to_ints_op ].
      rew IH. rewrite_preserves (integers_to_group Z₁ Z₂).
      revert b. ℤ₂_induction; simplify; rewrite_preserves (integers_to_group Z₁ Z₂); now simplify.
    Qed.

    Definition Z : set@{u}.
    Proof. let t := constr:(projected_set (tuncurry (to_ints_op SignedNat@{u}))) in
           let t := eval red in t in
           let t := eval red in t in exact t.
    Defined.
    Lemma is_proj : IsProjectedSet Z (f:=tuncurry (to_ints_op SignedNat@{u})).   Proof. now unfold Z. Qed.
    Local Hint Extern 1 (IsProjectedSet (set_T Z)) => notypeclasses refine is_proj : typeclass_instances.

    Lemma to_ints_is_fun {ℤ:integers@{u}} : @IsFun Z ℤ (tuncurry (to_ints_op ℤ)).
    Proof. intros x y.
      change (tuncurry (to_ints_op SignedNat) x = tuncurry (to_ints_op SignedNat) y ⊸ tuncurry (to_ints_op ℤ) x = tuncurry (to_ints_op ℤ) y).
      rew [ (to_ints_coherent SignedNat ℤ x) | (to_ints_coherent SignedNat ℤ y) ].
      exact (is_fun (integers_to_group SignedNat ℤ) _ _).
    Qed.

    Definition to_ints (ℤ:integers@{u}) : Z ⇾ ℤ := @func_make _ _ _ to_ints_is_fun.
    Local Abbreviation i := (to_ints _).
    Lemma to_ints_inj (ℤ:integers@{u}) : Injective (to_ints ℤ).
    Proof. intros x y.
      change (tuncurry (to_ints_op ℤ) x = tuncurry (to_ints_op ℤ) y ⊸ tuncurry (to_ints_op SignedNat) x = tuncurry (to_ints_op SignedNat) y).
      rew [ (to_ints_coherent ℤ SignedNat x) | (to_ints_coherent ℤ SignedNat y) ].
      exact (is_fun (integers_to_group ℤ SignedNat) _ _).
    Qed.
    Local Hint Extern 1 (Injective i) => simple notypeclasses refine (to_ints_inj _) : typeclass_instances.

    Definition decidable : DecidableEquality Z := projected_set_dec_eq.
    Local Hint Extern 1 (DecidableEquality Z) => refine decidable : typeclass_instances.
    Local Hint Extern 1 (AffirmativeEquality Z) => refine decidable : typeclass_instances.
    Local Hint Extern 1 (RefutativeEquality Z) => refine decidable : typeclass_instances.
    Local Hint Extern 1 (StrongSet Z) => refine decidable : typeclass_instances.

    Local Hint Extern 1 (Zero Z) => refine (false, nil) : typeclass_instances.
    Local Hint Extern 1 (One Z) => refine (false, nil :: true) : typeclass_instances.


    Lemma zero_correct {ℤ:integers} : i 0 = 0 :> ℤ.  Proof. change (-0 = 0 :> ℤ); now simplify. Qed.
    Lemma one_correct {ℤ:integers} : i 1 = 1 :> ℤ.   Proof. change (2 · - ϕ 0 + ϕ 1 = 1 :> ℤ); now simplify. Qed.

    Local Hint Extern 2 (SimplifiesTo (func_op (to_ints ?Z) (?l, nil)) ?out) => change (SimplifiesTo (-(bit_to_ℤ Z l)) out) : typeclass_instances.
    Local Hint Extern 2 (SimplifiesTo (func_op (to_ints ?Z) (?l, ?m :: ?b)) ?out) => change (SimplifiesTo (2 · to_ints Z (l, m) + bit_to_ℤ Z b) out) : typeclass_instances.

    Definition append_bit_op (b:ℤ₂) (l : ℤ₂) : list ℤ₂ → list ℤ₂ := fix F n :=
      match n with
      | nil => if dec (=) (b, l) then nil else nil :: b
      | _ => n :: b
      end.
    Lemma append_bit_op_correct {ℤ:integers} : ∀ (b:ℤ₂) l n, i (l, append_bit_op b l n) = 2 · i (l, n) +  ϕ b :> ℤ.
    Proof. intros b l [|a n]; [| refl ].
      simplify; cbn [ append_bit_op ]. generalize (dec_spec (=) (b, l)).
      destruct (dec (=) (b, l)) as [|].
      * intros []; simplify. rew (mult_2_plus_l _), (negate_plus_distr _ _); now simplify.
      * intros _; now simplify.
    Qed.

    Definition succ_op (l : ℤ₂) : list ℤ₂ → Z := fix F n :=
      match n with
      | nil => (false, if l then nil else nil :: true)
      | n' :: b =>
          if b then (let '(l', n'') := F n' in (l', append_bit_op false l' n''))
               else (l, append_bit_op true l n')
      end.

    Lemma succ_op_correct {ℤ:integers} l : ∀ n, i (succ_op l n) = i (l, n) + 1 :> ℤ.
    Proof. refine (list_sinduction _ _ _).
    + cbn [ succ_op ]. revert l. ℤ₂_induction.
      * change (i 1 = i 0 + 1 :> ℤ). rew [one_correct | zero_correct]; now simplify.
      * change (i 0 = - 1 + 1 :> ℤ). rew zero_correct. now simplify.
    + intros b n'. cbn [ succ_op ]. destruct (succ_op l n') as [l' n'']. intro IH.
      revert b. ℤ₂_induction; simplify; rew (append_bit_op_correct _ _ _); simplify.
      * exact _.
      * rew IH. rew (plus_mult_distr_l _ _ _); simplify; add_grp.
    Qed.

    Definition pred_op (l : ℤ₂) : list ℤ₂ → Z := fix F n :=
      match n with
      | nil => (true, if l then nil :: false else nil)
      | n' :: b =>
          if b then (l, append_bit_op false l n')
               else (let '(l', n'') := F n' in (l', append_bit_op true l' n''))
      end.

    Lemma pred_op_correct {ℤ:integers} l : ∀ n, i (pred_op l n) = i (l, n) - 1 :> ℤ.
    Proof. refine (list_sinduction _ _ _).
    + cbn [ pred_op ]. revert l. ℤ₂_induction.
      * change (-1 = i 0 - 1 :> ℤ). rew zero_correct; now simplify.
      * change (2·(-1) + 0 = -1 - 1 :> ℤ); simplify. add_grp.
    + intros b n'. cbn [ pred_op ]. destruct (pred_op l n') as [l' n'']. intro IH.
      revert b. ℤ₂_induction; simplify; rew (append_bit_op_correct _ _ _); simplify.
      * rew IH. rew (plus_mult_distr_l _ _ _); simplify; add_grp.
      * exact _.
    Qed.

    Definition flip_bits : list ℤ₂ → list ℤ₂ := fix F n :=
      match n with
      | nil => nil
      | n' :: b => F n' :: notb b
      end.

    Lemma flip_bits_correct {ℤ:integers} l : ∀ n, i (notb l, flip_bits n) = - i (l, n) - 1 :> ℤ.
    Proof. refine (list_sinduction _ _ _).
    + cbn [ flip_bits ]. revert l. ℤ₂_induction.
      * change (-1 = -i 0 - 1 :> ℤ). rew zero_correct; now simplify.
      * change (i 0 = -(-1) - 1 :> ℤ). rew zero_correct; now simplify.
    + intros b n'. cbn [ flip_bits ]. intro IH. simplify.
      rew IH. set (x := i (l, n')). rew ?(mult_2_plus_l _).
      revert b. ℤ₂_induction; simplify; add_grp.
    Qed.

    Definition negater (l : ℤ₂) : list ℤ₂ → Z := fix F n :=
      match n with
      | nil => if l then (false, nil :: true) else (false, nil)
      | n' :: b => if b then (notb l, append_bit_op true (notb l) (flip_bits n'))
                        else let (l', n'') := F n' in (l', append_bit_op false l' n'')
      end.

    Lemma negater_correct {ℤ:integers} l : ∀ n, i (negater l n) = - i (l, n) :> ℤ.
    Proof. refine (list_sinduction _ _ _).
    + cbn [ negater ]. revert l. ℤ₂_induction.
      * change (i 0 = -i 0 :> ℤ). rew zero_correct; now simplify.
      * change (i 1 = -(-1) :> ℤ). rew one_correct; now simplify.
    + intros b n'. cbn [ negater ]. destruct (negater l n') as [l' n''].
      intro IH. simplify. revert b; ℤ₂_induction; simplify; rew (append_bit_op_correct _ _ _); simplify.
      * rew IH; now simplify.
      * rew (flip_bits_correct _ _). rew ?(mult_2_plus_l _); add_grp.
    Qed.

    Definition negate_op : Z → Z := λ '(l, n), negater l n.
    Lemma negate_op_correct {ℤ:integers} : ∀ x : Z, i (negate_op x) = -i x :> ℤ.
    Proof. intros [l n]. exact (negater_correct l n). Qed.

    Local Instance neg : Negate Z
      := @func_make Z Z (λ '(l, n), negater l n)
            (projected_is_fun (X:=Z) (λ '(l, n), negater l n) (-) negate_op_correct).
    Definition negate_correct {ℤ:integers} x : i (-x) = -(i x) :> ℤ := negate_op_correct x.



    Definition add_bits (a b c : ℤ₂) : ℤ₂ ∗ ℤ₂ := (if a then orb (b, c) else b·c, a+b+c).
    Local Hint Extern 2 (@SimplifiesTo ?X (add_bits 0 0 0) ?out) => change (@SimplifiesTo X (@zero ℤ₂ _, @zero ℤ₂ _) out) : typeclass_instances.
    Local Hint Extern 2 (@SimplifiesTo ?X (add_bits 1 0 0) ?out) => change (@SimplifiesTo X (@zero ℤ₂ _, @one ℤ₂ _) out) : typeclass_instances.
    Local Hint Extern 2 (@SimplifiesTo ?X (add_bits 0 1 0) ?out) => change (@SimplifiesTo X (@zero ℤ₂ _, @one ℤ₂ _) out) : typeclass_instances.
    Local Hint Extern 2 (@SimplifiesTo ?X (add_bits 0 0 1) ?out) => change (@SimplifiesTo X (@zero ℤ₂ _, @one ℤ₂ _) out) : typeclass_instances.
    Local Hint Extern 2 (@SimplifiesTo ?X (add_bits 1 1 0) ?out) => change (@SimplifiesTo X (@one ℤ₂ _, @zero ℤ₂ _) out) : typeclass_instances.
    Local Hint Extern 2 (@SimplifiesTo ?X (add_bits 1 0 1) ?out) => change (@SimplifiesTo X (@one ℤ₂ _, @zero ℤ₂ _) out) : typeclass_instances.
    Local Hint Extern 2 (@SimplifiesTo ?X (add_bits 0 1 1) ?out) => change (@SimplifiesTo X (@one ℤ₂ _, @zero ℤ₂ _) out) : typeclass_instances.
    Local Hint Extern 2 (@SimplifiesTo ?X (add_bits 1 1 1) ?out) => change (@SimplifiesTo X (@one ℤ₂ _, @one ℤ₂ _) out) : typeclass_instances.

    Local Hint Extern 2 (@SimplifiesTo (notb 0) ?out) => change (SimplifiesTo (@one ℤ₂ _) out) : typeclass_instances.
    Local Hint Extern 2 (@SimplifiesTo (notb 1) ?out) => change (SimplifiesTo (@zero ℤ₂ _) out) : typeclass_instances.

    Lemma add_bits_correct {ℤ:integers} : ∀ a b c, ϕ a + ϕ b + ϕ c = 2 · ϕ (π₁ (add_bits a b c)) + ϕ (π₂ (add_bits a b c)) :> ℤ.
    Proof. ℤ₂_induction; ℤ₂_induction; ℤ₂_induction; now simplify. Qed.

    Definition adder (l₁ l₂ : ℤ₂) : list ℤ₂ → list ℤ₂ → ℤ₂ → Z := fix F m :=
      match m with
      | nil => λ n carry, if l₁ then (if carry then (l₂, n) else pred_op l₂ n)
                                else (if carry then succ_op l₂ n else (l₂, n))
      | m' :: b₁ => λ n carry,
        match n with
        | nil => if l₂ then (if carry then (l₁, m) else pred_op l₁ m)
                       else (if carry then succ_op l₁ m else (l₁, m))
        | n' :: b₂ => let '(c, b) := add_bits b₁ b₂ carry in
                      let '(l₃, s) := F m' n' c in (l₃, append_bit_op b l₃ s)
        end
      end.

    Lemma adder_correct {ℤ:integers} (l₁ l₂ : ℤ₂) : ∀ m n c, i (adder l₁ l₂ m n c) = i (l₁, m) + i (l₂, n) + ϕ c :> ℤ.
    Proof. refine (list_sinduction _ _ _).
    + cbn [ adder ]. intros n carry. revert l₁ carry; ℤ₂_induction; ℤ₂_induction; simplify; try exact _.
      * apply succ_op_correct.
      * rew (pred_op_correct _ _). exact (commutativity (+) _ _).
    + intros b₁ m' IH. intros [|b₂ n'].
      * clear IH. intros carry. cbn [ adder ]. set (m:=m' :: b₁).
        revert l₂ carry; ℤ₂_induction; ℤ₂_induction; simplify; try exact _.
        - apply succ_op_correct.
        - apply pred_op_correct.
      * intros carry. cbn [ adder ].
        generalize (add_bits_correct (ℤ:=ℤ) b₁ b₂ carry). destruct (add_bits b₁ b₂ carry) as [c b]; simplify.
        specialize (IH n' c). revert IH. destruct (adder l₁ l₂ m' n' c) as [l₃ s].
        intros IH E. rew (append_bit_op_correct _ _ _), IH. clear IH. set (x:=i (l₁, m')). set (y:=i (l₂, n')).
        rew (plus_mult_distr_l _ _ _), <-(associativity (+) _ _ _), <-E.
        rew (plus_mult_distr_l 2 x y). add_grp.
    Qed.

    Definition plus_op : Z ∗ Z → Z := λ '((l₁, m), (l₂, n)), adder l₁ l₂ m n false.
    Lemma plus_op_correct {ℤ:integers} : ∀ p : Z ⊗ Z, i (plus_op p) = i (π₁ p) + i (π₂ p) :> ℤ.
    Proof. intros [[l₁ m] [l₂ n]]; change (i (adder l₁ l₂ m n 0) = i (l₁, m) + i (l₂, n) :> ℤ).
      rew (adder_correct _ _ _ _ _); now simplify.
    Qed.

    Local Instance pls : Plus Z
      := @func_make (Z ⊗ Z) Z (λ '((l₁, m), (l₂, n)), adder l₁ l₂ m n 0) (projected_is_fun (X:=Z ⊗ Z) plus_op (+) plus_op_correct).
    Definition plus_correct {ℤ:integers} x y : i (x + y) = i x + i y :> ℤ := plus_op_correct (x, y).



    Definition multiplier (l₁ l₂ : ℤ₂) (m : list ℤ₂) : list ℤ₂ → Z := fix F n :=
      match n with
      | nil => if l₂ then negater l₁ m else (false, nil)
      | n' :: b => let '(l, n'') := F n' in let n''' := append_bit_op false l n'' in
           if b then adder l₁ l m n''' false else (l, n''')
      end.

    Lemma multiplier_correct {ℤ:integers} (l₁ l₂ : ℤ₂) m : ∀ n, i (multiplier l₁ l₂ m n) = i (l₁, m) · i (l₂, n) :> ℤ.
    Proof. refine (list_sinduction _ _ _); cbn [ multiplier ].
    + revert l₂; ℤ₂_induction.
      * change (i 0 = i (l₁, m) · i 0 :> ℤ). rew zero_correct; now simplify.
      * change (i (negater l₁ m) = i (l₁, m) · (-1) :> ℤ). rew (negater_correct _ _); now simplify.
    + intros b n'. destruct (multiplier l₁ l₂ m n') as [l n'']. intro IH. revert b; ℤ₂_induction; simplify.
      * rew (append_bit_op_correct _ _ _), IH; simplify.
        rew ?(associativity (·) _ _ _). now rew (commutativity (·) _ 2).
      * rew (plus_mult_distr_l _ _ _), (adder_correct _ _ _ _ _), (append_bit_op_correct _ _ _); simplify.
        rew (associativity (·) _ _ _), (commutativity (·) _ 2), <-(associativity (·) _ _ _), <-IH.
        exact (commutativity (+) _ _).
    Qed.

    Definition mult_op : Z ∗ Z → Z := λ '((l₁, m), (l₂, n)), multiplier l₁ l₂ m n.
    Lemma mult_op_correct {ℤ:integers} : ∀ p : Z ⊗ Z, i (mult_op p) = i (π₁ p) · i (π₂ p) :> ℤ.
    Proof. intros [[l₁ m] [l₂ n]]. exact (multiplier_correct l₁ l₂ m n). Qed.

    Local Instance mlt : Mult Z
      := @func_make (Z ⊗ Z) Z (λ '((l₁, m), (l₂, n)), multiplier l₁ l₂ m n) (projected_is_fun (X:=Z ⊗ Z) mult_op (·) mult_op_correct).
    Definition mult_correct {ℤ:integers} x y : i (x · y) = i x · i y :> ℤ := mult_op_correct (x, y).



    Local Instance is_com_ring : CommutativeRing Z
      := projected_commutative_ring (to_ints SignedNat)  plus_correct mult_correct zero_correct one_correct negate_correct.
    Let inst : CommutativeRing Z.  Proof. exact is_com_ring. Qed.

    Definition to_ints_mor {ℤ:integers} : Rig_Morphism (to_ints ℤ)
      := Build_Ring_Morphism plus_correct mult_correct one_correct.
    Local Hint Extern 2 (Rig_Morphism i) => simple notypeclasses refine to_ints_mor : typeclass_instances.
    Local Hint Extern 2 (AdditiveMonoid_Morphism i) => simple notypeclasses refine to_ints_mor : typeclass_instances.
    Local Hint Extern 2 (AdditiveSemiGroup_Morphism i) => simple notypeclasses refine to_ints_mor : typeclass_instances.
    Local Hint Extern 2 (MultiplicativeMonoid_Morphism i) => simple notypeclasses refine to_ints_mor : typeclass_instances.
    Local Hint Extern 2 (MultiplicativeSemiGroup_Morphism i) => simple notypeclasses refine to_ints_mor : typeclass_instances.
    Local Hint Extern 2 (One_Pointed_Morphism i) => simple notypeclasses refine to_ints_mor : typeclass_instances.
    Local Hint Extern 2 (Rg_Morphism i) => simple notypeclasses refine to_ints_mor : typeclass_instances.
    Local Hint Extern 2 (Zero_Pointed_Morphism i) => simple notypeclasses refine to_ints_mor : typeclass_instances.


    Definition from_nat_op : Nat → Z := fix F n :=
      match n with
      | nat_0 => (false, nil)
      | nat_S n' => let '(l, m) := F n' in succ_op l m
      end.
    Lemma from_nat_op_correct {ℤ:integers} : ∀ n, i (from_nat_op n) = naturals_to_mon Nat ℤ n.
    Proof. refine (fix IH n := _). destruct n as [| n']; cbn [ from_nat_op ].
    + simplify. sym. exact (preserves_0 _).
    + specialize (IH n'). revert IH. destruct (from_nat_op n') as [l m]. intro E.
      rew (succ_op_correct _ _). change (nat_S n') with (1 + n').
      rewrite_preserves (naturals_to_mon Nat ℤ). rew <-E. exact (commutativity (+) _ _).
    Qed.

    Definition from_nat := default_eq_func from_nat_op.
    Definition from_nat_correct {ℤ:integers} : ∀ n,  i (from_nat n) = naturals_to_mon Nat ℤ n := from_nat_op_correct.
    Lemma from_nat_mor : Rig_Morphism from_nat.
    Proof. apply alt_Build_Rig_Morphism.
    + intros x y. apply (injective (to_ints SignedNat)).
      rewrite_preserves (to_ints SignedNat).
      rew ?(from_nat_op_correct _).
      exact (preserves_plus _ _ _).
    + intros x y. apply (injective (to_ints SignedNat)).
      rewrite_preserves (to_ints SignedNat).
      rew ?(from_nat_op_correct _).
      exact (preserves_mult _ _ _).
    + refl.
    + refl.
    Qed.
    Local Hint Extern 2 (Rig_Morphism from_nat) => simple notypeclasses refine from_nat_mor : typeclass_instances.
    Local Hint Extern 2 (AdditiveMonoid_Morphism from_nat) => simple notypeclasses refine from_nat_mor : typeclass_instances.
    Local Hint Extern 2 (AdditiveSemiGroup_Morphism from_nat) => simple notypeclasses refine from_nat_mor : typeclass_instances.
    Local Hint Extern 2 (MultiplicativeMonoid_Morphism from_nat) => simple notypeclasses refine from_nat_mor : typeclass_instances.
    Local Hint Extern 2 (MultiplicativeSemiGroup_Morphism from_nat) => simple notypeclasses refine from_nat_mor : typeclass_instances.
    Local Hint Extern 2 (One_Pointed_Morphism from_nat) => simple notypeclasses refine from_nat_mor : typeclass_instances.
    Local Hint Extern 2 (Rg_Morphism from_nat) => simple notypeclasses refine from_nat_mor : typeclass_instances.
    Local Hint Extern 2 (Zero_Pointed_Morphism from_nat) => simple notypeclasses refine from_nat_mor : typeclass_instances.

    Definition from_ints (ℤ:integers@{u}) := from_group_completion2 (naturals_to_mon Nat ℤ) from_nat.
    Definition from_ints_mor {ℤ:integers@{u}} : Rig_Morphism (from_ints ℤ) := from_group_completion_rig_mor.
    Definition from_ints_spec (ℤ:integers@{u}) : from_ints ℤ ∘ (naturals_to_mon Nat ℤ) = from_nat
      := from_group_completion2_spec.
    Local Hint Extern 2 (Rig_Morphism (from_ints _)) => simple notypeclasses refine from_ints_mor : typeclass_instances.
    Local Hint Extern 2 (AdditiveMonoid_Morphism (from_ints _)) => simple notypeclasses refine from_ints_mor : typeclass_instances.
    Local Hint Extern 2 (AdditiveSemiGroup_Morphism (from_ints _)) => simple notypeclasses refine from_ints_mor : typeclass_instances.
    Local Hint Extern 2 (MultiplicativeMonoid_Morphism (from_ints _)) => simple notypeclasses refine from_ints_mor : typeclass_instances.
    Local Hint Extern 2 (MultiplicativeSemiGroup_Morphism (from_ints _)) => simple notypeclasses refine from_ints_mor : typeclass_instances.
    Local Hint Extern 2 (One_Pointed_Morphism (from_ints _)) => simple notypeclasses refine from_ints_mor : typeclass_instances.
    Local Hint Extern 2 (Rg_Morphism (from_ints _)) => simple notypeclasses refine from_ints_mor : typeclass_instances.
    Local Hint Extern 2 (Zero_Pointed_Morphism (from_ints _)) => simple notypeclasses refine from_ints_mor : typeclass_instances.

    Local Hint Extern 2 (Inverse (from_ints ?Z)) => refine (to_ints Z) : typeclass_instances.
    Local Hint Extern 2 (Inverse (to_ints ?Z)) => refine (from_ints Z) : typeclass_instances.
    Lemma from_ints_surj {ℤ:integers} : Surjective (from_ints ℤ).
    Proof. intro x. change (from_ints ℤ (i x) = x).
      apply (injective (to_ints ℤ)). set (a := i x). clearbody a. clear x.
      pose proof group_completion_decompose (naturals_to_mon Nat ℤ) a as [p [n E]].
      rew E. rewrite_preserves (from_ints ℤ).
      rew ?2(from_ints_spec _ _ : from_ints ℤ (naturals_to_mon Nat ℤ _) = from_nat _).
      rewrite_preserves (to_ints ℤ). now rew ?2(from_nat_correct _).
    Qed.
    Local Hint Extern 2 (Surjective (from_ints _)) => simple notypeclasses refine from_ints_surj : typeclass_instances.

    Local Hint Extern 2 (AdditiveMonoid_Morphism (inverse (from_ints _))) => simple notypeclasses refine to_ints_mor : typeclass_instances.
    Local Hint Extern 2 (One_Pointed_Morphism (inverse (from_ints _))) => simple notypeclasses refine to_ints_mor : typeclass_instances.

    Definition to_group : IntegersToGroup Z := retract_is_int_to_group (from_ints SignedNat).
    Local Hint Extern 2 (IntegersToGroup Z) => refine to_group : typeclass_instances.
    Lemma is_integers : Integers Z.
    Proof. exact (retract_is_int (from_ints SignedNat)). Qed.
    Let inst2 : Integers Z.  Proof. exact is_integers. Qed.


    Local Hint Extern 2 (OrderEmbedding i) => simple notypeclasses refine (integers_to_ring_ord_embedding _) : typeclass_instances.
    Local Hint Extern 2 (OrderPreserving i) => simple notypeclasses refine (integers_to_ring_ord_embedding _) : typeclass_instances.
    Local Hint Extern 2 (OrderReflecting i) => simple notypeclasses refine (integers_to_ring_ord_embedding _) : typeclass_instances.

    Local Hint Extern 2 (SimplifiesTo (bool_to_aprop 0) ?out) => change (SimplifiesTo afalse out) : typeclass_instances.
    Local Hint Extern 2 (SimplifiesTo (bool_to_aprop 1) ?out) => change (SimplifiesTo atrue out) : typeclass_instances.

    Lemma bit_nonneg {ℤ:integers} : ∀ b, 0 ≤ bit_to_ℤ ℤ b.   Proof. ℤ₂_induction; now simplify. Qed.
    Lemma bit_le_1   {ℤ:integers} : ∀ b, bit_to_ℤ ℤ b ≤ 1.   Proof. ℤ₂_induction; now simplify. Qed.

    Lemma leading_bit_negative_iff l : ∀ n, (l, n) < 0 :> Z ⧟ bool_to_aprop l.
    Proof. intros n. rew (strictly_order_embedding (to_ints SignedNat) _ _); rewrite_preserves (to_ints SignedNat).
      revert n. refine (list_sinduction _ _ _).
    + revert l. ℤ₂_induction; simplify.
      * now change (0 ≤ 0 :> SignedNat).
      * rew (strictly_order_embedding_simp (+ 1) _ _); now simplify.
    + intros b n' IH. rew <-IH. clear IH. simplify. set (x := i (l, n')). clearbody x. clear l n'.
      split.
      * apply by_contrapositive. rew <-(bit_nonneg b); simplify.
        exact ( order_preserving_simp (2·) 0 x ).
      * rew ?(integers_lt_plus_1 _ _). rew (bit_le_1 b).
        enough (1 + (2 · x + 1) = 2 · (1 + x)) as E.
        - rew E. exact (order_preserving_simp (2·) _ _).
        - rew ?(mult_2_plus_l _). rew (commutativity (+) 1 x) at 2.
          now rew ?(associativity (+) _ _ _).
    Qed.
    Lemma l_0_nonneg n : 0 ≤ (0, n) :> Z.
    Proof. rew ( contrapositive_iff (leading_bit_negative_iff 0 n) ); now simplify. Qed.
    Lemma l_1_neg n : (1, n) < 0 :> Z.
    Proof. rew ( leading_bit_negative_iff 1 n ); now simplify. Qed.

    Lemma l_nonneg_0 (x:Z) : 0 ≤ x ⧟ π₁ x = 0.
    Proof. apply by_contrapositive_iff. destruct x as [l n]; simplify.
      rew (leading_bit_negative_iff _ _); clear n.
      revert l; ℤ₂_induction; now simplify.
    Qed.


    (* Operations defined above preserve being "reduced" to canonical representations of 0, -1.
       But only if the inputs are reduced. *)
(*
    Definition is_reduced : Z → Ω := λ '(l, n),
      match n with
      | nil => atrue
      | _ => anot ((l, n) = (l, nil) :> Z)
      end.

    Lemma is_reduced_decidable z : Decidable (is_reduced z).
    Proof. destruct z as [l [| b n]]; now cbn [ is_reduced ]. Qed.
    Local Hint Extern 2 (Decidable (is_reduced _)) => simple notypeclasses refine (is_reduced_decidable _) : typeclass_instances.
    Local Hint Extern 2 (Affirmative (is_reduced _)) => simple notypeclasses refine (is_reduced_decidable _) : typeclass_instances.
    Local Hint Extern 2 (Refutative (is_reduced _)) => simple notypeclasses refine (is_reduced_decidable _) : typeclass_instances.

    Lemma append_bit_op_reduced : ∀ (b:ℤ₂) l n, is_reduced (l, n) ⊸ is_reduced (l, append_bit_op b l n).
    Proof. intros b l [| b' n' ].
    + cbn [ is_reduced append_bit_op ]; simplify.
      revert b l; ℤ₂_induction; ℤ₂_induction; change (dec equiv ?x ?x) with true; change (dec equiv _ _) with false; simplify;
        cbn [ is_reduced ]; try easy.
      * change (to_ints SignedNat (1, nil :: 0) ≠ (-1)); simplify.
        apply (contrapositive (injective (X:=SignedNat) (-) 2 1)).
        rew (injective_iff_simp (+ -1) _ _); now simplify.
      * exact one_nonzero.
    + cbn [ is_reduced append_bit_op ]. set (n := n' :: b'). clearbody n. clear b' n'.
      change (to_ints SignedNat (l, n) ≠ to_ints SignedNat (l, nil) ⊸ 
              to_ints SignedNat (l, n :: b) ≠ to_ints SignedNat (l, nil)); simplify.
      revert l; ℤ₂_induction; simplify.
      * set (x := to_ints SignedNat (0, n)).
        assert (0 ≤ x) by ( apply ( preserves_nonneg (to_ints SignedNat) (0, n) ) ; exact (l_0_nonneg n) ).
        apply affirmative_aimpl; intro. apply lt_ne_flip. rew <-(bit_nonneg _); simplify.
        apply (strictly_order_preserving_simp (2·) 0 x).
        apply le_prod_ne_lt; split; trivial. now rew (symmetry_iff (=) _ _).
      * set (x := to_ints SignedNat (1, n)).
        assert (x < 0) by ( apply ( preserves_neg (to_ints SignedNat) (0, n) ) ; exact (l_1_neg n) ).
        apply affirmative_aimpl; intro. apply lt_ne. rew (bit_le_1 _).
        rew (strictly_order_embedding_simp (+ -1) _ _); simplify. rew <-(mult_2_plus_l (-1)).
        apply (strictly_order_preserving_simp (2·) x (-1)).
        apply le_prod_ne_lt; split; trivial.
        rew (integers_le_plus_1 x (-1)); now simplify.
    Qed.
*)

    (*
    Lemma pred_op_reduced l : ∀ n, is_reduced (pred_op l n).
    Proof. refine (list_sinduction _ _ _).
    + cbn [ pred_op ]. revert l; ℤ₂_induction.
      * now change (apos (atrue)).
      * change ( anot (-2 = -1 :> Z )). apply lt_ne.
        rew (strictly_order_embedding_simp (+2) _ _).
        now change (0 < 1 :> Z).
    + intros b n'. cbn [ pred_op ]. destruct (pred_op l n') as [l' n'']. intro IH.
      revert b. ℤ₂_induction; simplify.
    *)

    Definition dec_nonzero : list ℤ₂ → bool := fix F n :=
      match n with
      | nil => false
      | n' :: b => (b || (F n'))%bool
      end.

    Lemma dec_nonzero_correct : ∀ n, (0, n) ≠ 0 :> Z ⧟ bool_to_aprop (dec_nonzero n).
    Proof. refine (list_sinduction _ _ _).
    + change (0 ≠ 0 :> Z ⧟ afalse); now simplify.
    + intros b n'. intros IH. cbn [ dec_nonzero ].
      revert b. ℤ₂_induction.
      * change (0 || dec_nonzero n')%bool with (dec_nonzero n'). rew <-IH.
        rew ?( injective_iff (to_ints SignedNat) _ _); rew zero_correct; simplify.
        set (x := to_ints SignedNat (0, n')); clearbody x; clear IH n'.
        rew (nonzero_product_prod_iff _ _). now enough (2 ≠ 0 :> SignedNat) by now simplify.
      * clear IH. change ((0, n' :: 1) ≠ 0 :> Z ⧟ atrue); simplify.
        rew ?( injective_iff (to_ints SignedNat) _ _); rew zero_correct; simplify.
        rew (is_fun (integers_to_group SignedNat ℤ₂) _ _).
        rew (preserves_plus _ _ _); now simplify.
    Qed.

    Definition trch : Trich Z := λ '(x, y), let '(l, n) := x - y in
      if l then is_lt else (if dec_nonzero n then is_gt else is_eq).
    Local Hint Extern 2 (Trich Z) => refine trch : typeclass_instances.

    Lemma trch_correct : IsTrich Z.
    Proof. split; try exact _; unfold trich, trch. intros x y.
      set (z := x - y). assert (z = x - y) as E by refl; revert E; clearbody z;
        destruct z as [l n].
    + destruct l as [|]; intro E.
      - rew (strictly_order_embedding_simp (+ -y) x y), <-E. exact (l_1_neg _).
      - change ((false, n)) with ((@zero ℤ₂ _, n)) in E.
        pose proof (l_0_nonneg n).
        generalize (dec_nonzero_correct n); destruct (dec_nonzero n) as [|]; simplify; intros E2.
        * rew (strictly_order_embedding_simp (+ -y) y x), <-E.
          apply le_prod_ne_lt; split; trivial. now rew (symmetry_iff (=) _ _).
        * rew (injective_iff_simp (+ -y) x y). now rew <-E.
    Qed.
  End with_ref.

  #[global] Hint Extern 1 (Zero Z) => refine (false, nil) : typeclass_instances.
  #[global] Hint Extern 1 (One Z) => refine (false, nil :: true) : typeclass_instances.
  #[global] Hint Extern 1 (Plus Z) => refine pls : typeclass_instances.
  #[global] Hint Extern 1 (Mult Z) => refine mlt : typeclass_instances.
  #[global] Hint Extern 1 (Negate Z) => refine neg : typeclass_instances.
  #[global] Hint Extern 1 (IntegersToGroup Z) => refine to_group : typeclass_instances.
  #[global] Hint Extern 1 (Trich Z) => refine trch : typeclass_instances.

  #[global] Hint Extern 1 (Integers Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveCancellation Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveGroup Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveMonoid Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveNonComGroup Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveNonComMonoid Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveNonComSemiGroup Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveSemiGroup Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AffirmativeEquality Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (AffirmativeRelation Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (CommutativeRig Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (CommutativeRing Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (DecidableEquality Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (IntegralDomain Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRg Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRig Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRing Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRng Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeComMonoid Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeMonoid Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeSemiGroup Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (NearRg Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (NearRig Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (NearRing Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (NearRng Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (NonZeroMultiplicativeCancellation Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (NoZeroDivisors Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (OneNonZero Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (RefutativeEquality Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (Rg Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (Rig Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (Ring Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (Rng Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (StrongNoZeroDivisors Z) => simple notypeclasses refine is_integers : typeclass_instances.
  #[global] Hint Extern 1 (StrongSet Z) => simple notypeclasses refine is_integers : typeclass_instances.

  #[global] Hint Extern 1 (IsTrich Z) => simple notypeclasses refine trch_correct : typeclass_instances.
  #[global] Hint Extern 1 (IsDecEq Z) => simple notypeclasses refine trch_correct : typeclass_instances.
  #[global] Hint Extern 1 (IsDecLe Z) => simple notypeclasses refine trch_correct : typeclass_instances.

  Import cone_notation.
  Section naturals.
    Universes u.
    Definition N : set@{u}.
    Proof. simple refine (@set_make (list ℤ₂) (λ '(x, y), (0, x) = (0, y) :> Z) _); try exact _.
      refine (@projected_set_IsProjectedSet (list ℤ₂) Z (λ x, (0, x))).
    Defined.

    Lemma N_to_Zplus_is_fun : @IsFun N Z⁺ (λ x, to_subset (U:=Z⁺) (0, x) (el:=l_0_nonneg x)).
    Proof. now intros x y. Qed.
    Definition N_to_Zplus : N ⇾ Z⁺ := @func_make _ _ _ N_to_Zplus_is_fun.
    Local Abbreviation ϕ := N_to_Zplus.

    Lemma Zplus_to_N_is_fun : @IsFun Z⁺ N (λ x, π₂ (subset_pt x)).
    Proof. intros [x elx] [y ely]. change (x = y ⊸ (0, π₂ x) = (0, π₂ y) :> Z).
      assert (π₁ x = 0) as Elx by now rew <-(l_nonneg_0 _).
      assert (π₁ y = 0) as Ely by now rew <-(l_nonneg_0 _).
      destruct x as [l₁ m]; destruct y as [l₂ n].
      revert Elx Ely; simplify; intros Elx Ely.
      rew (symmetry_iff (=) _ _) in Elx. destruct Elx as [].
      rew (symmetry_iff (=) _ _) in Ely. destruct Ely as [].
      refl.
    Qed.
    Definition Zplus_to_N : Z⁺ ⇾ N := @func_make _ _ _ Zplus_to_N_is_fun.

    Local Hint Extern 2 (Inverse N_to_Zplus) => refine Zplus_to_N : typeclass_instances.
    Local Hint Extern 2 (Inverse Zplus_to_N) => refine N_to_Zplus : typeclass_instances.

    Lemma N_to_Zplus_bij : Bijective N_to_Zplus.
    Proof. split.
    + now intros x y.
    + intros [x elx].
      assert (π₁ x = 0) as Elx by now rew <-(l_nonneg_0 _).
      destruct x as [l m]; revert Elx; simplify; intros Elx.
      rew (symmetry_iff (=) _ _) in Elx. destruct Elx as [].
      refl.
    Qed.
    Local Hint Extern 2 (Bijective N_to_Zplus) => simple notypeclasses refine N_to_Zplus_bij : typeclass_instances.
    Local Hint Extern 2 (Injective N_to_Zplus) => simple notypeclasses refine N_to_Zplus_bij : typeclass_instances.
    Local Hint Extern 2 (Surjective N_to_Zplus) => simple notypeclasses refine N_to_Zplus_bij : typeclass_instances.

    Local Hint Extern 1 (Zero N) => refine nil : typeclass_instances.
    Local Hint Extern 1 (One N) => refine (nil :: true) : typeclass_instances.

    Lemma N_zero_correct: N_to_Zplus 0 = 0.  Proof. refl. Qed.
    Lemma N_one_correct: N_to_Zplus 1 = 1.   Proof. refl. Qed.

    Local Open Scope fun_inv_scope.

    Definition N_plus_op: N ∗ N → N := λ '(m, n), π₂ (adder false false m n false).
    Lemma N_plus_op_correct: ∀ p : N ⊗ N, ϕ (N_plus_op p) = ϕ (π₁ p) + ϕ (π₂ p).
    Proof. intros [m n]. change ((ϕ ∘ ϕ⁻¹) (ϕ m + ϕ n) = (ϕ m + ϕ n)). now rew (surjective ϕ). Qed.

    Lemma N_is_proj: IsProjectedSet N (f:=ϕ).  Proof. tautological. Qed.
    Local Hint Extern 2 (IsProjectedSet (set_T N)) => notypeclasses refine N_is_proj : typeclass_instances.

    Local Instance N_pls : Plus N
      := @func_make (N ⊗ N) N (λ '(m, n), π₂ (adder false false m n false)) (projected_is_fun (X:=N ⊗ N) N_plus_op (+) N_plus_op_correct).
    Definition N_plus_correct x y : ϕ (x + y) = ϕ x + ϕ y := N_plus_op_correct (x, y).

    Definition N_mult_op: N ∗ N → N := λ '(m, n), π₂ (multiplier false false m n).
    Lemma N_mult_op_correct: ∀ p : N ⊗ N, ϕ (N_mult_op p) = ϕ (π₁ p) · ϕ (π₂ p).
    Proof. intros [m n]. change ((ϕ ∘ ϕ⁻¹) (ϕ m · ϕ n) = (ϕ m · ϕ n)). now rew (surjective ϕ). Qed.

    Local Instance N_mlt : Mult N
      := @func_make (N ⊗ N) N (λ '(m, n), π₂ (multiplier false false m n)) (projected_is_fun (X:=N ⊗ N) N_mult_op (·) N_mult_op_correct).
    Definition N_mult_correct x y : ϕ (x · y) = ϕ x · ϕ y := N_mult_op_correct (x, y).

    Local Instance N_is_com_rig : CommutativeRig N
      := projected_commutative_rig ϕ  N_plus_correct N_mult_correct N_zero_correct N_one_correct.
    Let inst : CommutativeRig N.  Proof. exact N_is_com_rig. Qed.

    Lemma N_to_Zplus_rig_mor : Rig_Morphism ϕ.
    Proof. exact (alt_Build_Rig_Morphism N_plus_correct N_mult_correct N_zero_correct N_one_correct). Qed.
    Let inst2 : Rig_Morphism ϕ.  Proof. exact N_to_Zplus_rig_mor. Qed.

    Definition N_to_mon : NaturalsToMon N := retract_is_nat_to_mon ϕ⁻¹.
    Local Hint Extern 2 (NaturalsToMon N) => refine N_to_mon : typeclass_instances.
    Lemma N_is_naturals : Naturals N.
    Proof. exact (retract_is_nat ϕ⁻¹). Qed.
    Let inst3 : Naturals N.  Proof. exact N_is_naturals. Qed.

    Lemma N_to_Zplus_ord_embedding : OrderEmbedding ϕ.
    Proof. exact (naturals_to_rig_ord_embedding _). Qed.
    Let inst4 : OrderEmbedding ϕ.  Proof. exact N_to_Zplus_ord_embedding. Qed.

    Local Instance N_trich : Trich N := λ '(x, y), trch ((0, x), (0, y)).
    Lemma N_trich_correct : IsTrich N.
    Proof. split; try exact _. intros x y. change (trich (x, y)) with (trich (subset_pt (ϕ x), subset_pt (ϕ y))).
      generalize (trich_spec (subset_pt (ϕ x)) (subset_pt (ϕ y))).
      destruct (trich (subset_pt (ϕ x), subset_pt (ϕ y))) as [ | | ].
    + change (ϕ x < ϕ y → x < y). apply (strictly_order_reflecting ϕ x y).
    + change (ϕ x = ϕ y → x = y). apply (injective ϕ x y).
    + change (ϕ y < ϕ x → y < x). apply (strictly_order_reflecting ϕ y x).
    Qed.
  End naturals.

  #[global] Hint Extern 1 (Zero N) => refine nil : typeclass_instances.
  #[global] Hint Extern 1 (One N) => refine (nil :: true) : typeclass_instances.
  #[global] Hint Extern 1 (Plus N) => refine N_pls : typeclass_instances.
  #[global] Hint Extern 1 (Mult N) => refine N_mlt : typeclass_instances.
  #[global] Hint Extern 1 (Trich N) => refine N_trich : typeclass_instances.
  #[global] Hint Extern 1 (NaturalsToMon N) => refine N_to_mon : typeclass_instances.

  #[global] Hint Extern 1 (Naturals N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveCancellation N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveMonoid N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveNonComMonoid N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveNonComSemiGroup N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (AdditiveSemiGroup N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (AffirmativeEquality N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (CommutativeRig N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (DecidableEquality N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRg N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (LeftNearRig N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeComMonoid N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeMonoid N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (MultiplicativeSemiGroup N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (NaturalNumbersObject N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (NearRg N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (NearRig N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (NonZeroMultiplicativeCancellation N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (NoZeroDivisors N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (OneNonZero N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (RefutativeEquality N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (Rg N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (Rig N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (StrongNoZeroDivisors N) => simple notypeclasses refine N_is_naturals : typeclass_instances.
  #[global] Hint Extern 1 (StrongSet N) => simple notypeclasses refine N_is_naturals : typeclass_instances.

  #[global] Hint Extern 1 (IsTrich N) => simple notypeclasses refine N_trich_correct : typeclass_instances.
  #[global] Hint Extern 1 (IsDecEq N) => simple notypeclasses refine N_trich_correct : typeclass_instances.
  #[global] Hint Extern 1 (IsDecLe N) => simple notypeclasses refine N_trich_correct : typeclass_instances.
End bin_int.

Canonical Structure BinInt_ring := make_ring bin_int.Z.
Canonical Structure BinInt := Build_integers BinInt_ring bin_int.to_group bin_int.is_integers.

#[global] Hint Extern 1 (Trich (ring_car (ints_ring BinInt))) => refine bin_int.trch : typeclass_instances.
#[global] Hint Extern 1 (IsTrich (ring_car (ints_ring BinInt))) => refine bin_int.trch_correct : typeclass_instances.
#[global] Hint Extern 1 (IsDecEq (ring_car (ints_ring BinInt))) => refine bin_int.trch_correct : typeclass_instances.
#[global] Hint Extern 1 (IsDecLe (ring_car (ints_ring BinInt))) => refine bin_int.trch_correct : typeclass_instances.


Canonical Structure BinNat_near_rig := make_near_rig bin_int.N.
Canonical Structure BinNat := Build_naturals BinNat_near_rig bin_int.N_to_mon bin_int.N_is_naturals.

#[global] Hint Extern 1 (Trich (near_rig_car (nats_near_rig BinNat))) => refine bin_int.N_trich : typeclass_instances.
#[global] Hint Extern 1 (IsTrich (near_rig_car (nats_near_rig BinNat))) => simple notypeclasses refine bin_int.N_trich_correct : typeclass_instances.
#[global] Hint Extern 1 (IsDecEq (near_rig_car (nats_near_rig BinNat))) => simple notypeclasses refine bin_int.N_trich_correct : typeclass_instances.
#[global] Hint Extern 1 (IsDecLe (near_rig_car (nats_near_rig BinNat))) => simple notypeclasses refine bin_int.N_trich_correct : typeclass_instances.


