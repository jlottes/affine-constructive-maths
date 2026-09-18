Require Import sprop srelations.
Require Import logic.aprop relations.
Require Import set_lambda.
Require Import orders.orders orders.maps.
Require Import easy rewrite.
Require Export interfaces.reflection_pair.

Import of_course_set_notation.

Local Open Scope sprop_scope.
Local Notation "C 'ᵒ'" := (fiber_op C) (at level 1, format "C 'ᵒ'").

Lemma IniClassSpec_op `{HI:@IniClassSpec C F H R J} : IniClassSpec C ᵒ.
Proof. intros ???? f. change (Ini C f ↔ Rfl C f ∧ Hom C f). now rew (initial_split_iff _). Qed.
#[global] Hint Extern 2 (IniClassSpec _ ᵒ) => simple notypeclasses refine IniClassSpec_op : typeclass_instances.

Lemma EmbClassSpec_op `{HE:@EmbClassSpec C F H R J HJ E} : EmbClassSpec C ᵒ.
Proof. intros ???? f. change (Emb C f ↔ Ini C f ∧ Injective f). now rew (embed_split_iff _). Qed.
#[global] Hint Extern 2 (EmbClassSpec _ ᵒ) => simple notypeclasses refine EmbClassSpec_op : typeclass_instances.

Definition ReflectionPairClasses_op C {CD:ReflectionPairClasses C} : ReflectionPairClasses C ᵒ.
Proof. now esplit. Defined.
#[global] Hint Extern 2 (ReflectionPairClasses ?C ᵒ) => simple notypeclasses refine (ReflectionPairClasses_op C) : typeclass_instances.

Lemma ReflectionPair_op `{HC:@ReflectionPair C CD} : ReflectionPair C ᵒ.
Proof. unshelve esplit; try exact _; apply HC. Qed.
#[global] Hint Extern 2 (ReflectionPair _ ᵒ) => simple notypeclasses refine ReflectionPair_op : typeclass_instances.

Lemma ClovenPair_op `{HC:@ClovenPair C CD CC} : ClovenPair C ᵒ.
Proof. unshelve esplit. intros. exact (cloven_cert _ (c:=HC) u). Qed.
#[global] Hint Extern 2 (ClovenPair _ ᵒ) => simple notypeclasses refine ClovenPair_op : typeclass_instances.

Lemma SaturatedPair_op `{HS:@SaturatedPair C CD} : SaturatedPair C ᵒ.
Proof. unshelve esplit; try exact _.
+ intros X Y FX FY HX HY m P. exact (rp_hom_detect m P).
+ intros X Y FX FY HX HY m P. exact (rp_rfl_detect m P).
Qed.
#[global] Hint Extern 2 (SaturatedPair _ ᵒ) => simple notypeclasses refine SaturatedPair_op : typeclass_instances.

(** The two clauses of saturation, each joined with its cancellation law. *)
Lemma rfl_detect_iff `{HS:@SaturatedPair C CD} {X Y:set} {FX:Fib C X} {FY:Fib C Y} `{!Obj C X, !Obj C Y} (m:X ⇾ Y)
  : Rfl C m ↔ ∀ (S:set) (FS:Fib C S) (g:S ⇾ X), Hom C (m ∘ g) → Hom C g.
Proof. split; [| exact (rp_rfl_detect m) ]. intros Hm S FS g. exact (rp_cancel_fwd m). Qed.

Lemma hom_detect_iff `{HS:@SaturatedPair C CD} {X Y:set} {FX:Fib C X} {FY:Fib C Y} `{!Obj C X, !Obj C Y} (m:X ⇾ Y)
  : Hom C m ↔ ∀ (S:set) (FS:Fib C S) (g:S ⇾ X), Rfl C (m ∘ g) → Rfl C g.
Proof. exact (rfl_detect_iff (C:=C ᵒ) m). Qed.


Coercion ini_construct `{@ReflectionPair C CD} : IniConstruct C.
Proof. split; change (Hom C ?f) with (Ini C f).
+ intros. rew (initial_split_iff _). now split.
+ intros ???? f. rew (initial_split_iff _). now intros [Hf _].
+ intros ???? f. rew (initial_split_iff _). now intros [Hf _].
+ intros ?????? f g. rew (initial_split_iff _). intros [Hf1 Hf2] [Hg1 Hg2]. now split.
Qed.
#[global] Hint Extern 2 (IniConstruct _) => simple notypeclasses refine ini_construct : typeclass_instances.

Coercion emb_construct `{@ReflectionPair C CD} : EmbConstruct C.
Proof. split; change (Hom C ?f) with (Emb C f).
+ intros. rew (embed_split_iff _). now split.
+ intros ???? f. rew (embed_split_iff _). now intros [Hf _].
+ intros ???? f. rew (embed_split_iff _). now intros [Hf _].
+ intros ?????? f g. rew (embed_split_iff _). intros [Hf1 Hf2] [Hg1 Hg2]. now split.
Qed.
#[global] Hint Extern 2 (EmbConstruct _) => simple notypeclasses refine emb_construct : typeclass_instances.


Local Open Scope fun_inv_scope.

Lemma invert_hom `{@ReflectionPair C CD} {X Y:set} {FX:Fib C X} {FY:Fib C Y}
  {f:X ⇾ Y} `{!Hom C f} `{!Inverse f, !Bijective f} : Rfl C f⁻¹.
Proof. apply (rp_cancel_rfl f); try exact _. now rew (surjective f). Qed.
#[global] Hint Extern 2 (Rfl _ _⁻¹) => simple notypeclasses refine invert_hom : typeclass_instances.

#[global] Hint Extern 1 (@Fib ?C ᵒ ?F ?X) => change (@Fib C F X) : typeclass_instances.


Lemma invert_rfl `{@ReflectionPair C CD} {X Y:set} {FX:Fib C X} {FY:Fib C Y}
  {f:X ⇾ Y} `{!Rfl C f} `{!Inverse f, !Bijective f} : Hom C f⁻¹.
Proof. exact (invert_hom (C:=C ᵒ)). Qed.
#[global] Hint Extern 2 (Hom _ _⁻¹) => simple notypeclasses refine invert_rfl : typeclass_instances.

Lemma invert_ini `{@ReflectionPair C CD} {X Y:set} {FX:Fib C X} {FY:Fib C Y}
  {f:X ⇾ Y} `{!Ini C f} `{!Inverse f, !Bijective f} : Emb C f⁻¹.
Proof. rew (embed_split_iff _), (initial_split_iff _). repeat (split; try exact _). Qed.
#[global] Hint Extern 2 (Emb _ _⁻¹) => simple notypeclasses refine invert_ini : typeclass_instances.
#[global] Hint Extern 2 (Ini _ _⁻¹) => simple notypeclasses refine invert_ini : typeclass_instances.

(** Cloven pairs are a fibration and its fiberwise opposite *)

Definition to_fib C `{HC:@Construct C F O H} {X:set} (FX:Fib C X) `{!Obj C X} : fib C X
  := {| fib_Fib := FX ; fib_Obj := _ |}.

Definition obj `(Φ:@fib C F O H HC X) := X.
Definition vert `(Φ:@fib C F O H HC X) (Ψ:fib C X) : obj Φ ⇾ obj Ψ := id_fun X.
#[global] Typeclasses Opaque obj.
#[global] Hint Extern 0 (Fib _ (obj ?Φ)) => refine (fib_Fib Φ) : typeclass_instances.
#[global] Hint Extern 0 (Obj _ (obj ?Φ)) => refine (fib_Obj Φ) : typeclass_instances.

#[global] Hint Extern 0 (Inverse (@vert ?C ?F ?O ?H ?HC ?X ?Φ ?Ψ)) => refine (@vert C F O H HC X Ψ Φ) : typeclass_instances.
#[global] Hint Extern 0 (Bijective (vert _ _)) => unfold vert : typeclass_instances.
#[global] Hint Extern 0 (Injective (vert _ _)) => unfold vert : typeclass_instances.
#[global] Hint Extern 0 (Surjective (vert _ _)) => unfold vert : typeclass_instances.


Lemma detect_hom@{u} `{@ReflectionPair@{u} C CD} {X Y Z:set@{u}} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z}
  (g:X ⇾ Y) (m:Y ⇾ Z) `{!Hom C m} `{!Rfl C m} : Hom C (m ∘ g) ↔ Hom C g.
Proof. split; intros; [ now apply (rp_cancel_fwd m) | exact _ ]. Qed.

Lemma detect_rfl@{u} `{@ReflectionPair@{u} C CD} {X Y Z:set@{u}} {FX:Fib C X} {FY:Fib C Y} {FZ:Fib C Z}
  (g:X ⇾ Y) (m:Y ⇾ Z) `{!Hom C m} `{!Rfl C m} : Rfl C (m ∘ g) ↔ Rfl C g.
Proof. exact (detect_hom (C:=C ᵒ) g m). Qed.

Lemma pull_cart_hom@{u} `{@ClovenPair@{u} C CD CC} {S X Z:set@{u}} {FS:Fib C S} {FZ:Fib C Z}
  (g:S ⇾ X) (f:X ⇾ Z) `{!Obj C Z} : Hom C (f ∘ g) ↔ Hom C (FY:=pull C f) g.
Proof. exact (detect_hom g f). Qed.

Lemma pull_cart_rfl@{u} `{@ClovenPair@{u} C CD CC} {S X Z:set@{u}} {FS:Fib C S} {FZ:Fib C Z}
  (g:S ⇾ X) (f:X ⇾ Z) `{!Obj C Z} : Rfl C (f ∘ g) ↔ Rfl C (FY:=pull C f) g.
Proof. exact (pull_cart_hom (C:=C ᵒ) g f). Qed.


Definition pull_fib C `{HC:@ClovenPair C CD CC} {X Y:set} (f:X ⇾ Y) (Ψ:fib C Y) : fib C X
  := {| fib_Fib := pull C f ; fib_Obj := ini_construct_hom_X (cloven_cert C f) |}.
#[global] Hint Extern 2 (Ini ?C (FX:=fib_Fib (pull_fib ?C ?f _)) ?g) => match f with g => simple notypeclasses refine (cloven_cert C f) end : typeclass_instances.
#[global] Hint Extern 2 (Hom ?C (FX:=fib_Fib (pull_fib ?C ?f _)) ?g) => match f with g => simple notypeclasses refine (initial_hom (Hf:=cloven_cert C f)) end : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (FX:=fib_Fib (pull_fib ?C ?f _)) ?g) => match f with g => simple notypeclasses refine (initial_rfl (Hf:=cloven_cert C f)) end : typeclass_instances.

Section two_fibrations.
  Local Notation "f *" := (pull_fib _ f) (at level 1, left associativity, format "f *").
  Local Coercion obj : fib >-> set.

  Universes u.
  Context `{HC:@ClovenPair@{u} C CD CC}.
  
  Lemma rfl_fiber_op {X:set@{u}} {Φ:fib C X} {Ψ:fib C X}
    : Φ ≤ Ψ ↔ Rfl C (vert Ψ Φ).
  Proof. split.
  + change (Hom C (vert Φ Ψ) → Rfl C (vert Φ Ψ)⁻¹). now intro.
  + change (Rfl C (vert Ψ Φ) → Hom C (vert Ψ Φ)⁻¹). now intro.
  Qed.
  
  Section cleavage_order.
    Context {X Y:set@{u}} {Φ:fib C X} {Ψ:fib C Y} (f:X ⇾ Y).
  
    Lemma hom_pull_alt : Hom C f ↔ Φ ≤ f* Ψ.
    Proof. exact (pull_cart_hom (id_fun _) f). Qed.
  
    Lemma rfl_pull_alt : Rfl C f ↔ f* Ψ ≤ Φ.
    Proof. rew rfl_fiber_op. exact (pull_cart_rfl (id_fun _) f). Qed.
    
    Lemma ini_pull_alt : Ini C f ↔ f* Ψ = Φ.
    Proof. rew [(symmetry_iff (=) _ _)|(initial_split_iff f)].
      now rew [hom_pull_alt|rfl_pull_alt].
    Qed.
  
    Lemma hom_pull_alt2 : of_course (Hom C f) ⧟ Φ ≤ f* Ψ.
    Proof. apply affirmative_aiff. exact hom_pull_alt. Qed.
  
    Lemma rfl_pull_alt2 : of_course (Rfl C f) ⧟ f* Ψ ≤ Φ.
    Proof. apply affirmative_aiff. exact rfl_pull_alt. Qed.
  End cleavage_order.
  
  Lemma pull_fib_mono {X Y:set@{u}} (f:X ⇾ Y) (Ψ₁ Ψ₂ : fib C Y)
    : Ψ₁ ≤ Ψ₂ ⊸ f* Ψ₁ ≤ f* Ψ₂.
  Proof. apply affirmative_aimpl. intro.
    rew <-(hom_pull_alt f). now change (Hom C (vert Ψ₁ Ψ₂ ∘ (f:f* Ψ₁ ⇾ Ψ₁))).
  Qed.
End two_fibrations.

Section fib_pull.
  Universes u.
  Context `{HC:@ClovenPair@{u} C CD CC} {S Z:set@{u}}.
  
  Lemma fib_pull_is_fun_aux (u v : S ⇾ Z) (Ψ:fib C Z) : u = v → Hom C (FX:=pull C u) (FY:=pull C v) (id_fun S).
  Proof. intros Eu.  unshelve refine (rp_cancel_fwd (FY:=pull C v) v _); try exact _.
    change (v ∘ id_fun _) with v. now rew <-Eu.
  Qed.

  Local Instance fib_pull_is_fun : @IsFun (!(S ⇾ Z) ⊗ fib C Z) (fib C S) (λ '(f, Ψ), pull_fib C f Ψ).
  Proof. apply coordinatewise_is_fun.
  + intros u v Ψ. apply affirmative_aimpl. intros Eu. split.
    * exact (fib_pull_is_fun_aux u v _ Eu).
    * refine (fib_pull_is_fun_aux v u _ _). now apply symmetry.
  + intros u; change (set_T (S ⇾ Z)) in u. intros Ψ₁ Ψ₂. apply aand_intro.
    * rew (eq_le _ _). exact (pull_fib_mono _ _ _).
    * rew (eq_le_flip _ _). exact (pull_fib_mono _ _ _).
  Qed.
  
  Definition fib_pull := curry (@func_make _ _ _ fib_pull_is_fun).
  Local Notation "f *" := (func_op fib_pull f) (at level 1, left associativity, format "f *").

  Local Instance fib_pull_order_preserving (f:S ⇾ Z) : OrderPreserving f*.
  Proof. apply alt_Build_OrderPreserving. exact (pull_fib_mono f). Qed.
End fib_pull.

Local Notation "f *" := (func_op fib_pull f) (at level 1, left associativity, format "f *").
#[global] Hint Extern 2 (OrderPreserving _*) => simple notypeclasses refine fib_pull_order_preserving : typeclass_instances.

#[global] Hint Extern 2 (Ini ?C (FX:=fib_Fib (func_op ?f * _)) ?g) => match f with g => simple notypeclasses refine (cloven_cert C f) end : typeclass_instances.
#[global] Hint Extern 2 (Hom ?C (FX:=fib_Fib (func_op ?f * _)) ?g) => match f with g => simple notypeclasses refine (initial_hom (Hf:=cloven_cert C f)) end : typeclass_instances.
#[global] Hint Extern 2 (Rfl ?C (FX:=fib_Fib (func_op ?f * _)) ?g) => match f with g => simple notypeclasses refine (initial_rfl (Hf:=cloven_cert C f)) end : typeclass_instances.

Lemma fib_pull_id@{u} `{HC:@ClovenPair@{u} C CD CC} {X:set@{u}} {Φ:fib C X} : (id_fun X)* Φ = Φ.
Proof. now apply ini_pull_alt. Qed.

Local Coercion obj : fib >-> set.

Lemma fib_pull_compose@{u} `{HC:@ClovenPair@{u} C CD CC} {X Y Z:set@{u}}
  (f:X ⇾ Y) (g:Y ⇾ Z) (Ξ:fib C Z) : (g ∘ f)* Ξ = f* (g* Ξ).
Proof. apply ini_pull_alt. now change (Ini C ((g:g* Ξ ⇾ Z) ∘ (f:f* (g* Ξ) ⇾ g* Ξ))). Qed.

(** Cloven pairs are saturated: the identity at the pullback lift is the
    universal test, for both clauses. *)
Lemma cloven_rfl_detect `{HC:@ClovenPair C CD CC} {X Y:set} {FX:Fib C X} {FY:Fib C Y} `{!Obj C X, !Obj C Y} (m:X ⇾ Y)
  : (∀ (S:set) (FS:Fib C S) (g:S ⇾ X), Hom C (m ∘ g) → Hom C g) → Rfl C m.
Proof. intro P. apply (rfl_pull_alt (Φ:=to_fib C FX) (Ψ:=to_fib C FY) m).
  change (Hom C (FX:=pull C m) (FY:=FX) (id_fun X)).
  apply (P X (pull C m) (id_fun X)). now change (Hom C (FX:=pull C m) m).
Qed.

Coercion cloven_saturated `{HC:@ClovenPair C CD CC} : SaturatedPair C.
Proof. unshelve esplit; try exact _.
+ intros X Y FX FY HX HY m. exact (cloven_rfl_detect m).
+ intros X Y FX FY HX HY m. exact (cloven_rfl_detect (C:=C ᵒ) m).
Qed.


(** The lifting-UP face of 𝓜: the Joy-of-Cats initial-morphism UP, abstract in
    any cloven pair.  Forward is detection (pair-only); the converse tests the
    identity at the pullback lift. *)
Lemma ini_lift_alt `{HC:@ClovenPair C CD CC} {X Z:set} {FX:Fib C X} {FZ:Fib C Z}
  (f:X ⇾ Z) `{!Obj C X} `{!Obj C Z}
  : Ini C f ↔ (∀ (S:set) (FS:Fib C S), Obj C S → ∀ (g:S ⇾ X), (Hom C (f ∘ g) ↔ Hom C g)).
Proof. split.
+ intros Hf S FS HS g. exact (detect_hom g f).
+ intro P. rew (initial_split_iff f). split.
  * pose proof P X FX _ (id_fun X) as [_ Hb]. exact (Hb _).
  * pose (Φ := to_fib C FX). pose (Ψ := to_fib C FZ).
    apply (rfl_pull_alt (Φ:=Φ) (Ψ:=Ψ) f); change (Hom C (vert (f* Ψ) Φ)).
    apply (P X (f* Ψ) _ (vert (f* Ψ) Φ)).
    now change (Hom C (f:f* Ψ ⇾ Ψ) ).
Qed.

Lemma ini_lift_alt2 `{HC:@ClovenPair C CD CC} {X Z:set} {FX:Fib C X} {FZ:Fib C Z}
  (f:X ⇾ Z) `{!Hom C f}
  : Ini C f ↔ (∀ (S:set) (FS:Fib C S), Obj C S → ∀ (g:S ⇾ X), (Hom C (f ∘ g) → Hom C g)).
Proof. rew (ini_lift_alt f). split; intros P S FS HS g.
+ now apply P.
+ split; [ now apply P | now intro ].
Qed.

(** Restriction to a full subcategory (doc §2.1/§2.3 item 4), key-free: over a
    fiber predicate closed under the cleavage, 𝓜-membership is detected by the
    restricted tests alone.  Forward is detection (no closure needed); the
    converse tests the identity at the pullback lift, legitimately in the
    subcategory by [Hpull]. *)
Lemma ini_lift_alt_restrict `{HC:@ClovenPair C CD CC}
  (Good : ∀ X:set, Fib C X → SProp)
  (Hpull : ∀ (S Z:set) (u:S ⇾ Z) (FZ:Fib C Z), Obj C Z → Good Z FZ → Good S (pull C u))
  {X Z:set} {FX:Fib C X} {FZ:Fib C Z}
  (f:X ⇾ Z) `{!Obj C X} `{!Obj C Z} (GX : Good X FX) (GZ : Good Z FZ)
  : Ini C f ↔ (∀ (S:set) (FS:Fib C S), Obj C S → Good S FS → ∀ (g:S ⇾ X), (Hom C (f ∘ g) ↔ Hom C g)).
Proof. split.
+ intros Hf S FS HS GS g. exact (detect_hom g f).
+ intro P. rew (initial_split_iff f). split.
  * pose proof P X FX _ GX (id_fun X) as [_ Hb]. exact (Hb _).
  * pose (Φ := to_fib C FX). pose (Ψ := to_fib C FZ).
    apply (rfl_pull_alt (Φ:=Φ) (Ψ:=Ψ) f); change (Hom C (vert (f* Ψ) Φ)).
    apply (P X (f* Ψ) _ (Hpull X Z f FZ _ GZ) (vert (f* Ψ) Φ)).
    now change (Hom C (f:f* Ψ ⇾ Ψ) ).
Qed.

(** * Pair morphisms: derived theory.
    The class swap is the identity on pair morphisms; Obj/𝓜/Emb-preservation and
    the cloven-fibred-functor comparison are theorems, not data. *)

Lemma PairMorphism_op `{HM:PairMorphism C D} : PairMorphism C ᵒ D ᵒ.
Proof. now split. Qed.
#[global] Hint Extern 2 (PairMorphism _ ᵒ _ ᵒ) => simple notypeclasses refine PairMorphism_op : typeclass_instances.

Lemma pmap_obj `{HM:PairMorphism C D}
  {X:set} {FX:Fib C X} : Obj C X → Obj D X (FX:=fmap C D FX).
Proof. intro. now pose proof (hom_map C D (id_fun X)). Qed.

Lemma ini_map C D `{HM:PairMorphism C D}
  {X Y:set} {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y)
  `{!Ini C f} : Ini D (FX:=fmap C D FX) (FY:=fmap C D FY) f.
Proof.  apply (initial_split_iff f). split.
+ exact (hom_map C D f).
+ exact (rfl_map C D f).
Qed.

Lemma emb_map C D `{HM:PairMorphism C D}
  {X Y:set} {FX:Fib C X} {FY:Fib C Y} (f:X ⇾ Y)
  `{!Emb C f} : Emb D (FX:=fmap C D FX) (FY:=fmap C D FY) f.
Proof. apply (embed_split_iff f). split.
+ exact (ini_map C D f).
+ exact _.
Qed.

Definition fib_map_opn C D `{HM:PairMorphism C D} {X:set} (Φ:fib C X) : fib D X
:= {| fib_Fib := fmap C D (fib_Fib Φ) ; fib_Obj := pmap_obj (fib_Obj Φ) |}.

Lemma fib_map_mono C D `{HM:PairMorphism C D} {X:set} (Φ Ψ:fib C X) : Φ ≤ Ψ ⊸ fib_map_opn C D Φ ≤ fib_map_opn C D Ψ.
Proof. apply affirmative_aimpl. intro E. exact (hom_map C D (id_fun X)). Qed.

Lemma fib_map_is_fun C D `{HM:PairMorphism C D}
  {X:set} : @IsFun (fib_set C X) (fib_set D X) (fib_map_opn C D).
Proof. intros Φ Ψ. apply aand_intro.
+ rew (eq_le _ _). exact (fib_map_mono C D _ _).
+ rew (eq_le_flip _ _). exact (fib_map_mono C D _ _).
Qed.

Definition fib_map C D `{HM:PairMorphism C D}
  {X:set} : fib_set C X ⇾ fib_set D X := @func_make _ _ _ (fib_map_is_fun C D).

Lemma fib_map_order_preserving C D `{HM:PairMorphism C D}
  {X:set} : OrderPreserving (fib_map C D (X:=X)).
Proof. apply alt_Build_OrderPreserving. exact (fib_map_mono C D). Qed.

(** Between cloven pairs, every pair morphism is a cloven fibred functor:
    it commutes with the cleavage up to the fiber equality. *)
Lemma fib_map_pull C D `{HC:ClovenPair C, HD:ClovenPair D} `{HM:!PairMorphism C D (U:=U)} {X Y:set} (f:X ⇾ Y) (Ψ:fib C Y)
  : f* (fib_map C D Ψ) = fib_map C D (f* Ψ).
Proof. apply ini_pull_alt. exact (ini_map C D f). Qed.

Definition fmap_id C {FC:Fiber C} : FiberMap C C := λ X FX, FX.
#[global] Hint Extern 2 (FiberMap ?C ?C) => exact (fmap_id C) : typeclass_instances.

Lemma PairMorphism_id C `{ReflectionPair C} : PairMorphism C C.
Proof. split; try exact _; now intros. Qed.

Definition fmap_compose@{u} {C D K:Cat} {FC FD FK} (U:@FiberMap@{u} C D FC FD) (V:@FiberMap@{u} D K FD FK)
  : @FiberMap C K FC FK := λ X FX, V X (U X FX).

Lemma PairMorphism_compose@{u} C D K
  `{HM1:@PairMorphism@{u} C D CD DD U}
  `{HM2:@PairMorphism@{u} D K DD KD V}
  : PairMorphism C K (U:=fmap_compose U V).
Proof. split; try exact _; intros X Y FX FY f Hf.
+ pose proof (hom_map C D f).
  change (Hom K (FX:=fmap D K (fmap C D FX)) (FY:=fmap D K (fmap C D FY)) f).
  exact (hom_map D K f).
+ pose proof (rfl_map C D f).
  change (Rfl K (FX:=fmap D K (fmap C D FX)) (FY:=fmap D K (fmap C D FY)) f).
  exact (rfl_map D K f).
Qed. 


