(**

  Because the functions
<<
       set_T : set → Type 
       func_op : ∀ X Y : set, func X Y → ( set_T X → set_T Y )
>>

  comprising the forgetful functor U : 𝐬𝐞𝐭 → 𝐓𝐲𝐩𝐞 are coercions,
  we can write, e.g.,

     [ λ x y : X , f y x ]

  in a context where [ X Z : set ], [ f : X ⇾ X ⇾ Z ]. That is, the
  internal language of 𝐬𝐞𝐭 is valid syntax. However, the type of the above
  term is not [ X ⇾ X ⇾ Z ], a morphism in 𝐬𝐞𝐭, but rather
  [ set_T X → set_T X → set_T Z ], the underlying function in 𝐓𝐲𝐩𝐞.
  That is, when we write a term designating a morphism g in the internal
  language of 𝐬𝐞𝐭, Coq inserts coercions and we recover only U g. The idea
  of the [ set_internalize ] tactic implemented below is to recover
  [ g : X ⇾ X ⇾ Z ] by inspecting syntax, essentially by implementing a
  model of the categorical semantics of 𝐬𝐞𝐭.

  Typing judgments

     Ξ | Γ ⊢ t : X

  are interpretted as functions

     ⟦ Ξ ⟧ → ⟦ Γ ⟧ ⇾ X.

  Some of the most important typing rules are
<<

  Ξ | Γ, Θ ⊢ t : X     Ξ | Δ, Θ ⊢ u : Y    Θ empty / has affirmative equality
  ───────────────────────────────────────────────────────────────────────────
                          Ξ | Γ, Θ, Δ ⊢ (t, u) : X ⊗ Y               (⊗-pairs)

  Ξ | Γ, Θ ⊢ t : X     Ξ | Δ, Θ ⊢ u : Y
  ─────────────────────────────────────     (×-pairs)
      Ξ | Γ, Θ, Δ ⊢ (t, u) : X × Y


   Ξ | Γ, x : X ⊢ t : Y
  ──────────────────────      (abstraction)
  Ξ | Γ ⊢ λ x, t : X ⇾ Y


   Ξ | Γ ⊢ (f, x) : (X' ⇾ Y) ⊗ X       X coercable to X'
  ──────────────────────────────────────────────────────    (application)
                      Ξ | Γ ⊢ f x : Y


   Ξ, x : X | Γ ⊢ t : Ω             Ξ, x : X | Γ ⊢ t : Ω
  ──────────────────────           ──────────────────────   (quantification)
    Ξ | Γ ⊢ ∏ x, t : Ω              Ξ | Γ ⊢ ∐ x, t : Ω

>>
  Each of these is implemented by some term mapping interpretations of
  the judgements above the line to an interpretation of the judgement below.

*)


Require Import sprop logic.aprop relations theory.set.
Require Import interfaces.set_lambda.notation interfaces.subset.notation.
Require Import easy rewrite tactics.misc.

Import projection_notation.
Import tensor_map_notation.
Import of_course_set_notation.
Local Open Scope fun_inv_scope.

Local Notation α := (tensor_assoc_l _ _ _).
Local Notation uₗ := (tensor_unit_l _).
Local Notation uᵣ := (tensor_unit_r _).

Inductive Environment@{i} :=
| Environment_Empty : Environment
| Environment_Cons (Γ : Environment) (X : set@{i}) (x : X) : Environment.

Module notation.
  Notation "⦃⦄" := Environment_Empty.
  Notation "Γ ,, x" := (Environment_Cons Γ _ x) (at level 40, left associativity).
  Notation Environment_Cons_op x Γ := (Environment_Cons Γ _ x) (only parsing).
  Notation "⦃ x , .. , y ⦄" := (Environment_Cons_op y (.. (Environment_Cons_op x Environment_Empty) ..)).
End notation.
Import notation.

Local Ltac debug_msg tac := idtac.
(* Local Ltac debug_msg tac := match goal with |- ?G => tac G end. *)

(* returns ⟦ Γ ⟧ *)
Ltac env_dom Γ :=
  lazymatch Γ with
  | Environment_Empty => constr:(unit_set)
  | Environment_Cons ?Γ' ?X _ =>
      let D := env_dom Γ' in constr:(D ⊗ X)
  end.

(* returns ( Γ : ⟦ Γ ⟧) *)
Ltac env_reify Γ :=
  lazymatch Γ with
  | Environment_Empty => constr:(tt)
  | Environment_Cons ?Γ' ?X ?x =>
      let p := env_reify Γ' in constr:( (p, x) )
  end.


Definition env_split_cons@{i} {D D' X : set@{i}} (p:D' ⊗ X ⇾ D) Y : D' ⊗ Y ⊗ X ⇾ D ⊗ Y
  := ⟨p, id⟩ ∘ tensor_swap_tail _ _ _.

(* split var from environment Γ.
   returns False if not found, else
     ( Γ', p )
   where
     Γ = Γ', var : X
     p : ⟦ Γ' ⟧ ⊗ X ⇾ ⟦ Γ ⟧
 *)
Ltac env_split Γ var :=
  (* let _ := debug_msg ltac:(idtac; idtac "env_split" Γ var) in *)
  lazymatch Γ with
  | Environment_Empty => constr:(False)
  | Environment_Cons ?Γ' ?X var =>
    let D := env_dom Γ in
    constr:((Γ', id_fun D))
  | Environment_Cons ?Γ' ?X ?x =>
    let res := env_split Γ' var in
    lazymatch res with
    | False => res
    | ( ?Γ'', ?p ) => constr:( ( Environment_Cons Γ'' X x, env_split_cons p X ))
    end
  end.


Definition env_union_base@{i} (Δ:set@{i}) : (Δ ⇾ Δ ⊗ 𝟏 ⊗ 𝟏) ⊗ (Δ ⊗ 𝟏 ⇾ Δ) ⊗ (𝟏 ⊗ 𝟏 ⇾ 𝟏).
Proof. refine (_, _, _).
+ refine (uᵣ ∘ uᵣ)⁻¹.
+ refine uᵣ.
+ refine uᵣ.
Defined.

Definition env_union_left@{i} {Γ Δ Ξ Θ Δ' Θ' Δ'' X : set@{i}} :
   (Γ ⇾ Δ'' ⊗ Ξ ⊗ Θ') ⊗ (Δ'' ⊗ Ξ ⇾ Δ') ⊗ (Θ' ⊗ Ξ ⇾ Θ)
 → (Δ' ⊗ X ⇾ Δ)
 → (Γ ⊗ X ⇾ Δ'' ⊗ (Ξ ⊗ X) ⊗ Θ') ⊗ (Δ'' ⊗ (Ξ ⊗ X) ⇾ Δ) ⊗ (Θ' ⊗ (Ξ ⊗ X) ⇾ Θ ⊗ X).
Proof. intros [[f g]h] p. refine (_, _, _).
+ refine (⟨α, id⟩ ∘ tensor_swap_tail _ _ _ ∘ ⟨f, id⟩).
+ refine (p ∘ ⟨g, id⟩ ∘ α⁻¹).
+ refine (⟨h, id⟩ ∘ α⁻¹).
Defined.

Definition env_union_right@{i} {Γ Δ Ξ Θ Δ' Θ' : set@{i}} (X:set@{i}) :
   (Γ ⇾ Δ' ⊗ Ξ ⊗ Θ') ⊗ (Δ' ⊗ Ξ ⇾ Δ) ⊗ (Θ' ⊗ Ξ ⇾ Θ)
 → (Γ ⊗ X ⇾ Δ' ⊗ Ξ ⊗ (Θ' ⊗ X)) ⊗ (Δ' ⊗ Ξ ⇾ Δ) ⊗ ((Θ' ⊗ X) ⊗ Ξ ⇾ Θ ⊗ X).
Proof. intros [[f g]h]. refine (_, g, _).
+ exact (α ∘ ⟨f, id⟩).
+ refine (⟨h, id⟩ ∘ tensor_swap_tail _ _ _).
Defined.

(* union environments Δ, Θ.
   returns ( Γ, (p, p₁, p₂) )
   where
     Γ = Δ' , Ξ , Θ'
     Δ = Δ' , Ξ
     Θ = Θ' , Ξ
     p : ⟦ Γ ⟧ ⇾ ⟦ Δ' ⟧ ⊗ ⟦ Ξ ⟧ ⊗ ⟦ Θ' ⟧
     p₁ : ⟦ Δ' ⟧ ⊗ ⟦ Ξ ⟧ ⇾ ⟦ Δ ⟧
     p₂ : ⟦ Θ' ⟧ ⊗ ⟦ Ξ ⟧ ⇾ ⟦ Θ ⟧
 *)
Ltac env_union_rec Δ Θ :=
  (* let _ := match goal with _ => idtac "union_env_rec" Δ Θ end in *)
  lazymatch Θ with
  | Environment_Empty =>
      let D := env_dom Δ in
      constr:( (Δ, env_union_base D) )
  | Environment_Cons ?Θ' ?X ?x =>
      let res := env_split Δ x in lazymatch res with
      | (?Δ', ?p) =>
        (* let _ := match goal with _ => let t := type of p in idtac Δ' t end in *)
        let res := env_union_rec Δ' Θ' in lazymatch res with
          (?Γ, ?u) =>
            (* let _ := match goal with _ => let t := type of u in idtac Γ t end in *)
            constr:( (Environment_Cons Γ X x, env_union_left u p) )
        end
      | False =>
        let res := env_union_rec Δ Θ' in lazymatch res with
          (?Γ, ?u) =>
            (* let _ := match goal with _ => let t := type of u in idtac Γ t end in *)
            constr:( (Environment_Cons Γ X x, env_union_right X u) )
        end
      end
  end.

Definition env_union_share@{i} {Γ Δ Ξ Θ Δ' Θ' : set@{i}} :
   (Γ ⇾ Δ' ⊗ Ξ ⊗ Θ') ⊗ (Δ' ⊗ Ξ ⇾ Δ) ⊗ (Θ' ⊗ Ξ ⇾ Θ) → Γ ⇾ Δ × Θ.
Proof. intros [[f g]h]. refine (to_prod (g ∘ tensor_proj1 _ _, h ∘ _) ∘ f).
  refine (tensor_proj2 _ _ ∘ α ∘ tensor_swap_tail _ _ _).
Defined.

Definition env_union_copy@{i} {Γ Δ Ξ Θ Δ' Θ' : set@{i}} `{!AffirmativeEquality Ξ} :
   (Γ ⇾ Δ' ⊗ Ξ ⊗ Θ') ⊗ (Δ' ⊗ Ξ ⇾ Δ) ⊗ (Θ' ⊗ Ξ ⇾ Θ) → Γ ⇾ Δ ⊗ Θ.
Proof. intros [[f g]h]. refine (⟨g, h ∘ tensor_swap _ _⟩ ∘ α ∘ ⟨α⁻¹ ∘ ⟨id, tensor_diag Ξ⟩, id⟩ ∘ f). Defined.

Definition env_union_disjoint@{i} {Γ Δ Θ Δ' Θ' : set@{i}} :
   (Γ ⇾ Δ' ⊗ 𝟏 ⊗ Θ') ⊗ (Δ' ⊗ 𝟏 ⇾ Δ) ⊗ (Θ' ⊗ 𝟏 ⇾ Θ) → Γ ⇾ Δ ⊗ Θ.
Proof. intros [[f g]h]. refine (⟨g, h ∘ uᵣ⁻¹⟩ ∘ f). Defined.

(* union environments Δ, Θ.
   returns ( Γ, p )
   where
     Γ = Δ ∪ Θ
     p : ⟦ Γ ⟧ ⇾ ⟦ Δ ⟧ × ⟦ Θ ⟧
 *)
Ltac env_union_prod_proj Δ Θ :=
  let res := env_union_rec Δ Θ in lazymatch res with
    (?Γ, ?u) => constr:( (Γ, env_union_share u) )
  end.

(* union environments Δ, Θ.
   returns ( Γ, p )
   where
     Γ = Δ ∪ Θ
     p : ⟦ Γ ⟧ ⇾ ⟦ Δ ⟧ ⊗ ⟦ Θ ⟧  if disjoint, or the overlap has affirmative equality
     p : ⟦ Γ ⟧ ⇾ ⟦ Δ ⟧ × ⟦ Θ ⟧  otherwise
 *)
Ltac env_union_proj Δ Θ :=
  let res := env_union_rec Δ Θ in lazymatch res with (?Γ, ?u) =>
    let t := type of u in
    lazymatch t with
    | set_T (_ ⊗ (_ ⊗ 𝟏 ⇾ _)) =>  constr:( (Γ, env_union_disjoint u) )
    | _ => match goal with
           | _ => constr:( (Γ, env_union_copy u) )
           | _ => constr:( (Γ, env_union_share u) )
           end
    end
  end.

Definition env_const@{i} (T:Type@{i}) {X:set@{i}} (x:X) : T → 𝟏 ⇾ X := λ _, const x.

(* returns (⦃⦄, X, m, tm)
     ⊢ tm : X,
     m : ⟦ Ξ ⟧ → ⟦ ⟧ ⇾ X
 *)
Ltac env_const Ξ tm :=
  let T := type of Ξ in
  let m := constr:(env_const T tm) in
  lazymatch m with @env_const _ ?X _ => constr:( (Environment_Empty, X, m, tm) ) end.


Definition env_var@{i} (T:Type@{i}) (X:set@{i}) : T → 𝟏 ⊗ X ⇾ X := λ _, uₗ.

(* look up tm in environment Γ.
   returns (Δ, X, m, tm)
   where
     Δ ⊆ Γ  and  Δ ⊢ tm : X,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ X
 *)
Ltac affine_env_lookup Ξ Γ tm :=
  lazymatch Γ with
  | Environment_Empty => env_const Ξ tm
  | Environment_Cons ?Γ' ?X ?var =>
      lazymatch tm with
      | var =>
        let Δ := constr:(Environment_Cons Environment_Empty X var) in
        let T := type of Ξ in
        constr:( (Δ, X, env_var T X, tm) )
      | _ => affine_env_lookup Ξ Γ' tm
      end
  end.

Definition nonlinear_env_var@{i} (T:Type@{i}) (X:set@{i}) : T * X → 𝟏 ⇾ X := λ p, const (π₂ p).
Definition nonlinear_env_cons@{i} {T:Type@{i}} {Y:set@{i}} (m:T → 𝟏 ⇾ Y) (X:set@{i})
  : T * X → 𝟏 ⇾ Y := λ p, m (π₁ p).

(* look up tm in nonlinear environment Ξ.
   returns False if not found, or else
     (X, m)
   where
     Ξ | ⊢ tm : X,
     m : ⟦ Ξ ⟧ → 𝟏 ⇾ X
 *)
Ltac nonlinear_env_lookup Ξ tm :=
  lazymatch Ξ with
  | tt => constr:(False)
  | @pair ?T (set_T ?X) ?Ξ' ?var =>
    lazymatch tm with
    | var => constr:( (X, nonlinear_env_var T X) )
    | _ =>
      let res := nonlinear_env_lookup Ξ' tm in
      lazymatch res with
      | False => res
      | (?Y, ?m) => constr:( (Y, nonlinear_env_cons m X) )
      end
    end
  end.

(* look up tm in environment Ξ | Γ.
   returns (Δ, X, m, tm)
   where
     Δ ⊆ Γ and  Ξ | Δ ⊢ tm : X,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ X
 *)
Ltac env_lookup Ξ Γ tm :=
  let res := nonlinear_env_lookup Ξ tm in
  lazymatch res with
  | (?X, ?m) => constr:( ( Environment_Empty, X, m, tm ) )
  | False => affine_env_lookup Ξ Γ tm
  end.


Definition abs_const@{i} {T:Type@{i}} {D Y:set@{i}} (m:T → D ⇾ Y) X : T → D ⇾ X ⇾ Y := λ e, const ∘ (m e).
Definition abs_fun@{i} {T:Type@{i}} {D D' X Y:set@{i}} (m:T → D ⇾ Y) (p:D' ⊗ X ⇾ D) : T → D' ⇾ X ⇾ Y := λ e, curry ((m e) ∘ p).

(* interpret tm ≡ (λ var, body) in environment Ξ | Γ.
   returns (via exact) (Δ, Y, m, body')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ tm : X ⇾ Y,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ (X ⇾ Y)
 *)
Ltac interpret_abstraction_inner interpret Ξ Γ var body :=
  (* let _ := match goal with _ => idtac "abstraction" end in *)
  let v := constr:(var : set_T _) in
  let X := lazymatch type of v with set_T ?X => X end in
  let Γ' := constr:(Environment_Cons Γ X var) in
  let res := interpret Ξ Γ' body in
  lazymatch res with  (?Δ, ?Y, ?m, ?body') =>
    let res := env_split Δ var in
    lazymatch res with
    | False => exact (Δ, X ⇾ Y, abs_const m X, body')
    | ( ?Δ', ?p ) => exact (Δ', X ⇾ Y, abs_fun m p, body')
    end
  end.

(* interpret tm ≡ (λ var : X, body) in environment Ξ | Γ.
   returns (Δ, Y, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ tm : X ⇾ Y,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ (X ⇾ Y)
 *)
Ltac interpret_abstraction interpret Ξ Γ tm :=
  (* let _ := match goal with |- _ => idtac "interpret_abstraction" "Γ=" Γ "tm=" tm  end in *)
  lazymatch tm with
  | λ binder : ?T, ?body =>
    let res := eval_under_binder_pair ltac:(interpret_abstraction_inner interpret Ξ Γ) binder T body in
    lazymatch res with (?Δ, ?X ⇾ ?Y, ?m, ?tm') =>
      let env := env_reify Δ in
      let f := constr:( (@set_lambda X Y tm' (func_is_fun (m Ξ env)))) in
      constr:((Δ, X ⇾ Y, m, f))
    end
  end.

Ltac interpret_subset_comprehension interpret Ξ Γ f :=
  let res := interpret_abstraction interpret Ξ Γ f in
  lazymatch res with (?Δ, ?X ⇾ _, ?m, @set_lambda ?X _ ?f' ?H) =>
    constr:( (Δ, 𝒫 X, m, @subset_comprehension X f' H) )
  end.


Definition uncurry_mor@{i} {T:Type@{i}} {Δ X₁ X₂ Y : set@{i}} : (T → Δ ⇾ X₁ ⇾ X₂ ⇾ Y) → (T → Δ ⇾ X₁ ⊗ X₂ ⇾ Y)
:= λ m e, curry (uncurry (uncurry (m e)) ∘ α⁻¹).

(* interpret tm ≡ (λ '(var1, var2) : X, body) in environment Ξ | Γ.
   returns (Δ, Y, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ tm : X ⇾ Y,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ (X ⇾ Y)
 *)
Ltac interpret_pair_abstraction interpret Ξ Γ tm :=
  lazymatch tm with
  | λ pat, let binder0 := pat in let binder1 : ?T1 := proj1 binder0 in let binder2 : ?T2 := proj2 binder0 in ?body =>
    let f := constr:(λ (binder1:T1) (binder2:T2), body) in
    let res := interpret_abstraction interpret Ξ Γ f in
    lazymatch res with  (?Δ, ?X₁ ⇾ ?X₂ ⇾ ?Y, ?m,
                         set_lambda (λ var1:?T1', set_lambda (λ var2:?T2', ?body')) (H:=func_is_fun ?sf)) =>
      let m' := constr:(uncurry_mor m) in
      let f' := constr:(λ pat, let binder0 := pat in let binder1:T1' := proj1 binder0 in let binder2:T2' := proj2 binder0 in
                          match binder1 with var1 => match binder2 with var2 => body' end end) in
      let tm' := constr:(set_lambda f' (H:=func_is_fun (uncurry sf))) in
      constr:((Δ, X₁ ⊗ X₂ ⇾ Y, m', tm'))
    end
  end.

Ltac build_coercion X Y :=
  let _ := debug_msg ltac:(fun _ => idtac "build_coercion" X Y) in
  lazymatch constr:( (X, Y) ) with
  | ( ?X, ?X ) => constr:(id_fun X)
  | ( ! ?X, ?X ) => constr:(of_course_counit X)
  | ( ! ?X, ! ?Y ) =>
    let c := build_coercion constr:(!X) Y in constr:(of_course_extend c)
  | ( ! (?X ⊗ ?Y), ?Z ) =>
    let c := build_coercion constr:(!X ⊗ !Y) Z in constr:(c ∘ of_course_tensor_set X Y)
  | ( ! (?X × ?Y), ?Z ) =>
    let c := build_coercion constr:(!X ⊗ !Y) Z in constr:(c ∘ of_course_prod_set X Y)
  | ( ?X ⊗ ?Y , ?Z ⊗ ?W ) =>
    let c₁ := build_coercion X Z in let c₂ := build_coercion Y W in constr:(⟨c₁, c₂⟩)
  | ( ?X ⊗ ?Y , ?Z × ?W ) =>
    let c₁ := build_coercion X Z in let c₂ := build_coercion Y W in constr:(tensor_to_prod _ _ ∘ ⟨c₁, c₂⟩)
  | ( ?X × ?Y , ?Z × ?W ) =>
    let c₁ := build_coercion X Z in let c₂ := build_coercion Y W in constr:(prod_map (c₁, c₂))
  | ( ! ?X, _ ) => constr:(of_course_counit X)
  | _ => constr:(id_fun X)
  end.

Definition apply_coercion@{i} {T:Type@{i}} {Γ : set@{i}} {X X': set@{i}}
  (m : T → Γ ⇾ X) (c: X ⇾ X') : T → Γ ⇾ X'
:= λ e, c ∘ m e.

Definition app_mor@{i} {T:Type@{i}} {Γ Δ Θ : set@{i}} {X Y : set@{i}}
  (p : Γ ⇾ Δ ⊗ Θ) (f : T → Δ ⇾ (X ⇾ Y)) (x : T → Θ ⇾ X) : (T → Γ ⇾ Y)
:= λ e, eval ∘ ⟨f e, x e⟩ ∘ p.

Definition app_mor_strong@{i} {T:Type@{i}} {Γ Δ Θ : set@{i}} {X Y : set@{i}} `{!StrongOp (@eval X Y)}
  (p : Γ ⇾ Δ × Θ) (f : T → Δ ⇾ (X ⇾ Y)) (x : T → Θ ⇾ X) : (T → Γ ⇾ Y)
:= λ e, strong_op eval ∘ prod_map (f e, x e) ∘ p.


(* interpret application tm := (f x) in environment Ξ | Γ.
   returns (Δ, Y, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ f x : Y,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ Y
 *)
Ltac interpret_application interpret Ξ Γ tm :=
let _ := debug_msg ltac:(fun _ => idtac "application" Γ tm) in
lazymatch tm with ?f ?x =>
  let res := interpret Ξ Γ x in
  lazymatch res with  (?Θ, ?X, ?mx, ?x') =>
    (* coerce f to a strong op, if needed *)
    let res := lazymatch f with
    | @func_op ?X' ?Y' ?g =>
      lazymatch constr:((X, X')) with
      | ((_ × _), (?A ⊗ ?B)) => 
        let h := constr:(@strong_op A B Y' g _) in
        let res := interpret Ξ Γ h in
        lazymatch res with (?res, strong_op ?f') =>
          constr:( (res, f') )
        end
      | _ => interpret Ξ Γ g
      end
    | _ => interpret Ξ Γ f
    end in
    lazymatch res with  (?Δ, ?F, ?mf, ?f') =>
      let res := env_union_proj Δ Θ in
      lazymatch res with (?ΔΘ, ?p) =>
        let force_function_type m F :=
          lazymatch F with
          | _ ⇾ _ => constr:( (m, F) )
          | _ => let F' := eunify uconstr:(_ ⇾ _) F in constr:( (m, F') )
          end in
        let res := lazymatch F with
        | of_course_set ?F' =>
          let mf' := constr:( apply_coercion mf (of_course_counit F') ) in force_function_type mf' F'
        | _ => force_function_type mf F
        end in
        lazymatch res with (?mf, ?X' ⇾ ?Y) =>
          let _ := debug_msg ltac:(fun _ => idtac "applying" X X' Y) in
          let mx := lazymatch X with
          | X' => constr:(mx)
          | _ => let c := build_coercion X X' in constr:(apply_coercion mx c)
          end in
          lazymatch type of p with
          | set_T (_ ⇾ _ ⊗ _) => constr:( (ΔΘ, Y, app_mor        p mf mx, f' x') )
          | set_T (_ ⇾ _ × _) => constr:( (ΔΘ, Y, app_mor_strong p mf mx, f' x') )
          end
        end
      end
    end
  end
end.


Definition tensor_pair_mor@{i} {T:Type@{i}} {Γ Δ Θ : set@{i}} {X Y : set@{i}}
  (p : Γ ⇾ Δ ⊗ Θ) (f : T → Δ ⇾ X) (g : T → Θ ⇾ Y) : (T → Γ ⇾ X ⊗ Y)
:= λ e, ⟨f e, g e⟩ ∘ p.

Definition prod_pair_mor@{i} {T:Type@{i}} {Γ Δ Θ : set@{i}} {X Y : set@{i}}
  (p : Γ ⇾ Δ × Θ) (f : T → Δ ⇾ X) (g : T → Θ ⇾ Y) : (T → Γ ⇾ X × Y)
:= λ e, prod_map (f e, g e) ∘ p.

(* interpret tm := (x, y) in environment Ξ | Γ.
   returns (Δ, Z, m, tm')
   where
     Z = X ⊗ Y if possible (only copyable hypotheses shared), or X × Y otherwise
     Δ ⊆ Γ  and  Ξ | Δ ⊢ (x, y) : Z,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ T
 *)
Ltac interpret_pair interpret Ξ Γ x y :=
  let res₁ := interpret Ξ Γ x in
  let res₂ := interpret Ξ Γ y in
  lazymatch constr:( (res₁, res₂) ) with
    ( (?Δ₁, ?X, ?mx, ?x'), (?Δ₂, ?Y, ?my, ?y') ) =>
      let tm' := constr:(pair x' y') in
      let res := env_union_proj Δ₁ Δ₂ in
      lazymatch res with (?Δ, ?p) =>
        lazymatch type of p with
        | set_T (_ ⇾ _ ⊗ _) => constr:( (Δ, X ⊗ Y, tensor_pair_mor p mx my, tm') )
        | set_T (_ ⇾ _ × _) => constr:( (Δ, X × Y, prod_pair_mor   p mx my, tm') )
        end
      end
  end.


(* interpret tm := (x, y) as a cartesian pair in environment Ξ | Γ.
   returns (Δ, X × Y, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ (x, y) : X × Y,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ X × Y
 *)
Ltac interpret_prod_pair interpret Ξ Γ x y :=
  let res := interpret_pair interpret Ξ Γ x y in
  lazymatch res with
  | (_, _ × _, _, _) => constr:(res)
  | (?Δ, ?X ⊗ ?Y, ?m, ?tm') =>
    let Z := constr:(X ⊗ Y) in let Z' := constr:(X × Y) in
    let c := build_coercion Z Z' in
    constr:( (Δ, Z', apply_coercion m c, tm') )
  end.


(* interpret tm := πᵢ _ in environment Ξ | Γ.
   returns (Δ, X, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ tm : X,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ X
 *)
Ltac interpret_projection interpret Ξ Γ tm :=
  (* let _ := match goal with _ => idtac "interpret_projection" "Γ=" Γ "tm=" tm end in *)
  let p := lazymatch tm with _ ?p => p end in
  let res := interpret Ξ Γ p in
  lazymatch res with (?Δ, ?T, ?m, ?p') =>
    lazymatch T with
    | ?X ⊗ ?Y =>
      lazymatch tm with
      | proj1 _ => constr:( (Δ, X, λ e, tensor_proj1 X Y ∘ m e, proj1 p') )
      | proj2 _ => constr:( (Δ, Y, λ e, tensor_proj2 X Y ∘ m e, proj2 p') )
      end
    | ?X × ?Y =>
      lazymatch tm with
      | proj1 _ => constr:( (Δ, X, λ e, prod_proj1 X Y ∘ m e, proj1 p') )
      | proj2 _ => constr:( (Δ, Y, λ e, prod_proj2 X Y ∘ m e, proj2 p') )
      end
    end
  end.

(* interpret tm := (let _ := _ in _) in environment Ξ | Γ.
   returns (Δ, X, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ tm : X,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ X
 *)
Ltac interpret_let_in interpret Ξ Γ tm :=
  (* let _ := match goal with _ => idtac "interpret_let_in" "Γ=" Γ "tm=" tm end in *)
  lazymatch tm with
  | let binder : ?T := ?expr in ?body =>
    let tm' := constr:( (fun binder : T => body) expr ) in
    let res := interpret_application interpret Ξ Γ tm' in
    lazymatch res with (?res, func_op (set_lambda (fun w => ?body')) ?x) =>
      constr:( (res, let binder : T := x in match binder with w => body' end) )
    end
  end.


(* interpret tm in environment Ξ | Γ
   returns (Δ, X, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ tm : X,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ X
 *)
Ltac interpret_coerce_app_or_const interpret Ξ Γ tm :=
  let _ := debug_msg ltac:(fun _ => idtac "interpret_coerce_app_or_const" "Γ=" Γ "tm=" tm) in
  let c := match tm with
  | ?f ?x ?y ?z => let f' := eval red in (@id (func _ _) (eval_tuncurry3 f)) in constr:((tt, f, f' (x, y, z)))
  | ?f ?x ?y => let f' := eval red in (@id (func _ _) (tuncurry f)) in constr:((true, f, f' (x, y)))
  | ?f ?x => let f' := eval red in (@id (func _ _) f) in constr:((false, f, f' x))
  | _ => constr:(False)
  end in
  let _ := debug_msg ltac:(fun _ => idtac "coerce application" c) in
  lazymatch c with
  | False => env_const Ξ tm
  | (?double, ?f, ?tm') =>
    let f' := lazymatch tm' with ?f' _ => constr:(f') end in
    let res := interpret_application interpret Ξ Γ tm' in
    lazymatch res with (?res, f' ?a) =>
      lazymatch double with
      | false => constr:((res, f a))
      | true => lazymatch a with (?x, ?y) => constr:((res, f x y)) end
      | tt => lazymatch a with (?x, ?y, ?z) => constr:((res, f x y z)) end
      end
    end
  end.

Lemma all_mor_prop@{i} {T A:Type@{i}} {Γ:set@{i}} (m:T * A → Γ ⇾ Ω) (e:T) : @IsFun Γ Ω (λ u : Γ, ∏ x : A, m (e, x) u).
Proof. intros u v. change (?P = ?Q :> AProp_set) with (P ⧟ Q). rew <-(all_aiff _ _), <-all_adj.
  intros x. exact (is_fun (m (e, x)) _ _).
Qed.

Lemma aex_mor_prop@{i} {T A:Type@{i}} {Γ:set@{i}} (m:T * A → Γ ⇾ Ω) (e:T) : @IsFun Γ Ω (λ u : Γ, ∐ x : A, m (e, x) u).
Proof. intros u v. change (?P = ?Q :> AProp_set) with (P ⧟ Q). rew <-(aex_aiff _ _), <-all_adj.
  intros x. exact (is_fun (m (e, x)) _ _).
Qed.

Definition all_mor@{i} {T A:Type@{i}} {Γ:set@{i}} (m:T * A → Γ ⇾ Ω) : T → Γ ⇾ Ω := λ e, @make_fun _ _ _ (all_mor_prop m e).
Definition aex_mor@{i} {T A:Type@{i}} {Γ:set@{i}} (m:T * A → Γ ⇾ Ω) : T → Γ ⇾ Ω := λ e, @make_fun _ _ _ (aex_mor_prop m e).

(* interpret tm in environment Ξ | Γ
   returns (Δ, X, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ tm : X,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ X
 *)
Ltac interpret_quantifier interpret Ξ Γ tm :=
  let res := lazymatch tm with
  | all ?P => constr:( (@all_mor, P) )
  | aex ?P => constr:( (@aex_mor, P) )
  end in
  lazymatch res with
  | ( ?quant_mor, λ binder : ?T, ?body ) =>
    let inner_tac var b :=
      let Ξ' := constr:(pair Ξ var) in
      let res := interpret Ξ' Γ b in
      lazymatch res with  (?Δ, ?Y, ?m, ?body') =>
        exact ( (Δ, Ω, quant_mor _ _ _ m, body') )
      end
    in
    let res := eval_under_binder_pair inner_tac binder T body in
    lazymatch res with (?Δ, _, ?m, ?tm') =>
      lazymatch tm with
      | all _ => constr:( (Δ, Ω, m, all tm') )
      | aex _ => constr:( (Δ, Ω, m, aex tm') )
      end
    end
  end.


(* interpret tm in environment Ξ | Γ
   returns (Δ, X, m, tm')
   where
     Δ ⊆ Γ  and  Ξ | Δ ⊢ tm : X,
     m : ⟦ Ξ ⟧ → ⟦ Δ ⟧ ⇾ X
 *)
Ltac interpret Ξ Γ tm :=
  let _ := debug_msg ltac:(fun _ => idtac "interpret" "Ξ=" Ξ "Γ=" Γ "tm=" tm) in
  lazymatch tm with
  (* abstraction *)
  | λ pat, let x := pat in let binder1 := proj1 x in let binder2 := proj2 x in ?body =>
     interpret_pair_abstraction interpret Ξ Γ tm
  | λ binder : ?T, ?body => interpret_abstraction interpret Ξ Γ tm
  | set_lambda ?f => interpret_abstraction interpret Ξ Γ f
  | subset_comprehension ?f => interpret_subset_comprehension interpret Ξ Γ f
  | let binder := _ in _ => interpret_let_in interpret Ξ Γ tm
  (* application *)
  | func_op (func_op prod_pair ?x) ?y => interpret_prod_pair interpret Ξ Γ x y
  | func_op ?f ?x => interpret_application interpret Ξ Γ tm
  | (λ binder, ?body) ?x => interpret_application interpret Ξ Γ tm
  (* products *)
  | (?x, ?y) => interpret_pair interpret Ξ Γ x y
  | proj1 ?x => interpret_projection interpret Ξ Γ tm
  | proj2 ?x => interpret_projection interpret Ξ Γ tm
  (* quantifiers *)
  | all _ => interpret_quantifier interpret Ξ Γ tm
  | aex _ => interpret_quantifier interpret Ξ Γ tm
  (* variables, constants
       and applications not in the above forms *)
  | _ =>
    let tm_is_var := constr:( ltac:( solve [ is_var tm; exact True | exact False ] ) ) in
    lazymatch tm_is_var with
    | True => env_lookup Ξ Γ tm
    | False => interpret_coerce_app_or_const interpret Ξ Γ tm
    end
  end.

Tactic Notation "set_internalize_tac" open_constr(tm) :=
  let res := interpret constr:(tt) constr:(Environment_Empty) tm in
  lazymatch res with (_, ?tm) => exact tm end.

(*
Notation "'set:(' expr )" := ltac:(set_internalize_tac expr) (only parsing, expr constr at level 200).

Ltac solve_SetLambda := match goal with |- SetLambdaDerivation ?expr =>
  let f := constr:( set:(expr) ) in exact (func_is_fun f) end.

Global Hint Extern 20 (SetLambdaDerivation _) => solve_SetLambda : typeclass_instances.

Section test.

  Universes i.
  Context (X Y Z W : set@{i}).

  Section blah.
    Context (f : X ⇾ Y) (x : !X) (y:Y).
    Check set:( f x ).
  End blah.

  Check set:(λ (f : !(X ⊗ Z ⇾ X)) (g : !(X ⊗ Y ⇾ Z)), ∏ (x : X) (y : Y), f (x, g (x, y)) = x) .

  Context (f: X ⇾ X ⇾ W).

  Context (y:Z) (p: X × Y).

  Check set:(λ h:of_course_set (Z ⊗ Z ⇾ Z), h (h (y, y), y)).

  Fail Check set:(λ h : (Z ⊗ Z ⇾ Z), h (h (y, y), y)).

  Check fun _ : StrongSet Z => set:(λ h : (Z ⊗ Z ⇾ Z), h (h (y, y), y)).

  Import projection_notation.


  Check set:(λ (x:Z), ∐ z, z = x ∧ x = z).

  Check set:(λ P : Ω, P ∧ P : Ω).

  Fail Check set:(λ (z:X), λ  '(x, y), (x = y :> X) ⊠ (y = x) : Ω).

  Check (uncurry set:(λ x y, f x y)).
  Fail Check set:(λ p, f (π₁ p) (π₂ p)).

  Check set:(λ (x:X) (y:X) (P:Ω), aand_fun (eq_fun (x, y), P)).

  Check set:(λ p: X ⊗ Y, proj2 p).

  Check set:( λ x:Z, (proj2 p, proj1 p) ).

  Check set:(let t := y in t).

  Check set:(λ y x, let g := f x in g y).

  Check set:(λ y x, f x y).
  Check (λₛ y x, f x y).


  Check set:(λ x : X, (x,(y, x))).
  Check set:(λ x : X, (x,prod_pair y x)).

  Check set:(λ y x, (λ f : _ ⇾ _, f x) f y).

  Context (g: X ⊗ X ⇾ Y) `{!StrongOp g}.
  Check strong_op g.

  Check set:(λ x, g (x, x)).

  Fail Check set:(λ x, f x x).
  Check set:(λ x : !X, f x x).

  Goal prod_diag X = set:(λ x : X, (x, x)). easy. Abort.

  Check set:(λ y x, (λ f, f) f x y).

  Goal set:(λ x y, (λ f, f) f x y) = f. easy. Abort.

  Goal f = (λₛ x y, (λₛ f, f) f x y). easy. Abort.

  Context `{!AffirmativeEquality X}.

  Check set:(λ x : X, (x, x)).
End test.
*)
