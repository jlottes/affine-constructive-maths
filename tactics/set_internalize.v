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

*)


Require Import prop_eq sprop logic.aprop relations theory.set.
Require Import interfaces.set_lambda.notation interfaces.subset.notation.
Require Import easy rewrite tactics.misc.

Import projection_notation.
Import tensor_map_notation.
Import of_course_set_notation.
Local Open Scope fun_inv_scope.

Local Ltac debug_msg tac := idtac.
(* Local Ltac debug_msg tac := match goal with |- ?G => tac G end. *)

Local Abbreviation α := (tensor_assoc_l _ _ _).
Local Abbreviation uₗ := (tensor_unit_l _).
Local Abbreviation uᵣ := (tensor_unit_r _).

Inductive AShape@{u} : set@{u} → Type :=
| AUnit : AShape 𝟏
| AAtom (X:set@{u}) : AShape X
| IAtom (X:set@{u}) : (X ⇾ X ⊗ X) → AShape X
| AProdT {X Y:set@{u}} : AShape X → AShape Y → AShape (X ⊗ Y)
| AProdC {X Y:set@{u}} : AShape X → AShape Y → AShape (X × Y).

Inductive ACtx : Type :=
| AEmpty : ACtx
| ACons (Γ:ACtx) `(A:AShape X) : X → ACtx.

Inductive ASubShape@{u} : ∀ `(A:AShape@{u} X), Type :=
| ASubTop `(A:AShape@{u} X) : ASubShape A
| ASubBot `(A:AShape@{u} X) : ASubShape A
| ASubProdT {X Y} {A:AShape@{u} X} {B:AShape@{u} Y} : ASubShape A → ASubShape B → ASubShape (AProdT A B)
| ASubProdC {X Y} {A:AShape@{u} X} {B:AShape@{u} Y} : ASubShape A → ASubShape B → ASubShape (AProdC A B).

Inductive ASubCtx@{u} : ACtx@{u} → Type :=
| ASubEmpty : ASubCtx AEmpty
| ASubCons {Γ:ACtx@{u}} `{A:AShape@{u} X} : ASubCtx Γ → ∀ (x:X), ASubShape A → ASubCtx (ACons Γ A x).

Inductive SMor@{u} `(A:AShape@{u} X) `(B:AShape@{u} Y) :=
| smor : (X ⇾ Y) → SMor A B.

Inductive AliasList : Type :=
| AliasEmpty : AliasList
| AliasCons (ρ : AliasList) (X:set) (lhs rhs : X) : AliasList.

(** Judgment *)
Record Judgment@{u}
  `(T:ASubCtx@{u} Γ) (D X:set@{u}) := judgment
{ judgment_mor : D ⇾ X
; judgment_tm  : X
}.
Arguments judgment {Γ} T D X _ _.


(** Errors *)
Inductive Excn :=
| var_not_found : Excn
| nonlinear_var_use {X:set} : X → Excn
| unexpected_projection : Excn
| not_implemented : Excn
| type_not_a_set : Excn
| operation_open_arg {A:Type} : A → Excn
| not_closed {A:Type} : A → Excn.


Module notation.

  (* AShape — tree-structured shape (𝟏 only at top; products combine atoms) *)
  Notation "'𝟏ₐ'" := AUnit (only printing).
  Notation "'[' X ']'" := (AAtom X) (only printing).
  Notation "'!' '[' X ']'" := (IAtom X _) (only printing, format "! [ X ]").
  Notation "A '⊗ₐ' B" := (AProdT A B)
    (at level 55, left associativity, only printing).
  Notation "A '×ₐ' B" := (AProdC A B)
    (at level 55, left associativity, only printing).

  (* ACtx — variable spine, each entry typed by an AShape *)
  Notation "'∅'" := AEmpty (only printing).
  Notation "Γ ';;' x '⦂' A" := (ACons Γ A x)
    (at level 60, left associativity, only printing).

  (* ASubShape — selection tree mirroring an AShape (⊤/⊥ at leaves) *)
  Notation "'⊤ₛ'" := (ASubTop _) (only printing).
  Notation "'⊥ₛ'" := (ASubBot _) (only printing).
  Notation "S '⊗ₛ' T" := (ASubProdT S T)
    (at level 55, left associativity, only printing).
  Notation "S '×ₛ' T" := (ASubProdC S T)
    (at level 55, left associativity, only printing).

  (* ASubCtx — selection spine mirroring an ACtx *)
  Notation "'∅ₛ'" := ASubEmpty (only printing).
  Notation "S ';;' x '↦' T" := (ASubCons S x T)
    (at level 60, left associativity, only printing).

  (* SMor — wrapped morphism between two shapes; show only the underlying map *)
  Notation "⟦ m ⟧" := (smor _ _ m) (only printing).

  (* AliasList — list of let-bound aliases lhs ≔ rhs *)
  Notation "'∅ᵨ'" := AliasEmpty (only printing).
  Notation "ρ ';;' lhs '≔' rhs" := (AliasCons ρ _ lhs rhs)
    (at level 60, left associativity, only printing).

End notation.
Import notation.


Ltac closed_wrt_ctx Γ x := lazymatch Γ with
  | AEmpty => constr:(true)
  | ACons ?Γ' _ ?v => lazymatch x with
    | context[v] => constr:(false)
    | _ => closed_wrt_ctx Γ' x
    end
  end.

Ltac closed_wrt_aliases ρ x := lazymatch ρ with
  | AliasEmpty => constr:(true)
  | AliasCons ?ρ' _ ?lhs _ => lazymatch x with
    | context[lhs] => constr:(false)
    | _ => closed_wrt_aliases ρ' x
    end
  end.

Ltac closed_wrt Γ ρ x :=
  let r := closed_wrt_ctx Γ x in
  lazymatch r with false => constr:(false) | true => closed_wrt_aliases ρ x end.
  

Ltac reify_ctx Γ := lazymatch Γ with
| AEmpty => constr:(tt)
| ACons AEmpty _ ?x => constr:(x)
| ACons ?Γ' _ ?x => let p := reify_ctx Γ' in constr:((p, x))
end. 

Ltac aprodt A B := lazymatch A with
| AUnit => B
| _ => lazymatch B with
  | AUnit => A
  | _ => constr:(AProdT A B)
  end
end.

Ltac aprodc A B := lazymatch A with
| AUnit => B
| _ => lazymatch B with
  | AUnit => A
  | _ => constr:(AProdC A B)
  end
end.

Ltac realize_shape S := lazymatch S with
| ASubTop ?A  => A
| ASubBot _ => constr:(AUnit)
| ASubProdT ?S ?T =>
  let A := realize_shape S in
  let B := realize_shape T in
  aprodt A B
| ASubProdC ?S ?T =>
  let A := realize_shape S in
  let B := realize_shape T in
  aprodc A B
end.

Ltac realize_ctx_shape T := lazymatch T with
| ASubEmpty => constr:(AUnit)
| ASubCons ?T' _ ?S =>
  let A := realize_ctx_shape T' in
  let B := realize_shape S in
  aprodt A B
end.

Ltac comp g f :=
  lazymatch g with
  | id_fun _ => f
  | _ => lazymatch f with
    | id_fun _ => g
    | _ => constr:(g ∘ f)
    end
  end.
  
Ltac tmap f g :=
  let t := constr:((f, g)) in lazymatch t with
  | (id_fun ?X, id_fun ?Y) => constr:(id_fun (X ⊗ Y))
  | _ => constr:(⟨f, g⟩)
  end.

Ltac pmap f g :=
  let t := constr:((f, g)) in lazymatch t with
  | (id_fun ?X, id_fun ?Y) => constr:(id_fun (X × Y))
  | _ => constr:(prod_map t)
  end.

Ltac aprodt_mor c₁ c₂ :=
  lazymatch c₁ with @smor ?X₁ ?A₁ ?Y₁ ?B₁ ?m₁ =>
  lazymatch c₂ with @smor ?X₂ ?A₂ ?Y₂ ?B₂ ?m₂ =>
    lazymatch A₁ with
    | AUnit => constr:( smor A₂ B₂ m₂ )
    | _ => lazymatch A₂ with
      | AUnit => constr:( smor A₁ B₁ m₁ )
      | _ => lazymatch B₁ with
        | AUnit =>
          let m := comp m₂ constr:(tensor_proj2 X₁ X₂) in
          constr:( smor (AProdT A₁ A₂) B₂ m )
        | _ => lazymatch B₂ with
          | AUnit =>
            let m := comp m₁ constr:(tensor_proj1 X₁ X₂) in
            constr:( smor (AProdT A₁ A₂) B₁ m )
          | _ =>
            let m := tmap m₁ m₂ in
            constr:( smor (AProdT A₁ A₂) (AProdT B₁ B₂) m )
          end
        end
      end
    end
  end end.

Ltac aprodc_mor c₁ c₂ :=
  lazymatch c₁ with @smor ?X₁ ?A₁ ?Y₁ ?B₁ ?m₁ =>
  lazymatch c₂ with @smor ?X₂ ?A₂ ?Y₂ ?B₂ ?m₂ =>
    lazymatch A₁ with
    | AUnit => constr:( smor A₂ B₂ m₂ )
    | _ => lazymatch A₂ with
      | AUnit => constr:( smor A₁ B₁ m₁ )
      | _ => lazymatch B₁ with
        | AUnit =>
          let m := comp m₂ constr:(prod_proj2 X₁ X₂) in
          constr:( smor (AProdC A₁ A₂) B₂ m )
        | _ => lazymatch B₂ with
          | AUnit =>
            let m := comp m₁ constr:(prod_proj1 X₁ X₂) in
            constr:( smor (AProdC A₁ A₂) B₁ m )
          | _ =>
            let m := pmap m₁ m₂ in
            constr:( smor (AProdC A₁ A₂) (AProdC B₁ B₂) m )
          end
        end
      end
    end
  end end.

Ltac realize_shape_mor S := lazymatch S with
| @ASubTop ?X ?A => constr:( smor A A (id_fun X) )
| @ASubBot ?X ?A => constr:( smor A AUnit (to_Unit X) )
| ASubProdT ?S ?T =>
  let r₁ := realize_shape_mor S in
  let r₂ := realize_shape_mor T in
  aprodt_mor r₁ r₂
| ASubProdC ?S ?T =>
  let r₁ := realize_shape_mor S in
  let r₂ := realize_shape_mor T in
  aprodc_mor r₁ r₂
end.

Ltac realize_ctx_shape_mor T := lazymatch T with
| ASubEmpty => constr:( smor AUnit AUnit (id_fun 𝟏) )
| ASubCons ?T' _ ?S =>
  let r₁ := realize_ctx_shape_mor T' in
  let r₂ := realize_shape_mor S in
  aprodt_mor r₁ r₂
end.

(** The functor F_A : Sub(A) → C on morphisms.
    Given S, T ∈ ASubShape(A) with T ≤ S, produces SMor A_S A_T. *)
Ltac F_A_mor S T := lazymatch T with
| ASubBot _ =>
  let A_S := realize_shape S in
  let X_S := lazymatch type of A_S with AShape ?X => X end in
  constr:( smor A_S AUnit (to_Unit X_S) )
| _ => lazymatch S with
  | ASubTop _ => realize_shape_mor T
  | ASubProdT ?S₁ ?S₂ => lazymatch T with ASubProdT ?T₁ ?T₂ =>
      let r₁ := F_A_mor S₁ T₁ in
      let r₂ := F_A_mor S₂ T₂ in
      aprodt_mor r₁ r₂
    end
  | ASubProdC ?S₁ ?S₂ => lazymatch T with ASubProdC ?T₁ ?T₂ =>
      let r₁ := F_A_mor S₁ T₁ in
      let r₂ := F_A_mor S₂ T₂ in
      aprodc_mor r₁ r₂
    end
  end
end.

(** The functor F_Γ : Sub(Γ) → C on morphisms.
    Given S, T ∈ ASubCtx(Γ) with T ≤ S, produces SMor (Γ_S) (Γ_T). *)
Ltac F_Γ_mor S T := lazymatch S with
| ASubEmpty => constr:( smor AUnit AUnit (id_fun 𝟏) )
| ASubCons ?S' _ ?SubA_S => lazymatch T with ASubCons ?T' _ ?SubA_T =>
    let r_prefix := F_Γ_mor S' T' in
    let r_var := F_A_mor SubA_S SubA_T in
    aprodt_mor r_prefix r_var
  end
end.


(** Linearity check for F_Γ_mor / F_A_mor.
    Walks two ASubShapes [S, T] (over the same underlying AShape) in lockstep,
    accumulating projection chains in [tm]. Returns sentinel [le_ok] when
    [T ≤ S], else returns the constr [proj_chain] from [tm] to a leaf where
    T = ASubTop but S = ASubBot — i.e., the resource T uses that S doesn't have. *)

Inductive LeOk : Set := le_ok : LeOk.

(** Find any ASubBot leaf in S (used when T = ASubTop and we must verify S
    selects all leaves). *)
Ltac find_bot_leaf S tm := lazymatch S with
  | ASubTop _ => constr:(le_ok)
  | ASubBot _ => tm
  | ASubProdT ?S₁ ?S₂ =>
      let r := find_bot_leaf S₁ constr:(proj1 tm) in
      lazymatch r with le_ok => find_bot_leaf S₂ constr:(proj2 tm) | _ => r end
  | ASubProdC ?S₁ ?S₂ =>
      let r := find_bot_leaf S₁ constr:(proj1 tm) in
      lazymatch r with le_ok => find_bot_leaf S₂ constr:(proj2 tm) | _ => r end
  end.

(** Find any ASubTop leaf in T (used when S = ASubBot and T uses something). *)
Ltac find_top_leaf T tm := lazymatch T with
  | ASubBot _ => constr:(le_ok)
  | ASubTop _ => tm
  | ASubProdT ?T₁ ?T₂ =>
      let r := find_top_leaf T₁ constr:(proj1 tm) in
      lazymatch r with le_ok => find_top_leaf T₂ constr:(proj2 tm) | _ => r end
  | ASubProdC ?T₁ ?T₂ =>
      let r := find_top_leaf T₁ constr:(proj1 tm) in
      lazymatch r with le_ok => find_top_leaf T₂ constr:(proj2 tm) | _ => r end
  end.

(** Lockstep walk of [S, T] looking for a leaf where T = top but S = bot. *)
Ltac find_violation S T tm := lazymatch T with
  | ASubBot _ => constr:(le_ok)
  | ASubTop _ => find_bot_leaf S tm
  | ASubProdT ?T₁ ?T₂ => lazymatch S with
      | ASubTop _ => constr:(le_ok)
      | ASubBot _ => find_top_leaf T tm
      | ASubProdT ?S₁ ?S₂ =>
          let r := find_violation S₁ T₁ constr:(proj1 tm) in
          lazymatch r with le_ok => find_violation S₂ T₂ constr:(proj2 tm) | _ => r end
      end
  | ASubProdC ?T₁ ?T₂ => lazymatch S with
      | ASubTop _ => constr:(le_ok)
      | ASubBot _ => find_top_leaf T tm
      | ASubProdC ?S₁ ?S₂ =>
          let r := find_violation S₁ T₁ constr:(proj1 tm) in
          lazymatch r with le_ok => find_violation S₂ T₂ constr:(proj2 tm) | _ => r end
      end
  end.

(** Spine walk: check T ≤ S across all variables in Γ. *)
Ltac find_violation_Γ S T := lazymatch S with
  | ASubEmpty => constr:(le_ok)
  | ASubCons ?S' _ ?S_var => lazymatch T with ASubCons ?T' ?x ?T_var =>
      let r := find_violation_Γ S' T' in
      lazymatch r with
      | le_ok => find_violation S_var T_var x
      | _     => r
      end
    end
  end.

(** F_Γ_mor with linearity check: returns the SMor if T ≤ S, else
    [nonlinear_var_use chain] where [chain] pinpoints the offending resource. *)
Ltac F_Γ_mor_checked S T :=
  let r := find_violation_Γ S T in
  lazymatch r with
  | le_ok => F_Γ_mor S T
  | _     => constr:(nonlinear_var_use r)
  end.

(** Test: T ≤ S — F_Γ_mor_checked succeeds with an SMor.
    Γ = ε ;; x ⦂ [X] ;; y ⦂ [Y]⊗[Z]; S uses everything, T uses only x. *)
Definition test_check_ok (X Y Z : set) (x : X) (y : set_T (Y ⊗ Z))
  : SMor (AProdT (AAtom X) (AProdT (AAtom Y) (AAtom Z))) (AAtom X)
  := ltac:(
       let A_y := constr:(AProdT (AAtom Y) (AAtom Z)) in
       let S := constr:(ASubCons (ASubCons ASubEmpty x (ASubTop (AAtom X))) y
                          (ASubTop A_y)) in
       let T := constr:(ASubCons (ASubCons ASubEmpty x (ASubTop (AAtom X))) y
                          (ASubBot A_y)) in
       let r := F_Γ_mor_checked S T in exact r
     ).

(** Test: whole-variable violation — T uses y, S has nothing at y's slot.
    Expected: nonlinear_var_use y. *)
Definition test_check_var_violation (X Y Z : set) (x : X) (y : set_T (Y ⊗ Z))
  : Excn
  := ltac:(
       let A_y := constr:(AProdT (AAtom Y) (AAtom Z)) in
       let S := constr:(ASubCons (ASubCons ASubEmpty x (ASubTop (AAtom X))) y
                          (ASubBot A_y)) in
       let T := constr:(ASubCons (ASubCons ASubEmpty x (ASubTop (AAtom X))) y
                          (ASubTop A_y)) in
       let r := F_Γ_mor_checked S T in
       let _ := match goal with _ => constr_eq r constr:(nonlinear_var_use y) end in
       exact r
     ).

(** Test: leaf-level violation — T uses everything, S has only the left half of y.
    Expected: nonlinear_var_use (proj2 y). *)
Definition test_check_leaf_violation (X Y Z : set) (x : X) (y : set_T (Y ⊗ Z))
  : Excn
  := ltac:(
       let A_y := constr:(AProdT (AAtom Y) (AAtom Z)) in
       let S := constr:(ASubCons (ASubCons ASubEmpty x (ASubTop (AAtom X))) y
                          (ASubProdT (ASubTop (AAtom Y)) (ASubBot (AAtom Z)))) in
       let T := constr:(ASubCons (ASubCons ASubEmpty x (ASubTop (AAtom X))) y
                          (ASubTop A_y)) in
       let r := F_Γ_mor_checked S T in
       let _ := match goal with _ => constr_eq r constr:(nonlinear_var_use (proj2 y)) end in
       exact r
     ).


(** Residue machinery: F_A_split S T produces SplitMor A_S A_T A_U
    where U is the maximal residue. *)

Inductive SplitMor@{u} `(A:AShape@{u} X) `(B:AShape@{u} Y) `(C:AShape@{u} Z) :=
| splitmor : (X ⇾ Y ⊗ Z) → SplitMor A B C.

Definition exchange@{u} {A B C D : set@{u}}
  : ((A ⊗ B) ⊗ (C ⊗ D)) ⇾ ((A ⊗ C) ⊗ (B ⊗ D))
  := α ∘ ⟨tensor_swap_tail _ _ _, id_fun _⟩ ∘ α⁻¹.

(** Unitor that combines ⟦A⟧ ⊗ ⟦B⟧ → ⟦aprodt A B⟧, dispatching on AUnit. *)
Ltac unitor_combine_t A B :=
  lazymatch type of A with AShape ?X =>
  lazymatch type of B with AShape ?Y =>
    lazymatch constr:((A, B)) with
    | (AUnit, AUnit) => constr:(tensor_unit_r 𝟏)
    | (AUnit, _)     => constr:(tensor_unit_l Y)
    | (_, AUnit)     => constr:(tensor_unit_r X)
    | (_, _)         => constr:(id_fun (X ⊗ Y))
    end
  end end.

(** Smart combine for SplitMor over ⊗-recursion. *)
Ltac aprodt_split r₁ r₂ :=
  lazymatch r₁ with @splitmor ?X₁ ?A₁ ?Y₁ ?B₁ ?Z₁ ?C₁ ?m₁ =>
  lazymatch r₂ with @splitmor ?X₂ ?A₂ ?Y₂ ?B₂ ?Z₂ ?C₂ ?m₂ =>
    lazymatch A₁ with
    | AUnit => constr:( splitmor A₂ B₂ C₂ m₂ )
    | _ => lazymatch A₂ with
      | AUnit => constr:( splitmor A₁ B₁ C₁ m₁ )
      | _ =>
        let B := aprodt B₁ B₂ in
        let C := aprodt C₁ C₂ in
        let elideB := unitor_combine_t B₁ B₂ in
        let elideC := unitor_combine_t C₁ C₂ in
        let raw := tmap m₁ m₂ in
        let elide_tmap := tmap elideB elideC in
        let exch := constr:(@exchange Y₁ Z₁ Y₂ Z₂) in
        let inner := comp exch raw in
        let m := comp elide_tmap inner in
        constr:( splitmor (AProdT A₁ A₂) B C m )
      end
    end
  end end.

(** Walk an AShape tree to compute its maximal residue.
    AAtom: residue AUnit. IAtom: residue itself, morphism Δ.
    AProdT: combine children. AProdC: residue AUnit (commit-to-branch). *)
Ltac asplit_all A := lazymatch A with
| AUnit =>
    constr:( splitmor AUnit AUnit AUnit (inverse (tensor_unit_r 𝟏)) )
| @AAtom ?X =>
    constr:( splitmor (AAtom X) (AAtom X) AUnit (inverse (tensor_unit_r X)) )
| @IAtom ?X ?Δ =>
    constr:( splitmor (IAtom X Δ) (IAtom X Δ) (IAtom X Δ) Δ )
| AProdT ?A₁ ?A₂ =>
    let r₁ := asplit_all A₁ in
    let r₂ := asplit_all A₂ in
    aprodt_split r₁ r₂
| @AProdC ?X ?Y ?A₁ ?A₂ =>
    constr:( splitmor (AProdC A₁ A₂) (AProdC A₁ A₂) AUnit
                      (inverse (tensor_unit_r (X × Y))) )
end.

(** F_A_split with S = ⊤ A: recurse on T's structure. *)
Ltac realize_shape_split T := lazymatch T with
| ASubTop ?A => asplit_all A
| @ASubBot ?X ?A => constr:( splitmor A AUnit A (inverse (tensor_unit_l X)) )
| ASubProdT ?T₁ ?T₂ =>
    let r₁ := realize_shape_split T₁ in
    let r₂ := realize_shape_split T₂ in
    aprodt_split r₁ r₂
| @ASubProdC ?X₁ ?X₂ ?A₁ ?A₂ ?T₁ ?T₂ =>
    lazymatch T₁ with
    | ASubBot _ =>
        let r₂ := realize_shape_split T₂ in
        lazymatch r₂ with @splitmor _ _ _ ?B₂ _ ?C₂ ?m₂ =>
          let m := comp m₂ constr:(prod_proj2 X₁ X₂) in
          constr:( splitmor (AProdC A₁ A₂) B₂ C₂ m )
        end
    | _ => lazymatch T₂ with
      | ASubBot _ =>
        let r₁ := realize_shape_split T₁ in
        lazymatch r₁ with @splitmor _ _ _ ?B₁ _ ?C₁ ?m₁ =>
          let m := comp m₁ constr:(prod_proj1 X₁ X₂) in
          constr:( splitmor (AProdC A₁ A₂) B₁ C₁ m )
        end
      | _ =>
        let r₁ := realize_shape_mor T₁ in
        let r₂ := realize_shape_mor T₂ in
        lazymatch r₁ with @smor _ _ _ ?B₁ ?m₁ =>
        lazymatch r₂ with @smor _ _ _ ?B₂ ?m₂ =>
          let m_cart := pmap m₁ m₂ in
          let m := constr:(uᵣ⁻¹ ∘ m_cart) in
          constr:( splitmor (AProdC A₁ A₂) (AProdC B₁ B₂) AUnit m )
        end end
      end
    end
end.

(** F_A_split: full residue functor on Sub(A) morphisms. *)
Ltac F_A_split S T := lazymatch T with
| ASubBot _ =>
    let A_S := realize_shape S in
    let X_S := lazymatch type of A_S with AShape ?X => X end in
    constr:( splitmor A_S AUnit A_S (inverse (tensor_unit_l X_S)) )
| _ => lazymatch S with
  | ASubTop _ => realize_shape_split T
  | ASubProdT ?S₁ ?S₂ => lazymatch T with ASubProdT ?T₁ ?T₂ =>
      let r₁ := F_A_split S₁ T₁ in
      let r₂ := F_A_split S₂ T₂ in
      aprodt_split r₁ r₂
    end
  | ASubProdC ?S₁ ?S₂ =>
    lazymatch T with ASubProdC ?T₁ ?T₂ =>
      lazymatch S₁ with
      | ASubBot _ => F_A_split S₂ T₂
      | _ => lazymatch S₂ with
        | ASubBot _ => F_A_split S₁ T₁
        | _ =>
          lazymatch T₁ with
          | ASubBot _ =>
            let r₂ := F_A_split S₂ T₂ in
            lazymatch r₂ with @splitmor ?X_S₂ ?A_real_S₂ _ ?B₂ _ ?C₂ ?m₂ =>
              let A_real_S₁ := realize_shape S₁ in
              let X_S₁ := lazymatch type of A_real_S₁ with AShape ?X => X end in
              let m := comp m₂ constr:(prod_proj2 X_S₁ X_S₂) in
              constr:( splitmor (AProdC A_real_S₁ A_real_S₂) B₂ C₂ m )
            end
          | _ => lazymatch T₂ with
            | ASubBot _ =>
              let r₁ := F_A_split S₁ T₁ in
              lazymatch r₁ with @splitmor ?X_S₁ ?A_real_S₁ _ ?B₁ _ ?C₁ ?m₁ =>
                let A_real_S₂ := realize_shape S₂ in
                let X_S₂ := lazymatch type of A_real_S₂ with AShape ?X => X end in
                let m := comp m₁ constr:(prod_proj1 X_S₁ X_S₂) in
                constr:( splitmor (AProdC A_real_S₁ A_real_S₂) B₁ C₁ m )
              end
            | _ =>
              let r₁ := F_A_mor S₁ T₁ in
              let r₂ := F_A_mor S₂ T₂ in
              lazymatch r₁ with @smor _ ?A_real_S₁ _ ?B₁ ?m₁ =>
              lazymatch r₂ with @smor _ ?A_real_S₂ _ ?B₂ ?m₂ =>
                let m_cart := pmap m₁ m₂ in
                let m := constr:(uᵣ⁻¹ ∘ m_cart) in
                constr:( splitmor (AProdC A_real_S₁ A_real_S₂) (AProdC B₁ B₂) AUnit m )
              end end
            end
          end
        end
      end
    end
  end
end.

(** F_Γ_split: residue functor on Sub(Γ) morphisms.
    Given S, T ∈ ASubCtx(Γ) with T ≤ S, produces SplitMor (Γ_S) (Γ_T) (Γ_U). *)
Ltac F_Γ_split S T := lazymatch S with
| ASubEmpty => constr:( splitmor AUnit AUnit AUnit (inverse (tensor_unit_r 𝟏)) )
| ASubCons ?S' _ ?SubA_S => lazymatch T with ASubCons ?T' _ ?SubA_T =>
    let r_prefix := F_Γ_split S' T' in
    let r_var := F_A_split SubA_S SubA_T in
    aprodt_split r_prefix r_var
  end
end.


Ltac asubprodt U₁ U₂ :=
  let U := constr:(ASubProdT U₁ U₂) in lazymatch U with
  | ASubProdT (ASubTop ?A₁) (ASubTop ?A₂) => constr:(ASubTop (AProdT A₁ A₂))
  | ASubProdT (ASubBot ?A₁) (ASubBot ?A₂) => constr:(ASubBot (AProdT A₁ A₂))
  | _ => U
  end.

Ltac asubprodc U₁ U₂ :=
  let U := constr:(ASubProdC U₁ U₂) in lazymatch U with
  | ASubProdC (ASubTop ?A₁) (ASubTop ?A₂) => constr:(ASubTop (AProdC A₁ A₂))
  | ASubProdC (ASubBot ?A₁) (ASubBot ?A₂) => constr:(ASubBot (AProdC A₁ A₂))
  | _ => U
  end.

Ltac asub_union S T := lazymatch S with
| ASubTop _ => S
| ASubBot _ => T
| _ => lazymatch T with
  | ASubTop _ => T
  | ASubBot _ => S
  | ASubProdT ?T₁ ?T₂ => lazymatch S with ASubProdT ?S₁ ?S₂ =>
      let U₁ := asub_union S₁ T₁ in let U₂ := asub_union S₂ T₂ in asubprodt U₁ U₂
    end
  | ASubProdC ?T₁ ?T₂ => lazymatch S with ASubProdC ?S₁ ?S₂ =>
      let U₁ := asub_union S₁ T₁ in let U₂ := asub_union S₂ T₂ in asubprodc U₁ U₂
    end
  end
end.


Ltac asubctx_empty Γ := lazymatch Γ with
| AEmpty => ASubEmpty
| @ACons ?Γ' _ ?A ?x =>
  let T := asubctx_empty Γ' in
  constr:(ASubCons T x (ASubBot A))
end.


Ltac asubctx_union T₁ T₂ := lazymatch T₁ with
| ASubEmpty => T₁
| ASubCons (X:=?X) ?T₁' ?x ?S₁ =>
  lazymatch T₂ with ASubCons ?T₂' _ ?S₂ =>
    let T := asubctx_union T₁' T₂' in
    let S := asub_union S₁ S₂ in
    constr:(ASubCons (X:=X) T x S)
  end
end.


(** Residue at the AShape level after using T from S = ASubTop A.
    Mirrors asplit_all's residue rules at the ASubShape level:
    AAtom consumed, IAtom preserved, AProdC commits, AProdT recurses.
    [T = ASubBot] is filtered first so unused branches keep their full residue. *)
Ltac asplit_residue A T := lazymatch T with
| ASubBot _ => constr:(ASubTop A)
| _ => lazymatch A with
  | AUnit => constr:(ASubTop AUnit)
  | @AAtom ?X => constr:(ASubBot (AAtom X))
  | @IAtom ?X ?Δ => constr:(ASubTop (IAtom X Δ))
  | AProdT ?A₁ ?A₂ => lazymatch T with
      | ASubTop _ =>
          let r₁ := asplit_residue A₁ (ASubTop A₁) in
          let r₂ := asplit_residue A₂ (ASubTop A₂) in
          asubprodt r₁ r₂
      | ASubProdT ?T₁ ?T₂ =>
          let r₁ := asplit_residue A₁ T₁ in
          let r₂ := asplit_residue A₂ T₂ in
          asubprodt r₁ r₂
      end
  | AProdC ?A₁ ?A₂ => constr:(ASubBot (AProdC A₁ A₂))
  end
end.

(** Residue at the ASubShape level: mirrors F_A_split's rules. *)
Ltac asub_residue_subshape S T := lazymatch T with
| ASubBot _ => S
| _ => lazymatch S with
  | ASubTop ?A => asplit_residue A T
  | ASubProdT ?S₁ ?S₂ => lazymatch T with
      | ASubTop ?A => lazymatch A with AProdT ?A₁ ?A₂ =>
          let r₁ := asub_residue_subshape S₁ (ASubTop A₁) in
          let r₂ := asub_residue_subshape S₂ (ASubTop A₂) in
          asubprodt r₁ r₂
        end
      | ASubProdT ?T₁ ?T₂ =>
          let r₁ := asub_residue_subshape S₁ T₁ in
          let r₂ := asub_residue_subshape S₂ T₂ in
          asubprodt r₁ r₂
      end
  | ASubProdC _ _ =>
      let A := lazymatch type of S with ASubShape ?A => A end in
      constr:(ASubBot A)
  end
end.

(** Residue ASubCtx after using T from S, walking the spine of Γ. *)
Ltac asubctx_residue S T := lazymatch S with
| ASubEmpty => constr:(ASubEmpty)
| ASubCons (X:=?X) ?S' ?x ?S_var =>
    lazymatch T with ASubCons ?T' _ ?T_var =>
      let r' := asubctx_residue S' T' in
      let r := asub_residue_subshape S_var T_var in
      constr:(ASubCons (X:=X) r' x r)
    end
end.


Ltac var_shape Γ var := lazymatch Γ with
| AEmpty => constr:(var_not_found)
| ACons _ ?A var => A
| ACons ?Γ' _ _ => var_shape Γ' var
end.

Ltac resource_shape Γ tm := lazymatch tm with
| proj1 ?p => let res := resource_shape Γ p in lazymatch res with
  | var_not_found => constr:(var_not_found)
  | AProdT ?A _ => A
  | AProdC ?A _ => A
  | _ => constr:(unexpected_projection)
  end
| proj2 ?p => let res := resource_shape Γ p in lazymatch res with
  | var_not_found => constr:(var_not_found)
  | AProdT _ ?A => A
  | AProdC _ ?A => A
  | _ => constr:(unexpected_projection)
  end
| _ => var_shape Γ tm
end.


Ltac lookup_alias ρ tm :=
  lazymatch ρ with
  | AliasEmpty => constr:(var_not_found)
  | AliasCons _ _ tm ?rhs => rhs
  | AliasCons ?ρ' _ _ _ => lookup_alias ρ' tm
  end.

Ltac expand_alias Γ ρ tm :=
  lazymatch tm with
  | proj1 ?p => let res := expand_alias Γ ρ p in lazymatch res with
    | var_not_found => constr:(var_not_found)
    | (AProdT ?A _, ?tm') => constr:( (A, proj1 tm') )
    | (AProdC ?A _, ?tm') => constr:( (A, proj1 tm') )
    | _ => constr:(unexpected_projection)
    end
  | proj2 ?p => let res := expand_alias Γ ρ p in lazymatch res with
    | var_not_found => constr:(var_not_found)
    | (AProdT _ ?A, ?tm') => constr:( (A, proj2 tm') )
    | (AProdC _ ?A, ?tm') => constr:( (A, proj2 tm') )
    | _ => constr:(unexpected_projection)
    end
  | _ => let tm' := lookup_alias ρ tm in lazymatch tm' with
    | var_not_found => let res := var_shape Γ tm in lazymatch res with
      | var_not_found => res
      | _ => constr:( (res, tm) )
      end
    | _ => let res := resource_shape Γ tm' in lazymatch res with
      | var_not_found => res
      | unexpected_projection => res
      | _ => constr:( (res, tm') )
      end
    end
  end.

(** Peel projections off [tm], returning a pair [(root, path)] where [root] is
    [tm] with all leading projections stripped and [path] is a nested pair
    encoding the projection chain. Outer projections of [tm] (= deeper
    descents) become the inner of the accumulator, so reading [path]
    head-first gives the path from [root]: [(true, _)] = "go left",
    [(false, _)] = "go right". Call with [acc = tt]. *)
Ltac proj_path_acc tm acc :=
  lazymatch tm with
  | proj1 ?p => proj_path_acc p (true, acc)
  | proj2 ?p => proj_path_acc p (false, acc)
  | _        => constr:((tm, acc))
  end.

Ltac alias_proj_path_acc ρ tm acc :=
  lazymatch tm with
  | proj1 ?p => alias_proj_path_acc ρ p (true, acc)
  | proj2 ?p => alias_proj_path_acc ρ p (false, acc)
  | _ => let res := lookup_alias ρ tm in
    lazymatch res with
    | var_not_found => constr:((tm, acc))
    | _ => proj_path_acc res acc
    end 
  end.

(** Walk down [A] guided by [path], placing [ASubTop] at the leaf reached and
    [ASubBot] elsewhere. *)
Ltac descend_subshape A path :=
  lazymatch path with
  | tt => constr:(ASubTop A)
  | (true, ?rest) => lazymatch A with
      | AProdT ?A₁ ?A₂ => let S := descend_subshape A₁ rest in constr:(ASubProdT S (ASubBot A₂))
      | AProdC ?A₁ ?A₂ => let S := descend_subshape A₁ rest in constr:(ASubProdC S (ASubBot A₂))
      end
  | (false, ?rest) => lazymatch A with
      | AProdT ?A₁ ?A₂ => let S := descend_subshape A₂ rest in constr:(ASubProdT (ASubBot A₁) S)
      | AProdC ?A₁ ?A₂ => let S := descend_subshape A₂ rest in constr:(ASubProdC (ASubBot A₁) S)
      end
  end.

(* TODO: switch to Coerce typeclass *)
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

(** Walk Γ from the most-recent variable inward, looking for one whose value
    is [x]. Slots before the match get [ASubBot]; the matched slot gets the
    refined subshape from [descend_subshape A path]. Returns [var_not_found]
    if no slot matches. *)
Ltac interpret_var_aux Γ tm x path :=
  lazymatch Γ with
  | AEmpty => constr:(var_not_found)
  | @ACons ?Γ' _ ?A x =>
    let S := descend_subshape A path in
    let A_S := realize_shape S in
    let D := lazymatch type of A_S with AShape ?D => D end in
    let T' := asubctx_empty Γ' in
    let T := constr:(ASubCons T' x S) in
    constr:(judgment T D D (id_fun D) tm)
  | @ACons ?Γ' _ ?A ?y =>
    let res := interpret_var_aux Γ' tm x path in lazymatch res with
    | @judgment _ ?T ?D ?X ?m ?tm' =>
        let T' := constr:(ASubCons T y (ASubBot A)) in
        constr:(@judgment _ T' D X m tm')
    | _ => res
    end
  end.

(** Variable look-up: succeeds with a [Judgment] when [tm] is a variable in
    [Γ] or a chain-of-projections of one; returns [var_not_found] otherwise.
    The [bias] is the call site's expected Gallina type — typically [set_T Y]
    for some target set [Y]; if it doesn't match the variable's natural type,
    [build_coercion] inserts a structural coercion. A non-[set_T] [bias] is
    treated as no bias. *)
Ltac interpret_var Γ ρ bias tm :=
  let rp := alias_proj_path_acc ρ tm tt in lazymatch rp with (?r, ?path) =>
    let j := interpret_var_aux Γ tm r path in lazymatch j with
    | @judgment _ ?T ?D ?X ?m ?tm' =>
        lazymatch bias with
        | set_T X => j
        | set_T ?Y => let c := build_coercion X Y in
            constr:(@judgment _ T D _ (c ∘ m) tm')
        | _ => j
        end
    | _ => j
    end
  end.

(*
Definition test_iv_var (X:set) (x:X) : Judgment (ASubCons ASubEmpty x (ASubTop (AAtom X))) X X
  := ltac:( let Γ := constr:(ACons AEmpty (AAtom X) x) in
            let res := interpret_var Γ (set_T X) x in exact res ).

Definition test_iv_proj (X Y Z:set) (x : X) (y : set_T (Y ⊗ Z))
  : Judgment (ASubCons (ASubCons ASubEmpty x (ASubBot (AAtom X))) y
                       (ASubProdT (ASubBot (AAtom Y)) (ASubTop (AAtom Z)))) Z Z
  := ltac:( let Γ := constr:(ACons (ACons AEmpty (AAtom X) x)
                                   (AProdT (AAtom Y) (AAtom Z)) y) in
            let res := interpret_var Γ (set_T Z) constr:(π₂ y) in exact res ).
*)



(** Abstraction *)


(** Classify a [set] [X] as tensor [_ ⊗ _], cartesian [_ × _], or atomic, and
    build the corresponding [AShape X]. Recurses on the components. The
    convertibility probe uses [eq_refl (_ ⊗ _) : _ ≡ X] (and similarly for
    [×]): unification against the equality forces the tested shape, but only
    succeeds if [X] is convertible to it — so aliases unfolding to a product
    are seen through, while a syntactic [lazymatch X with ?A ⊗ ?B => ...] would
    miss them. At atoms, dispatch between [AAtom] and [IAtom] based on whether
    [X] has an [AffirmativeEquality] instance (which supplies the diagonal
    via [tensor_diag]). *)
Ltac ashape_from_set X :=
  let probe := match goal with
  | _ => constr:(eq_refl (_ ⊗ _) : _ ≡ X)
  | _ => constr:(eq_refl (_ × _) : _ ≡ X)
  | _ => constr:(eq_refl X)
  end in
  lazymatch probe with
  | eq_refl (?X₁ ⊗ ?X₂) =>
      let A := ashape_from_set X₁ in
      let B := ashape_from_set X₂ in
      constr:(AProdT A B)
  | eq_refl (?X₁ × ?X₂) =>
      let A := ashape_from_set X₁ in
      let B := ashape_from_set X₂ in
      constr:(AProdC A B)
  | _ =>
      let H := match goal with
      | _ => get_instance (AffirmativeEquality X)
      | _ => constr:(false)
      end in
      lazymatch H with
      | false => constr:(AAtom X)
      | _     => constr:(IAtom X (@tensor_diag X H))
      end
  end.

(** Entry point: deduce an [AShape A] for a Gallina type [T = set_T X] up to
    convertibility. Pulls [X] out of [T] via the same [eq_refl] convertibility
    trick, then defers to [ashape_from_set]. Returns sentinel [type_not_a_set]
    if [T] is not convertible to [set_T _]. *)
Ltac ashape_from_type T :=
  let X_pkg := match goal with
  | _ => constr:( eq_refl (set_T _) : _ ≡ T )
  | _ => constr:( type_not_a_set )
  end in
  lazymatch X_pkg with
  | eq_refl (set_T ?X) => ashape_from_set X
  | _ => constr:(type_not_a_set)
  end.

Definition test_ashape_atom (X:set) : AShape X
  := ltac:( let A := ashape_from_type (set_T X) in exact A ).

Definition test_ashape_iatom (X:set) `{!AffirmativeEquality X} : AShape X
  := ltac:( let A := ashape_from_type (set_T X) in exact A ).

Definition test_ashape_tensor (X Y:set) : AShape (X ⊗ Y)
  := ltac:( let A := ashape_from_type (set_T (X ⊗ Y)) in exact A ).

Definition test_ashape_cart (X Y:set) : AShape (X × Y)
  := ltac:( let A := ashape_from_type (set_T (X × Y)) in exact A ).

Definition test_ashape_nested (X Y Z:set) : AShape ((X ⊗ !Y) × Z)
  := ltac:( let A := ashape_from_type (set_T ((X ⊗ !Y) × Z)) in exact A ).

Record JudgmentAbsInner@{u}
  `(T:ASubCtx@{u} Γ) (D X Y:set@{u}) := judgment_abs_inner
{ judgment_abs_inner_mor : D ⇾ (X ⇾ Y)
; judgment_abs_inner_tm  : Y
}.
Arguments judgment_abs_inner {Γ} T D X Y _ _.

(** Interpret λ var:T, body in context Γ against a result-type [bias]. *)
Ltac interpret_abs_inner interpret Γ ρ bias T var body :=
  let A := ashape_from_type T in
  let X := lazymatch type of A with AShape ?X => X end in
  let Γ' := constr:(ACons Γ A var) in
  let j := interpret Γ' ρ bias body in
  lazymatch j with
  | @judgment _ ?T' _ ?Y ?m ?tm' =>
      lazymatch T' with ASubCons ?T_for_Γ _ _ =>
        let U' := constr:(ASubCons T_for_Γ var (ASubTop A)) in
        let F := F_Γ_mor U' T' in
        let mF := lazymatch F with @smor _ _ _ _ ?mF => mF end in
        let A_T := realize_ctx_shape T_for_Γ in
        let DΓ := lazymatch type of A_T with AShape ?D => D end in
        let m_lifted := comp m mF in
        let m' := lazymatch A_T with
          | AUnit => comp m_lifted constr:(tensor_unit_l X)
          | _     => m_lifted
          end in
        exact (judgment_abs_inner T_for_Γ DΓ X Y (curry m') tm')
      end
  | _ => exact j
  end.

(** A stub [interpret] for tests: only handles the [var-or-projection-chain] case.
    Real [interpret] will dispatch on syntax of [tm]. *)
Ltac interpret_stub Γ ρ bias tm := interpret_var Γ ρ bias tm.

(** Test: λ x:X, x  in empty context, expecting set_T (X ⇾ X).
    Should produce judgment_abs_inner ASubEmpty 𝟏 X X (curry (id ∘ uₗ)) x. *)
Definition test_abs_id (X:set) (x:X)
  : JudgmentAbsInner ASubEmpty 𝟏 X X
  := ltac:(
      interpret_abs_inner interpret_stub
                    constr:(AEmpty) constr:(AliasEmpty) constr:(set_T X) constr:(set_T X) x
                    constr:(x : set_T X)
     ).

(** Test: λ p:X⊗Y, π₂ p  in empty context.
    Exercises a nontrivial binder shape (AProdT) plus a projection in the body. *)
Definition test_abs_proj (X Y:set) (p : set_T (X ⊗ Y))
  : JudgmentAbsInner ASubEmpty 𝟏 (X ⊗ Y) Y
  := ltac:(
      interpret_abs_inner interpret_stub
                    constr:(AEmpty) constr:(AliasEmpty) constr:(set_T Y)
                    constr:(set_T (X ⊗ Y)) p
                    constr:(π₂ p)
     ).

(** Test: λ y:Y, x  in context (x:X) — body uses Γ, not the binder.
    Exercises a non-AUnit ⟦Γ_T⟧ (so the peel is identity rather than uₗ),
    and the recursive case in interpret_var_aux that walks past the binder. *)
Definition test_abs_const_ctx (X Y:set) (x:X) (y:Y)
  : JudgmentAbsInner (ASubCons ASubEmpty x (ASubTop (AAtom X))) X Y X
  := ltac:(
       interpret_abs_inner interpret_stub
                    constr:(ACons AEmpty (AAtom X) x) constr:(AliasEmpty) constr:(set_T X)
                    constr:(set_T Y) y
                    constr:(x : set_T X) 
     ).


Ltac unwrap_abs_inner Γ binder res :=
  lazymatch res with
  | λ var, judgment_abs_inner ?T ?D ?X ?Y ?m ?body' =>
    let f := constr:(λ binder : X, match binder with var => body' end) in
    let smr := realize_ctx_shape_mor T in
    let r := lazymatch smr with @smor _ _ _ _ ?g => g end in
    let env := reify_ctx Γ in
    let tm' := constr:(@set_lambda X Y f (func_is_fun ((m ∘ r) env))) in
    constr:(judgment T D (X ⇾ Y) m tm')
  | _ => res
  end.


Ltac interpret_abs interpret Γ ρ bias tm :=
  let body_bias := lazymatch bias with _ → ?T => T end in
  lazymatch tm with λ binder : ?T, ?body =>
    let res := eval_under_binder ltac:(interpret_abs_inner interpret Γ ρ body_bias T) binder T body in
    unwrap_abs_inner Γ binder res
    (*lazymatch res with
    | λ var, judgment_abs_inner ?T ?D ?X ?Y ?m ?body' =>
      let f := constr:(λ binder : X, match binder with var => body' end) in
      let smr := realize_ctx_shape_mor T in
      let r := lazymatch smr with @smor _ _ _ _ ?g => g end in
      let env := reify_ctx Γ in
      let tm' := constr:(@set_lambda X Y f (func_is_fun ((m ∘ r) env))) in
      constr:(judgment T D (X ⇾ Y) m tm')
    | _ => res
    end*)
  end.

(** Test interpret_abs: λ x:X, x  in empty context.
    Top-level entry point given a Gallina lambda; should produce a Judgment
    over ASubEmpty with codomain set X ⇾ X. *)
Definition test_iabs_id (X:set)
  : Judgment ASubEmpty 𝟏 (X ⇾ X)
  := ltac:(
       let res := interpret_abs interpret_stub
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T X → set_T X)
                    constr:(λ x : X, x) in
       exact res
     ).

(** Test: λ p:X⊗Y, π₂ p — nontrivial binder shape and a projection in body. *)
Definition test_iabs_proj (X Y:set)
  : Judgment ASubEmpty 𝟏 (X ⊗ Y ⇾ Y)
  := ltac:(
       let res := interpret_abs interpret_stub
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T (X ⊗ Y) → set_T Y)
                    constr:(λ p : X ⊗ Y, π₂ p) in
       exact res
     ).

(** Test: λ y:Y, x  in context (x:X) — body uses Γ, not the binder. *)
Definition test_iabs_const_ctx (X Y:set) (x:X)
  : Judgment (ASubCons ASubEmpty x (ASubTop (AAtom X))) X (Y ⇾ X)
  := ltac:(
       let res := interpret_abs interpret_stub
                    constr:(ACons AEmpty (AAtom X) x) constr:(AliasEmpty)
                    constr:(set_T Y → set_T X)
                    constr:(λ y : Y, x) in
       exact res
     ).


Ltac interpret_subset_comprehension interpret Γ ρ X f :=
  let res := interpret_abs interpret Γ ρ constr:(set_T X → set_T AProp_set) f in
  lazymatch res with
  | judgment _ _ _ _ _ =>
    lazymatch res with ?j (?X ⇾ _) ?m (@set_lambda ?X _ ?f' ?H) =>
      constr:( j (𝒫 X) m (@subset_comprehension X f' H) )
    end
  | _ => res
  end.


(** Pairs *)

Inductive PairBias : Set := NoPairBias | TensorBias | CartesianBias.

Ltac interpret_pair_aux j₁ j₂ b :=
  lazymatch j₁ with
  | judgment ?T₁ ?D₁ ?X₁ ?m₁ ?tm₁ =>
    lazymatch j₂ with
    | judgment ?T₂ ?D₂ ?X₂ ?m₂ ?tm₂ =>
      let tm := constr:((tm₁, tm₂)) in
      let T := asubctx_union T₁ T₂ in
      let cart b := (* b is a dummy arg *)
        let sm₁ := F_Γ_mor T T₁ in let f₁ := lazymatch sm₁ with smor _ _ ?f => f end in
        let sm₂ := F_Γ_mor T T₂ in let f₂ := lazymatch sm₂ with smor _ _ ?f => f end in
        let m₁' := comp m₁ f₁ in let m₂' := comp m₂ f₂ in
        constr:(judgment T _ (X₁ × X₂) (to_prod (m₁', m₂')) tm)
      in lazymatch b with
      | CartesianBias => cart b
      | _ =>
        let U := asubctx_residue T T₁ in
        let sm₂ := F_Γ_mor_checked U T₂ in lazymatch sm₂ with
        | smor _ _ ?g =>
            let res := F_Γ_split T T₁ in lazymatch res with splitmor _ _ _ ?f =>
              let m₂' := comp m₂ g in
              let m' := tmap m₁ m₂' in
              let m := comp m' f in
              constr:(judgment T _ (X₁ ⊗ X₂) m tm)
            end
        | _ => lazymatch b with
          | TensorBias => sm₂
          | _ => cart b
          end
        end
      end
    | _ => j₂
    end
  | _ => j₁
  end.


Ltac split_bias bias :=
  lazymatch bias with
  | tprod ?A ?B => constr:( (A, B) )
  | set_T ?X =>
    let t := match goal with
    | _ => constr:(eq_refl (_ ⊗ _) : _ ≡ X)
    | _ => constr:(eq_refl (_ × _) : _ ≡ X)
    end in lazymatch t with
    | eq_refl (?X₁ ⊗ ?X₂) => constr:( (set_T X₁, set_T X₂) )
    | eq_refl (?X₁ × ?X₂) => constr:( (set_T X₁, set_T X₂) )
    end
  end.

Ltac interpret_pair interpret Γ ρ bias tm := lazymatch tm with (?tm₁, ?tm₂) =>
  let res := split_bias bias in lazymatch res with (?bias₁, ?bias₂) =>
    let j₁ := interpret Γ ρ bias₁ tm₁ in
    let j₂ := interpret Γ ρ bias₂ tm₂ in
    lazymatch bias with
    | set_T (_ ⊗ _) => interpret_pair_aux j₁ j₂ constr:(TensorBias)
    | set_T (_ × _) => interpret_pair_aux j₁ j₂ constr:(CartesianBias)
    | _ => interpret_pair_aux j₁ j₂ constr:(NoPairBias)
    end
  end
end.



(** Application *)

Definition strong_eval@{u} (X Y : set@{u}) `{!StrongSet Y} : (X ⇾ Y) × X ⇾ Y := strong_op eval.

Lemma strong_eval_op_is_fun@{u} (X₁ X₂ Y : set@{u}) `{!StrongSet Y}
  : @IsFun ((X₁ ⊗ X₂ ⇾ Y) × (X₁ × X₂)) Y (λ '(f, p), f p).
Proof. intros [f p][g q]; unfold_pair_eq.
  rew (is_fun (strong_op f) p q); change (strong_op f ?a) with (f a).
  change (f = g) with (∏ r, f r = g r).
  rew (all_lb _ q), (aand_com _ _).
  now apply strong_transitivity.
Qed.
Definition strong_eval_op@{u} (X₁ X₂ Y : set@{u}) `{!StrongSet Y} : (X₁ ⊗ X₂ ⇾ Y) × (X₁ × X₂) ⇾ Y
  := @func_make _ _ _ (strong_eval_op_is_fun X₁ X₂ Y).


Ltac force_fun_type F m := lazymatch F with
| _ ⇾ _ => constr:((F, m))
| of_course_set ?F' =>
  let m' := constr:(of_course_counit F' ∘ m) in
  force_fun_type F' m'
| _ => let t := constr:(id_fun (_ ⇾ _) ∘ m) in
    lazymatch t with id_fun ?F' ∘ m => constr:((F', m)) end
end.

Ltac find_eval X Y := match goal with
| _ => let H := get_instance constr:(StrongSet Y) in
  lazymatch X with
  | ?X₁ ⊗ ?X₂ => constr:(@strong_eval_op X₁ X₂ Y H)
  | _ => constr:(@strong_eval X Y H)
  end
| _ => constr:(@eval X Y)
end.

Ltac interpret_app_aux interpret Γ ρ j₁ x := lazymatch j₁ with
| judgment ?T ?D ?F ?m ?f =>
  let res := force_fun_type F m in lazymatch res with (?X ⇾ ?Y, ?m') =>
    let j₁' := constr:(judgment T D (X ⇾ Y) m' f) in
    let ev := find_eval X Y in lazymatch type of ev with
    | set_T (_ × ?X' ⇾ _) =>
      let j₂ := interpret Γ ρ (set_T X') x in
      let res := interpret_pair_aux j₁' j₂ constr:(CartesianBias) in lazymatch res with
      | judgment ?T' ?D' (_ × ?X'') ?mp (_, ?x') =>
        let m := lazymatch X'' with
        | X' => constr:(ev ∘ mp)
        | _ => let c := build_coercion X'' X' in constr:(ev ∘ prod_map (id_fun _, c) ∘ mp)
        end in
        constr:(judgment T' D' Y m (f x'))
      | _ => res
      end
    | set_T (_ ⊗ ?X' ⇾ _) =>
      let j₂ := interpret Γ ρ (set_T X') x in
      let res := interpret_pair_aux j₁' j₂ constr:(TensorBias) in lazymatch res with
      | judgment ?T' ?D' (_ ⊗ ?X'') ?mp (_, ?x') =>
        let m := lazymatch X'' with
        | X' => constr:(ev ∘ mp)
        | _ => let c := build_coercion X'' X' in constr:(ev ∘ ⟨id_fun _, c⟩ ∘ mp)
        end in
        constr:(judgment T' D' Y m (f x'))
      | _ => res
      end
    end
  end
| _ => j₁
end.

Ltac check_for_strong_op j :=
match j with
| judgment ?T ?D (_ ⊗ _ ⇾ _) (func_op (@const ?E _) ?f) ?tm =>
    constr:(judgment T D _ (@const E _ (strong_op f)) (strong_op f))
| _ => constr:(false)
end.

Ltac interpret_func_op_app interpret Γ ρ tm :=
  lazymatch tm with @func_op ?X ?Y ?f ?x =>
    let j := interpret Γ ρ constr:(set_T X → set_T Y) f in
    let j' := check_for_strong_op j in lazymatch j' with
    | false => interpret_app_aux interpret Γ ρ j x
    | _ => let res := interpret_app_aux interpret Γ ρ j' x in lazymatch res with
      | judgment _ _ _ _ _ => lazymatch res with ?j (func_op (strong_op ?f') ?x') =>
          constr:(j (func_op f' x'))
        end
      | _ => res
      end
    end
  end.

Ltac interpret_lambda_app interpret Γ ρ bias tm :=
  lazymatch tm with ?f ?x =>
    let A := lazymatch type of f with ?A → _ => A end in
    let j₁ := interpret_abs interpret Γ ρ constr:(A → bias) f in
    interpret_app_aux interpret Γ ρ j₁ x
  end.

(** Builds [const tm] assuming [tm] is already known closed w.r.t. Γ/ρ. *)
Ltac interpret_const_raw Γ tm :=
  let T := asubctx_empty Γ in constr:(judgment T 𝟏 _ (const tm) tm).

(** Closedness-checked const: errors with [not_closed tm] if [tm] mentions a
    linear resource (which would otherwise produce a [const] that captures a
    bound variable and fails inscrutably downstream). *)
Ltac interpret_const Γ ρ tm :=
  let c := closed_wrt Γ ρ tm in
  lazymatch c with
  | true => interpret_const_raw Γ tm
  | false => constr:(not_closed tm)
  end.

(** Reached when the application-head reification [@id (func _ _) f] failed,
    i.e. the head is not a morphism.  If [tm = f x] with [f] an *operation*
    (bare function, type [A → set_T Y] or [set_T (operation A Y)]), rewrite
    [f x ↝ eval_pt x f = func_op (eval_pt x) f] — a genuine morphism applied
    to a variable — interpret through the existing func-application machinery,
    and reconstruct [f x] on the way out.  Gated on closedness of the argument:
      - arg open (depends on a linear resource): [f x] is not a morphism — error;
      - arg closed, head a resource: the eval_pt rewrite;
      - arg closed, head closed (whole term closed): plain const.
    Anything that isn't an operation application falls back to [interpret_const]. *)
Ltac interpret_operation_eval_or_const interpret Γ ρ bias tm :=
  let _ := debug_msg ltac:(fun _ => idtac "interpret_operation_eval_or_const" "Γ=" Γ "ρ=" ρ "bias=" bias "tm=" tm) in
  let probe := match tm with
  | ?f ?x => let _ := constr:(@id (operation _ _) f) in constr:((f, x))
  | _ => constr:(false)
  end in
  lazymatch probe with
  | false => interpret_const Γ ρ tm
  | (?f, ?x) =>
    let xc := closed_wrt Γ ρ x in
    lazymatch xc with
    | false => constr:(operation_open_arg x)
    | true =>
      let fc := closed_wrt Γ ρ f in
      lazymatch fc with
      | true => interpret_const_raw Γ tm
      | false =>
        let res := interpret Γ ρ bias constr:(eval_pt x f) in
        lazymatch res with
        | judgment _ _ _ _ _ =>
          lazymatch res with ?j (func_op (eval_pt ?xx) ?ff) => constr:(j (ff xx)) end
        | _ => res
        end
      end
    end
  end.

Ltac interpret_coerce_app_or_const interpret Γ ρ bias tm :=
  let _ := debug_msg ltac:(fun _ => idtac "interpret_coerce_app_or_const" "Γ=" Γ "ρ=" ρ "bias=" bias "tm=" tm) in
  lazymatch closed_wrt Γ ρ tm with
  | true => interpret_const_raw Γ tm
  | false =>
    let c := match tm with
    | ?f ?x ?y ?z => let f' := eval red in (@id (func _ _) (eval_tuncurry3 f)) in constr:((tt, f, f' (x, y, z)))
    | ?f ?x ?y => let f' := eval red in (@id (func _ _) (tuncurry f)) in constr:((true, f, f' (x, y)))
    | ?f ?x => let f' := eval red in (@id (func _ _) f) in constr:((false, f, f' x))
    | _ => constr:(false)
    end in
    lazymatch c with
    | false => interpret_operation_eval_or_const interpret Γ ρ bias tm
    | (?double, ?f, ?tm') =>
      let f' := lazymatch tm' with ?f' _ => constr:(f') end in
      let res := interpret_func_op_app interpret Γ ρ tm' in lazymatch res with
      | judgment _ _ _ _ _ => lazymatch res with ?j (f' ?a) =>
          lazymatch double with
          | false => constr:(j (f a))
          | true => lazymatch a with (?x, ?y) => constr:(j (f x y)) end
          | tt => lazymatch a with (?x, ?y, ?z) => constr:(j (f x y z)) end
          end
        end
      | _ => res
      end
    end
  end.



(** let _ := _ in _ *)

(* let var : set_T X := defn in body *)
Ltac interpret_alias_let_inner interpret Γ ρ bias defn X var body :=
  let ρ' := constr:(AliasCons ρ X var defn) in
  let j := interpret Γ ρ' bias body in
  exact j.
  

Ltac interpret_let_in interpret Γ ρ bias tm :=
  lazymatch tm with let binder : ?T := ?expr in ?body =>
    let expr' := expand_alias Γ ρ expr in lazymatch expr' with
    | var_not_found =>
      let res := eval_under_binder ltac:(interpret_abs_inner interpret Γ ρ bias T) binder T body in
      let j₁ := unwrap_abs_inner Γ binder res in
      let j' := interpret_app_aux interpret Γ ρ j₁ expr in lazymatch j' with
      | judgment _ _ _ _ _ => lazymatch j' with (?j (func_op (set_lambda (λ var, ?body')) ?tm')) =>
          constr:(j (let binder : T := tm' in match binder with var => body' end))
        end
      | _ => j'
      end
    | ( ?A, ?defn ) => let X := lazymatch type of A with AShape ?X => X end in
      let res := eval_under_let
        ltac:(interpret_alias_let_inner interpret Γ ρ bias defn X) binder T expr body in
      lazymatch res with
      | let var := _ in judgment ?U ?D ?Y ?m ?body' =>
        let tm' := constr:(let binder : T := expr in match binder with var => body' end) in
        constr:(judgment U D Y m tm')
      | _ => res
      end
    | _ => expr' 
    end
  end.


(** Quantifiers *)

Lemma all_mor_prop@{u} {A:Type@{u}} {Γ:set@{u}} (m:A → Γ ⇾ Ω) : @IsFun Γ Ω (λ u : Γ, ∏ x : A, m x u).
Proof. intros u v. change (?P = ?Q :> AProp_set) with (P ⧟ Q). rew <-(all_aiff _ _), <-all_adj.
  intros x. exact (is_fun (m x) _ _).
Qed.

Lemma aex_mor_prop@{u} {A:Type@{u}} {Γ:set@{u}} (m:A → Γ ⇾ Ω) : @IsFun Γ Ω (λ u : Γ, ∐ x : A, m x u).
Proof. intros u v. change (?P = ?Q :> AProp_set) with (P ⧟ Q). rew <-(aex_aiff _ _), <-all_adj.
  intros x. exact (is_fun (m x) _ _).
Qed.

Definition all_mor@{u} {A:Type@{u}} {Γ:set@{u}} (m:A → Γ ⇾ Ω) : Γ ⇾ Ω := @func_make _ _ _ (all_mor_prop m).
Definition aex_mor@{u} {A:Type@{u}} {Γ:set@{u}} (m:A → Γ ⇾ Ω) : Γ ⇾ Ω := @func_make _ _ _ (aex_mor_prop m).

Ltac interpret_quantifier interpret Γ ρ tm :=
  let _ := debug_msg ltac:(fun _ => idtac "interpret_quantifier Γ=" Γ "ρ=" ρ "tm=" tm) in
  let P := lazymatch tm with
  | all ?P => constr:( P )
  | aex ?P => constr:( P )
  end in
  lazymatch P with
  | ( λ binder : ?A, ?body ) =>
    let inner_tac var b := let res := interpret Γ ρ constr:(set_T AProp_set) b in exact res in
    let res := eval_under_binder inner_tac binder A body in
    lazymatch res with (λ binder', judgment ?T ?D _ ?m ?tm' ) =>
      lazymatch tm with
      | all _ => constr:( judgment T D AProp_set (all_mor (λ binder' : A, m)) (all (λ binder' : A, tm')) )
      | aex _ => constr:( judgment T D AProp_set (aex_mor (λ binder' : A, m)) (aex (λ binder' : A, tm')) )
      end
    | _ => res
    end
  end.


(* interpret tm in environment Γ
    Input:
      Γ - ACtx
      ρ - AliasList
      bias - type of tm  (preserving e.g., Cast nodes)
      tm - term to interpret
 *)
Ltac interpret Γ ρ bias tm :=
  let _ := debug_msg ltac:(fun _ => idtac "interpret Γ=" Γ "ρ=" ρ "bias=" bias "tm=" tm) in
  lazymatch tm with
  (* abstraction *)
  | λ binder, ?body => interpret_abs interpret Γ ρ bias tm
  | @set_lambda ?X ?Y ?f _ => interpret_abs interpret Γ ρ constr:(set_T X → set_T Y) f
  | @subset_comprehension ?X ?f _ => interpret_subset_comprehension interpret Γ ρ X f
  (* application *)
  | func_op _ _ => interpret_func_op_app interpret Γ ρ tm
  | (λ binder, ?body) _ => interpret_lambda_app interpret Γ ρ bias tm
  (* products *)
  | (_, _) => interpret_pair interpret Γ ρ bias tm
  (*
  | tuncurry ?f => interpret_tuncurry interpret Γ f
  *)
  (* let in *)
  | let binder := _ in _ => interpret_let_in interpret Γ ρ bias tm
  (* quantifiers *)
  | all _ => interpret_quantifier interpret Γ ρ tm
  | aex _ => interpret_quantifier interpret Γ ρ tm
  (* variables, constants
       and applications not in the above forms *)
  | _ =>
    let res := interpret_var Γ ρ bias tm in lazymatch res with
    | judgment _ _ _ _ _ => res
    | var_not_found => interpret_coerce_app_or_const interpret Γ ρ bias tm
    | _ => res
    end
  end.

(** Test: λ y:Y, x  in context (x:X) — body uses Γ, not the binder. *)
Definition test_iabs_const_ctx2 (X Y:set) (x:X)
  : Judgment (ASubCons ASubEmpty x (ASubTop (AAtom X))) X (Y ⇾ X)
  := ltac:(
       let res := interpret
                    constr:(ACons AEmpty (AAtom X) x) constr:(AliasEmpty)
                    constr:(set_T Y → set_T X)
                    constr:(λ y : Y, x) in
       exact res
     ).

(** Test: λ '(x,y) : X ⊗ Y, x *)
Definition test_iabs_proj1 (X Y : set)
  : Judgment ASubEmpty 𝟏 (X ⊗ Y ⇾ X)
  := ltac:(
       let res := interpret
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T (X ⊗ Y) → set_T X)
                    constr:(λ '(x, y) : X ⊗ Y, x) in
       exact res
     ).


(** Test: λ '(x,y) : X ⊗ Y, (y, x) — tensor swap.
    EXPECTED FAILURE: pair construction (y, x) and pair destructure '(x,y)
    aren't dispatched yet; will fall to interpret_var → var_not_found. *)
Definition test_iabs_swap_t (X Y : set)
  : Judgment ASubEmpty 𝟏 (X ⊗ Y ⇾ Y ⊗ X)
  := ltac:(
       let res := interpret
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T (X ⊗ Y) → set_T (Y ⊗ X))
                    constr:(λ '(x, y) : X ⊗ Y, ((y, x) : Y ⊗ X)) in
       exact res
     ).

(** Test: λ '(x,y) : X × Y, (y, x) — cartesian swap.
    EXPECTED FAILURE: same reason as above. *)
Definition test_iabs_swap_c (X Y : set)
  : Judgment ASubEmpty 𝟏 (X × Y ⇾ Y × X)
  := ltac:(
       let res := interpret
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T (X × Y) → set_T (Y × X))
                    constr:(λ '(x, y) : X × Y, ((y, x) : Y × X)) in
       exact res
     ).


(** Test: λ '(x,y) : X × Y, (y, x) — cartesian swap.
    EXPECTED FAILURE: same reason as above. *)
Definition test_iabs_swap_infer (X Y : set)
  : Judgment ASubEmpty 𝟏 _
  := ltac:(
       let res := interpret
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T (X ⊗ Y) → Y ∗ X)
                    constr:(λ '(x, y) : X ⊗ Y, (y, x)) in
       exact res
     ).

(** Test: f x  in context (f:X⇾Y, x:X) — exercises interpret_func_op_app. *)
Definition test_app (X Y : set) (f : X ⇾ Y) (x : X)
  : Judgment
      (ASubCons (ASubCons ASubEmpty f (ASubTop (AAtom (X ⇾ Y)))) x (ASubTop (AAtom X)))
      ((X ⇾ Y) ⊗ X) Y
  := ltac:(
       let res := interpret
                    constr:(ACons (ACons AEmpty (AAtom (X ⇾ Y)) f) (AAtom X) x)
                    constr:(AliasEmpty)
                    constr:(set_T Y)
                    constr:(f x) in
       exact res
     ).

(** Test: λ x:X, f x  in context (f:X⇾Y) — exercises lambda + app + curry. *)
Definition test_iabs_eta (X Y : set) (f : X ⇾ Y)
  : Judgment
      (ASubCons ASubEmpty f (ASubTop (AAtom (X ⇾ Y))))
      (X ⇾ Y) (X ⇾ Y)
  := ltac:(
       let res := interpret
                    constr:(ACons AEmpty (AAtom (X ⇾ Y)) f)
                    constr:(AliasEmpty)
                    constr:(set_T X → set_T Y)
                    constr:(λ x : X, f x) in
       exact res
     ).

(** Test: λ x:X, let y := x in y — simple alias of a Γ variable. *)
Definition test_iabs_let_alias (X : set)
  : Judgment ASubEmpty 𝟏 (X ⇾ X)
  := ltac:(
       let res := interpret
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T X → set_T X)
                    constr:(λ x : X, let y := x in y) in
       exact res
     ).

(** Test: λ p:X⊗Y, let x := π₁ p in x — alias of a projection chain. *)
Definition test_iabs_let_proj (X Y : set)
  : Judgment ASubEmpty 𝟏 (X ⊗ Y ⇾ X)
  := ltac:(
       let res := interpret
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T (X ⊗ Y) → set_T X)
                    constr:(λ p : X ⊗ Y, let x := π₁ p in x) in
       exact res
     ).

(** Test: λ p:X⊗Y, let x := p in let y := π₂ x in y — alias chain (eager
    resolution: y ↦ π₂ p, not π₂ x). *)
Definition test_iabs_let_chain (X Y : set)
  : Judgment ASubEmpty 𝟏 (X ⊗ Y ⇾ Y)
  := ltac:(
       let res := interpret
                    constr:(AEmpty) constr:(AliasEmpty)
                    constr:(set_T (X ⊗ Y) → set_T Y)
                    constr:(λ p : X ⊗ Y, let x := p in let y := π₂ x in y) in
       exact res
     ).


Tactic Notation "set_internalize_tac" open_constr(tm) :=
  let T := type of tm in
  let res := interpret AEmpty AliasEmpty T tm in
  lazymatch res with
  | judgment _ _ _ _ ?tm' => exact tm'
  | _ => fail "set_internalize failure:" res
  end.

(** Solve a [SetLambdaDerivation ?expr] goal: internalize [expr] and provide
    its [IsFun].  The goal supplies the intended domain/codomain sets, so bias
    the interpretation with them rather than [type of expr] (which collapses
    e.g. [Ω] vs [!Ω] to the bare carrier).  The derived codomain can still be
    finer than the one the goal asks for — e.g. a modal-headed body reifies
    through the canonical [of_course_fun : SProp_set ⇾ !Ω] and lands in [!Ω]
    where a subset comprehension asks for [Ω] — so post-compose with the
    [build_coercion] coercion (carrier-identity, hence transparent to
    [func_is_fun]). *)
Ltac solve_SetLambda := lazymatch goal with |- @SetLambdaDerivation ?X ?Y ?expr =>
  let res := interpret AEmpty AliasEmpty constr:(set_T X → set_T Y) expr in
  lazymatch res with
  | judgment _ _ (_ ⇾ ?Y') _ ?f =>
    let c := build_coercion Y' Y in
    let f' := comp c f in
    exact (func_is_fun f')
  | judgment _ _ _ _ ?f => exact (func_is_fun f)
  | _ => fail "set_internalize failure:" res
  end
end.


(** Testing *)
(*
Notation "'set:(' expr )" := ltac:(set_internalize_tac expr) (only parsing, expr constr at level 200).

Global Hint Extern 20 (SetLambdaDerivation _) => solve_SetLambda : typeclass_instances.


Section test.
  Context (X Y Z : set).
  Context (A B C : set) `{!AffirmativeEquality A, !AffirmativeEquality B}
    `{!AffirmativeEquality C}.
  Context (f:X ⇾ Y).
  
  Check set:(λ x:!X, x:X).
  
  Check set:(λ (a b : X), let '(x,y) := (a,b) in x).

  Check set:(λ '(a,b) : (X⊗Y), a).
  
  Check set:(λ '((a,b),c) : ((X×Y)⊗Z), (c,(b,a)) : Z ⊗ (Y × X)).

  Check set:( λ (P:X ⇾ Ω) (Q:𝒫 X), {  x : X | ∐ y:X, x = y ⊠ P y ⊠ Q y} ).

  (*
  Goal True.
    let tm := constr:( λ (P:X ⇾ Ω) (Q:𝒫 X), {  x : X | ∐ y:X, x = y ⊠ P y ⊠ Q y} ) in idtac "tm=" tm;
    (* let tm := constr:( λ (P : X ⇾ Ω), { x : X | ∐ y:X, x = y ⊠ P y } ) in idtac "tm=" tm; *)
    (* let tm := constr:( λ (P Q : X ⇾ Ω), ∏ x, P x ∧ P x ) in idtac "tm=" tm; *)
    (* let tm := constr:( λ (P Q : Ω), P ∧ Q : Ω) in idtac "tm=" tm; *)
    (* let tm := constr:( λ p : Ω × Ω, π₁ p ∧ π₂ p : Ω) in idtac "tm=" tm; *)
    (* let tm := constr:( λ x:(X ⊗ Y), π₁ x ) in idtac "tm=" tm; *)
    (* let tm := constr:( λ (f:!(X ⊗ Y ⇾ Y)) (x:!X) (y:Y), f (x, y) ) in idtac "tm=" tm; *)
    (* let tm := constr:(λ (x:X), (x, λ (y:Y), (y, y))) in idtac "tm=" tm; *)
    (* let tm := constr:(λ (x:X) (y:Y) (z:Z) (a:A), y) in idtac "tm=" tm; *)
    let T := type of tm in idtac "T=" T; 
    let res := interpret constr:(ictx _ AEmpty uᵣ⁻¹) ANoVars AEmpty T tm in
    let T := type of res in
      idtac res; idtac T.
  Abort.
  *)
End test.

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

  Check fun _ : StrongSet Z => set:(λ (h : Z ⊗ Z ⇾ Z) (y:Z), h (h (y, y), y)).

  Check set:(λ (x:Z), ∐ z, z = x ∧ x = z).

  Check set:(λ P : Ω, P ∧ P : Ω).

  Fail Check set:(λ (z:X), λ  '(x, y), (x = y :> X) ⊠ (y = x) : Ω).

  Check (uncurry set:(λ x y, f x y)).
  Check set:(λ p, f (π₁ p) (π₂ p)).

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

