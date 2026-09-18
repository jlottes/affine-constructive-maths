Require Export prelude try_all_hyps.

Reserved Notation "x → y" (at level 99, right associativity, y at level 200).
Reserved Notation "x ⊸ y" (at level 99, right associativity, y at level 200).
Reserved Notation "x ↔ y" (at level 95, no associativity).
Reserved Notation "x ⧟ y" (at level 95, no associativity).
Reserved Notation "x ≅ y" (at level 95, no associativity).
Reserved Notation "x ⇾ y" (at level 92, right associativity, y at level 200).
Reserved Notation "x ⟶ y" (at level 90, right associativity).
Reserved Notation "x ⇒ y" (at level 85, right associativity).
Reserved Notation "x ∨ y" (at level 85, right associativity).
Reserved Notation "x ⊞ y" (at level 85, right associativity).
Reserved Notation "x ∧ y" (at level 80, right associativity).
Reserved Notation "x ⊠ y" (at level 80, right associativity).
Reserved Notation "¬ x" (at level 75, right associativity).

Reserved Notation "x = y :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).

Reserved Notation "x ≠ y :> T" (at level 70, y at next level, no associativity).
Reserved Notation "x ≠ y" (at level 70, no associativity).

Reserved Notation "x ≡ y :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x ≡ y" (at level 70, no associativity).
Reserved Notation "x ≣ y" (at level 70, no associativity).

Reserved Notation "x ≤ y :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x ≤ y" (at level 70, no associativity).

Reserved Notation "x < y :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).
Reserved Notation "x ⊆ y" (at level 70, no associativity).

Reserved Notation "x ⊔ y" (at level 59, left associativity).
Reserved Notation "x ⊓ y" (at level 54, left associativity).

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).
Reserved Notation "x ⊕ y" (at level 50, left associativity).
(** Note: '∗' is not '*' *)
Reserved Notation "x ∗ y" (at level 40, left associativity).
Reserved Notation "x × y" (at level 40, left associativity).
Reserved Notation "x · y" (at level 40, left associativity).
Reserved Notation "x ⊗ y" (at level 40, left associativity).
Reserved Notation "x ∙ y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "( x , y , .. , z )" (at level 0).

Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x && y" (at level 40, left associativity).

Reserved Notation "g ∘ f" (at level 30, left associativity).
Reserved Notation "g ⊚ f" (at level 30, left associativity).
Reserved Notation "R ⋄ S" (at level 30, left associativity).

Reserved Notation "x ⁻¹" (at level 1, left associativity, format "x ⁻¹").
Reserved Notation "x *" (at level 1, left associativity, format "x *").

Notation "'∀' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 10, x binder, y binder, P at level 200) : type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 10, x binder, y binder, t at level 200).
  
Notation "A → B" := (∀ _ : A, B) : type_scope.

Infix "∗" := tprod : type_scope.
Notation "( a , b , .. , c )" := (pair .. (pair a b) .. c ).

Module projection_notation.
  Abbreviation π₁ := proj1.
  Abbreviation π₂ := proj2.
End projection_notation.


(* Allow type annotations on patterns. *)
Notation "'λ' ' pat : T , t" := (fun pat : T => t)
  (at level 10, pat pattern, t at level 200, only parsing).
(* But don't require them. *)
Notation "'λ' ' pat , t" := (fun pat => t)
  (at level 10, pat pattern, t at level 200, only parsing).

(** Pretty-printing for binary destructuring lambdas at the top level.
    When the pattern lambda is nested inside other lambdas, the recursive
    [λ x .. y, t] form absorbs the pattern binder; the [let '(...)]
    printing notation below recovers the destructuring in the body. *)
Notation "'λ' ' '(' a ',' b ')' ',' t" :=
  (fun pat => let p := pat in let a := proj1 p in let b := proj2 p in t)
  (at level 10, t at level 200, only printing,
   format "'λ'  ''' '(' a ','  b ')' ','  t").

(** Pretty-printing for binary destructuring let-bindings.  Recovers
    [let '(a, b) := p in t] sugar from the desugared [let]-chain that
    primitive projections produce. *)
Notation "'let' ' '(' a ',' b ')' ':=' p 'in' t" :=
  (let x := p in let a := proj1 x in let b := proj2 x in t)
  (at level 10, t at level 200, only printing,
   format "'[hv' 'let'  ''' '(' a ','  b ')'  ':='  p  'in'  '/' t ']'").

(** Pretty-printing for doubly-nested binary destructuring let-bindings. *)
Notation "'let' ' '(' '(' x1 ',' y1 ')' ',' '(' x2 ',' y2 ')' ')' ':=' p 'in' t" :=
  (let z := p in
   let a := proj1 z in let b := proj2 z in
   let w := a in let x1 := proj1 w in let y1 := proj2 w in
   let v := b in let x2 := proj1 v in let y2 := proj2 v in
   t)
  (at level 10, t at level 200, only printing,
   format "'[hv' 'let'  ''' '(' '(' x1 ','  y1 ')' ','  '(' x2 ','  y2 ')' ')'  ':='  p  'in'  '/' t ']'").

(** Pretty-printing for doubly-nested binary destructuring lambdas. *)
Notation "'λ' ' '(' '(' x1 ',' y1 ')' ',' '(' x2 ',' y2 ')' ')' ',' t" :=
  (fun pat =>
   let z := pat in
   let a := proj1 z in let b := proj2 z in
   let w := a in let x1 := proj1 w in let y1 := proj2 w in
   let v := b in let x2 := proj1 v in let y2 := proj2 v in
   t)
  (at level 10, t at level 200, only printing,
   format "'λ'  ''' '(' '(' x1 ','  y1 ')' ','  '(' x2 ','  y2 ')' ')' ','  t").





Module sigma_notation.
  Notation "'Σ' x .. y , P" := (tsig (fun x => .. (tsig (fun y => P)) ..))
    (at level 10, x binder, y binder, P at level 200) : type_scope.
End sigma_notation.

Module tsum_notation.
  Infix "+" := tsum : type_scope.
End tsum_notation.

Reserved Notation "{ x | P }" (at level 0, x binder).
Reserved Notation "{ x : A | P }" (at level 0, x binder).

Set Typeclasses Unique Instances.

(** Notation for the unique term of some type. *)
Declare Scope the_scope.
Delimit Scope the_scope with the.

Class The X := the : X.
(* Notation "!" := the : the_scope. *)
Global Hint Mode The + : typeclass_instances.
Global Typeclasses Transparent The.

(** Notations for categories *)
Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
(*Global Open Scope cat_scope.*)

Class BoldZero Ob := bzero : Ob.
Notation "𝟎" := bzero : cat_scope.
Global Hint Mode BoldZero + : typeclass_instances.

Class BoldOne Ob := bone : Ob.
Notation "𝟏" := bone : cat_scope.
Global Hint Mode BoldOne + : typeclass_instances.

Class Product Ob := prod : Ob → Ob → Ob.
Notation "X × Y" := (prod X Y) : cat_scope.
Global Hint Mode Product + : typeclass_instances.

Class Tensor Ob := tensor : Ob → Ob → Ob.
Notation "X ⊗ Y" := (tensor X Y) : cat_scope.
Global Hint Mode Tensor + : typeclass_instances.

Global Typeclasses Transparent BoldZero BoldOne Product Tensor.

Global Hint Extern 1 (BoldZero Type) => refine empty : typeclass_instances.
Global Hint Extern 1 (BoldOne  Type) => refine unit  : typeclass_instances.
Global Hint Extern 1 (Product  Type) => refine tprod : typeclass_instances.

Unset Typeclasses Unique Instances.
