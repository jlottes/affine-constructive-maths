Require Import interfaces.set sprop logic.srelations.
Require Import easy tactics.misc.

(** Extensible typeclass mechanism for inferring a simplfication of a term. *)
Class SimplifiesTo {X:set} (x y : X) : SProp := { simplify : x = y }.
Global Hint Mode SimplifiesTo + + - : typeclass_instances.
Arguments simplify {X} x {y _}.
Tactic Notation "solve_simplify" uconstr(t) := match goal with |- @SimplifiesTo ?X ?x ?y => notypeclasses refine (Build_SimplifiesTo X x y t) end.

Ltac simplify := let G := get_goal in refine (sprop.andr (simplify G) _).

Definition simplify_base {X:set} {x:X} : SimplifiesTo x x := {| simplify := reflexivity (=) _ |}.
Global Hint Extern 200 (SimplifiesTo ?x _) =>
  (* idtac "simplify base" x; *)
  simple notypeclasses refine simplify_base : typeclass_instances.


Definition SimplifiesToR {X:set} : srelation X := λ '(x, y), @SimplifiesTo X x y.

Lemma SimplifiesToR_sEquivalence {X} : sEquivalence (@SimplifiesToR X).
Proof. split.
+ now intros ?; split.
+ intros ??[?]; split; sym.
+ intros ? y ? [?][?]; split; trans y.
Qed.
Global Hint Extern 2 (sEquivalence SimplifiesToR) => simple notypeclasses refine SimplifiesToR_sEquivalence : typeclass_instances.
Global Hint Extern 2 (sReflexive SimplifiesToR) => simple notypeclasses refine SimplifiesToR_sEquivalence : typeclass_instances.
Global Hint Extern 2 (sSymmetric SimplifiesToR) => simple notypeclasses refine SimplifiesToR_sEquivalence : typeclass_instances.
Global Hint Extern 2 (sTransitive SimplifiesToR) => simple notypeclasses refine SimplifiesToR_sEquivalence : typeclass_instances.

Definition simplify_chain {X:set} {x y z : X} : SimplifiesTo x y → SimplifiesTo y z → SimplifiesTo x z := stransitivity (R:=SimplifiesToR) _ _ _.

(** "Runs" SimplifiesTo at top level until it makes no progress. *)
Definition FullSimplifiesTo := @SimplifiesTo.
Arguments FullSimplifiesTo {_} _ _.
Existing Class FullSimplifiesTo.
Global Hint Mode FullSimplifiesTo + + - : typeclass_instances.
Definition full_simplify {X} x {y} {H:@FullSimplifiesTo X x y} : x = y := simplify x.

Definition full_simplify_chain {X:set} {x y z : X} : SimplifiesTo x y → FullSimplifiesTo y z → FullSimplifiesTo x z := simplify_chain.

Global Hint Extern 2 (FullSimplifiesTo ?x ?y) =>
  (* idtac "full simplify" x y; *)
  let t := 
     let s := constr:(simplify x) in lazymatch s with ?E.(simplify _) => constr:(E) end in
  ( progress notypeclasses refine (full_simplify_chain t _)
    || refine t ) : typeclass_instances.

Ltac full_simplify := let G := get_goal in refine (sprop.andr (full_simplify G) _).


Ltac simplify_progress t :=
  lazymatch type of t with
  | SimplifiesTo ?a ?b =>
      lazymatch a with
      | b => fail 1
      | _ => notypeclasses refine (simplify_chain t _)
      end
  end.

(** The congruence lemmas below carry [coerce] in their conclusion only so they
    typecheck at the ambient set [A] (whose carrier matches the function
    codomain's by convention, not definitionally).  [simplify_progress_at A t]
    erases it: it extracts the [coerce] arguments from [t]'s type and re-ascribes
    [t] to the clean [@SimplifiesTo A a b], which typechecks because [A] is
    concrete in the goal.  This keeps [coerce] out of every [SimplifiesTo] arg
    that the chain produces. *)
Ltac simplify_progress_at A t :=
  lazymatch type of t with
  | @SimplifiesTo _ (func_op _ ?a) (func_op _ ?b) =>
      simplify_progress constr:(t : @SimplifiesTo A a b)
  end.


Lemma simplify_tensor_pair {X Y} `{@SimplifiesTo X x x'} `{@SimplifiesTo Y y y'} : SimplifiesTo (X:=X⊗Y) (x, y) (x', y').
Proof. split. split; now apply simplify. Qed.
Global Hint Extern 4 (SimplifiesTo (X:=_ ⊗ _) (_, _) _) => notypeclasses refine simplify_tensor_pair : typeclass_instances.

Lemma simplify_prod_pair {X Y} `{@SimplifiesTo X x x'} `{@SimplifiesTo Y y y'} : SimplifiesTo (X:=X×Y) (x, y) (x', y').
Proof. split. split; now apply simplify. Qed.
Global Hint Extern 4 (SimplifiesTo (X:=_ × _) (_, _) _) => notypeclasses refine simplify_prod_pair : typeclass_instances.

Lemma simplify_app {X Y A} `{c:Coerce Y A} `{@SimplifiesTo (X ⇾ Y) f f'} `{@SimplifiesTo X x x'}
  : @SimplifiesTo A (coerce Y A (f x)) (coerce Y A (f' x')).
Proof. split. apply (is_fun (coerce Y A) (f x) (f' x')).
  trans (f' x). exact (simplify f _). apply (is_fun f'). exact (simplify x).
Qed.
Global Hint Extern 100 (SimplifiesTo (func_op ?f ?x) _) =>
  lazymatch goal with
  | |- @SimplifiesTo ?A _ _ =>
      simplify_progress_at A constr:(simplify_app (A:=A) (f:=f) (x:=x))
  end : typeclass_instances.

Lemma simplify_arg (X Y A:set) (f:X → Y) (H:IsFun f) x `{c:Coerce Y A} `{@SimplifiesTo X x x'}
  : @SimplifiesTo A (coerce Y A (f x)) (coerce Y A (f x')).
Proof. split. apply (is_fun (coerce Y A) (f x) (f x')). apply H. exact (simplify x). Qed.

Lemma simplify_tensor_arg2 (X Y Z A:set) (f:X → Y → Z) (H:IsFun (X:=X⊗Y) (tuncurry f)) x y
  `{c:Coerce Z A} `{@SimplifiesTo X x x'} `{@SimplifiesTo Y y y'}
  : @SimplifiesTo A (coerce Z A (f x y)) (coerce Z A (f x' y')).
Proof. split. apply (is_fun (coerce Z A) (f x y) (f x' y')).
  change (tuncurry f (x, y) = tuncurry f (x', y')). apply H; split; now apply simplify.
Qed.

Lemma simplify_prod_arg2 (X Y Z A:set) (f:X → Y → Z) (H:IsFun (X:=X×Y) (tuncurry f)) x y
  `{c:Coerce Z A} `{@SimplifiesTo X x x'} `{@SimplifiesTo Y y y'}
  : @SimplifiesTo A (coerce Z A (f x y)) (coerce Z A (f x' y')).
Proof. split. apply (is_fun (coerce Z A) (f x y) (f x' y')).
  change (tuncurry f (x, y) = tuncurry f (x', y')). apply H; split; now apply simplify.
Qed.

Global Hint Extern 102 (SimplifiesTo (?f ?x₁ ?x₂) ?y) =>
  lazymatch f with
  | func_op => fail 1
  | func_op _ => fail 1
  | func_op _ _ => fail 1
  | func_op _ _ _ => fail 1
  | _ => idtac
  end;
  lazymatch goal with
  | |- @SimplifiesTo ?A _ _ =>
    lazymatch constr:(@id (func _ _) (tuncurry f)) with
    | @id (func (?X ⊗ ?Y) ?Z) ?f' => simplify_progress_at A constr:(simplify_tensor_arg2 X Y Z A f (func_is_fun f') x₁ x₂)
    | @id (func (?X × ?Y) ?Z) ?f' => simplify_progress_at A constr:(simplify_prod_arg2 X Y Z A f (func_is_fun f') x₁ x₂)
    end
  end
  : typeclass_instances.

Global Hint Extern 103 (SimplifiesTo (?f ?x) ?y) =>
  lazymatch f with
  | func_op => fail 1
  | func_op _ => fail 1
  | func_op _ _ => fail 1
  | func_op _ _ _ => fail 1
  | _ => idtac
  end;
  lazymatch goal with
  | |- @SimplifiesTo ?A _ _ =>
    lazymatch constr:(@id (func _ _) f) with @id (func ?X ?Y) ?f' =>
       simplify_progress_at A constr:(simplify_arg X Y A f (func_is_fun f') x)
    end
  end
  : typeclass_instances.


Global Hint Extern 2 (SimplifiesTo (tuncurry ?f (?a, ?b)) ?out) => change (SimplifiesTo (f a b) out) : typeclass_instances.

