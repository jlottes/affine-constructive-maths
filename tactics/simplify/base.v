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


(** * One step at a time, to a fixpoint

    A [SimplifiesTo x z] goal is solved by iterating single steps.  The hint at
    priority 0 wraps the goal as a chain
    [SimplifiesTo x (simplify_step_full y) → SimplifiesToAfter x y z]: the
    identity [simplify_step_full] on the output marks the step subgoal, which
    is solved by the ordinary hints (a rule, a congruence, or reflexivity: a
    rule's output unifies with the marked evar by unfolding) and is not wrapped
    again.  [SimplifiesToAfter x y z] then compares: if nothing changed it
    closes by reflexivity, otherwise it continues with [SimplifiesTo y z].  A
    rule's output is simplified again in full.  A congruence's output comes
    wrapped in the identity [simplify_descended]; the tail strips it and
    continues with a [simplify_step_root] step, on which the congruence hints
    stand aside: the parts were just simplified, so only the rules at the root
    remain to be tried.  Without this every level of a chain re-traverses the
    whole subtree below it, which is what made the old design quadratic on
    deep progress.

    The marker lives on the output, not in the context (a hypothesis would be
    scanned by every hypothesis-trying hint of every nested resolution) and not
    on the input or the set (the hint index keys on the head symbol there, and
    a marked set would leak into the instance arguments of rule lemmas).  A
    rule whose premise is [SimplifiesTo x x'] for a part [x] inherits the mark
    on [x']: that part then takes a single step, and the tail finishes the work
    at the rule's level.

    When the output [z] is already known (a lemma's [SimplifiesTo] premise
    instantiated by [rew] before resolution), the normal form is computed once
    by a nested resolution and compared by conversion.  Running the chain
    instead would let a mismatch at the end backtrack through every
    alternative of every step. *)
Definition simplify_step_full {X:set} (y : X) : X := y.
Definition simplify_step_root {X:set} (y : X) : X := y.
Definition simplify_descended {X:set} (y : X) : X := y.
Definition simplify_descended_intro {X:set} {x y : X} (H : SimplifiesTo x y)
  : SimplifiesTo x (simplify_step_full (simplify_descended y)) := H.

Definition SimplifiesToAfter {X:set} (x y z : X) := @SimplifiesTo X y z.
Existing Class SimplifiesToAfter.
Global Hint Mode SimplifiesToAfter + + + - : typeclass_instances.

Definition simplify_chain_full {X:set} {x y z : X} : SimplifiesTo x (simplify_step_full y) → SimplifiesToAfter x y z → SimplifiesTo x z := simplify_chain.
Definition simplify_chain_root {X:set} {x y z : X} : SimplifiesTo x (simplify_step_root y) → SimplifiesToAfter x y z → SimplifiesTo x z := simplify_chain.

(** Constants, constructors and nullary operations ([0], [(+)]: a class
    projection applied to a set and an instance of a class on that set)
    simplify to themselves.  Deciding this here saves a step search per leaf,
    and leaves are where the hint index is weakest: a transparent head matches
    every pattern, so every rule would be tried.  Variables are not included,
    since a hypothesis [SimplifiesTo x x'] may be in scope for them. *)
Ltac simplify_is_atom t :=
  first
  [ is_const t
  | is_constructor t
  | lazymatch t with ?c ?X ?inst =>
      is_const c;
      lazymatch type of X with set => idtac end;
      lazymatch type of inst with ?cls X => first [ is_const cls | is_ind cls ] end
    end ].

Global Hint Extern 0 (@SimplifiesTo ?X ?x ?z) =>
  tryif simplify_is_atom x then simple notypeclasses refine simplify_base else
  lazymatch z with
  | simplify_step_full _ => fail
  | simplify_step_root _ => fail
  | _ =>
    tryif is_evar z then notypeclasses refine (simplify_chain_full _ _)
    else let p := constr:(simplify x) in simple notypeclasses refine (Build_SimplifiesTo X x z p)
  end : typeclass_instances.

(** The congruence lemmas below carry [coerce] in their conclusion only so they
    typecheck at the ambient set [A], whose carrier matches the function
    codomain's.  The tail erases it by conversion (and keeps it in the one
    case where that fails), so [coerce] never reaches a [SimplifiesTo]
    argument that the chain produces. *)
Ltac simplify_strip_coerce t :=
  lazymatch t with
  | func_op (@coerce _ _ _) ?t' => t'
  | _ => t
  end.

(** A step's output may still carry a step marker when the step went through
    a set alias ([simplifies_of_course_set]): the marked evar then has a
    different set than the solution, and unification assigns the whole marked
    term. *)
Ltac simplify_strip_step t :=
  lazymatch t with
  | simplify_step_full ?t' => simplify_strip_step t'
  | simplify_step_root ?t' => simplify_strip_step t'
  | _ => t
  end.

Global Hint Extern 1 (@SimplifiesToAfter ?A ?x ?y ?z) =>
  let y := simplify_strip_step y in
  lazymatch y with
  | simplify_descended ?y0 =>
    let y' := simplify_strip_coerce y0 in
    lazymatch x with
    | y' => change (@SimplifiesTo A y' z); simple notypeclasses refine simplify_base
    | _ => first
      [ change (@SimplifiesTo A y' z); notypeclasses refine (simplify_chain_root _ _)
      | change (@SimplifiesTo A y0 z); notypeclasses refine (simplify_chain_root _ _) ]
    end
  | _ =>
    lazymatch x with
    | y => change (@SimplifiesTo A y z); simple notypeclasses refine simplify_base
    | _ =>
      change (@SimplifiesTo A y z);
      tryif simplify_is_atom y then simple notypeclasses refine simplify_base else idtac
    end
  end : typeclass_instances.

(** Every congruence hint starts with this: it fires on full steps only. *)
Ltac simplify_congruence_start :=
  lazymatch goal with
  | |- @SimplifiesTo _ _ (simplify_step_full _) => idtac
  | _ => fail
  end.

(** The identity coercion is by far the common case; resolving it by hand
    saves a nested resolution per node. *)
Ltac simplify_coerce_instance Y A :=
  lazymatch Y with
  | A => constr:(id_fun A)
  | _ => constr:(ltac:(first [ exact (id_fun A) | exact _ ]) : Coerce Y A)
  end.


Lemma simplify_tensor_pair {X Y} `{@SimplifiesTo X x x'} `{@SimplifiesTo Y y y'} : SimplifiesTo (X:=X⊗Y) (x, y) (x', y').
Proof. split. split; now apply simplify. Qed.
Global Hint Extern 4 (SimplifiesTo (X:=_ ⊗ _) (_, _) _) =>
  simplify_congruence_start; notypeclasses refine (simplify_descended_intro simplify_tensor_pair) : typeclass_instances.

Lemma simplify_prod_pair {X Y} `{@SimplifiesTo X x x'} `{@SimplifiesTo Y y y'} : SimplifiesTo (X:=X×Y) (x, y) (x', y').
Proof. split. split; now apply simplify. Qed.
Global Hint Extern 4 (SimplifiesTo (X:=_ × _) (_, _) _) =>
  simplify_congruence_start; notypeclasses refine (simplify_descended_intro simplify_prod_pair) : typeclass_instances.

Lemma simplify_app {X Y A} `{c:Coerce Y A} `{@SimplifiesTo (X ⇾ Y) f f'} `{@SimplifiesTo X x x'}
  : @SimplifiesTo A (coerce Y A (f x)) (coerce Y A (f' x')).
Proof. split. apply (is_fun (coerce Y A) (f x) (f' x')).
  trans (f' x). exact (simplify f _). apply (is_fun f'). exact (simplify x).
Qed.
Global Hint Extern 100 (SimplifiesTo (func_op ?f ?x) _) =>
  simplify_congruence_start;
  lazymatch goal with
  | |- @SimplifiesTo ?A _ _ =>
      (* [f]'s codomain, through the definitional classes ([SgOp G] is [G ⊗ G ⇾ G]) *)
      lazymatch constr:(@id (func _ _) f) with @id (func _ ?Y) _ =>
        let c := simplify_coerce_instance Y A in
        notypeclasses refine (simplify_descended_intro (simplify_app (A:=A) (c:=c) (f:=f) (x:=x)))
      end
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
  simplify_congruence_start;
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
    | @id (func (?X ⊗ ?Y) ?Z) ?f' =>
        let c := simplify_coerce_instance Z A in
        notypeclasses refine (simplify_descended_intro (simplify_tensor_arg2 X Y Z A f (func_is_fun f') x₁ x₂ (c:=c)))
    | @id (func (?X × ?Y) ?Z) ?f' =>
        let c := simplify_coerce_instance Z A in
        notypeclasses refine (simplify_descended_intro (simplify_prod_arg2 X Y Z A f (func_is_fun f') x₁ x₂ (c:=c)))
    end
  end
  : typeclass_instances.

Global Hint Extern 103 (SimplifiesTo (?f ?x) ?y) =>
  simplify_congruence_start;
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
       let c := simplify_coerce_instance Y A in
       notypeclasses refine (simplify_descended_intro (simplify_arg X Y A f (func_is_fun f') x (c:=c)))
    end
  end
  : typeclass_instances.


Global Hint Extern 2 (SimplifiesTo (tuncurry ?f (?a, ?b)) ?out) => change (SimplifiesTo (f a b) out) : typeclass_instances.
