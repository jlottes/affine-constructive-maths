Require Export theory.set.

Set Typeclasses Unique Instances.

Declare Scope op_scope.
Delimit Scope op_scope with op.
Global Open Scope op_scope.

Class MonUnit (M:set) := mon_unit : M.
Global Hint Mode MonUnit + : typeclass_instances.

Class Zero (X:set) := zero : X.
Notation "0" := zero : op_scope.
Global Hint Mode Zero + : typeclass_instances.

Class One (X:set) := one : X.
Notation "1" := one : op_scope.
Global Hint Mode One + : typeclass_instances.

Class Top (L:set) := top : L.
Notation "⊤" := top : op_scope.
Global Hint Mode Top + : typeclass_instances.

Class Bottom (L:set) := bottom : L.
Notation "⊥" := bottom : op_scope.
Global Hint Mode Bottom + : typeclass_instances.

Class SgOp (G:set) := sg_op : G ⊗ G ⇾ G.
Declare Scope grp_scope.
Notation "x ∙ y" := (func_op sg_op (x, y)) : grp_scope.
Notation "(∙)" := sg_op : grp_scope.
Notation "( x ∙)" := (func_op2 ap1 sg_op x) : grp_scope.
Notation "(∙ x )" := (func_op2 ap2 sg_op x) : grp_scope.
Global Hint Mode SgOp + : typeclass_instances.
Global Hint Extern 1 (StrongOp (@sg_op _ (?f ∘ tensor_to_prod _ _))) => simple notypeclasses refine (is_fun f) : typeclass_instances.

Class Inv G := inv : G ⇾ G.
Notation "x ⁻¹" := (func_op inv x) : grp_scope.
Notation "(⁻¹)" := inv : grp_scope.
Global Hint Mode Inv + : typeclass_instances.

Class Plus (X:set) := plus : X ⊗ X ⇾ X.
Notation "x + y" := (func_op plus (x, y)) : op_scope.
Notation "(+)" := plus : op_scope.
Notation "( x +)" := (func_op2 ap1 plus x) : op_scope.
Notation "(+ x )" := (func_op2 ap2 plus x) : op_scope.
Global Hint Mode Plus + : typeclass_instances.
Global Hint Extern 1 (StrongOp (@plus _ (?f ∘ tensor_to_prod _ _))) => simple notypeclasses refine (is_fun f) : typeclass_instances.

Class Mult (X:set) := mult : X ⊗ X ⇾ X.
Declare Scope mult_scope.
Notation "x · y" := (func_op mult (x, y)) : mult_scope.
Notation "(·)" := mult : mult_scope.
Notation "( x ·)" := (func_op2 ap1 mult x) : mult_scope.
Notation "(· x )" := (func_op2 ap2 mult x) : mult_scope.
Global Hint Mode Mult + : typeclass_instances.
Global Hint Extern 1 (StrongOp (@mult _ (?f ∘ tensor_to_prod _ _))) => simple notypeclasses refine (is_fun f) : typeclass_instances.

Class Negate G := negate : G ⇾ G.
Notation "- x" := (func_op negate x) : op_scope.
Notation "(-)" := negate : op_scope.
Notation "x - y" := (x + -y) : op_scope.
Global Hint Mode Negate + : typeclass_instances.

Class Meet (L:set) := meet : L ⊗ L ⇾ L.
Notation "x ⊓ y" := (func_op meet (x, y)) : op_scope.
Notation "(⊓)" := meet : op_scope.
Notation "( x ⊓)" := (func_op2 ap1 meet x) : op_scope.
Notation "(⊓ x )" := (func_op2 ap2 meet x) : op_scope.
Global Hint Mode Meet + : typeclass_instances.
Global Hint Extern 1 (StrongOp (@meet _ (?f ∘ tensor_to_prod _ _))) => simple notypeclasses refine (is_fun f) : typeclass_instances.

Class Join (L:set) := join : L ⊗ L ⇾ L.
Notation "x ⊔ y" := (func_op join (x, y)) : op_scope.
Notation "(⊔)" := join : op_scope.
Notation "( x ⊔)" := (func_op2 ap1 join x) : op_scope.
Notation "(⊔ x )" := (func_op2 ap2 join x) : op_scope.
Global Hint Mode Join + : typeclass_instances.
Global Hint Extern 1 (StrongOp (@join _ (?f ∘ tensor_to_prod _ _))) => simple notypeclasses refine (is_fun f) : typeclass_instances.

Unset Typeclasses Unique Instances.

Notation "2" := (1 + 1) : op_scope.
Notation "3" := (1 + (1 + 1)) : op_scope.
Notation "4" := (1 + (1 + (1 + 1))) : op_scope.
Notation "- 1" := (-(1)) : op_scope.
Notation "- 2" := (-(2)) : op_scope.
Notation "- 3" := (-(3)) : op_scope.
Notation "- 4" := (-(4)) : op_scope.

Definition semigroup_op (G:set) := G.
Global Hint Extern 1 (SgOp (semigroup_op ?G)) => notypeclasses refine (@sg_op G _ ∘ tensor_swap G G) : typeclass_instances.
Global Hint Extern 1 (MonUnit (semigroup_op ?G)) => change (MonUnit G) : typeclass_instances.
Global Hint Extern 1 (Inv (semigroup_op ?G)) => change (Inv G) : typeclass_instances.

Definition AdditiveGroupOps       (X:set) := X.
Global Hint Extern 1 (SgOp    (AdditiveGroupOps ?X)) => change (Plus   X) : typeclass_instances.
Global Hint Extern 1 (MonUnit (AdditiveGroupOps ?X)) => change (Zero   X) : typeclass_instances.
Global Hint Extern 1 (Inv     (AdditiveGroupOps ?X)) => change (Negate X) : typeclass_instances.

Definition MultiplicativeGroupOps (X:set) := X.
Global Hint Extern 1 (SgOp    (MultiplicativeGroupOps ?X)) => change (Mult X) : typeclass_instances.
Global Hint Extern 1 (MonUnit (MultiplicativeGroupOps ?X)) => change (One  X) : typeclass_instances.

Definition ring_op (R:set) := R.
Global Hint Extern 1 (Mult   (ring_op ?R)) => notypeclasses refine (@mult R _ ∘ tensor_swap R R) : typeclass_instances.
Global Hint Extern 1 (Plus   (ring_op ?R)) => change (Plus    R) : typeclass_instances.
Global Hint Extern 1 (Zero   (ring_op ?R)) => change (Zero    R) : typeclass_instances.
Global Hint Extern 1 (One    (ring_op ?R)) => change (One     R) : typeclass_instances.
Global Hint Extern 1 (Negate (ring_op ?R)) => change (Negate  R) : typeclass_instances.


Definition MeetSemigroupOps (L:set) := L.
Definition JoinSemigroupOps (L:set) := L.
Global Hint Extern 1 (SgOp (MeetSemigroupOps ?L)) => change (Meet L) : typeclass_instances.
Global Hint Extern 1 (SgOp (JoinSemigroupOps ?L)) => change (Join L) : typeclass_instances.
Global Hint Extern 1 (MonUnit (MeetSemigroupOps ?L)) => change (Top L) : typeclass_instances.
Global Hint Extern 1 (MonUnit (JoinSemigroupOps ?L)) => change (Bottom L) : typeclass_instances.

Definition order_op (X:set) := X.
Global Hint Extern 2 (Meet   (order_op ?L)) => change (Join   L) : typeclass_instances.
Global Hint Extern 2 (Join   (order_op ?L)) => change (Meet   L) : typeclass_instances.
Global Hint Extern 2 (Top    (order_op ?L)) => change (Bottom L) : typeclass_instances.
Global Hint Extern 2 (Bottom (order_op ?L)) => change (Top    L) : typeclass_instances.


