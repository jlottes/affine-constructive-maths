Require Export algebra_notation.
Require Import strip_coercions.

Set Implicit Arguments.

Record > has_le T := HasLe { op_le : Le T }.

Record > has_mon_unit X := HasMonUnit { op_mon_unit : MonUnit X }.
Record > has_zero     X := HasZero    { op_zero     : Zero    X }.
Record > has_one      X := HasOne     { op_one      : One     X }.
Record > has_top      X := HasTop     { op_top      : Top     X }.
Record > has_bottom   X := HasBottom  { op_bottom   : Bottom  X }.
Record > has_sg_op    X := HasSgOp    { op_sg_op    : SgOp    X }.
Record > has_inv      X := HasInv     { op_inv      : Inv     X }.
Record > has_plus     X := HasPlus    { op_plus     : Plus    X }.
Record > has_mult     X := HasMult    { op_mult     : Mult    X }.
Record > has_negate   X := HasNegate  { op_negate   : Negate  X }.
Record > has_meet     X := HasMeet    { op_meet     : Meet    X }.
Record > has_join     X := HasJoin    { op_join     : Join    X }.

Record has_dec_eq (X:set) := HasDecEq { op_dec_eq : Dec (A:=X) (=) }.
Unset Implicit Arguments.

Global Hint Extern 4 (Le      ?T) => let t := strip_coercions T in refine (op_le       t) : typeclass_instances.
Global Hint Extern 4 (MonUnit ?X) => let t := strip_coercions X in refine (op_mon_unit t) : typeclass_instances.
Global Hint Extern 4 (Zero    ?X) => let t := strip_coercions X in refine (op_zero     t) : typeclass_instances.
Global Hint Extern 4 (One     ?X) => let t := strip_coercions X in refine (op_one      t) : typeclass_instances.
Global Hint Extern 4 (Top     ?X) => let t := strip_coercions X in refine (op_top      t) : typeclass_instances.
Global Hint Extern 4 (Bottom  ?X) => let t := strip_coercions X in refine (op_bottom   t) : typeclass_instances.
Global Hint Extern 4 (SgOp    ?X) => let t := strip_coercions X in refine (op_sg_op    t) : typeclass_instances.
Global Hint Extern 4 (Inv     ?X) => let t := strip_coercions X in refine (op_inv      t) : typeclass_instances.
Global Hint Extern 4 (Plus    ?X) => let t := strip_coercions X in refine (op_plus     t) : typeclass_instances.
Global Hint Extern 4 (Mult    ?X) => let t := strip_coercions X in refine (op_mult     t) : typeclass_instances.
Global Hint Extern 4 (Negate  ?X) => let t := strip_coercions X in refine (op_negate   t) : typeclass_instances.
Global Hint Extern 4 (Meet    ?X) => let t := strip_coercions X in refine (op_meet     t) : typeclass_instances.
Global Hint Extern 4 (Join    ?X) => let t := strip_coercions X in refine (op_join     t) : typeclass_instances.

Global Hint Extern 4 (Dec (A:=set_T ?X) (=)) => let t := strip_coercions X in refine (op_dec_eq t) : typeclass_instances.

Module definition_hints.
  Local Ltac find h o := lazymatch goal with H : h ?X |- _ ?X => exact (o _ H) end.
  #[export] Hint Extern 8 (MonUnit _) => find has_mon_unit op_mon_unit : typeclass_instances.
  #[export] Hint Extern 8 (Zero    _) => find has_zero     op_zero     : typeclass_instances.
  #[export] Hint Extern 8 (One     _) => find has_one      op_one      : typeclass_instances.
  #[export] Hint Extern 8 (SgOp    _) => find has_sg_op    op_sg_op    : typeclass_instances.
  #[export] Hint Extern 8 (Inv     _) => find has_inv      op_inv      : typeclass_instances.
  #[export] Hint Extern 8 (Plus    _) => find has_plus     op_plus     : typeclass_instances.
  #[export] Hint Extern 8 (Negate  _) => find has_negate   op_negate   : typeclass_instances.
  #[export] Hint Extern 8 (Mult    _) => find has_mult     op_mult     : typeclass_instances.

  #[export] Hint Extern 8 (Dec (A:=set_T ?X) (=)) => lazymatch goal with H : has_dec_eq X |- _ => exact (op_dec_eq H) end : typeclass_instances.
End definition_hints.

