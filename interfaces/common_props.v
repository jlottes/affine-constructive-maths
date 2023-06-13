Require Export theory.set.

Require Import set_lambda.

Import of_course_set_notation.

(** Affine definitions. *)

Definition aAssociative      {X    } := set:(λ f : !(X ⊗ X ⇾ X), ∏ x y z, f(x, f(y, z)) = f(f(x, y), z) ).
Definition aCommutative      {X Y  } := set:(λ f : !(X ⊗ X ⇾ Y), ∏ x y, f(x, y) = f(y, x) ).
Definition aBinaryIdempotent {X    } := set:(λ f :  (X ⊗ X ⇾ X), ∏ x, f (x, x) = x ).
Definition aInvolutive       {X    } := set:(λ f : !(X ⇾ X), ∏ x, f (f x) = x ).
Definition aAbsorption       {X Y Z} := set:(λ (f:X ⊗ Z ⇾ X) (g:X ⊗ Y ⇾ Z), ∏ x y, f(x, g(x, y)) = x ).
Definition aLeftDistribute   {X    } := set:(λ (f g : !(X ⊗ X ⇾ X)), ∏ x y z, f(x, g(y, z)) = g(f(x, y), f(x, z)) ).
Definition aRightDistribute  {X    } := set:(λ (f g : !(X ⊗ X ⇾ X)), ∏ x y z, f(g(x, y), z) = g(f(x, z), f(y, z)) ).

Definition aLeftIdentity     {X Y  } := set:(λ (f : (X ⊗ Y ⇾ Y)) (x: X), ∏ y, f (x, y) = y ).
Definition aRightIdentity    {X Y  } := set:(λ (f : (X ⊗ Y ⇾ X)) (y: Y), ∏ x, f (x, y) = x ).
Definition aLeftAbsorb       {X Y  } := set:(λ (f : (X ⊗ Y ⇾ X)) (x:!X), ∏ y, f (x, y) = x ).
Definition aRightAbsorb      {X Y  } := set:(λ (f : (X ⊗ Y ⇾ Y)) (y:!Y), ∏ x, f (x, y) = y ).

Definition aLeftInverse      {X Y Z} := set:( λ (f:X ⊗ Y ⇾ Z) (inv:Y ⇾ X) (unit:Z), ∏ y, f (inv y, y) = unit ).
Definition aRightInverse     {X Y Z} := set:( λ (f:X ⊗ Y ⇾ Z) (inv:X ⇾ Y) (unit:Z), ∏ x, f (x, inv x) = unit ).

(** A declaration such as

   [ H : aCommutative (+) ]

   is really

   [ H : apos (aCommutative (+)) ]

   involving the implicit coercion [apos] to an [SProp]. It's convenenient to define [SProp] versions
   so that they may participate in coercions.
*)

Definition Associative      {X}     (f:X ⊗ X ⇾ X)               : SProp := Eval simpl in aAssociative f.
Definition Commutative      {X Y  } (f:X ⊗ X ⇾ Y)               : SProp := Eval simpl in aCommutative f.
Definition BinaryIdempotent {X    } (f:X ⊗ X ⇾ X)               : SProp := Eval simpl in aBinaryIdempotent f.
Definition Involutive       {X    } (f:X ⇾ X)                   : SProp := Eval simpl in aInvolutive f.
Definition Absorption       {X Y Z} (f:X ⊗ Z ⇾ X) (g:X ⊗ Y ⇾ Z) : SProp := Eval simpl in aAbsorption f g.
Definition LeftDistribute   {X    } (f g : X ⊗ X ⇾ X)           : SProp := Eval simpl in aLeftDistribute f g.
Definition RightDistribute  {X    } (f g : X ⊗ X ⇾ X)           : SProp := Eval simpl in aRightDistribute f g.

Definition LeftIdentity     {X Y  } (f : X ⊗ Y ⇾ Y) (x:X) : SProp := Eval simpl in aLeftIdentity f x.
Definition RightIdentity    {X Y  } (f : X ⊗ Y ⇾ X) (y:Y) : SProp := Eval simpl in aRightIdentity f y.
Definition LeftAbsorb       {X Y  } (f : X ⊗ Y ⇾ X) (x:X) : SProp := Eval simpl in aLeftAbsorb f x.
Definition RightAbsorb      {X Y  } (f : X ⊗ Y ⇾ Y) (y:Y) : SProp := Eval simpl in aRightAbsorb f y.

Definition LeftInverse      {X Y Z} (f:X ⊗ Y ⇾ Z) (inv:Y ⇾ X) (unit:Z) : SProp := Eval simpl in aLeftInverse f inv unit.
Definition RightInverse     {X Y Z} (f:X ⊗ Y ⇾ Z) (inv:X ⇾ Y) (unit:Z) : SProp := Eval simpl in aRightInverse f inv unit.

Existing Class Associative.
Existing Class Commutative.
Existing Class BinaryIdempotent.
Existing Class Involutive.
Existing Class Absorption.
Existing Class LeftDistribute.
Existing Class RightDistribute.

Existing Class LeftIdentity.
Existing Class RightIdentity.
Existing Class LeftAbsorb.
Existing Class RightAbsorb.
Existing Class LeftInverse.
Existing Class RightInverse.


Definition associativity      {X    } f {H:@Associative X f} x y z := H x y z.
Definition commutativity      {X Y  } f {H:@Commutative X Y f} x y := H x y.
Definition binary_idempotency {X    } f {H:@BinaryIdempotent X f} x := H x.
Definition involutive         {X    } f {H:@Involutive X f} x := H x.
Definition absorption         {X Y Z} f g {H:@Absorption X Y Z f g} x y := H x y.
Definition distribute_l       {X    } f g {H:@LeftDistribute X f g} x y z := H x y z.
Definition distribute_r       {X    } f g {H:@RightDistribute X f g} x y z := H x y z.
Definition left_identity      {X Y  } f `{H:@LeftIdentity X Y f x} y := H y.
Definition right_identity     {X Y  } f `{H:@RightIdentity X Y f y} x := H x.
Definition left_absorb        {X Y  } f `{H:@LeftAbsorb X Y f x} y := H y.
Definition right_absorb       {X Y  } f `{H:@RightAbsorb X Y f y} x := H x.
Definition left_inverse       {X Y Z} f {inv unit} `{H:@LeftInverse X Y Z f inv unit} y := H y.
Definition right_inverse      {X Y Z} f {inv unit} `{H:@RightInverse X Y Z f inv unit} x := H x.



Definition weaken_apred1 {X:set} : (X ⇾ Ω) → (!X ⇾ SProp) := λ P, apos ∘ of_course_map P.
Definition weaken_apred2 {X Y:set} : (X ⇾ Y ⇾ Ω) → (!X ⊗ !Y ⇾ SProp) := λ P, apos ∘ of_course_op (uncurry P).
Definition weaken_apred3 {X Y Z:set} : (X ⇾ Y ⇾ Z ⇾ Ω) → (!X ⊗ !Y ⊗ !Z ⇾ SProp) := λ P, apos ∘ of_course_op3 (uncurry (uncurry P)).

Canonical Structure Associative_fun {X} := make_fun_alt (@Associative X) (weaken_apred1 (@aAssociative X)).
Canonical Structure Commutative_fun {X Y} := make_fun_alt (@Commutative X Y) (weaken_apred1 (@aCommutative X Y)).
Canonical Structure BinaryIdempotent_fun {X} := make_fun_alt (@BinaryIdempotent X) (weaken_apred1 (@aBinaryIdempotent X)).
Canonical Structure Involutive_fun {X} := make_fun_alt (@Involutive X) (weaken_apred1 (@aInvolutive X)).
Canonical Structure Absorption_fun {X Y Z} := make_fun_alt (eval_tuncurry (@Absorption X Y Z))   (weaken_apred2 (@aAbsorption X Y Z)).
Canonical Structure LeftDistribute_fun {X} := make_fun_alt (eval_tuncurry (@LeftDistribute X))   (weaken_apred2 (@aLeftDistribute X)).
Canonical Structure RightDistribute_fun {X} := make_fun_alt (eval_tuncurry (@RightDistribute X))   (weaken_apred2 (@aRightDistribute X)).
Canonical Structure LeftIdentity_fun {X Y} := make_fun_alt (eval_tuncurry (@LeftIdentity X Y))  (weaken_apred2 (@aLeftIdentity X Y)).
Canonical Structure RightIdentity_fun {X Y} := make_fun_alt (eval_tuncurry (@RightIdentity X Y))  (weaken_apred2 (@aRightIdentity X Y)).
Canonical Structure LeftAbsorb_fun {X Y} := make_fun_alt (eval_tuncurry (@LeftAbsorb X Y))  (weaken_apred2 (@aLeftAbsorb X Y)).
Canonical Structure RightAbsorb_fun {X Y} := make_fun_alt (eval_tuncurry (@RightAbsorb X Y))  (weaken_apred2 (@aRightAbsorb X Y)).
Canonical Structure LeftInverse_fun {X Y Z} := make_fun_alt (eval_tuncurry3 (@LeftInverse X Y Z))  (weaken_apred3 (@aLeftInverse X Y Z)).
Canonical Structure RightInverse_fun {X Y Z} := make_fun_alt (eval_tuncurry3 (@RightInverse X Y Z))  (weaken_apred3 (@aRightInverse X Y Z)).

