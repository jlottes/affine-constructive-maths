Require Import abstract_algebra.
Require Import logic.aprop relations.
Require Import easy rewrite tactics.misc.
Require Export theory.common_props.
Require Import quote.base.

Lemma id_pointed {X:set} {x:X} : Pointed_Morphism x x id.
Proof. now red. Qed.
Global Hint Extern 2 (Pointed_Morphism _ _ (id_fun _)) => simple notypeclasses refine id_pointed : typeclass_instances.

Definition id_unit_pointed   {X:set} {u:MonUnit X} : MonUnit_Pointed_Morphism (id_fun X) := id_pointed.
Definition id_top_pointed    {X:set} {t:Top     X} : Top_Pointed_Morphism     (id_fun X) := id_pointed.
Definition id_bottom_pointed {X:set} {b:Bottom  X} : Bottom_Pointed_Morphism  (id_fun X) := id_pointed.
Definition id_zero_pointed   {X:set} {z:Zero    X} : Zero_Pointed_Morphism    (id_fun X) := id_pointed.
Definition id_one_pointed  {  X:set} {o:One     X} : One_Pointed_Morphism     (id_fun X) := id_pointed.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (id_fun _)) => simple notypeclasses refine id_unit_pointed   : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism     (id_fun _)) => simple notypeclasses refine id_top_pointed    : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism  (id_fun _)) => simple notypeclasses refine id_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism    (id_fun _)) => simple notypeclasses refine id_zero_pointed   : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism     (id_fun _)) => simple notypeclasses refine id_one_pointed    : typeclass_instances.

Lemma compose_pointed {X Y Z:set} {x:X} {y:Y} {z:Z} {g f} : Pointed_Morphism x y f → Pointed_Morphism y z g
  → Pointed_Morphism x z (g ∘ f).
Proof. intros. change (g (f x) = z). rew (preserves_point f). exact (preserves_point g). Qed.
Global Hint Extern 2 (Pointed_Morphism _ _ (_ ∘ _)) => simple notypeclasses refine (compose_pointed _ _) : typeclass_instances.

Definition compose_unit_pointed {X Y Z:set} {x:MonUnit X} {y:MonUnit Y} {z:MonUnit Z} {g:Y ⇾ Z} {f:X ⇾ Y}
  : MonUnit_Pointed_Morphism f → MonUnit_Pointed_Morphism g → MonUnit_Pointed_Morphism (g ∘ f) := compose_pointed.
Definition compose_top_pointed {X Y Z:set} {x:Top X} {y:Top Y} {z:Top Z} {g:Y ⇾ Z} {f:X ⇾ Y}
  : Top_Pointed_Morphism f → Top_Pointed_Morphism g → Top_Pointed_Morphism (g ∘ f) := compose_pointed.
Definition compose_bottom_pointed {X Y Z:set} {x:Bottom X} {y:Bottom Y} {z:Bottom Z} {g:Y ⇾ Z} {f:X ⇾ Y}
  : Bottom_Pointed_Morphism f → Bottom_Pointed_Morphism g → Bottom_Pointed_Morphism (g ∘ f) := compose_pointed.
Definition compose_zero_pointed {X Y Z:set} {x:Zero X} {y:Zero Y} {z:Zero Z} {g:Y ⇾ Z} {f:X ⇾ Y}
  : Zero_Pointed_Morphism f → Zero_Pointed_Morphism g → Zero_Pointed_Morphism (g ∘ f) := compose_pointed.
Definition compose_one_pointed {X Y Z:set} {x:One X} {y:One Y} {z:One Z} {g:Y ⇾ Z} {f:X ⇾ Y}
  : One_Pointed_Morphism f → One_Pointed_Morphism g → One_Pointed_Morphism (g ∘ f) := compose_pointed.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (_ ∘ _)) => simple notypeclasses refine (compose_unit_pointed   _ _) : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism     (_ ∘ _)) => simple notypeclasses refine (compose_top_pointed    _ _) : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism  (_ ∘ _)) => simple notypeclasses refine (compose_bottom_pointed _ _) : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism    (_ ∘ _)) => simple notypeclasses refine (compose_zero_pointed   _ _) : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism     (_ ∘ _)) => simple notypeclasses refine (compose_one_pointed    _ _) : typeclass_instances.

Local Open Scope fun_inv_scope.

Lemma invert_pointed {X Y:set} {x:X} {y:Y} {f} `{!Pointed_Morphism x y f} `{!Inverse f} `{!Bijective f}
  : Pointed_Morphism y x f⁻¹.
Proof. red. now rew (injective_iff f _ _), (surjective_applied f _). Qed.
Global Hint Extern 2 (Pointed_Morphism _⁻¹) => simple notypeclasses refine invert_pointed : typeclass_instances.

Definition invert_unit_pointed {X Y:set} {x:MonUnit X} {y:MonUnit Y} {f:X ⇾ Y} `{!MonUnit_Pointed_Morphism f} `{!Inverse f} `{!Bijective f}
  : MonUnit_Pointed_Morphism f⁻¹ := invert_pointed.
Definition invert_top_pointed {X Y:set} {x:Top X} {y:Top Y} {f:X ⇾ Y} `{!Top_Pointed_Morphism f} `{!Inverse f} `{!Bijective f}
  : Top_Pointed_Morphism f⁻¹ := invert_pointed.
Definition invert_bottom_pointed {X Y:set} {x:Bottom X} {y:Bottom Y} {f:X ⇾ Y} `{!Bottom_Pointed_Morphism f} `{!Inverse f} `{!Bijective f}
  : Bottom_Pointed_Morphism f⁻¹ := invert_pointed.
Definition invert_zero_pointed {X Y:set} {x:Zero X} {y:Zero Y} {f:X ⇾ Y} `{!Zero_Pointed_Morphism f} `{!Inverse f} `{!Bijective f}
  : Zero_Pointed_Morphism f⁻¹ := invert_pointed.
Definition invert_one_pointed {X Y:set} {x:One X} {y:One Y} {f:X ⇾ Y} `{!One_Pointed_Morphism f} `{!Inverse f} `{!Bijective f}
  : One_Pointed_Morphism f⁻¹ := invert_pointed.
Global Hint Extern 2 (MonUnit_Pointed_Morphism _⁻¹) => simple notypeclasses refine invert_unit_pointed   : typeclass_instances.
Global Hint Extern 2 (Top_Pointed_Morphism     _⁻¹) => simple notypeclasses refine invert_top_pointed    : typeclass_instances.
Global Hint Extern 2 (Bottom_Pointed_Morphism  _⁻¹) => simple notypeclasses refine invert_bottom_pointed : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism    _⁻¹) => simple notypeclasses refine invert_zero_pointed   : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism     _⁻¹) => simple notypeclasses refine invert_one_pointed    : typeclass_instances.



Lemma quote_mon_unit_alt `(f:X ⇾ Y) `{MonUnit_Pointed_Morphism (X:=X) (Y:=Y) (f:=f)}
  : quote f mon_unit mon_unit.
Proof preserves_unit f.

Lemma quote_top_alt `(f:X ⇾ Y) `{Top_Pointed_Morphism (X:=X) (Y:=Y) (f:=f)}
  : quote f ⊤ ⊤.
Proof preserves_top f.

Lemma quote_bottom_alt `(f:X ⇾ Y) `{Bottom_Pointed_Morphism (X:=X) (Y:=Y) (f:=f)}
  : quote f ⊥ ⊥.
Proof preserves_bottom f.

Lemma quote_zero_alt `(f:X ⇾ Y) `{Zero_Pointed_Morphism (X:=X) (Y:=Y) (f:=f)}
  : quote f 0 0.
Proof preserves_0 f.

Lemma quote_one_alt `(f:X ⇾ Y) `{One_Pointed_Morphism (X:=X) (Y:=Y) (f:=f)}
  : quote f 1 1.
Proof preserves_1 f.

Global Hint Extern 4 (quote _ mon_unit _) => quote_hint_strip (fun f => refine (quote_mon_unit_alt f)) : quote.
Global Hint Extern 4 (quote _ _ mon_unit) => quote_hint_strip (fun f => refine (quote_mon_unit_alt f)) : quote.

Global Hint Extern 4 (quote _ ⊤ _) => quote_hint_strip (fun f => refine (quote_top_alt f)) : quote.
Global Hint Extern 4 (quote _ _ ⊤) => quote_hint_strip (fun f => refine (quote_top_alt f)) : quote.

Global Hint Extern 4 (quote _ ⊥ _) => quote_hint_strip (fun f => refine (quote_bottom_alt f)) : quote.
Global Hint Extern 4 (quote _ _ ⊥) => quote_hint_strip (fun f => refine (quote_bottom_alt f)) : quote.

Global Hint Extern 4 (quote _ 0 _) => quote_hint_strip (fun f => refine (quote_zero_alt f)) : quote.
Global Hint Extern 4 (quote _ _ 0) => quote_hint_strip (fun f => refine (quote_zero_alt f)) : quote.

Global Hint Extern 4 (quote _ 1 _) => quote_hint_strip (fun f => refine (quote_one_alt f)) : quote.
Global Hint Extern 4 (quote _ _ 1) => quote_hint_strip (fun f => refine (quote_one_alt f)) : quote.
