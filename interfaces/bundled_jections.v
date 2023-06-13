Require Import theory.set theory.projected_set interfaces.cat.
Require Import strip_coercions.
Require Import easy.

Set Implicit Arguments.

Local Open Scope fun_inv_scope.
Import tensor_map_notation.

Record injection_t@{i} (X Y : set@{i}) :=
{ injection_fun  :> func X Y
; #[canonical=no] injection_prop :> Injective injection_fun
}.
Global Hint Extern 2 (StripCoercions (injection_fun ?f)) => strip_coercions_chain f : strip_coercions.
Global Hint Extern 4 (Injective ?f) => exact_strip_coercions f : typeclass_instances.
Canonical Structure injection@{i} (X Y : set@{i}) := projected_set (@injection_fun X Y).
Definition make_injection : ∀ {X Y : set} (f:X ⇾ Y) `{!Injective f}, injection X Y := @Build_injection_t.
Arguments make_injection {X Y} f {_}.

Global Hint Extern 2 (IsProjectedSet (set_T (injection _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Definition injection_to_func@{i} (X Y : set@{i}) := make_injection (projected_set_project (injection X Y)).

Definition injection_cat_t := Build_cat_t set injection.
Canonical Structure id_injection@{i} (X : set@{i}) := make_injection (id_fun X).
Global Hint Extern 1 (Id injection_cat_t) => simple notypeclasses refine @id_injection : typeclass_instances.

Local Notation make_projected_op op f := (@make_fun _ _ _ (projected_is_fun (tuncurry op) f (λ _, reflexivity (=) _))).
Local Notation make_compose_fun c := (make_projected_op c (∘)).

Canonical Structure injection_compose_op@{i} {X Y Z : set@{i}} (g:injection Y Z) (f:injection X Y) : injection X Z := make_injection (g ∘ f).
Definition injection_compose@{i} {X Y Z : set@{i}} := make_compose_fun (@injection_compose_op X Y Z).
Global Hint Extern 1 (Compose injection_cat_t) => refine @injection_compose : typeclass_instances.

Local Instance injection_is_cat : IsCat injection_cat_t.  Proof. now split. Qed.
Canonical Structure injection_cat := Build_cat injection_cat_t.


Record surjection_t@{i} (X Y : set@{i}) :=
{ surjection_fun  :> func X Y
; surjection_inv  :> Inverse surjection_fun
; #[canonical=no] surjection_prop :> Surjective surjection_fun
}.
Global Hint Extern 2 (StripCoercions (surjection_fun ?f)) => strip_coercions_chain f : strip_coercions.
Global Hint Extern 4 (Inverse ?f) => exact_strip_coercions f : typeclass_instances.
Global Hint Extern 4 (Surjective ?f) => exact_strip_coercions f : typeclass_instances.
Canonical Structure surjection@{i} (X Y : set@{i}) := projected_set (@surjection_fun X Y).
Definition make_surjection : ∀ {X Y : set} (f:X ⇾ Y) `{!Inverse f} `{!Surjective f}, surjection X Y := @Build_surjection_t.
Arguments make_surjection {X Y} f {_ _}.

Global Hint Extern 2 (IsProjectedSet (set_T (surjection _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Definition surjection_to_func@{i} (X Y : set@{i}) := make_injection (projected_set_project (surjection X Y)).


Definition surjection_cat_t := Build_cat_t set surjection.
Canonical Structure id_surjection@{i} (X : set@{i}) := make_surjection (id_fun X).
Global Hint Extern 1 (Id surjection_cat_t) => simple notypeclasses refine @id_surjection : typeclass_instances.

Canonical Structure surjection_compose_op@{i} {X Y Z : set@{i}} (g:surjection Y Z) (f:surjection X Y) : surjection X Z := make_surjection (g ∘ f).
Definition surjection_compose@{i} {X Y Z : set@{i}} := make_compose_fun (@surjection_compose_op X Y Z).
Global Hint Extern 1 (Compose surjection_cat_t) => refine @surjection_compose : typeclass_instances.

Local Instance surjection_is_cat : IsCat surjection_cat_t.  Proof. now split. Qed.
Canonical Structure surjection_cat := Build_cat surjection_cat_t.



Record bijection_t@{i} (X Y : set@{i}) :=
{ bijection_fun  :> func X Y
; bijection_inv  :> Inverse bijection_fun
; #[canonical=no] bijection_prop :> Bijective bijection_fun
}.
Global Hint Extern 2 (StripCoercions (bijection_fun ?f)) => strip_coercions_chain f : strip_coercions.
Global Hint Extern 4 (Bijective ?f) => exact_strip_coercions f : typeclass_instances.
Canonical Structure bijection@{i} (X Y : set@{i}) := projected_set (@bijection_fun X Y).
Definition make_bijection : ∀ {X Y : set} (f:X ⇾ Y) `{!Inverse f} `{!Bijective f}, bijection X Y := @Build_bijection_t.
Arguments make_bijection {X Y} f {_ _}.

Global Hint Extern 2 (IsProjectedSet (set_T (bijection _ _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Definition bijection_to_func@{i} (X Y : set@{i}) := make_injection (projected_set_project (bijection X Y)).

Module notation.
  Notation "X ≅ Y" := (bijection X Y).
End notation.
Import notation.

Definition bijection_cat_t := Build_cat_t set bijection.
Canonical Structure id_bijection@{i} (X : set@{i}) := make_bijection (id_fun X).
Global Hint Extern 1 (Id bijection_cat_t) => simple notypeclasses refine @id_bijection : typeclass_instances.

Canonical Structure bijection_compose_op@{i} {X Y Z : set@{i}} (g: Y ≅ Z) (f:X ≅ Y) : X ≅ Z := make_bijection (g ∘ f).
Definition bijection_compose@{i} {X Y Z : set@{i}} := make_compose_fun (@bijection_compose_op X Y Z).
Global Hint Extern 1 (Compose bijection_cat_t) => refine @bijection_compose : typeclass_instances.

Local Instance bijection_is_cat : IsCat bijection_cat_t.  Proof. now split. Qed.
Canonical Structure bijection_cat := Build_cat bijection_cat_t.

Canonical Structure invert_bijection {X Y} (f:X ≅ Y) : Y ≅ X := make_bijection f⁻¹.

Canonical Structure bijection_as_injection@{i} {X Y : set@{i}} (f:X ≅ Y) : injection X Y := make_injection f.
Canonical Structure bijection_as_surjection@{i} {X Y : set@{i}} (f:X ≅ Y) : surjection X Y := make_surjection f.
Definition bijection_t_as_injection_t@{i} {X Y : set@{i}} (f: bijection_t X Y) : injection_t X Y := bijection_as_injection f.
Coercion bijection_t_as_injection_t : bijection_t >-> injection_t.
Definition bijection_t_as_surjection_t@{i} {X Y : set@{i}} (f: bijection_t X Y) : surjection_t X Y := bijection_as_surjection f.
Coercion bijection_t_as_surjection_t : bijection_t >-> surjection_t.


Canonical Structure tensor_swap_bijection X Y : X ⊗ Y ≅ Y ⊗ X := make_bijection (tensor_swap X Y).
Canonical Structure prod_swap_bijection X Y : X × Y ≅ Y × X := make_bijection (prod_swap X Y).

Canonical Structure tensor_assoc_l_bijection X Y Z : X ⊗ Y ⊗ Z ≅ X ⊗ (Y ⊗ Z) := make_bijection (tensor_assoc_l X Y Z).
Canonical Structure tensor_assoc_r_bijection X Y Z : X ⊗ (Y ⊗ Z) ≅ X ⊗ Y ⊗ Z := make_bijection (tensor_assoc_r X Y Z).

Canonical Structure prod_assoc_l_bijection X Y Z : X × Y × Z ≅ X × (Y × Z) := make_bijection (prod_assoc_l X Y Z).
Canonical Structure prod_assoc_r_bijection X Y Z : X × (Y × Z) ≅ X × Y × Z := make_bijection (prod_assoc_r X Y Z).

Canonical Structure tensor_unit_l_bijection X : 𝟏 ⊗ X ≅ X := make_bijection (tensor_unit_l X).
Canonical Structure tensor_unit_r_bijection X : X ⊗ 𝟏 ≅ X := make_bijection (tensor_unit_r X).

Canonical Structure tensor_swap_tail_bijection X Y Z : X ⊗ Y ⊗ Z ≅ X ⊗ Z ⊗ Y := make_bijection (tensor_swap_tail X Y Z).

Canonical Structure tensor_injection_op@{i} {X₁ X₂ Y₁ Y₂: set@{i}} (f₁:injection X₁ Y₁) (f₂:injection X₂ Y₂)
  := make_injection ⟨f₁, f₂⟩.
Definition tensor_injection@{i} {X₁ X₂ Y₁ Y₂: set@{i}} := make_projected_op (@tensor_injection_op X₁ X₂ Y₁ Y₂) tensor_map_op.

Canonical Structure tensor_surjection_op@{i} {X₁ X₂ Y₁ Y₂: set@{i}} (f₁:surjection X₁ Y₁) (f₂:surjection X₂ Y₂)
  := make_surjection ⟨f₁, f₂⟩.
Definition tensor_surjection@{i} {X₁ X₂ Y₁ Y₂: set@{i}} := make_projected_op (@tensor_surjection_op X₁ X₂ Y₁ Y₂) tensor_map_op.

Canonical Structure tensor_bijection_op@{i} {X₁ X₂ Y₁ Y₂: set@{i}} (f₁:X₁ ≅ Y₁) (f₂:X₂ ≅ Y₂) : X₁ ⊗ X₂ ≅ Y₁ ⊗ Y₂
  := make_bijection ⟨f₁, f₂⟩.
Definition tensor_bijection@{i} {X₁ X₂ Y₁ Y₂: set@{i}} := make_projected_op (@tensor_bijection_op X₁ X₂ Y₁ Y₂) tensor_map_op.

(*
Section test.
  Universes i.
  Context (X Y Z : set@{i}).
  Context (g: Y ≅ Z) (f:X ≅ Y).
  Check (id : X ≅ X).
  Check (g ∘ f : X ≅ Z).
  Check (f⁻¹ : Y ≅ X).
  Check ⟨f, g⟩ : X ⊗ Y ≅ Y ⊗ Z.
*)


