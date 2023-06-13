Require Import abstract_algebra interfaces.bundled_algebra interfaces.free.generators.
Require Import nat list.
Require Import strip_coercions.

Module free_additive_monoid.
  Import definition_hints.
  Record t :=
  { car :> additive_monoid
  ; #[canonical=no] var :> has_var car
  ; #[canonical=no] dec_eq :> has_dec_eq car
  ; #[canonical=no] is_dec_eq :> IsDecEq car
  }.
  Global Hint Extern 2 (StripCoercions (car ?F)) => strip_coercions_chain F : strip_coercions.

  Canonical Structure to_var_set (F:t) := make_var_set F.
  Coercion to_var_set : t >-> var_set.
  Global Hint Extern 2 (StripCoercions (to_var_set ?X)) => strip_coercions_chain X : strip_coercions.

  Set Implicit Arguments.
  Record mor (F:t) {M:additive_monoid} (Γ:list M) :=
  { mor_f :> additive_non_com_monoid_morphism_t F M
  ; #[canonical=no] mor_prop :> Var_Morphism Γ mor_f
  }.
  Unset Implicit Arguments.
  Global Hint Extern 2 (StripCoercions (mor_f ?f)) => strip_coercions_chain f : strip_coercions.

  Canonical Structure to_var_mor `(f:mor F (M:=M) Γ) : var_morphism_t F Γ := make_var_morphism Γ f.
  Global Coercion to_var_mor : mor >-> var_morphism_t.
  Global Hint Extern 2 (StripCoercions (to_var_mor ?f)) => strip_coercions_chain f : strip_coercions.

  Record F :=
  { X :> t
  ; #[canonical=no] eval : ∀ {M:additive_monoid} (Γ:list M), mor X Γ
  }.
End free_additive_monoid.
Notation free_additive_monoid := free_additive_monoid.F.

Global Coercion free_additive_monoid.car : free_additive_monoid.t >-> additive_monoid.
Global Coercion free_additive_monoid.var : free_additive_monoid.t >-> has_var.
Global Coercion free_additive_monoid.dec_eq : free_additive_monoid.t >-> has_dec_eq.
Global Coercion free_additive_monoid.is_dec_eq : free_additive_monoid.t >-> IsDecEq.
Global Coercion free_additive_monoid.to_var_set : free_additive_monoid.t >-> var_set.
Global Coercion free_additive_monoid.mor_f : free_additive_monoid.mor >-> additive_non_com_monoid_morphism_t.
Global Coercion free_additive_monoid.mor_prop : free_additive_monoid.mor >-> Var_Morphism.
Global Coercion free_additive_monoid.to_var_mor : free_additive_monoid.mor >-> var_morphism_t.
Global Coercion free_additive_monoid.X : free_additive_monoid.F >-> free_additive_monoid.t.



Module free_commutative_monoid.
  Import definition_hints.
  Record t :=
  { car :> commutative_monoid
  ; #[canonical=no] var :> has_var car
  ; #[canonical=no] dec_eq :> has_dec_eq car
  ; #[canonical=no] is_dec_eq :> IsDecEq car
  }.
  Global Hint Extern 2 (StripCoercions (car ?F)) => strip_coercions_chain F : strip_coercions.

  Canonical Structure to_var_set (F:t) := make_var_set F.
  Coercion to_var_set : t >-> var_set.
  Global Hint Extern 2 (StripCoercions (to_var_set ?X)) => strip_coercions_chain X : strip_coercions.

  Set Implicit Arguments.
  Record mor (F:t) {M:commutative_monoid} (Γ:list M) :=
  { mor_f :> monoid_morphism_t F M
  ; #[canonical=no] mor_prop :> Var_Morphism Γ mor_f
  }.
  Unset Implicit Arguments.
  Global Hint Extern 2 (StripCoercions (mor_f ?f)) => strip_coercions_chain f : strip_coercions.

  Canonical Structure to_var_mor `(f:mor F (M:=M) Γ) : var_morphism_t F Γ := make_var_morphism Γ f.
  Global Coercion to_var_mor : mor >-> var_morphism_t.
  Global Hint Extern 2 (StripCoercions (to_var_mor ?f)) => strip_coercions_chain f : strip_coercions.

  Record F :=
  { X :> t
  ; #[canonical=no] eval : ∀ {M:commutative_monoid} (Γ:list M), mor X Γ
  }.
End free_commutative_monoid.
Notation free_commutative_monoid := free_commutative_monoid.F.

Global Coercion free_commutative_monoid.car : free_commutative_monoid.t >-> commutative_monoid.
Global Coercion free_commutative_monoid.var : free_commutative_monoid.t >-> has_var.
Global Coercion free_commutative_monoid.dec_eq : free_commutative_monoid.t >-> has_dec_eq.
Global Coercion free_commutative_monoid.is_dec_eq : free_commutative_monoid.t >-> IsDecEq.
Global Coercion free_commutative_monoid.to_var_set : free_commutative_monoid.t >-> var_set.
Global Coercion free_commutative_monoid.mor_f : free_commutative_monoid.mor >-> monoid_morphism_t.
Global Coercion free_commutative_monoid.mor_prop : free_commutative_monoid.mor >-> Var_Morphism.
Global Coercion free_commutative_monoid.to_var_mor : free_commutative_monoid.mor >-> var_morphism_t.
Global Coercion free_commutative_monoid.X : free_commutative_monoid.F >-> free_commutative_monoid.t.



Module free_additive_group.
  Import definition_hints.
  Record t :=
  { car :> additive_group
  ; #[canonical=no] var :> has_var car
  ; #[canonical=no] dec_eq :> has_dec_eq car
  ; #[canonical=no] is_dec_eq :> IsDecEq car
  }.
  Global Hint Extern 2 (StripCoercions (car ?F)) => strip_coercions_chain F : strip_coercions.

  Canonical Structure to_var_set (F:t) := make_var_set F.
  Coercion to_var_set : t >-> var_set.
  Global Hint Extern 2 (StripCoercions (to_var_set ?X)) => strip_coercions_chain X : strip_coercions.

  Set Implicit Arguments.
  Record mor (F:t) {G:additive_group} (Γ:list G) :=
  { mor_f :> additive_non_com_monoid_morphism_t F G
  ; #[canonical=no] mor_prop :> Var_Morphism Γ mor_f
  }.
  Unset Implicit Arguments.
  Global Hint Extern 2 (StripCoercions (mor_f ?f)) => strip_coercions_chain f : strip_coercions.

  Definition to_var_mor `(f:mor F (G:=G) Γ) : var_morphism_t F Γ := make_var_morphism Γ f.
  Global Coercion to_var_mor : mor >-> var_morphism_t.
  Global Hint Extern 2 (StripCoercions (to_var_mor ?f)) => strip_coercions_chain f : strip_coercions.

  Record F :=
  { X :> t
  ; #[canonical=no] eval : ∀ {G:additive_group} (Γ:list G), mor X Γ
  }.
End free_additive_group.
Notation free_additive_group := free_additive_group.F.

Global Coercion free_additive_group.car : free_additive_group.t >-> additive_group.
Global Coercion free_additive_group.var : free_additive_group.t >-> has_var.
Global Coercion free_additive_group.dec_eq : free_additive_group.t >-> has_dec_eq.
Global Coercion free_additive_group.is_dec_eq : free_additive_group.t >-> IsDecEq.
Global Coercion free_additive_group.to_var_set : free_additive_group.t >-> var_set.
Global Coercion free_additive_group.mor_f : free_additive_group.mor >-> additive_non_com_monoid_morphism_t.
Global Coercion free_additive_group.mor_prop : free_additive_group.mor >-> Var_Morphism.
Global Coercion free_additive_group.to_var_mor : free_additive_group.mor >-> var_morphism_t.
Global Coercion free_additive_group.X : free_additive_group.F >-> free_additive_group.t.


