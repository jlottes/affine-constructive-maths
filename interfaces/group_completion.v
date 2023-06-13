Require Import abstract_algebra bundled_algebra.

Section definition.
  Universes i.
  Context `{AdditiveMonoid@{i} M} `{AdditiveGroup@{i} K}.

  Class FromGroupCompletion (i:M ⇾ K) := from_group_completion
    : ∀ {A:additive_non_com_group@{i}} (f:M ⇾ A) `{!AdditiveMonoid_Morphism f}, (K ⇾ A).
  Global Arguments from_group_completion i {_ A} f {_}.

  Class FromGroupCompletionProp (i:M ⇾ K)
    {A:additive_non_com_group@{i}} (f : M ⇾ A) (g : K ⇾ A) : SProp :=
  { from_group_completion_mor : AdditiveMonoid_Morphism g
  ; from_group_completion_spec : g ∘ i = f
  ; from_group_completion_unique (h : K ⇾ A) `{!AdditiveMonoid_Morphism h} : h ∘ i = f → h = g
  }.

  Class GroupCompletion (i:M ⇾ K) {U:FromGroupCompletion i} : SProp :=
  { group_completion_src : AdditiveMonoid M
  ; group_completion_dst : AdditiveGroup K
  ; group_completion_mor : AdditiveMonoid_Morphism i
  ; from_group_completion_prop {A:additive_non_com_group@{i}} (f : M ⇾ A) `{!AdditiveMonoid_Morphism f}
    : FromGroupCompletionProp i f (from_group_completion i f)
  }.
End definition.
Coercion group_completion_src : GroupCompletion >-> AdditiveMonoid.
Coercion group_completion_mor : GroupCompletion >-> AdditiveMonoid_Morphism.
