(** * ATop does not have binary products.

    The existence of cartesian products of arbitrary affine topological
    spaces is refutable in the antithesis model, and the factor can be
    taken to be a strong set:

      [products_imply_False] : "every pair of affine topological spaces
      has a cartesian product satisfying the universal property of
      [CartesianProductTopology]" is contradictory.

    This justifies the design of [CartesianProductTopology] as a
    certificate that *a particular* product exists (e.g. for
    uniformizable topologies), rather than as a construction.

    ** The space [X]

    Three points [x], [x'], [y].  The equality has [(x = x') = (0,0)],
    the pair proved by nothing and refuted by nothing, and the other two
    off-diagonal equalities [𝐅]: [x] and [x'] are neither equal nor
    apart, and [y] is apart from both.  Such pairs are unavoidable in
    the antithesis model: "not both" is the only compatibility condition
    closed under the Chu-construction connectives (cf. Shulman §3).  The
    inequality is cotransitive, so [X] is a strong set ([X_strong]); its
    equality is not refutative.

    The topology,

      [z ⪽ U  :=  z ∊ U ∧ (z = x ∨ y ∊ U)],

    makes [x] and [y] isolated while every neighborhood of [x'] contains
    [y].  Built from additive connectives only, it is a set morphism for
    free, and the topology axioms close by [tautological].  The pair
    [(0,0)] is what makes it work: at [x'] the disjunction is affirmed
    only through [y ∊ U], but refuting it would require refuting
    [x' = x], which is impossible.  So [x' ⪽ U] is refuted only by
    [x' ∊̸ U], never through [y].  (Defining the neighborhoods by cases,
    [x' ∊ U ∧ y ∊ U] at [x'] and [x ∊ U] at [x], would not be a morphism:
    [{x}] would be a neighborhood of [x] and refutably not one of [x'].)

    ** The argument

    Let [τ] be a topology on [X × X] with the universal property of
    [CartesianProductTopology], and let [M := {(x,x)}].

    1. [τ] affirms [M] at [(x,x)]: the projections are continuous, [x]
       is isolated, and binary additivity's positive component is a
       plain conjunction.
    2. [τ] refutes [M] at [(x',x')]: the comparison map [X ⊗ X ⇾ X × X]
       is continuous by the universal property, and the tensor topology
       refutes [M] at [(x',x')] uniformly in the basic box, since
       [(y,y)] lies in every box around [(x',x')] and is apart from
       [(x,x)].
    3. [p ↦ p ⪽ M] is a *morphism* [X × X ⇾ Ω], so strong
       extensionality turns the affirmation at [(x,x)] and the
       refutation at [(x',x')] into the additive inequality
       [(x,x) ≠ (x',x')], which is [⊥ ∨ ⊥].

    ** Scope

    Fixing the carrier of a product to the cartesian product of sets
    loses no generality, since the forgetful functor ATop → ASet has a
    left adjoint and so preserves limits.  As [X] is a strong set,
    products already fail on the subcategory of strong sets; the
    remaining question is refutative (tight) equalities, where this
    argument does not apply: tightness would affirm [x = x'], and step 2
    needs its positive part to be [⊥].  Uniformizable spaces do have
    products, so the topology on [X] is not uniformizable.

    Nothing below inspects the second component of [(0,0)]: with any
    pair [(0,Q)] in the slot [(x = x')] the same proofs go through and
    the final inequality becomes [Q ∨ Q], so the existence of that one
    product already implies [Q].  For [Q] an instance of WLEM this is
    the Brouwerian reading (not formalized). *)

Require Import interfaces.set interfaces.sprop logic.aprop set_lambda.
Require Import interfaces.subset interfaces.topology.
Require Import theory.set orders.subset topology.product.
Require Import rewrite easy simplify.

Local Open Scope topology_scope.

(** * The three-point set [X] *)

Inductive pt : Set := x | x' | y.

(** The pair [(0,0)]: proved by nothing, refuted by nothing. *)

Definition zero_zero : Ω := Build_AProp (full_tautology : NotBoth False False) I.

(** [x = x'] is the pair [(0,0)]; everything else off the diagonal is
    refuted outright. *)

Definition pt_equiv : Equiv pt := λ '(z, w),
  match z, w with
  | x, x | x', x' | y, y => 𝐓
  | x, x' | x', x => zero_zero
  | _, _ => 𝐅
  end.

Lemma pt_is_set : IsSet pt (e:=pt_equiv).
Proof. split.
+ now intros [].
+ now intros [][].
+ intros [][][]; cbn; tautological.
Qed.

Canonical Structure X : set := @set_make pt pt_equiv pt_is_set.

(** [X] is even a strong set: its inequality is cotransitive. *)

Lemma X_strong : StrongSet X.
Proof. intros [][][]; cbn; tautological. Qed.

(** * The topology *)

Local Instance X_nb : Neighborhood X :=
  set:(λ '(z, U) : X ⊗ 𝒫 X, z ∊ U ∧ (z = x ∨ y ∊ U)).

Local Ltac unfold_nb := change (?z ⪽ ?U) with (z ∊ U ∧ (z = x ∨ y ∊ U)).

Local Instance X_topology : Topology X.
Proof. split.
+ intros z U; unfold_nb; tautological.
+ intros z U V; unfold_nb.
  apply aand_intro; change (U ⊆ V) with (∏ w, w ∊ U ⊸ w ∊ V).
  - rew (all_lb _ z). tautological.
  - rew (all_lb _ y). tautological.
+ intros z. change (𝐓 ∧ (z = x ∨ 𝐓)). tautological.
+ intros z U V; unfold_nb. change (?z ∊ U ⊓ V) with (z ∊ U ∧ z ∊ V). tautological.
+ intros z U. change (z ∊ U ∧ (z = x ∨ y ∊ U)
    ⊸ (z ∊ U ∧ (z = x ∨ y ∊ U)) ∧ (z = x ∨ (y ∊ U ∧ (y = x ∨ y ∊ U)))).
  tautological.
Qed.

(** Strong extensionality, harvested: an Ω-valued map that affirms at [w]
    and refutes at [z] forces the inequality [w ≠ z].  Applied to the
    neighborhood map [p ↦ p ⪽ M], a bona fide morphism, it converts an
    affirmation/refutation pair into an *additive* disjunction of
    inequalities. *)

Lemma apos_aneg_apart {A:set} (P : A ⇾ Ω) (z w : A) :
  P w ⊠ (P z)ᗮ ⊸ w ≠ z.
Proof. rew (is_fun P w z). change (P w = P z) with (P w ⧟ P z). tautological. Qed.

(** * The product refutation *)

Local Open Scope fun_inv_scope.
Import image_notation.

(** The witness subset: the singleton of [(x,x)].  Pointwise it is the
    box [p₁*{x} ⊓ p₂*{x}], which is how the continuity of the projections
    sees it. *)

Definition M : 𝒫 (X × X) := singleton ((x, x) : X × X).

(** The tensor topology refutes [c* M] at [(x',x')], uniformly in the
    basic box [(U, V)]: [(y,y)] lies in every box around [(x',x')] and is
    apart from [(x,x)]; and the mixed pairs [(y,x')], [(x',y)], also
    apart from [(x,x)], transfer refutations back through the box. *)

Local Abbreviation β := (tensor_product_neighborhood_basis X_nb X_nb). 

Lemma req1 : ((x', x') ⪽ (tensor_to_prod X X)* M)ᗮ.
Proof.
  change (∏ W, (x', x') ∊ β W ⊸ ∐ p, p ∊ β W ⊠ (x, x) ≠ p :> X × X).
  intros [U V].
  rew <-(aor_elim (aex_ub _ (y, y)) (aor_elim (aex_ub _ (y, x')) (aex_ub _ (x', y)))).
  change ((?a, ?b) ∊ β (U, V)) with (a ⪽ U ⊠ b ⪽ V).
  unfold_nb; cbn; tautological.
Qed.

(** Any product topology on [X × X] affirms [M] at [(x,x)] and refutes
    it at [(x',x')]; strong extensionality of the neighborhood map then
    yields [(x,x) ≠ (x',x')], which is [⊥ ∨ ⊥]. *)

Theorem product_UP_False {NXX : Neighborhood (X × X)}
  (H : CartesianProductTopology (X:=X) (Y:=X) NXX) : False.
Proof.
  assert (pA : ((x, x) : X × X) ⪽ M).
  { change M with ((prod_proj1 X X)* (singleton x) ⊓ (prod_proj2 X X)* (singleton x)).
    rew <-(top_binary_additivity _ _ _).
    rew [<-(continuity (prod_proj1 X X) _ _)|<-(continuity (prod_proj2 X X) _ _)].
    change (x ⪽ singleton x ⊠ x ⪽ singleton x).
    unfold_nb. change (?a ∊ singleton ?b) with (b = a :> X). cbn. tautological. }
  assert (nB : (tensor_to_prod X X (x', x') ⪽ M)ᗮ).
  { rew (continuity (tensor_to_prod X X) _ _). exact req1. }
  destruct (aimpl_impl_pos (apos_aneg_apart (set:(λ p : X × X, p ⪽ M)) ((x', x') : X × X) ((x, x) : X × X)) (conj pA nB)) as [[]|[]].
Qed.

Theorem products_imply_False :
  (∀ `{@Topology A NA, @Topology B NB}, ∃ NAB, @CartesianProductTopology A B NA NB NAB) → False.
Proof. intros P.
  destruct (P _ X_nb X_topology _ X_nb X_topology) as [NXX H].
  exact (product_UP_False H).
Qed.
