# affine-constructive-maths

A library of constructive mathematics in the [Rocq](https://rocq-prover.org) prover, written in affine logic
following Michael Shulman's *Affine logic for constructive mathematics*.[^shulman]
Its design owes much to the [Math Classes](https://github.com/coq-community/math-classes) library.

Shulman observes that the dual pairs constructive mathematicians keep track of by hand
(equality and apartness, subgroups and antisubgroups, open and closed sets) arise
automatically if one writes classical definitions in affine logic and reads them through
his *antithesis* translation. Here that translation is the implementation: an affine
proposition is a pair of an `SProp` proof condition and an `SProp` refutation condition
that cannot both hold, and every set carries an equality valued in these propositions.
So each set comes with an inequality, each function is strongly extensional, each subset
is complemented, and each preorder induces a strict order, with no extra bookkeeping.

The library follows the paper through propositional and first-order affine logic, sets,
algebra (groups, rings, fields), order theory, and the naturals and integers, and then
continues into topology: uniform spaces, bornologies, and a Bishop-style theory of
continuity between open subsets, with the associated completion constructions.

| directory | contents |
|---|---|
| `interfaces/` | the logic (`sprop.v`, `aprop.v`), sets, and the typeclass hierarchies |
| `logic/` | theorems about the affine connectives, decidability, refutative reasoning |
| `tactics/` | a rewriting system for affine implications, decision procedures, internalization of lambda terms as set morphisms |
| `theory/`, `orders/` | sets, groups, rings, lattices, orders, naturals and integers |
| `implementations/` | concrete models: booleans, naturals, lists, free structures, integers |
| `topology/` | uniform spaces, bornologies, localization, completions |
| `counterexamples/` | independence results, valid in the antithesis model only |

The development is self-contained. It is compiled with `-nois` and does not use the Rocq
standard library.

## Building

The library needs an unreleased Rocq. Two things are missing from every released version:

1. **Algebraic universes**, from Matthieu Sozeau's experimental
   [`universes-clauses-on-master`](https://github.com/mattam82/coq/tree/universes-clauses-on-master)
   kernel branch.
2. A fix to the relevance of identity coercions into `SProp`
   ([rocq-prover/rocq#21858](https://github.com/rocq-prover/rocq/pull/21858)). It is merged
   upstream, but it landed after that branch forked from master.

The exact tree that builds this library, the branch tip plus that one commit cherry-picked
on top, is hosted at
[`jlottes/rocq`, branch `universes-clauses-on-master+sprop-fix`](https://github.com/jlottes/rocq/tree/universes-clauses-on-master+sprop-fix).
It reports itself as `9.2+alpha`.

Why algebraic universes: the library is universe polymorphic throughout and pervasively
*uncurried*. A set's equality is a map out of the product `X ∗ X`, a binary operation is a
morphism out of the tensor product, `X ⊗ X ⇾ X`, and every further structure is stacked on
top of such maps. Without algebraic universes each product, tensor, and morphism type
receives a fresh universe variable constrained by the levels of its components, and every
use of a polymorphic constant instantiates all of them again, so the number of universe
variables and constraints grows with each layer of packaging until elaboration and
typeclass resolution become impractical. With algebraic universes the intermediate levels
are just `max(u,v)` and no fresh variables are introduced; compare `tprod` in
`interfaces/prelude.v`.

To build, starting from an [opam](https://opam.ocaml.org) installation:

```sh
opam switch create affine ocaml-base-compiler.4.14.2
eval $(opam env --switch=affine --set-switch)
opam pin add -y rocq-runtime.dev "git+https://github.com/jlottes/rocq.git#universes-clauses-on-master+sprop-fix"
opam pin add -y rocq-core.dev    "git+https://github.com/jlottes/rocq.git#universes-clauses-on-master+sprop-fix"

git clone https://github.com/jlottes/affine-constructive-maths.git
cd affine-constructive-maths
rocq makefile -f _RocqProject -o Makefile
make -j
```

Only `rocq-core` and `rocq-runtime` are needed; the library uses no other opam packages.
Tested with OCaml 4.14.2.

### Classical conservativity check

The affine connectives are built over a small kernel, `interfaces/aprop_kernel.v`, whose
`Classicality` field is trivial in the default build. `classical/aprop_kernel.v` is a
drop-in replacement in which that field is decidability, derived from an `SProp`-level
excluded-middle axiom; under it the antithesis model collapses to classical logic.

```sh
scripts/classical-build.sh
```

rebuilds everything except `counterexamples/` against the classical kernel in an isolated
tree under `.build/classical/`, and additionally compiles `classical/sanity.v`, which
proves the internal law of excluded middle there. Everything that compiles in both builds
is a theorem of classical mathematics as well; the files in `counterexamples/` are exactly
those that must fail against the classical kernel.

## License

[MIT](LICENSE).

[^shulman]: Michael Shulman. Affine logic for constructive mathematics.
    *Bulletin of Symbolic Logic* 28(3):327–386, 2022.
    [doi:10.1017/bsl.2022.28](https://doi.org/10.1017/bsl.2022.28),
    [arXiv:1805.07518](https://arxiv.org/abs/1805.07518).
