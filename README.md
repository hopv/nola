# Nola: Power of Deep Embedding for Later-free Impredicative Invariants

Nola is a library for achieving expressive later-free impredicative invariants by the power of deep embedding.
It is fully mechanized in [Coq](https://coq.inria.fr/) with the [Iris](https://iris-project.org/) separation logic framework.

The name Nola comes from *No* *la*ters.
Incidentally, it is also a nickname for New Orleans.

- [Getting Started](#getting-started)
- [Story](#story)
  - [Semantic Sharing](#semantic-sharing)
  - [Obstacle: Laters](#obstacle-laters)
  - [Solution: Nola](#solution-nola)

## Getting Started

We use [opam](https://opam.ocaml.org/) ver 2.* for package management.

To set up an [opam switch](https://opam.ocaml.org/doc/man/opam-switch.html) named `nola` and link it to the folder:
```bash
opam switch create nola 5.0.0 # Choose an OCaml version
opam switch link nola .
```

To set up opam repos for Coq and Iris for the current opam switch:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

To fix development dependencies and compile Coq code:
```bash
make devdep
make -j16 # Choose a job number
```

Or to install as a library locally:
```bash
opam install .
```

To generate and browse a document:
```bash
make viewdoc
```

## Architecture

All the Coq code is in [`nola/`](nola/) and structured as follows:
- [`prelude`](nola/prelude.v) : Prelude
- [`util/`](nola/util/) : General-purpose utilities,
  extending [`stdpp`](https://gitlab.mpi-sws.org/iris/stdpp)
  + [`funext`](nola/util/funext.v) (Function extensionality),
    [`pred`](nola/util/pred.v) (Predicates),
    [`rel`](nola/util/rel.v) (Relations),
    [`wft`](nola/util/wft.v) (Well-founded types),
    [`list`](nola/util/list.v) (Lists)
- [`hgt`](nola/hgt.v) (General height of a tree),
  [`ctx`](nola/ctx.v) (Context with unguarded/guarded variables)
- [`sintp`](nola/sintp.v) (Strong interpretation)
- [`iris/`](nola/iris) : Iris libraries
  + [`fupd`](nola/iris/fupd.v) (Fancy update),
    [`wp`](nola/iris/wp.v) (Weakest precondition)
  + [`inv`](nola/iris/inv.v) (Invariant)
- [`examples/`](nola/examples/) : Examples
  + [`heap_lang/`](nola/examples/heap_lang/) : Variant of Iris HeapLang,
    with `Ndnat` (terminating infinite non-determinism) added
  + [`logic/`](nola/examples/logic/) : Nola Showcase Logic
    - [`prop`](nola/examples/logic/prop.v) (Proposition),
      [`subst`](nola/examples/logic/subst.v) (Substitution),
      [`iris`](nola/examples/logic/iris.v) (Iris preliminaries),
      [`intp`](nola/examples/logic/intp.v) (Interpretation),
      [`sintp`](nola/examples/logic/sintp.v) (Strong interpretation),
      [`inv`](nola/examples/logic/inv.v) (Invariant),
      [`facts`](nola/examples/logic/facts.v) (Facts)

## Story

### Semantic Sharing

We give a name *semantic sharing*
to sharing of mutable state under a protocol expressed by a separation-logic proposition `P` created dynamically.
Such sharing has been essential in the modern usage of separation logic.

#### Examples

One example is a shared invariant `inv N P : iProp`
in the separation logic [Iris](https://iris-project.org/).
Using this, we can *share* some mutable state, expressed by a separation-logic proposition `P: iProp`, across threads.

Another example is a full borrow `&{κ} P : iProp`,
of [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)'s lifetime logic in Iris,
for modeling a mutable borrow `&'a mut T` in [Rust](https://www.rust-lang.org/).
Using this, we can borrow, during the lifetime `κ`, some mutable state expressed by an Iris proposition `P: iProp`,
returned to the lender after `κ` ends.
Although the lifetime `κ` separates access to the mutable state,
the borrower and lender still *share* information about `P`.

### Obstacle: Laters

#### Step-Indexing

All the existing separation logics with semantic sharing,
such as [iCAP](https://www.cs.au.dk/~birke/papers/icap-conf.pdf) and Iris,
resort to *step-indexing*.
It is the technique of layering the logic world with step-indices `0, 1, 2, …: ℕ`,
having notions more defined as the step-index grows.
Why?

Their separation-logic proposition `iProp` is a predicate over an abstract resource `Res`.
For semantic sharing, `Res` should be able to model agreement on propositions.
So they define `Res` as some data type depending on `iProp`.
Naively, they have a domain equation like the following,
which is a *circular* definition:
```
iProp  ≜  Res → Prop     Res  ≜  F iProp
```
So they used step-indexing to make this solvable, like:
```
iProp  ≜  Res → sProp     Res  ≜  F (▶ iProp)
```
Here, `sProp` is a step-indexed proposition `ℕ →anti Prop`
and `▶` delays the definition of a data type by one step-index.

#### Laters in the Way

Sounds fine? But this comes with the cost of the *later modality* `▷`.

Due to `▶` added to `iProp`, we can use semantic sharing only for propositions under `▷`,
which delays the definition of a proposition by one step-index.
```
inv N P ={↑N,∅}=> ▷ P ∗ (▷ P ={∅,↑N}=∗ True)
```
This causes significant practical issues, especially for dealing with nested semantic sharing.

The later modality `▷` is ill-behaved: it is non-idempotent and doesn't commute with the update modality `|==>`.
Various efforts, such as [later credits](https://plv.mpi-sws.org/later-credits/), have been made to manage `▷`, but it is still hard to use.

More fundamentally, the power to strip off `▷` makes program predicates weaker,
ensuring only safety properties (absence of bad behaviors witnessed by finite steps),
but not liveness properties (absence of bad behaviors witnessed only by an infinite execution).
Indeed, [Simuliris](https://iris-project.org/pdfs/2022-popl-simuliris.pdf) just gave up *semantic sharing* in its program logic built in Iris for fair termination preservation, a rich liveness property.

### Solution: Nola

Nola achieves a form of semantic sharing without laters!

We no longer suffer from the later modality `▷` and can do advanced liveness verification like Simuliris.
And at the same time, we can use shared invariants and full borrows, for flexible reasoning.

#### Core Idea: Syntax

To achieve semantic sharing, Nola uses *syntax* `A` equipped with a semantic interpretation as a separation-logic proposition `⟦ ⟧ : A → iProp`.
Now we have broken the circular definition because the resource `Res` for a semantic proposition `iProp` depends just on `A`, like:
```
iProp  ≜  Res → Prop     Res  ≜  F A     ⟦ ⟧ : A → iProp
```
Easy!
