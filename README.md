# Nola: Deep-Embed Separation Logic to Wipe Laters Out

Nola is a new approach to propositional sharing
in non-step-indexed separation logic.
It is fully mechanized in [Coq](https://coq.inria.fr/) with the [Iris](https://iris-project.org/) separation logic framework.

The name Nola comes from *No* *la*ters.
It is also a nickname for New Orleans, a city I like.

- [Propositional Sharing](#propositional-sharing)
- [Nightmare: Step-Indexing](#nightmare-step-indexing)
- [Solution: Nola](#solution-nola)
- [Getting Started](#getting-started)

## Propositional Sharing

We give a name *propositional sharing*
to sharing of mutable state under a protocol expressed by a separation-logic proposition `P` created dynamically.

Such sharing has been essential in the modern usage of separation logic.

### Examples

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

## Nightmare: Step-Indexing

Step-indexing is layering the logic world with step-indices `0, 1, 2, …: ℕ`,
having notions more defined as the index grows.

Existing separation logics with propositional sharing,
such as [iCAP](https://www.cs.au.dk/~birke/papers/icap-conf.pdf) and Iris,
depend on step-indexing.

### Why?

Why do such separation logics resort to step-indexing?

Their separation-logic proposition `iProp` is a predicate over an abstract resource `Res`.
For propositional sharing, `Res` should be able to model agreement on propositions.
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

### Problems

Sounds fine? But this comes with costs.

First, we suffer from the later modality `▷`, which is non-idempotent and doesn't commute with the fancy update modality `|==>`.
Despite efforts like [later credits](https://plv.mpi-sws.org/later-credits/), it is still hard to manage.

More fundamentally, step-indexing is at odds with liveness verification.
Roughly speaking, the later modality `▷` automatically makes predicates on programs coinductive,
while liveness verification calls for inductive predicates.

Indeed, [Simuliris](https://iris-project.org/pdfs/2022-popl-simuliris.pdf) uses Iris<sup>light</sup>, a non-step-indexed variant of Iris, to construct a predicate for fair termination preservation, defined as a mixed fixed point.

### Paradox

Can't we have propositional sharing without step-indexing?
That was believed impossible because of a known paradox for a naive shared invariant without the later modality.

At the high level, the paradox corresponds to a folklore technique called Landin's knot,
causing a program loop using a shared mutable reference over the arrow type `evil: (unit -> unit) ref`:
```ocaml
let evil = ref (fun _ -> ()) in
evil := (fun _ -> !evil ());
!evil ()
```

## Solution: Nola

Nola achieves propositional sharing without step-indexing!

We no longer suffer from the later modality `▷` and can do advanced liveness verification like Simuliris.
And at the same time, we can use propositional sharing, like shared invariants and full borrows, for flexible reasoning.

### Core Idea

Separation logics like iCAP and Iris are fully semantic, using no syntax for propositions.

Instead, Nola introduces a closed-world *syntax* `nProp` for propositions and judgments over `nProp`.
Then we interpret Nola's syntactic separation logic in a semantic separation logic, Iris<sup>light</sup>.
Now we have broken the circular definition
because the resource `Res` for a semantic proposition `iProp` depends just on `nProp`, like:
```
iProp  ≜  Res → Prop     Res  ≜  F nProp
```
Then we give an interpretation `⟦ ⟧ : nProp → iProp`
and prove the soundness of the syntactic logic for the semantics.
Easy!

### Avoiding the Paradox

For soundness, Nola imposes a syntactic restriction:
roughly, we can't use the fancy update modality `|=[W]=>` in the proposition `P` of a shared invariant `inv N P`, full borrow `&{κ} P`, etc.

That amounts to restricting shared mutable references containing the arrow type, like `evil: (unit -> unit) ref`,
liberating Nola from the paradox analogous to Landin's knot.

### Infinite Propositions

A Nola proposition `P : nProp` can have an infinite syntax tree,
which helps construct assertions for infinite data structures.
To reason about such infinite syntax, we take advantage of parameterized coinduction by [Paco](https://plv.mpi-sws.org/paco/).

### Hacking Coq & Iris

Nola is fully mechanized in Coq with the Iris framework.
Nola's semantics is constructed in Iris<sup>light</sup>.
Also, reasoning about Nola's syntactic logic is accelerated
with a variant of [Iris Proof Mode](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf).

## Getting Started

We use [opam](https://opam.ocaml.org/) ver 2.* for package management.

To set up an [opam switch](https://opam.ocaml.org/doc/man/opam-switch.html) for Nola and link it to the folder:
```bash
opam switch create nola 4.14 # Choose an OCaml version
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
