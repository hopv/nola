# Noix: Propositional Sharing without Step-Indexing

Noix is a new approach to propositional sharing
in non-step-indexed separation logic.
It is fully mechanized in [Coq](https://coq.inria.fr/) with the [Iris](https://iris-project.org/) separation logic framework.

The name Noix comes from English *NO IndeX* and French [*noix*](https://en.wiktionary.org/wiki/noix) for a nut.
Its pronunciation is /nwa/ (like noir without r).
Isn't it cute?

## Propositional Sharing

By propositional sharing, we mean *sharing* of mutable state
under a protocol expressed by *separation-logic propositions* `P`.
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

## Step-Indexing

Step-indexing is layering the logic world with step-indices `0, 1, 2, …: ℕ`,
having notions more defined as the index grows.
Existing separation logics with propositional sharing,
such as [iCAP](https://www.cs.au.dk/~birke/papers/icap-conf.pdf) and Iris,
depend on step-indexing.

### Why Need It?

Why do such separation logics need step-indexing?
Their separation-logic proposition `iProp` is a predicate over an abstract resource `Res`.
For propositional sharing, `Res` should be able to model agreement on propositions.
So they define `Res` as some data type depending on `iProp`.
Naively, they have a domain equation like:
```
iProp  ≜  Res → Prop       Res  ≜  F iProp
```
Alas, this is a circular definition!
They make this solvable using step-indexing, like:
```
iProp  ≜  Res → sProp      Res  ≜  F (▶ iProp)
```
Here, `sProp` is a step-indexed proposition `ℕ →anti Prop`
and `▶` delays the definition of a data type by one step-index.

### Problems

Sounds fine? But this comes with costs.

First, we suffer from the later modality `▷`, which is non-idempotent and doesn't commute with the fancy update modality `|==>`.
Despite efforts like [later credits](https://plv.mpi-sws.org/later-credits/), it is still hard to manage.

More fundamentally, step-indexing is at odds with liveness verification.
Roughly speaking, the later modality `▷` automatically makes predicates on programs the greatest fixed points,
while liveness verification involves the least or mixed fixed points.

Indeed, [Simuliris](https://iris-project.org/pdfs/2022-popl-simuliris.pdf) uses Iris<sup>light</sup>, a non-step-indexed variant of Iris, to construct a predicate for fair termination preservation, defined as the mixed fixed point.

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

## Solution: Noix

Noix achieves propositional sharing without step-indexing!

We no longer suffer from the later modality `▷` and can do advanced liveness verification like Simuliris.
And at the same time, we can use propositional sharing, like shared invariants and full borrows, for flexible reasoning.

### Core Idea

Separation logics like iCAP and Iris are fully semantic, using no syntax for propositions.

Instead, Noix introduces a closed-world *syntax* `nProp` for propositions and judgments over `nProp`.
Then we interpret Noix's syntactic separation logic in a semantic separation logic, Iris<sup>light</sup>.
Now we have broken the circular definition
because the resource `Res` for a semantic proposition `iProp` depends just on `nProp`, like:
```
iProp  ≜  Res → Prop       Res  ≜  F nProp
```
Then we give an interpretation `⟦ ⟧ : nProp → iProp`
and prove the soundness of the syntactic logic for the semantics.
Easy!

### Avoiding the Paradox

For soundness, Noix imposes a syntactic restriction:
roughly, we can't use the fancy update modality `|==>` in the proposition `P` of a shared invariant `inv N P`, full borrow `&{κ} P`, etc.

This amounts to restricting shared mutable references containing the arrow type, like `evil: (unit -> unit) ref`,
and thus liberates Noix from the paradox analogous to Landin's knot.

### Infinite Propositions

A proposition `P : nProp` can have an infinite syntax tree,
which helps construct assertions for infinite data structures.
To reason about such infinite syntax, we take advantage of parameterized coinduction by [Paco](https://plv.mpi-sws.org/paco/).

### Mechanization

Noix is fully mechanized in Coq with the Iris framework.
The semantics of the logic is constructed in the Iris separation logic.
Also, reasoning about Noix's syntactic logic is accelerated
with a variant of [Iris Proof Mode](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf).
