# Nola: Deep-Embed Separation Logic to Wipe Laters Out

Nola is a new approach to propositional sharing
in non-step-indexed separation logic.
It is fully mechanized in [Coq](https://coq.inria.fr/) with the [Iris](https://iris-project.org/) separation logic framework.

The name Nola comes from *No* *la*ters.
It is also a nickname for New Orleans, a city I like.

- [Getting Started](#getting-started)
- [Story](#story)
  - [Propositional Sharing](#propositional-sharing)
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

## Story

### Propositional Sharing

We give a name *propositional sharing*
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

All the existing separation logics with propositional sharing,
such as [iCAP](https://www.cs.au.dk/~birke/papers/icap-conf.pdf) and Iris,
resort to *step-indexing*.
It is the technique of layering the logic world with step-indices `0, 1, 2, …: ℕ`,
having notions more defined as the step-index grows.
Why?

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

#### Laters in the Way

Sounds fine? But this comes with the cost of the *later modality* `▷`.

Due to `▶` added to `iProp`, we can use propositional sharing only for propositions under `▷`,
which delays the definition of a proposition by one step-index.
This causes significant practical issues, especially for dealing with nested propositional sharing.

The later modality `▷` is ill-behaved: it is non-idempotent and doesn't commute with the fancy update modality `|==>`.
Various efforts, such as [later credits](https://plv.mpi-sws.org/later-credits/), have been made to manage `▷`, but it is still hard to use.

More fundamentally, the power to strip off `▷` makes program predicates weaker,
ensuring only safety properties (absence of bad behaviors witnessed by finite steps),
but not liveness properties (absence of bad behaviors witnessed only by an infinite execution).
Indeed, [Simuliris](https://iris-project.org/pdfs/2022-popl-simuliris.pdf) just gave up *propositional sharing* in its program logic built in Iris for fair termination preservation, a rich liveness property.

#### Paradox

Can't we have propositional sharing without laters `▷`?
That was believed impossible because of a known paradox for a naive shared invariant without `▷`.

At the high level, the paradox corresponds to a folklore technique called Landin's knot,
causing a program loop using a shared mutable reference over the arrow type `evil: (unit -> unit) ref`:
```ocaml
let evil = ref (fun _ -> ()) in
evil := (fun _ -> !evil ());
!evil ()
```

### Solution: Nola

Surprisingly, Nola achieves propositional sharing without laters!

We no longer suffer from the later modality `▷` and can do advanced liveness verification like Simuliris.
And at the same time, we can use propositional sharing, like shared invariants and full borrows, for flexible reasoning.

#### Core Idea

Separation logics like iCAP and Iris are fully semantic, using *shallow embedding*, without syntax for propositions.

Instead, Nola uses *deep embedding*.
It constructs *syntax* `nProp` for propositions and judgments over `nProp`.
Then we interpret Nola's syntactic separation logic in a semantic separation logic, Iris.
Now we have broken the circular definition
because the resource `Res` for a semantic proposition `iProp` depends just on `nProp`, like:
```
iProp  ≜  Res → Prop     Res  ≜  F nProp
```
Then we give an interpretation `⟦ ⟧ : nProp → iProp`
and prove the soundness of the syntactic logic for the semantics.
Easy!

#### Avoiding the Paradox

For soundness, Nola imposes a syntactic restriction:
roughly, we can't use the fancy update modality `|=[W]=>` in the proposition `P` of a shared invariant `inv N P`, full borrow `&{κ} P`, etc.

That amounts to restricting shared mutable references containing the arrow type, like `evil: (unit -> unit) ref`,
liberating Nola from the paradox analogous to Landin's knot.

#### Extensibility

Using syntax might sound not extensible.
Amazingly, Nola is *extensible*.
Also, Nola's proofs are even composable,
i.e., proofs from different projects can be composed.

The key technique is parameterization of the syntax.
This is analogous to Iris's parameterization `iProp Σ` of `iProp` by the family of cameras `Σ`.
