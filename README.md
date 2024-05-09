# Nola: Parameterization for Later-Free Invariants and Borrows

Nola is a library to achieve _later-free invariants and borrows_ by the power
of _parameterization_.
It is fully mechanized in [Coq](https://coq.inria.fr/) with the
[Iris](https://iris-project.org/) separation logic framework.

The name Nola comes from _No_ *la*ters and a nickname for New Orleans,
Louisiana, US.

- [Publication](#publication)
- [Getting Started](#getting-started)
- [Story](#story)
  + [Nested invariants](#nested-invariants)
  + [Obstacle: Laters](#obstacle-laters)
  + [Solution: Nola](#solution-nola)

## Publication

- Non-Step-Indexed Separation Logic with Invariants and Rust-Style Borrows.
  Yusuke Matsushita. Ph.D. Thesis, University of Tokyo. Dec 2023.
  [Paper](https://shiatsumat.github.io/papers/phd-thesis.pdf)
  [Talk slides](https://shiatsumat.github.io/talks/phd-thesis-talk.pdf)

## Getting Started

We use [opam](https://opam.ocaml.org/) ver 2.* for package management.

To set up an [opam switch](https://opam.ocaml.org/doc/man/opam-switch.html)
named `nola` and link it to the folder:
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
- [`util/`](nola/util/) : General-purpose utilities, extending
  [`stdpp`](https://gitlab.mpi-sws.org/iris/stdpp)
  + [`funext`](nola/util/funext.v) (Function extensionality)
  + [`func`](nola/util/func.v) (Functions),
    [`pred`](nola/util/pred.v) (Predicates),
    [`rel`](nola/util/rel.v) (Relations),
    [`list`](nola/util/list.v) (Lists),
    [`nat`](nola/util/nat.v) (Natural numbers)
  + [`prod`](nola/util/prod.v) (Modified product),
    [`schoice`](nola/util/schoice.v) (Variant over a list),
    [`plist`](nola/util/plist.v) (Product list)
  + [`hgt`](nola/util/hgt.v) (General height of a tree),
    [`ctx`](nola/util/ctx.v) (Context with unguarded/guarded variables)
  + [`proph`](nola/util/proph.v) (Prophecy)
- [`iris/`](nola/iris) : Iris libraries
  + [`ofe`](nola/iris/ofe.v) (OFEs)
  + [`list`](nola/iris/list.v) (On `list`),
    [`gmap`](nola/iris/gmap.v) (On `gmap`),
    [`plist`](nola/iris/plist.v) (On `plist`)
  + [`deriv`](nola/iris/deriv.v) (Derivability)
  + [`upd`](nola/iris/upd.v) (Update),
    [`wp`](nola/iris/wp.v) (Weakest precondition)
  + [`later`](nola/iris/later.v) (Later)
  + [`sinv`](nola/iris/sinv.v) (Simple invariant),
    [`inv`](nola/iris/inv.v) (Invariant),
    [`na_inv`](nola/iris/na_inv.v) (Non-atomic invariant)
  + [`lft`](nola/iris/lft.v) (Lifetime),
    [`borrow`](nola/iris/borrow.v) (Borrowing)
  + [`proph`](nola/iris/proph.v) (Prophecy),
    [`proph_ag`](nola/iris/proph_ag.v) (Prophetic agreement),
    [`pborrow`](nola/iris/pborrow.v) (Prophetic borrowing)
  + [`paradox`](nola/iris/paradox.v) (Paradoxes)
- [`examples/`](nola/examples/) : Examples
  + [`heap_lang/`](nola/examples/heap_lang/) : Variant of Iris HeapLang,
    with `Ndnat` (terminating infinite non-determinism) added
  + [`minilogic`](nola/examples/minilogic.v) : Minimal showcase logic
  + [`later`](nola/examples/later.v) : Instantiating Nola with later
