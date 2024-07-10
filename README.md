# Nola: Parameterizing Higher-Order Ghost State to Clear the Later Modality

Nola is a library for _parameterizing higher-order ghost state_, which enables
wiping out the _later modality_.
It is fully mechanized in [Coq](https://coq.inria.fr/) with the
[Iris](https://iris-project.org/) separation logic framework.

The name Nola comes from '_No_ *la*ter' and the nickname for New Orleans,
Louisiana, US.

- [Publication](#publication)
- [Getting Started](#getting-started)
- [Architecture](#architecture)

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
  + [`fn`](nola/util/fn.v) (Functions),
    [`rel`](nola/util/rel.v) (Relations)
  + [`prod`](nola/util/prod.v) (Modified product),
    [`plist`](nola/util/plist.v) (Product list)
  + [`proph`](nola/util/proph.v) (Prophecy)
  + [`sem`](nola/util/sem.v) (Semantics)
  + [`order`](nola/util/order.v) (Order theory),
    [`psg`](nola/util/psg.v) (Pseudo-gfp)
  + [`cit`](nola/util/cit.v) (Coinductive-inductive tree)
- [`bi/`](nola/bi/) : Libraries for bunched implication logic
  + [`util`](nola/bi/util.v) (Utilities)
  + [`ofe`](nola/bi/ofe.v) (On OFE)
  + [`gmap`](nola/bi/gmap.v) (On `gmap`),
    [`plist`](nola/bi/plist.v) (On `plist`)
  + [`order`](nola/bi/order.v) (Order theory),
    [`deriv`](nola/bi/deriv.v) (Derivability)
  + [`genupd`](nola/bi/genupd.v) (General update),
    [`updw`](nola/bi/updw.v) (Update with a custom world satisfaction),
    [`wpw`](nola/bi/wpw.v) (Weakest precondition with a custom world
      satisfaction)
  + [`paradox`](nola/bi/paradox.v) (Paradoxes)
- [`iris/`](nola/iris/) : Libraries for Iris base logic
  + [`ofe`](nola/bi/ofe.v) (On OFE)
  + [`sinv`](nola/iris/sinv.v) (Simple invariant),
    [`sinv_deriv`](nola/iris/sinv_deriv.v) (Simple invariant relaxed with
      derivability)
  + [`inv`](nola/iris/inv.v) (Invariant),
    [`inv_deriv`](nola/iris/inv_deriv.v) (Invariant relaxed with derivability),
    [`na_inv`](nola/iris/na_inv.v) (Non-atomic invariant),
    [`na_inv_deriv`](nola/iris/na_inv_deriv.v) (Non-atomic invariant relaxed
      with derivability)
  + [`lft`](nola/iris/lft.v) (Lifetime),
    [`borrow`](nola/iris/borrow.v) (Borrowing),
    [`borrow_deriv`](nola/iris/borrow_deriv.v) (Borrowing relaxed with
      derivability)
  + [`proph`](nola/iris/proph.v) (Prophecy),
    [`proph_ag`](nola/iris/proph_ag.v) (Prophetic agreement),
    [`pborrow`](nola/iris/pborrow.v) (Prophetic borrowing)
  + [`cif`](nola/iris/cif.v) (Coinductive-inductive formula)
- [`heap_lang/`](nola/heap_lang/) : Variant of Iris HeapLang, supporting `Ndnat`
    (infinite non-determinism) and program logic with custom world satisfactions
  + [`lib/`](nola/heap_lang/lib/) : Libraries
    * [`mutex`](nola/heap_lang/lib/mutex.v) (Mutex machinery)
- [`examples/`](nola/examples/) : Examples
  + [`minilogic`](nola/examples/minilogic.v) (Minimal logic)
  + [`later`](nola/examples/later.v) (Instantiating with later)
  + [`logic`](nola/examples/logic.v) (Logic)
  + [`deriv`](nola/examples/deriv.v) (Logic with derivability)
