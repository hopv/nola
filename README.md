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
  + [`eq`](nola/util/eq.v) (Equality),
  + [`uip`](nola/util/uip.v) (UIP)
  + [`gmap`](nola/util/gmap.v) (On `gmap`),
    [`gmultiset`](nola/util/gmultiset.v) (On `gmultiset`)
  + [`prod`](nola/util/prod.v) (Modified product),
    [`plist`](nola/util/plist.v) (Product list),
    [`tagged`](nola/util/tagged.v) (Tagged type)
  + [`proph`](nola/util/proph.v) (Prophecy)
  + [`order`](nola/util/order.v) (Order theory),
    [`psg`](nola/util/psg.v) (Pseudo-gfp)
  + [`productive`](nola/util/productive.v) (Productivity)
  + [`nary`](nola/util/nary.v) (N-ary maps),
    [`cit`](nola/util/cit.v) (Coinductive-inductive tree)
- [`bi/`](nola/bi/) : Libraries for bunched implication logic
  + [`util`](nola/bi/util.v) (Utilities)
  + [`internal`](nola/bi/internal.v) (Internal equality)
  + [`gmap`](nola/bi/gmap.v) (On `gmap`),
    [`plist`](nola/bi/plist.v) (On `plist`)
  + [`order`](nola/bi/order.v) (Order theory),
    [`deriv`](nola/bi/deriv.v) (Derivability)
  + [`mod`](nola/bi/mod.v) (Modality classes),
    [`modw`](nola/bi/modw.v) (Modality with a custom world satisfaction),
    [`wpw`](nola/bi/wpw.v) (Weakest precondition with a custom world
      satisfaction)
  + [`paradox`](nola/bi/paradox.v) (Paradoxes)
- [`iris/`](nola/iris/) : Libraries for Iris base logic
  + [`iprop`](nola/iris/iprop.v) (`iprop`)
  + [`own`](nola/iris/own.v) (On `own`)
  + [`list`](nol/iris/list.v) (On lists)
  + [`option`](nola/iris/option.v) (On `option`),
    [`agree`](nola/iris/agree.v) (On `agree`),
    [`csum`](nola/iris/csum.v) (On `csum`)
  + [`sinv`](nola/iris/sinv.v) (Simple invariant)
  + [`inv`](nola/iris/inv.v) (Invariant),
    [`inv_deriv`](nola/iris/inv_deriv.v) (Invariant relaxed with derivability),
    [`na_inv`](nola/iris/na_inv.v) (Non-atomic invariant),
    [`na_inv_deriv`](nola/iris/na_inv_deriv.v) (Non-atomic invariant relaxed
      with derivability)
  + [`store`](nola/iris/store.v) (Stored propositions)
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
- [`rust_lang/`](nola/lrust/) : Variant of RustBelt's language, supporting
    `Ndnat` and program logic with termination sensitivity and custom world
    satisfactions
- [`examples/`](nola/examples/) : Examples
  + [`xty`](nola/examples/xty.v) (Syntactic type),
    [`con`](nola/examples/con.v) (Constructors),
    [`ilist`](nola/examples/ilist.v) (Infinite list),
    [`borrow`](nola/examples/borrow.v) (Borrow),
    [`mutex`](nola/examples/mutex.v) (Mutex),
    [`deriv`](nola/examples/deriv.v) (Derivability)
