# Nola: Later-Free Ghost State for Verifying Termination

Nola is a framework for _later-free higher-order ghost state_, enabling
termination verification in the presence of advanced features.

It is fully mechanized in [Coq](https://coq.inria.fr/) as a library for the
[Iris](https://iris-project.org/) separation logic framework.

The name Nola comes from '_No_ *la*ter' and the nickname for New Orleans,
Louisiana, USA, in memory of POPL 2020 held in that city.

- [Publications](#publications)
- [Getting Started](#getting-started)
- [Architecture](#architecture)

## Publications

- Yusuke Matsushita. Non-Step-Indexed Separation Logic with Invariants and
    Rust-Style Borrows. \
  Ph.D. Dissertation, University of Tokyo. Dec 6, 2023.
    [Paper](https://shiatsumat.github.io/papers/phd-thesis.pdf),
    [Talk slides](https://shiatsumat.github.io/talks/phd-thesis-talk.pdf).
- Yusuke Matsushita. Non-Step-Indexed Separation Logic with Invariants and
    Rust-Style Borrows. \
  Bulletin of Ph.D. Dissertations in AY 2023 Recommended by SIGs, Information
    Processing Society of Japan. Aug 15, 2024.
    [HTML](https://note.com/ipsj/n/nc0ae275045eb) (Japanese).

## Getting Started

Now we explain how to get started.

- [Setting up Opam](#setting-up-opam)
- [Building Nola](#building-nola)

### Setting up Opam

We use [opam](https://opam.ocaml.org/) ver `2.*` for package management. To
install opam, you can refer to
[the official installation guide](https://opam.ocaml.org/doc/Install.html).

To create a new [opam switch](https://opam.ocaml.org/doc/man/opam-switch.html)
named `for_nola` (you can choose any name), run:
```bash
opam switch create for_nola 4.14.2 # Choose any OCaml version you like
```
To activate the opam switch `for_nola` just globally, run:
```bash
opam switch set for_nola
```
Or, to activate the opam switch `for_nola` locally in the directory `NOLA_DIR`
where this `README.md` is located, run:
```bash
opam switch link for_nola NOLA_DIR
```

To set up opam repos for Coq and Iris for the active opam switch, run:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

### Building Nola

First, go to the directory `NOLA_DIR` where this `README.md` is located:
```bash
cd NOLA_DIR
```

To fix development dependencies and install them, run:
```bash
make devdep
```

To build Nola's code locally, run:
```bash
make -j16 # Choose a job number
```
Or, to install Nola as an opam library, run:
```bash
opam install .
```

To generate and browse a document for Nola's Coq code, run:
```bash
make viewdoc
```

## Architecture

All the Coq code is in [`nola/`](nola/) and structured as follows:
- [`prelude`](nola/prelude.v) : Prelude
- [`util/`](nola/util/) : General-purpose utilities, extending
  [`stdpp`](https://gitlab.mpi-sws.org/iris/stdpp)
  + [`eq`](nola/util/eq.v) (Equality)
  + [`uip`](nola/util/uip.v) (UIP)
  + [`fn`](nola/util/fn.v) (Functions)
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
    [`deriv`](nola/bi/deriv.v) (Magic derivability)
  + [`mod`](nola/bi/mod.v) (Modality classes),
    [`modw`](nola/bi/modw.v) (Modality with a custom world satisfaction),
    [`wpw`](nola/bi/wpw.v) (Weakest precondition with a custom world
      satisfaction)
  + [`judg`](nola/bi/judg.v) (Judgments)
  + [`paradox`](nola/bi/paradox.v) (Paradoxes)
- [`iris/`](nola/iris/) : Libraries for Iris base logic
  + [`iprop`](nola/iris/iprop.v) (Utility for `iProp`),
    [`own`](nola/iris/own.v) (Utility for `own`)
  + [`list`](nol/iris/list.v) (On lists),
    [`option`](nola/iris/option.v) (On `option`),
    [`agree`](nola/iris/agree.v) (On `agree`),
    [`csum`](nola/iris/csum.v) (On `csum`)
  + [`sinv`](nola/iris/sinv.v) (Simple invariants)
  + [`inv`](nola/iris/inv.v) (Invariants),
    [`inv_deriv`](nola/iris/inv_deriv.v) (Invariants relaxed with derivability),
    [`na_inv`](nola/iris/na_inv.v) (Non-atomic invariants),
    [`na_inv_deriv`](nola/iris/na_inv_deriv.v) (Non-atomic invariants relaxed
      with derivability)
  + [`dinv`](nola/iris/dinv.v) (Direct invariants),
    [`dinv_deriv`](nola/iris/dinv_deriv.v) (Direct invariants relaxed with
      derivability),
    [`store`](nola/iris/store.v) (Stored propositions),
    [`store_deriv`](nola/iris/store_deriv.v) (Stored propositions relaxed with
      derivability)
  + [`lft`](nola/iris/lft.v) (Lifetime),
    [`borrow`](nola/iris/borrow.v) (Borrows),
    [`borrow_deriv`](nola/iris/borrow_deriv.v) (Borrows relaxed with
      derivability),
    [`fborrow`](nola/iris/fborrow.v) (Fractured borrows)
  + [`proph`](nola/iris/proph.v) (Prophecy),
    [`proph_ag`](nola/iris/proph_ag.v) (Prophetic agreement),
    [`pborrow`](nola/iris/pborrow.v) (Prophetic borrows),
    [`pborrow_deriv`](nola/iris/pborrow_deriv.v) (Prophetic borrows relaxed with
      derivability)
  + [`cif`](nola/iris/cif.v) (Coinductive-inductive formula)
  + [`paradox`](nola/iris/paradox.v) (Paradox)
- [`heap_lang/`](nola/heap_lang/) : Variant of Iris HeapLang, supporting `Ndnat`
    (infinite non-determinism) and program logic with custom world satisfactions
    for Nola
  + [`locations`](nola/heap_lang/locations.v) (On locations)
  + [`lang`](nola/heap_lang/lang.v) (Language),
    [`pretty`](nola/heap_lang/pretty.v) (Pretty printing for the language),
    [`notation`](nola/heap_lang/notation.v) (Notation for the language),
    [`tactics`](nola/heap_lang/tactics.v) (Tactics for the language)
  + [`metatheory`](nola/heap_lang/metatheory.v) (Metatheory on the language),
    [`proph_erasure`](nola/heap_lang/proph_erasure.v) (Prophecy erasure theorem
      for the language)
  + [`class_instances`](nola/heap_lang/class_instances.v) (Class instances for
      the program logic),
    [`definitions`](nola/heap_lang/definitions.v) (Definitions for the program
      logic),
    [`primitive_laws`](nola/heap_lang/primitive_laws.v) (Primitive laws of the
      program logic),
    [`derived_laws`](nola/heap_lang/derived_laws.v) (Derived laws of the program
      logic),
    [`proofmode`](nola/heap_lang/proofmode.v) (Proof mode utility for the
      program logic)
  + [`adequacy`](nola/heap_lang/adequacy.v) (Safety adequacy of the program
      logic),
    [`total_adequacy`](nola/heap_lang/total_adequacy.v) (Termination adequacy of
      the program logic)
- [`rust_lang/`](nola/rust_lang/) : Variant of RustBelt's language, supporting
    `Ndnat` (infinite non-determinism) and program logic with termination
    sensitivity and custom world satisfactions for Nola
  + [`lang`](nola/rust_lang/lang.v) (Language),
    [`notation`](nola/rust_lang/notation.v) (Notation for the language),
    [`tactics`](nola/rust_lang/tactics.v) (Tactics for the language)
  + [`races`](nola/rust_lang/races.v) (Race freedom guarantee of the language)
  + [`heap`](nola/rust_lang/heap.v) (Ghost state for the heap),
    [`lifting`](nola/rust_lang/lifting.v) (Program logic),
    [`proofmode`](nola/rust_lang/proofmode.v) (Proof mode utility for the
      program logic)
  + [`adequacy`](nola/rust_lang/adequacy.v) (Adequacy of the program logic)
- [`examples/`](nola/examples/) : Examples
  + [`xty`](nola/examples/xty.v) (Syntactic type),
  + [`con`](nola/examples/con.v) (Constructors),
    [`ilist`](nola/examples/ilist.v) (Infinite list),
    [`borrow`](nola/examples/borrow.v) (Borrow),
    [`mutex`](nola/examples/mutex.v) (Mutex),
    [`deriv`](nola/examples/deriv.v) (Derivability)
  + [`rust_halt/`](nola/examples/rust_halt/) : RustHalt, a formal foundation of
      functional and termination-sensitive Rust program verification
    * [`base`](nola/examples/rust_halt/base.v) (Basics),
      [`type`](nola/examples/rust_halt/type.v) (Type model)
    * [`core`](nola/examples/rust_halt/core.v) (Core features)
    * [`num`](nola/examples/rust_halt/num.v) (Numeric types),
      [`uninit`](nola/examples/rust_halt/uninit.v) (Uninitialized data type)
    * [`prod`](nola/examples/rust_halt/prod.v) (Product type),
      [`sum`](nola/examples/rust_halt/sum.v) (Sum type)
    * [`rec`](nola/examples/rust_halt/rec.v) (Recursive type),
      [`mod`](nola/examples/rust_halt/mod.v) (Modification type)
    * [`ptr`](nola/examples/rust_halt/ptr.v) (Utility for pointer types),
      [`box`](nola/examples/rust_halt/box.v) (Box pointer type),
      [`shrref`](nola/examples/rust_halt/shrref.v) (Shared reference type),
      [`mutref`](nola/examples/rust_halt/mutref.v) (Mutable reference type),
      [`ptrs_more`](nola/examples/rust_halt/ptrs_more.v) (More on basic pointer
        types)
    * [`sum_more`](nola/examples/rust_halt/sum_more.v) (More on the sum type)
    * [`adequacy`](nola/examples/rust_halt/adequacy.v) (Adequacy)
    * [`verify/`](nola/examples/rust_halt/verify/) (Verification examples)
      - [`list`](nola/examples/rust_halt/verify/list.v) (Singly linked list
          type),
        [`list_more`](nola/examples/rust_halt/verify/list.v) (More on the list
          type)
