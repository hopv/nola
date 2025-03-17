# Nola: Later-Free Ghost State for Verifying Termination in Iris

Nola is a framework for _later-free higher-order ghost state_, enabling
termination verification in the presence of advanced features.

It is fully mechanized in [Coq](https://coq.inria.fr/) as a library for the
[Iris](https://iris-project.org/) separation logic framework.

The name Nola comes from '_No_ *la*ter' and the nickname for New Orleans,
Louisiana, USA, in memory of POPL 2020 held in that city.

- [Publications](#publications)
- [Getting Started](#getting-started)
- [Connection with the PLDI 2025 Paper](#connection-with-the-pldi-2025-paper)
- [Contents](#Contents)

## Publications

- Yusuke Matsushita and Takeshi Tsukada. Nola: Later-Free Ghost State for
    Verifying Termination in Iris. \
  ACM PLDI 2025. June 2025.
- Yusuke Matsushita. Non-Step-Indexed Separation Logic with Invariants and
    Rust-Style Borrows. \
  Ph.D. Dissertation, University of Tokyo. Dec 6, 2023.
    [Paper](https://shiatsumat.github.io/papers/phd-thesis.pdf),
    [Talk slides](https://shiatsumat.github.io/talks/phd-thesis-talk.pdf).
  + Yusuke Matsushita. Non-Step-Indexed Separation Logic with Invariants and
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

## Connection with the PLDI 2025 Paper

To check statements of the paper, you can refer to the following parts of our
Coq mechanization.

- [Paradoxes](#paradoxes)
- [Later-Free Ghost State](#later-free-ghost-state)
- [View Shifts and Hoare Triples](#view-shifts-and-hoare-triples)
- [Modular Construction of Formula Syntax](#modular-construction-of-formula-syntax)
- [Magic Derivability](#magic-derivability)
- [Examples and RustHalt](#examples-and-rusthalt)

### Paradoxes

- Paradoxes of the naive later-free invariant.
  + Paradox for the program logic based on Landin's knot:
      [`nola.bi.paradox.inv_landin`](nola/bi/paradox.v).
  + Purely logical paradox using view shifts:
      [`nola.bi.paradox.inv_fupd`](nola/bi/paradox.v).
- Paradox of the step-indexed total Hoare triple:
    [`nola.bi.paradox.twp`](nola/bi/paradox.v).
- Paradoxes of unbounded later weakening.
  + Paradoxes under finite step-indexing.
    * One based on the `bi` axioms:
        [`nola.bi.paradox.exist_laterN`](nola/bi/paradox.v).
    * One based on the `uPred` model:
        [`nola.iris.paradox.exist_laterN_uPred`](nola/iris/paradox.v).
  + Paradox under transfinite step-indexing:
      [`nola.bi.paradox.exist_laterOrd`](nola/bi/paradox.v).

### Later-Free Ghost State

All the proof rules are proved to be sound with respect to the semantic model.

- Nola's later-free invariant: [`nola.iris.inv`](nola/iris/inv.v).
  + INV-PERSIST: `inv_tok_persistent`, INV-ALLOC: `inv_tok_alloc`,
      INV-ACC: `inv_tok_acc_vs`, THOARE-INV: `inv_tok_acc_twp`,
      WINV-CREATE: `inv_wsat_alloc`.
- Nola's later-free borrow.
  + Lifetime: [`nola.iris.lft`](nola/iris/lft.v)
    * LFT-ALLOC: `lft_alloc`, LFT-END: `lft_end`.
  + Borrow: [`nola.iris.borrow`](nola/iris/borrow.v)
    * BOR-LEND-NEW: `bor_lend_tok_new`, LEND-BACK: `lend_tok_retrieve`,
        BOR-OPEN: `bor_tok_open`, OBOR-CLOSE: `obor_tok_close`,
        WBOR-CREATE: `borrow_wsat_alloc`.
  + Prophetic borrow: [`nola.iris.pborrow`](nola/iris/pborrow.v)

### View Shifts and Hoare Triples

- Parameterized view shifts: [`nola.iris.modw`](nola/bi/modw.v).
  + VS-EXPAND: `vsw-expand`.
- Parameterized Hoare triples: [`nola.iris.wpw`](nola/bi/wpw.v).
  + VS-THOARE: `vsw-thoarew`, THOARE-VS: `thoarew-vsw`,
      THOARE-EXPAND: `thoarew-expand`.
- Extended HeapLang: [`nola.heap_lang`](nola/heap_lang/).
  + Adequacy of the total Hoare triple:
      [`total_adequacy.heap_total`](nola/heap_lang/total_adequacy.v).
- Extended λRust, RustBelt's core language: [`nola.lrust`](nola/lrust/).
  + Adequacy of the total Hoare triple:
      [`adequacy.lrust_total`](nola/lrust/adequacy.v).

### Modular Construction of Formula Syntax

- Modular construction of formula syntax: [`nola.iris.cif`](nola/iris/cif.v).

### Magic Derivability

- Magic derivability: [`nola.bi.deriv`](nola/bi/deriv.v).
  + DER-SOUND: `der_sound`, DER-DERIV: `der_Deriv`, DERIV-MAP: `Deriv_mapl`.

### Examples and RustHalt

- Demonstration of how our program logic can emulate CFML:
    [`nola.examples.cfml`](nola/examples/cfml.v).
- Simple example of an unbounded loop:
    [`nola.examples.basic.twp_just_loop_nd`](nola/examples/basic.v).
- Examples of shared mutable infinite lists:
    [`nola.examples.ilist`](nola/examples/ilist.v).
  + Verifying tail access: `twp_tail_list`.
  + Verifying iterc: `twp_iter_ilist`,
      Verifying two threads running iterc: `twp_fork2_iter_ilist`,
      Verifying iterc for the multiple-of-three invariant:
        `twp_iter_ilist_faa3_mul3`.
  + Verifying iterc2, with two counters under the lexicographic order:
      `twp_iter2_ilist`.
  + Verifying iteration using any step function under any well-founded relation:
      `twp_iterst_ilist`, with an instantiation example
      `twp_iterst_ilist_step2`.
- Examples for magic derivability:
    [`nola.examples.deriv`](nola/examples/deriv.v).
  + Examples of semantic alteration: `inv'_sep_comm`, `inv'_inv'_sep_comm` and
      `inv'_bor_lft`.
  + Access via a view shift `invd_acc_vs`,
      Access via a total Hoare triple `invd_acc_thoare`,
      Allocation `inv'_alloc`,
      General rule for semantic alteration: `inv'_iff'`.
- RustHalt: [`nola.examples.rust_halt`](nola/examples/rust_halt/).
  + INT-ADD: [`num.type_add_int`](nola/examples/rust_halt/num.v),
      BOX-MUT-BORROW:
        [`ptrs_more.sub_borrow_box`](nola/examples/rust_halt/ptrs_more.v),
      MUT-REF-WRITE:
        [`mutref.write_mutref`](nola/examples/rust_halt/mutref.v),
      MUT-REF-SHARE:
        [`ptrs_more.type_share`](nola/examples/rust_halt/ptrs_more.v),
      FN-REC-CALL: [`core.type_call`](nola/examples/rust_halt/core.v),
      REAL: [`core.type_real`](nola/examples/rust_halt/core.v).
  + Borrow subdivision:
      [`prod_more.sub_mutref_prod_split`](nola/examples/rust_halt/prod_more.v),
      [`sum_more.type_case_sum_mutref`](nola/examples/rust_halt/sum_more.v)
      etc.,
    Reborrowing:
      [`ptrs_more.sub_reborrow`](nola/examples/rust_halt/ptrs_more.v),
      [`ptrs_more.type_deref_mutref_mutref`](nola/examples/rust_halt/ptrs_more.v)
      etc.
  + Verification examples: [`verify`](nola/examples/rust_halt/verify/).
    * Verifying mutation of a list:
        [`list_more.type_iter_list_mut_fun`](nola/examples/rust_halt/verify/list_more.v).
    * Verifying mutation of a rich list over a mutable reference:
        [`mutlist_more.type_iter_mutlist_mut_fun`](nola/examples/rust_halt/verify/mutlist_more.v).
  + Adequacy: [`adequacy`](nola/examples/rust_halt/adequacy.v).

## Contents

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
    [`bin`](nola/util/tree.v) (Binary tree),
    [`plist`](nola/util/plist.v) (Product list),
    [`tagged`](nola/util/tagged.v) (Tagged type)
  + [`proph`](nola/util/proph.v) (Prophecy)
  + [`order`](nola/util/order.v) (Order theory),
    [`psg`](nola/util/psg.v) (Pseudo-gfp)
  + [`wf`](nola/util/wf.v) (Well-foundedness)
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
- [`lrust/`](nola/lrust/) : Variant of λRust, or RustBelt's core language,
    supporting `Ndnat` (infinite non-determinism) and program logic with
    termination sensitivity and custom world satisfactions for Nola
  + [`lang`](nola/lrust/lang.v) (Language),
    [`notation`](nola/lrust/notation.v) (Notation for the language),
    [`tactics`](nola/lrust/tactics.v) (Tactics for the language)
  + [`races`](nola/lrust/races.v) (Race freedom guarantee of the language)
  + [`heap`](nola/lrust/heap.v) (Ghost state for the heap),
    [`lifting`](nola/lrust/lifting.v) (Program logic),
    [`proofmode`](nola/lrust/proofmode.v) (Proof mode utility for the program
      logic)
  + [`adequacy`](nola/lrust/adequacy.v) (Adequacy of the program logic)
- [`examples/`](nola/examples/) : Examples
  + [`xty`](nola/examples/xty.v) (Syntactic type),
  + [`con`](nola/examples/con.v) (Constructors)
  + [`cfml`](nola/examples/cfml.v) (Demonstration of how our program logic can
      emulate CFML),
    [`basic`](nola/examples/basic.v) (Basic examples),
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
      [`mutref`](nola/examples/rust_halt/mutref.v) (Mutable reference type)
    * [`ptrs_more`](nola/examples/rust_halt/ptrs_more.v) (More on basic pointer
        types),
      [`prod_more`](nola/examples/rust_halt/prod_more.v) (More on the product
        type)
      [`sum_more`](nola/examples/rust_halt/sum_more.v) (More on the sum type)
    * [`adequacy`](nola/examples/rust_halt/adequacy.v) (Adequacy)
    * [`verify/`](nola/examples/rust_halt/verify/) (Verification examples)
      - [`util`](nola/examples/rust_halt/verify/util.v) (Utility)
      - [`list`](nola/examples/rust_halt/verify/list.v) (Singly linked list
          type),
        [`list_more`](nola/examples/rust_halt/verify/list.v) (More on the list
          type)
      - [`mutlist`](nola/examples/rust_halt/verify/mutlist.v) (Singly linked
          list over a mutable reference),
        [`mutlist_more`](nola/examples/rust_halt/verify/mutlist_more.v) (More on
          `mutlist`)
