# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A research repository formalizing the semantics of Solidity's two data locations — **memory** and **storage** — and, crucially, the semantics of *copying between them* (in Solidity, memory↔storage assignments have subtly different aliasing and value-copy behavior). The primary formalization is in **Maude** (equational/rewriting logic); parallel formalizations of the same models exist in **Agda**, **F\***, and **Prolog** for cross-checking and proof.

There is no README, build system, or package manifest — each source file is a self-contained specification run directly by its tool.

## Commands

Maude is the main tool. Files end with `red`/`rew` commands that execute on load; run a spec with:

```sh
maude src/Memory.maude          # loads deps via `load`, runs the reductions at the bottom
maude -no-banner src/Storage.maude
```

If Maude reports `unable to locate file: prelude.maude`, its data dir isn't on the search path — point `MAUDE_LIB` at it (e.g. `export MAUDE_LIB=/usr/share/maude`, the Arch/Manjaro package location; the binary is `/usr/bin/maude`).

CI (`.github/workflows/maude.yml`) installs `maude` via apt and runs `maude full-maude.maude` — the parameterized modules (`fmod X{Field :: TRIV}`) rely on Full Maude.

**Verifying.** There is no import-all entry point, and there can't be one — sibling variants deliberately reuse module names (`STORAGE` is defined by `Storage.maude`, `StorageSelect.maude`, and `list/Storage.maude`; `BANK` by `Memory.maude` and `bank.maude`; `MemoryToStorage`/`StorageToMemory` by three files each), so loading them into one session clashes. Instead run each spec on its own: its trailing `red`/`rew` block is that file's test suite (loading a file also runs the reductions of everything it `load`s), and expected results are written inline as trailing `*** …` comments — a spec is "green" when no reduction is left stuck and the outputs match those comments. The `load`-graph roots that transitively cover the tree are the six translation files, `random.maude`, and `list-constructor.maude`, plus the `list/` specs (`list/Storage.maude`, `list/Memory.maude`). The storage `delete` reductions (per Solidity, `delete` must skip mappings — see the `MapField` sort in `Fields.maude`/`list/Field.maude`) live in `src/Storage.maude` (nested / lazy) and `src/list/Storage.maude` (flat / eager); verify them with `maude -no-banner src/Storage.maude` and `maude -no-banner src/list/Storage.maude`.

**The `src/sem/` executable semantics** is the one part of the tree with a
proper `load` chain and a runner. It layers a small-step Solidity semantics
on top of the storage/memory models (see `PLAN.md`): `Syntax` → `Config` →
`Expr` → `Stmt` → `Flow` → `Net` → `Contract` → `NetCallback` (a system
`mod`), plus `examples/Bank.maude`. Run the whole suite (each file green
when it emits no `Warning:` and leaves no reduction stuck) with:

```sh
bash src/sem/run-tests.sh
```

Individual files still run standalone (`maude -no-banner src/sem/Stmt.maude`)
and carry their expected results as trailing `*** …` comments. CI runs the
runner via `.github/workflows/maude.yml`.

Other tools:
- **Agda** (`proofs/`): a library rooted at `proofs/proofs.agda-lib` (`name: testing`, depends on `standard-library` and `cubical`). Files use `{-# OPTIONS --rewriting #-}`. Type-check with `agda proofs/<file>.agda`.
- **F\*** (`fstar/`): config in `fstar/fstar.fst.config.json` (include dir `.`). Verify with `fstar.exe fstar/<file>.fst`.
- **Prolog** (`prolog/`): SWI-Prolog with `clpfd`. Load with `swipl prolog/Memory.pl`.

## Architecture (Maude, `src/`)

Everything is built on an abstract field signature and layered upward. `load` statements wire the dependency graph.

- **`Fields.maude`** — `FIELDS{Field :: TRIV}`, the shared abstract signature. Key sorts: `Identity` (an object reference), `Value`, and `Field$Elt` split into `PrimField` (primitive-valued, e.g. a balance) vs `IdField` (reference-valued, points to another object). An `Identity` is `idC(PrimIdentity, List{Field})` — a base object plus an access path of fields.

- **`Memory.maude`** — `BANK{Field :: TRIV}`, the memory model: `add`/`read`/`write`/`delete`/`erase` keyed by `Identity` + field path. Reads/writes are defined equationally (`read(write(m,id,sel,val),id,sel) = val`, with conditional commutation over distinct id/selector pairs). `readR` reads along a `NeList{Field}` path.

- **`Storage.maude`** — `STORAGE{Field :: TRIV}`, the storage model as nested `Struct`s: `store`/`select`/`find`/`save`/`push`/`pop`. `find(st, path)` navigates a `List{Field}` into nested structs. `StorageSelect.maude` is a `select`-based variant.

- **Translations** (the core research artifact) — encode Solidity's copy semantics between the two models:
  - `MemoryToStorage.maude`, `MemoryToStorage-Eager.maude`, `MemoryToStorageSelect.maude` — memory → storage (`copyMem`).
  - `StorageToMemoryLazy.maude`, `StorageToMemoryCopyAllId.maude`, `StorageToMemoryCopyAllId-fixed.maude` — storage → memory (`copySt` / `copy-struct-mem`). **Eager vs Lazy** is the key axis: eager copies the whole structure at assignment time; lazy defers via equations that resolve on `read`/`find`.

- **Concrete instance / testing** — `bank-sort.maude` defines a concrete bank domain (Person, Account, `$alice`/`$bob`, selectors) with real `view`s to `TRIV`; `bank.maude` and `bank-structs-destructor.maude` build the read/write model on it; `random.maude` and `list-constructor.maude` generate random test terms (`pr RANDOM`).

- **`src/sem/`** — an executable **small-step Solidity semantics** built on
  the storage/memory models (the SolidiKeY-style layer; design + phase map in
  `PLAN.md`). A deep-embedded syntax (`SOL-SYNTAX`) is rewritten over a
  cell-soup configuration (`SOL-CONFIG`: `k`/`sto`/`mem`/`env`/`net`/`msg` +
  revert snapshots). Deterministic steps are equations (`SOL-EVAL` expression
  evaluation, `SOL-STMT` the assignment/copy/delete/push-pop family, `SOL-FLOW`
  if/while/require/return, `SOL-NET` the ISoLA payment ledger, `SOL-CONTRACT`
  calls/frames/struct-literals); only genuinely nondeterministic behavior is a
  rewrite rule (`SOL-CALLBACK`, a system `mod`: `call{value:}` re-entrancy,
  which `search` explores to find/exclude the DAO drain). Conventions: bools
  are Ints 0/1, Solidity operators are dotted (`+.` `===`), member access is
  `·`, modules are `SOL-`prefixed. Where driving the models from source-level
  syntax exposed gaps in the base `STORAGE`/`BANK` specs, the fix lives in
  `src/sem/` and is flagged in-comment for the Agda/F\*/Prolog twins.

- **`src/list/`** — an alternative model expressed with a proper parameterized `FIELD` theory and Maude `view`s (`Field.maude`, `Memory.maude`, `Storage.maude`), using an assoc list representation (`_·_`, `[_=_]`).

## Conventions

- Modules are parameterized functional modules over `TRIV` (`{Field :: TRIV}`); concrete constants use a `$`-prefix (`$alice`, `$balance`, `$account`).
- Files come in **variants** exploring the same idea (Eager/Lazy/Select, `-fixed`); when changing behavior, check whether a sibling variant should change too, and prefer adding a variant over silently altering an existing one — they are compared against each other.
- The same model is intentionally duplicated across Maude/Agda/F\*/Prolog; a semantic change in one usually needs a matching change in the others.
