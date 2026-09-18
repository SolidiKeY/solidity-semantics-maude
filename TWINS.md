# The non-Maude twins

`proofs/` (Agda), `fstar/` (F\*) and `prolog/` (Prolog) hold parallel
formalizations of the same memory/storage models, kept for cross-checking and
proof. The Maude tree in `src/` is the primary artifact and is what `CLAUDE.md`
documents; this file is everything else.

## Running them

- **Agda (`proofs/`)** — a library rooted at `proofs/proofs.agda-lib`
  (`name: testing`, `depend: standard-library cubical`). Files use
  `{-# OPTIONS --rewriting #-}`. Type-check one with `agda proofs/<file>.agda`.
  Files: `Field.agda`, `memory.agda`, `write.agda`, `mutual-ind.agda`,
  `proof-select-save.agda`, `storageToMemory.agda`, `testing.agda`.
- **F\* (`fstar/`)** — config in `fstar/fstar.fst.config.json` (include dir
  `.`). Verify with `fstar.exe fstar/<file>.fst`. Files: `Memory.fst`,
  `Storage.fst`, `StorageToMemory.fst`.
- **Prolog (`prolog/`)** — SWI-Prolog with `clpfd`. Load with
  `swipl prolog/Memory.pl`. Files: `Memory.pl`, `constraint.pl`.

## Staying in step

The duplication is intentional: a semantic change in one model usually needs a
matching change in the others. Where driving the Maude models from source-level
syntax exposed a gap in the base `STORAGE`/`BANK` specs, the fix lives in
`src/sem/` and is flagged in-comment for these twins to pick up.

## Naming drift

The twins still use the flat pre-hierarchy names — `store` / `select` / `add` /
`del` / `default` / `IdField` / `PrimIdentity` — rather than the
`Prim < StValue MemValue < Value` sort hierarchy that `src/Fields.maude` now
has. That is drift, not a second design.
