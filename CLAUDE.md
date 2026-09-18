# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A research repository formalizing the semantics of Solidity's two data locations — **memory** and **storage** — and, crucially, the semantics of *copying between them* (in Solidity, memory↔storage assignments have subtly different aliasing and value-copy behavior). The primary formalization is in **Maude** (equational/rewriting logic), and this file covers only that. Parallel formalizations of the same models live in `proofs/`, `fstar/` and `prolog/` — see `TWINS.md`, and read it before changing a model's semantics, since the twins are meant to stay in step.

There is no README, build system, or package manifest — each source file is a self-contained specification run directly by its tool.

## Commands

Maude is the main tool. Files end with `red`/`rew` commands that execute on load; run a spec with:

```sh
maude src/Memory.maude          # loads deps via `load`, runs the reductions at the bottom
maude -no-banner src/Storage.maude
```

If Maude reports `unable to locate file: prelude.maude`, its data dir isn't on the search path — point `MAUDE_LIB` at it (e.g. `export MAUDE_LIB=/usr/share/maude`, the Arch/Manjaro package location; the binary is `/usr/bin/maude`).

CI (`.github/workflows/maude.yml`) installs `maude` via apt and runs three steps: `maude full-maude.maude` (that file is *Maude's own*, in `$MAUDE_LIB` — it is only an install smoke test; every spec here runs under Core Maude), the `src/StorageCompare.maude` gate, and `bash src/sem/run-tests.sh`. The `StorageCompare` step encodes the pass criteria the rest of the tree is judged by, because `maude` exits 0 even on warnings:

```sh
out=$(maude -no-banner -batch src/StorageCompare.maude < /dev/null 2>&1)
! grep -Eq '^Warning|^result \[' <<< "$out"    # a kind-level `result [S,T]:` is a failure too
```

**Verifying.** There is no import-all entry point, and there can't be one — sibling variants deliberately reuse module names (`STORAGE` is defined by `Storage.maude`, `StorageCopy.maude`, `StorageSelect.maude`, and `list/Storage.maude`; `BANK` by `Memory.maude` and `bank.maude`; `MemoryToStorage`/`StorageToMemory` by three files each), so loading them into one session clashes. Instead run each spec on its own: its trailing `red`/`rew` block is that file's test suite (loading a file also runs the reductions of everything it `load`s), and expected results are written inline as trailing `*** …` comments — a spec is "green" when no reduction is left stuck and the outputs match those comments. The `load`-graph roots that transitively cover the tree are the six translation files, `random.maude`, and `list-constructor.maude`, plus the `list/` specs (`list/Storage.maude`, `list/Memory.maude`), `StorageCanonical.maude` (standalone — loads nothing), `StorageCopy.maude`, `StorageCompare.maude` (which pulls in `StorageApi` → `StorageCopy` + `StorageFlag`) and `FindSteps.maude`. The storage `delete` reductions (per Solidity, `delete` must skip mappings — see the `MapField` sort in `Fields.maude`/`list/Field.maude`) live in `src/Storage.maude` (nested / lazy) and `src/list/Storage.maude` (flat / eager); verify them with `maude -no-banner src/Storage.maude` and `maude -no-banner src/list/Storage.maude`.

**`src/sem/` runs on `StorageCopy.maude`, not `Storage.maude`.** The `load` at `src/sem/Config.maude` is the single switch between them.

**The `src/sem/` executable semantics** is the one part of the tree with a
proper `load` chain and a runner. It layers a small-step Solidity semantics
on top of the storage/memory models (see `PLAN.md`): `Syntax` → `Config` →
`Expr` → `Order` → `Stmt` → `Flow` → `Net` → `Contract` → `NetCallback` (a
system `mod`), plus `examples/Bank.maude`. Three further roots branch off
`Contract`: `Hoare.maude` → `examples/solkey/Store.maude` → the fifteen
`examples/solkey/` suites, and `Steps.maude` → `examples/paper/Domain.maude` →
the thirteen `examples/paper/` files. **Keep that chain linear** —
Maude's `load` is not idempotent, so a diamond re-executes the whole preamble
and silently duplicates modules (the storage-comparison files avoid this with
`sload`, Maude's idempotent load — that is how `StorageApi.maude` gets
`StorageCopy` and `StorageFlag` into one session). Run the whole suite (each file green
when it emits no `Warning:` and leaves no reduction stuck) with:

```sh
bash src/sem/run-tests.sh
```

The runner only checks for warnings, stuck terms and kind-level results — it
does **not** compare reductions against their trailing `*** …` expected-value
comments, so a `true` → `false` flip in a Hoare triple passes it silently.
`src/sem/golden.sh` is the gate for that: snapshot before a change, diff after.

```sh
bash src/sem/golden.sh > /tmp/before   # …edit…
bash src/sem/golden.sh > /tmp/after
diff /tmp/before /tmp/after
```

When the change is meant to be behaviour-preserving, that diff should be empty
(or purely additive if you added a root). Note the base-model files have their
own trailing `red` blocks, which the `sem/` roots run transitively — filter
`reduce in Example :` out when only the `sem/` semantics is under test.

Individual files still run standalone (`maude -no-banner src/sem/Stmt.maude`)
and carry their expected results as trailing `*** …` comments. CI runs the
runner via `.github/workflows/maude.yml`.

## Architecture (Maude, `src/`)

Everything is built on an abstract field signature and layered upward. `load` statements wire the dependency graph.

- **`Fields.maude`** — `FIELDS{Field :: TRIV}`, the shared abstract signature, mirroring SolKey's logic-sort hierarchy (`solidityDLHeader.key` + theory headers): `Prim < StValue MemValue < Value` with `Int < Prim`, `Identity < MemValue`, and `Struct < StValue` (declared in `Storage.maude`) — storage ops take/return `StValue`, memory ops `MemValue`. `Field$Elt` splits into `PrimField` (primitive-valued, e.g. a balance), `RefField` (reference-valued, points to another object), and `MapField`; the element-kind refinements `RefArrField < RefField` / `RefMapField < MapField` mark containers whose *elements* are structs (the executable stand-in for SolKey's `find<[Struct]>` cast — they let `accountMap[2] = accountMap[1]` copy a whole entry). An `Identity` is `idC(IdentityPrim, List{Field})` — a base object plus an access path of fields.

- **`Memory.maude`** — `BANK{Field :: TRIV}`, the memory model: `addM`/`read`/`write`/`delete`/`erase` keyed by `Identity` + field path. Reads/writes are defined equationally (`read(write(m,id,sel,val),id,sel) = val`, with conditional commutation over distinct id/selector pairs). `readR` reads along a `NeList{Field}` path.

- **`Storage.maude`** — `STORAGE{Field :: TRIV}`, the storage model as nested `Struct`s: `storeSt`/`selectSt`/`find`/`save`/`push`/`pop`. `find(st, path)` navigates a `List{Field}` into nested structs. `StorageSelect.maude` is a `selectSt`-based variant.
  - **`StorageCopy.maude`** — the variant aligned with SolKey's current `structRules.key`, and the one `src/sem/` runs on. Three deltas from `Storage.maude`: (a) `save`'s leaf does **not** collapse — a struct written over a location keeps *that location's* mapping members, because Solidity never copies a mapping, so the leaf becomes an irreducible `ovr(target, source)` read through by the member's sort (`MapField` → the target's, `PrimField`/`Int` → the source's, `RefField` → a leaf one level down); (b) `delete` is sort-directed via `delValue`/`delNode`, so the exact read of a deleted struct slot is a delete-*marked* struct rather than a primitive default, and a delete of a strict descendant survives a copy of its ancestor; (c) `push()` clears the appended slot. Dispatch is entirely by sort — `Prim` vs `Struct`, and the four disjoint subsorts of `Field$Elt` — so no new `owise` is introduced. `v→st` is the Maude spelling of SolKey's `cast<[Struct]>` and is needed wherever a path step can land on a slot whose zero-init is primitive.
  - **`StorageCanonical.maude`** — a standalone generic sibling with mapping
    identity carried by values (`map(store(...))`), rather than by field sorts
    or parameterized container modules. Ordinary structs are `mtst`/`store`
    histories and arrays are `array(contents)` histories containing `length`
    but no default-entry templates. It is helper-free: `save` and `delete`
    remain lazy path-update terms interpreted selector by selector by
    `select`/`find`; exact struct/array reads therefore remain suspended while
    leaf observations implement value-copy and recursive deletion. Explicit
    `MapStruct` copy markers deliberately have no resolving equation, so the
    runtime blocks direct and nested explicit mapping copies. Types containing
    mappings but no runtime marker remain a frontend legality obligation.
    Array push/pop are compositions of the same public lazy operations, and
    deleted slots remain underneath the zero length so nested mappings survive
    later reuse. `src/sem/` remains on `StorageCopy.maude`; this variant changes
    no executable semantics.
  - **`StorageFlag.maude`** — the same copy and delete semantics with the dispatch moved: map-ness is carried by the **value** at the path (`Map < Struct`, `mapOf(tm)`, `isMap`) rather than by the field's sort, so the field signature stays a bare `TRIV` element and a contract's layout is an initial term of `decl`s. No memberships and no `owise`; an explicit `prefix` predicate replaces both.
  - **`StorageApi.maude`** — the theory `STORAGE-API` and the views `Sorted` / `Flagged` that let those two models sit in one session, which `load` alone cannot do (both define the same API under `STORAGE` / `STORAGE-FLAG`). No reductions of its own. **`StorageCompare.maude`** is the head-to-head built on it: one suite of terms, instantiated twice, with the six divergences and the reason for each. **`FindSteps.maude`** is the other consumer — it steps a `find` one equation at a time in either model (`findSteps(M, find(…))`), the storage-level analogue of what `sem/Steps.maude` does for statements. One `~>` is one equation applied *anywhere* in the term, so a nested read — the `v→st(find(st, p))` that computes the copy leaf's left side — gets its own arrows instead of being normalized away; that needs `find` to carry no equations in the stepping clone, so the clone keeps a shadow copy under `findE` for the conditional dispatch of `StorageFlag.maude` to call.

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
  which `search` explores to find/exclude the DAO drain). `Hoare.maude` adds
  the Solidity-looking triple `< prog > (post)` that reduces to `true`/`false`
  — a property checked by one `red`. `Steps.maude` adds the pre-licentiate
  paper's DERIVATION notation on top, by metaprogramming: it reflects the
  domain module with `upModule` and turns every equation whose left-hand side
  is a configuration `{ … }` (the ~43 statement equations) into a *rule*,
  leaving the helpers equational, so one rule application is one step. That
  gives `steps(< prog >)` printing `G0 ~> G1 ~> … ~> Gn` over paper-style goals
  `{ storage := … || 'v := … }< rest >`, plus `~*>` for an elided run and a
  judgement `|- G0 ~> G1 ~*> G2` that reduces to `true` exactly when the
  written derivation is the one the semantics takes. It is pure addition: the
  object semantics is untouched and `< prog > (post)` still reduces in one
  `red`. The module being reflected must NOT itself import `META-LEVEL`, which
  is why each instance is two modules (a domain, then a `pr SOL-STEPS` layer
  defining `eq theModule = 'THE-DOMAIN .`). `examples/paper/` replays the
  paper's worked examples through it, one file per section, with the
  adaptations and the not-expressible forms documented in its `README.md`.
  `examples/solkey/` is the other example corpus and the cross-check that
  matters most: it re-expresses SolKey's own proof suite
  (`~/projects/solkey/keyext.solidity.examples/TestSuite.sol`, ~199 functions,
  plus the hand-written `net/*.key` obligations) as `red < body > (post) .`
  triples that must reduce to `true` exactly when SolKey closes the
  corresponding proof. Its `README.md` carries the file ↔ SolKey-category
  table; `Store.maude` holds the shared field vocabulary and is the only file
  there with no tests. Syntax reads like Solidity: member
  access `.`, assignment `=`, equality `==`, comparisons `< <= > >=`,
  `&& || !`. Conventions: conditions are a dedicated sort `Prop` (evaluated
  by `evalP` to the truth value 1/0, so guards stay Int-based); modules are
  `SOL-`prefixed.

  **`Exp` has its own kind.** `Field$Elt` and `Value` are deliberately *not*
  subsorts of `LValue`/`Exp`. That subsorting put `Int` in `Exp`'s kind, which
  forced `+ - *` to inherit the prelude INT declarations — `assoc comm` for
  `+` and `*` — so `'i ++ + 'i` and `'i + 'i ++` were the **same term** and
  solc's evaluation order was unstatable. Consequences to know: a literal is
  injected (`'x = # 5 ;`, `$values [ # 1 ]`); a field constant usable as a
  **root** lvalue is overloaded at the sort `Root` in whichever module
  declares it, plus one `lower` equation, so program text still reads
  `$alice . $age` with no injection; `+` is a free constructor, so syntax no
  longer *computes* — `# 1 + # 2` does not fold and terms keep their source
  shape rather than an AC normal form; and the two parser advisories this
  repo used to whitelist are gone, so any warning is now a real failure.

  **`Order.maude`** is the capture pass that imposes solc's legacy-pipeline
  evaluation order — right operand before left, and RHS → receiver → index —
  by rewriting an impure statement into `capture q = e ;` bindings over fresh
  `tq(N)` temps, mirroring SolKey's `_unfold_*` taclets. It hooks in with a
  single conditional equation on the `k` cell (Maude normalizes `k` bottom-up),
  so none of the statement equations in `Stmt.maude` know about it.

  **Array indices are bounds-checked** and revert out of range, matching the
  `inBounds`/`outOfBounds` goal pair on every SolKey array index taclet;
  mappings are total and carry no such branch. A *postcondition* read is
  deliberately unchecked — the `nochk` cell — because SolKey's postconditions
  are plain `find<[int]>` terms. An in-program `assert(…)` stays checked. Where driving the models from source-level syntax exposed
  gaps in the base `STORAGE`/`BANK` specs, the fix lives in `src/sem/` and is
  flagged in-comment.

- **`src/list/`** — an alternative model expressed with a proper parameterized `FIELD` theory and Maude `view`s (`Field.maude`, `Memory.maude`, `Storage.maude`), using an assoc list representation (`_·_`, `[_=_]`).

## Running Maude — two traps

- **`*** (` opens a *bracketed* comment.** Maude reads `***(` as a comment
  running to the matching `)`, so `*** (SolKey foo): bar` silently swallows the
  `)` and everything after it — usually the terminating `.` of the *next*
  equation. No warning, no failure, just a spec that quietly means something
  else. This has bitten three times; `run-tests.sh` now lints the whole tree
  for it and fails the build.
- **Scripted runs need `-batch` and a closed stdin.** `maude file.maude` drops
  into the interactive loop and hangs; always
  `maude -no-banner -batch file.maude < /dev/null`.

## Conventions

- Modules are parameterized functional modules over `TRIV` (`{Field :: TRIV}`); concrete constants use a `$`-prefix (`$alice`, `$balance`, `$account`).
- Files come in **variants** exploring the same idea (Eager/Lazy/Select, `-fixed`); when changing behavior, check whether a sibling variant should change too, and prefer adding a variant over silently altering an existing one — they are compared against each other.
