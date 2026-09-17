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

**Verifying.** There is no import-all entry point, and there can't be one — sibling variants deliberately reuse module names (`STORAGE` is defined by `Storage.maude`, `StorageCopy.maude`, `StorageSelect.maude`, and `list/Storage.maude`; `BANK` by `Memory.maude` and `bank.maude`; `MemoryToStorage`/`StorageToMemory` by three files each), so loading them into one session clashes. Instead run each spec on its own: its trailing `red`/`rew` block is that file's test suite (loading a file also runs the reductions of everything it `load`s), and expected results are written inline as trailing `*** …` comments — a spec is "green" when no reduction is left stuck and the outputs match those comments. The `load`-graph roots that transitively cover the tree are the six translation files, `random.maude`, and `list-constructor.maude`, plus the `list/` specs (`list/Storage.maude`, `list/Memory.maude`), `StorageCanonical.maude` and `StorageCopy.maude`. The storage `delete` reductions (per Solidity, `delete` must skip mappings — see the `MapField` sort in `Fields.maude`/`list/Field.maude`) live in `src/Storage.maude` (nested / lazy) and `src/list/Storage.maude` (flat / eager); verify them with `maude -no-banner src/Storage.maude` and `maude -no-banner src/list/Storage.maude`.

**`src/sem/` runs on `StorageCopy.maude`, not `Storage.maude`.** The `load` at `src/sem/Config.maude` is the single switch between them.

**The `src/sem/` executable semantics** is the one part of the tree with a
proper `load` chain and a runner. It layers a small-step Solidity semantics
on top of the storage/memory models (see `PLAN.md`): `Syntax` → `Config` →
`Expr` → `Order` → `Stmt` → `Flow` → `Net` → `Contract` → `NetCallback` (a
system `mod`), plus `examples/Bank.maude`. Two further roots branch off
`Contract`: `Hoare.maude`, and `Steps.maude` → `examples/paper/Domain.maude` →
the eleven `examples/paper/` sections. **Keep that chain linear** —
Maude's `load` is not idempotent, so a diamond re-executes the whole preamble
and silently duplicates modules. Run the whole suite (each file green
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

Other tools:
- **Agda** (`proofs/`): a library rooted at `proofs/proofs.agda-lib` (`name: testing`, depends on `standard-library` and `cubical`). Files use `{-# OPTIONS --rewriting #-}`. Type-check with `agda proofs/<file>.agda`.
- **F\*** (`fstar/`): config in `fstar/fstar.fst.config.json` (include dir `.`). Verify with `fstar.exe fstar/<file>.fst`.
- **Prolog** (`prolog/`): SWI-Prolog with `clpfd`. Load with `swipl prolog/Memory.pl`.

## Architecture (Maude, `src/`)

Everything is built on an abstract field signature and layered upward. `load` statements wire the dependency graph.

- **`Fields.maude`** — `FIELDS{Field :: TRIV}`, the shared abstract signature, mirroring SolKey's logic-sort hierarchy (`solidityDLHeader.key` + theory headers): `Prim < StValue MemValue < Value` with `Int < Prim`, `Identity < MemValue`, and `Struct < StValue` (declared in `Storage.maude`) — storage ops take/return `StValue`, memory ops `MemValue`. `Field$Elt` splits into `PrimField` (primitive-valued, e.g. a balance), `RefField` (reference-valued, points to another object), and `MapField`; the element-kind refinements `RefArrField < RefField` / `RefMapField < MapField` mark containers whose *elements* are structs (the executable stand-in for SolKey's `find<[Struct]>` cast — they let `accountMap[2] = accountMap[1]` copy a whole entry). An `Identity` is `idC(IdentityPrim, List{Field})` — a base object plus an access path of fields. The Agda/F\*/Prolog twins still use the flat pre-hierarchy names (`store`/`select`/`add`/`del`/`default`/`IdField`/`PrimIdentity`).

- **`Memory.maude`** — `BANK{Field :: TRIV}`, the memory model: `addM`/`read`/`write`/`delete`/`erase` keyed by `Identity` + field path. Reads/writes are defined equationally (`read(write(m,id,sel,val),id,sel) = val`, with conditional commutation over distinct id/selector pairs). `readR` reads along a `NeList{Field}` path.

- **`Storage.maude`** — `STORAGE{Field :: TRIV}`, the storage model as nested `Struct`s: `storeSt`/`selectSt`/`find`/`save`/`push`/`pop`. `find(st, path)` navigates a `List{Field}` into nested structs. `StorageSelect.maude` is a `selectSt`-based variant.
  - **`StorageCopy.maude`** — the variant aligned with SolKey's current `structRules.key`, and the one `src/sem/` runs on. Three deltas from `Storage.maude`: (a) `save`'s leaf does **not** collapse — a struct written over a location keeps *that location's* mapping members, because Solidity never copies a mapping, so the leaf becomes an irreducible `ovr(target, source)` read through by the member's sort (`MapField` → the target's, `PrimField`/`Int` → the source's, `RefField` → a leaf one level down); (b) `delete` is sort-directed via `delValue`/`delNode`, so the exact read of a deleted struct slot is a delete-*marked* struct rather than a primitive default, and a delete of a strict descendant survives a copy of its ancestor; (c) `push()` clears the appended slot. Dispatch is entirely by sort — `Prim` vs `Struct`, and the four disjoint subsorts of `Field$Elt` — so no new `owise` is introduced. `v→st` is the Maude spelling of SolKey's `cast<[Struct]>` and is needed wherever a path step can land on a slot whose zero-init is primitive.
  - **`StorageCanonical.maude`** — the typed sibling: well-formedness *by construction*, the Maude answer to the Lean twin finding that its `wellTypedStorageB` predicate is not tight (mapping default ≠ type default, duplicate keys, missing struct fields). Each struct type is a sort with one fixed-arity constructor (`Account : Int Token -> Account`, `Account < Struct`); `SOL-MAPPING{V :: VALTY}` / `SOL-ARRAY{V}` are parameterized over the value type (views `IntV`, `AccountD`, …) and carry it as a sort-level tag; entries are `assoc comm id:` with idempotency, a doubly-bound key normalizes to the sortless `conflict(K)`, and `K |-> default = empty` makes mappings extensional. A storage is well-typed iff it has a sort (`t :: Struct`) — no membership axioms, no checker predicate. Same `find`/`save`/`push`/`pop`/`delete` API; `src/sem/` still runs on the lazy model.

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
  adaptations and the not-expressible forms documented in its `README.md`. Syntax reads like Solidity: member
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
  flagged in-comment for the Agda/F\*/Prolog twins.

- **`src/list/`** — an alternative model expressed with a proper parameterized `FIELD` theory and Maude `view`s (`Field.maude`, `Memory.maude`, `Storage.maude`), using an assoc list representation (`_·_`, `[_=_]`).

## Conventions

- Modules are parameterized functional modules over `TRIV` (`{Field :: TRIV}`); concrete constants use a `$`-prefix (`$alice`, `$balance`, `$account`).
- Files come in **variants** exploring the same idea (Eager/Lazy/Select, `-fixed`); when changing behavior, check whether a sibling variant should change too, and prefer adding a variant over silently altering an existing one — they are compared against each other.
- The same model is intentionally duplicated across Maude/Agda/F\*/Prolog; a semantic change in one usually needs a matching change in the others.
