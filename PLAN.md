# PLAN — A SolidiKeY-style Solidity Semantics in Maude

Goal: grow this repository from a formalization of Solidity's *data locations*
(memory, storage, and copies between them) into a formalization of *Solidity
program semantics* comparable in coverage to SolKey/SolidiKeY
(`~/projects/solkey`, the KeY fork with `keyext.solidity.core`), but expressed
as an **executable rewriting-logic semantics** rather than a dynamic-logic
taclet calculus.

The guiding correspondence:

| SolidiKeY (KeY taclets) | Here (Maude) |
|---|---|
| Sequent + update `{storage := save(...)}` | Configuration term `< stmts \| storage \| memory \| net \| env >` rewritten by rules |
| Symbolic execution taclet per statement shape | One rewrite rule (or equation) per statement shape |
| Splitting rules (`if`, `x/0` revert branch) | Rewrite rules explored with `search` (all branches) |
| Storage logic (`store`/`select`/`find`/`save`, `delNode`) | Already here: `src/Storage.maude` — reuse as-is |
| Memory heap (`Identity`, aliasing, `copySt`/`copyMem`) | Already here: `src/Memory.maude` + translation files |
| Proof obligation (paper eq. 4) | `search` / `red` checks; LTL model checking for re-entrancy |

Scope discipline follows the paper (Ahrendt & Bubel, ISoLA 2020) and SolKey's
"Solidity Light": unbounded ints (no overflow branches), no gas, no bitwise
ops, no inheritance. Same tiering as `solkey/docs/taclet-ideas.md`.

## Design decisions (made up front)

1. **Deep embedding, small-step semantics.** A `SOLIDITY-SYNTAX` module defines
   `Exp`, `Stmt`, `LValue` sorts as constructors; a system module rewrites a
   configuration. This is the standard Maude/K style and lets `search`
   enumerate revert branches and callback interleavings — the analogue of
   KeY's proof splits.

2. **Equations for deterministic steps, rules for genuine branching.**
   Expression evaluation, assignment, `delete`, `push`/`pop` are confluent →
   `eq`/`ceq` in functional modules (fast, usable under `red`). Only
   nondeterminism gets `rl`/`crl`: external-call callbacks (havoc/re-entrancy)
   and, if we later model it, gas exhaustion. `require`/`revert` are
   deterministic (the guard value decides) and stay equational, producing a
   distinguished `reverted` configuration.

3. **Reuse the existing state layer unchanged.** The canonical pair is the
   nested lazy model: `src/Storage.maude` (`STORAGE`: `store`/`select`/`find`/
   `save`/`push`/`pop`, lazy `delete` that skips `MapField`) and
   `src/Memory.maude` (`BANK`: `add`/`read`/`write`/`delete`/`erase`), with
   `StorageToMemoryLazy.maude` / `MemoryToStorage.maude` for cross-location
   copies. The other variants stay as comparison artifacts, per repo
   convention. New semantics files `load` these; they do not fork them.

4. **`net` is a second storage term, not a field of `storage`** — exactly the
   SolKey decision (`solkey/docs/net.md` §3): `net` lives in its own
   configuration slot so `delete`, havoc, and `old`-style snapshots never
   touch it. `address` is modeled as the parameter sort used for map keys;
   `net(a) = 0` initially falls out of select-on-empty + default value.

5. **Paths are the interface between syntax and state.** Solidity lvalues
   (`s.member`, `a[i]`, aliases) lower to the `List{Field}` access paths that
   `find`/`save` already consume — the analogue of SolKey's `\sameAsTerm`
   lowering (`StoragePath` → logic `List`, `arr.length` → `size`, `a[i]` →
   `at(i)`). Storage-reference locals bind to *paths*, not values (SolKey's
   "storage aliases": `Token storage t = tokens[i];` binds `t` to the path).

6. **New code goes in `src/sem/`** so the existing flat-spec convention (each
   file self-contained, trailing `red`/`rew` block as its test suite, expected
   results in `*** …` comments) is preserved and module-name clashes with the
   sibling variants are avoided. Parameterization over `{Field :: TRIV}`
   continues; concrete test constants keep the `$`-prefix.

## File layout (target)

```
src/sem/
  Syntax.maude        -- Exp, Stmt, LValue, Block constructors (deep embedding)
  Path.maude          -- lvalue → List{Field} lowering; storage-alias binding
  Config.maude        -- configuration sort, env (locals), revert marker
  Expr.maude          -- big-step expression evaluation (Tier 1)
  Stmt.maude          -- assignment family, decl, delete, push/pop (Tier 2)
  Flow.maude          -- if / while / return / require / assert / revert (Tier 3)
  Net.maude           -- net ledger, msg, transfer (no-callback)
  NetCallback.maude   -- with-callback transfer, invariants, re-entrancy (rules)
  Contract.maude      -- contract decl, function table, call/inline, constructor
  examples/
    Bank.maude        -- the PaperTest.sol-style end-to-end suite
    Casino.maude      -- (stretch) the ISoLA paper's running example
```

Each phase below ends with its file(s) runnable standalone:
`maude -no-banner src/sem/<file>.maude`, green when no term is stuck and
outputs match the trailing `*** …` comments.

## Phase 0 — Groundwork: syntax + configuration

*Deliverables: `Syntax.maude`, `Config.maude`, `Path.maude`.*

- `Syntax.maude`: sorts `Exp < Stmt` ingredients — literals, variables,
  `_+_`, `_-_`, `_*_`, `_/_`, `_%_`, `_**_`, comparisons, `_&&_`, `_||_`,
  `!_`, unary `-`; lvalues `lv(root, path)`; statements `_:=_`, `_+=_` … ,
  `_++`/`++_` (pre/post), `decl`, `delete_`, `_.push(_)`, `_.pop`,
  `require_`, `assert_`, `revert`, `if_then_else_`, `while_do_`, `return_`,
  `skip`, `_;_` (sequencing). Mixfix with backquoted syntax so test terms read
  close to Solidity.
- `Config.maude`: sort `Conf` with constructor
  `< Stmt | Storage | Memory | Net | Env | Msg >` plus terminal forms
  `done(...)` and `reverted(...)`. `Env` maps local names to `Value`s,
  storage-alias paths (`List{Field}`), or memory `Identity`s — three
  distinguishable binding constructors, mirroring SolKey's
  `DataLocation`-disjoint program variables.
- `Path.maude`: `lower : LValue Env -> List{Field}` — resolves aliases,
  turns index access into `at(i)` fields, `.length` into `size`. This is where
  SolKey's simple/complex path distinction collapses: Maude evaluates index
  expressions before lowering, so no unfold-capture rules are needed.
- Tests: pure syntax reductions + path lowering on the bank signature from
  `bank-sort.maude`.

## Phase 1 — Expressions (SolKey Tier 1)

*Deliverable: `Expr.maude`.*

- Big-step `eval : Exp Conf -> Value?` where `Value? ::= val(Value) | rev` —
  `rev` propagates division/modulo by zero (SolKey's `/`,`%` revert guard).
  Unbounded integer arithmetic (Solidity Light; no overflow branch, matching
  SolKey's use of plain LDT ops).
- Reads: local lookup, `find` on storage paths, `read`/`readR` on memory
  identities — reusing the loaded state modules directly.
- `&&`/`||` short-circuit is *free* here (equational order of evaluation),
  unlike SolKey where it was deferred pending the `if` taclet — note this as a
  deliberate semantic commitment and add tests that pin it (RHS of `&&` with a
  reverting subterm).
- Tests: the Tier-1 matrix from `solkey/docs/taclets-implementation.md`
  ("Tier-1 expression operators"), including `x / 0` ⇒ `rev`.

## Phase 2 — Statements: the assignment family (SolKey Tier 2)

*Deliverable: `Stmt.maude`.*

- `step : Conf -> Conf` equations for:
  - local decl/assign; storage write at root/field/index via `save`; memory
    write via `write`.
  - whole-struct assignment = the four location pairs: storage→storage
    (value copy via `find` + `save`), storage→memory (`copySt`, lazy —
    load `StorageToMemoryLazy.maude`), memory→storage (`copyMem`, load
    `MemoryToStorage.maude`), memory→memory (reference aliasing, no copy).
    **This is the repo's core artifact finally driven from source-level
    syntax** — the tests here should reproduce the existing translation
    files' reductions from program terms.
  - compound assignments `+= -= *= /= %=` (with `/=`,`%=` reverting on zero),
    `++`/`--` pre/post incl. value-producing forms, desugared by equations
    into core reads+writes (Maude can desugar honestly; KeY needed direct
    rules only because desugaring in-sequent is awkward — record this note).
  - `delete`: dispatch to the existing storage `delete` (lazy `delValue`/
    mapping-skipping semantics already in `Storage.maude`) and memory delete;
    add the *dynamic-array delete = length reset*, which SolKey lists as an
    open refinement — a chance to get ahead of the reference.
  - `push`/`pop` on storage arrays: reuse `push`/`pop` from `Storage.maude`;
    `pop` on empty ⇒ `reverted`; popped slot cleared with the
    mapping-preserving delete (SolKey's `delNode` discipline — verify the
    existing Maude `pop` already matches; if not, fix in a `-variant` file
    per repo convention and flag for the Agda/F*/Prolog twins).
  - storage-alias declaration and rebinding (path-valued locals).
- Tests: port the SolKey focused-example matrix (`keyext.solidity.examples/
  taclets/`) — root/field/index × read/write/copy/inc-dec/compound, aliases,
  push/pop incl. RHS-before-LHS evaluation order (`testStorageEvaluationOrder`),
  deep-pop-preserves-mapping (`testDeepPopDoesNotResetMappingMember`).

## Phase 3 — Control flow (SolKey Tier 3: the keystone)

*Deliverable: `Flow.maude`.*

- `if`/`else`, `while` (direct rewriting — no invariant needed to *execute*;
  `search` gives bounded exploration where KeY needs unrolling taclets),
  `for` desugared to `while`, `return e` binding the named return value and
  discarding the block continuation (an abrupt-completion marker consumed by
  `_;_`), `break`/`continue` via the same marker sort.
- `require(c)` ⇒ `reverted` on false (state rolled back to the *entry*
  snapshot — carry the snapshot in the configuration); `assert(c)` ⇒ a
  distinguished `failed` terminal, keeping SolKey's require/assert distinction
  (`require-assert.md`): require-failure is a normal outcome, assert-failure
  is a bug the checks hunt for.
- Tests: guard-splitting examples run under `search` (both branches reachable),
  loop that computes a sum, revert restores pre-state.

## Phase 4 — Payments: `net`, `msg`, `transfer` (the ISoLA model)

*Deliverables: `Net.maude`, then `NetCallback.maude`.*

- `Net.maude` (no-callback slice, = SolKey's implemented Steps 1–3):
  `net` as a storage term keyed by address (`at(a)`), `msg.sender`/`msg.value`
  as `Msg` record fields in the configuration, `a.transfer(v)` ⇝ subtract `v`
  at `at(a)` in `net` (revert if the contract's own net balance is
  insufficient — the paper's implicit balance check). Entry protocol:
  invoking a public function adds `msg.value` to `net(msg.sender)`; a
  non-payable function requires `msg.value == 0`.
- `NetCallback.maude` (SolKey's *unimplemented* Step 4 — here Maude gets ahead
  of the reference): with-callback external calls as **rewrite rules** that
  nondeterministically re-enter public functions of the contract with fresh
  `msg` values. Strong data integrity ("invariant `I` holds whenever control
  leaves") becomes checkable: `search` for a reachable state where control is
  outside and `I` fails, or model-check `[] (outside -> I)` with Maude's LTL
  model checker on a finitized instance.
- Tests: the five `net-*` starter shapes from SolKey; a two-contract
  re-entrancy example where the naive contract violates its invariant
  (`search` finds it) and the guarded one doesn't (`search` exhausts).

## Phase 5 — Contracts and calls (SolKey Tier 4)

*Deliverable: `Contract.maude`.*

- Contract = function table (name ⇒ params/body/payability) + storage layout
  + constructor. Internal calls inline the body (SolKey's
  `ExpandFunctionBody`); external calls go through the Phase-4 protocol.
- `new` for memory structs/arrays (fresh `Identity` via a counter in the
  configuration — deterministic, unlike KeY's skolem branch), struct literals
  `Token(42)` as struct-value sources for copy/push (unblocks SolKey's own
  disabled `testStorageArrayPushPop` scenario).
- `emit` = skip after evaluating args (optionally append to an event log slot
  for observability in tests).
- Deferred, recorded as non-goals for now (same as SolKey Tier 5): bitwise
  ops, casts/width truncation, `try`/`catch`, slices, gas, `block.*`.

## Phase 6 — Verification story and cross-checks

- **Example suites as executable tests**: `examples/Bank.maude` mirrors
  SolKey's `PaperTest.sol` mainFeatures matrix end-to-end; every file keeps
  the repo's trailing `red`/`rew`-with-expected-comment convention.
- **Differential testing against SolKey**: the same source programs exist as
  `.key` problems in solkey; where both close/reduce, the final
  storage/memory/net terms must agree. Extend `random.maude` to generate
  random statement sequences over the bank signature and compare Maude runs
  against solc-executed ground truth (or the Prolog model) — the semantics
  analogue of the existing random term testing.
- **Cross-formalization**: per repo convention, semantic *state-layer* changes
  (e.g. if pop-clearing needs fixing) get matching updates in
  `proofs/` (Agda), `fstar/`, `prolog/`. The new statement semantics itself
  starts Maude-only; porting `Stmt`/`Flow` to Agda for metatheory (e.g.
  determinism of the equational fragment, revert-restores-state) is a
  stretch goal, not a phase gate.
- **CI**: extend `.github/workflows/maude.yml` to run each `src/sem/` root
  file; fail on `maude` output containing stuck operator terms (grep for the
  module's constructors in the result line, as the expected-comment
  convention already implies).

## Order of work and dependencies

Phases are sequential (each `load`s the previous). Suggested first milestone
worth a commit each: **0+1** (expressions evaluate over real storage/memory),
**2** (the copy semantics driven from syntax — the research payoff), **3**
(first `search`-based branching), **4** (re-entrancy checking — the headline
result SolKey hasn't reached yet), **5–6** (breadth + regression depth).

Known risks:
- Full Maude dependence: parameterized modules already require it in CI; the
  system-module + `search`/model-checker phases (3–4) should be checked early
  against Full Maude compatibility (metaInterpreter alternative if it bites).
- Module-name clashes: `src/sem/` must not reuse `STORAGE`/`BANK` variant
  names; prefix new modules `SOL-` (e.g. `SOL-SYNTAX`, `SOL-CONFIG`).
- Revert-as-rollback needs the entry snapshot threaded through nested calls
  (per-call frames), which interacts with Phase-5 inlining — design the
  configuration's call-frame stack in Phase 0 even though it's only exercised
  in Phase 5.
