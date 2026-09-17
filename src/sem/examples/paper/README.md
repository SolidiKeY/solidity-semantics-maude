# The paper's derivations, replayed

These files replay the worked examples of the pre-licentiate paper
(`~/projects/Pre-licenciate-paper`) against this executable semantics, using the
derivation notation that `src/sem/Steps.maude` adds: `~>` for one rule
application, `~*>` for several elided, and `|- …` for "this written derivation
is the one the semantics takes".

```sh
maude -no-banner src/sem/examples/paper/StorageExamples.maude   # one section
bash src/sem/run-tests.sh                                        # all of them
```

Each file ends in a block of reductions with the expected value in a trailing
`*** …` comment, per the repo convention. Three kinds of reduction appear:

| form | what it shows |
|---|---|
| `red steps(< prog >) .` | the derivation, `G0 ~> G1 ~> … ~> Gn` |
| `red \|- < prog > ~> { … } ~*> { … } .` | the paper's own claim about that derivation, as `true` |
| `red < prog > (post) .` | the value the paper ends at, as a Hoare triple |

## Files ↔ paper sections

| File | Section |
|---|---|
| `Domain.maude` | the running domain of `docs/PAPER.md`; no tests |
| `StorageExamples.maude` | `sections/storage-examples.tex` |
| `StorageArrays.maude` | `sections/storage-examples-arrays.tex` |
| `StorageDelete.maude` | `sections/storage-examples-delete.tex` |
| `Arithmetic.maude` | `sections/arithmetic.tex` (compound storage update) |
| `MemoryExamples.maude` | `sections/memory-examples.tex` |
| `MemoryDelete.maude` | `sections/memory-examples-delete.tex` |
| `MemoryArrays.maude` | `sections/memory-examples-arrays.tex` |
| `StorageToMemory.maude` | `sections/storage-to-memory.tex` |
| `MemoryToStorage.maude` | `sections/memory-to-storage.tex` |
| `Payment.maude` | `sections/payment.tex` |
| `EvalOrder.maude` | `sections/not-implemented.tex` |

## Translation dictionary

| paper | here |
|---|---|
| `alice.age` | `$alice . $age` |
| `⟨alice⟩.account` (an access path) | `$alice $account`, shown in a goal as `sp($alice $account)` |
| `{storage := …} φ` | `{ storage := … }` |
| `{x := v} ⟨rest⟩φ` | `{ 'x := v }< rest >` |
| `⇝` / `⇝*` | `~>` / `~*>` |
| `Account storage acc = …;` | `storage 'acc = … ;` |
| `Person memory carol;` | `memory 'carol = new ;` |
| `Token memory t = e;` | `memory 't = e ;` (**not** `var`: `var` takes a value) |
| `uint v = e;` | `var 'v = e ;` |
| `idC(r, [])` | `idC(pid(0), nil)`, fresh ids in allocation order |
| `add(mem, r)` | `addM(emptyMemory, pid(0))` |
| a literal | `# 5`; a symbolic value is a free constant, `# ageVal` |

## Systematic adaptations

The paper reasons about a **symbolic** `storage` and `memory`; these runs start
from `mtSt` and `emptyMemory`. That accounts for most of the differences:

1. **A read needs a preceding write.** `v = alice.age` becomes
   `$alice . $age = # ageVal ; var 'v = $alice . $age ;`. The value stays
   symbolic — `ageVal` is a free `Int` and flows through `save`/`find`
   unevaluated — so the final update really is the paper's.
2. **Array indices are concrete, mapping keys need not be.** A storage array
   index is bounds-checked, so arrays are grown with `push` first and the index
   is a numeral. Mappings are total and carry no bounds branch, so the paper's
   symbolic key survives (see `StorageExamples.maude` at `:265`, and the
   `m[i++] = i` derivation in `EvalOrder.maude`).
3. **The paper's box/diamond split becomes two runs**, one per branch: the
   in-bounds one, and an out-of-bounds twin ending `{ status := reverted }`.
4. **Memory arrays are allocated with a size and populated before being read.**
   `BANK` has no default for an `Int` selector (`src/Memory.maude:39-41`), so an
   untouched memory slot is not readable, where storage zero-initializes.
5. **Guards must decide.** A symbolic `require`/`if` would be discharged by
   `=/= 0` and pass vacuously, so conditions are concrete.

## Granularity: what one `~>` is

One `~>` is one **statement rule**, where the paper's `⇝` is one taclet. For a
**pure** statement the two differ: `alice.account.balance = 10;` is a single
rule here, where the paper first unfolds it into `pv` and `acc` temps. The final
update is the same.

For an **impure** statement they line up exactly, because `Order.maude`
transcribes SolKey's `_unfold_*` taclets: the capture pass fires as its own
step and emits `capture tq(0) = … ;` bindings that are the paper's `pv`, `idx1`,
`idx2`. `matrix[i++][i++] = 77;` is the clearest case — see
`StorageExamples.maude` at `:550`.

The desugarings `+=`, `++ ;`, `while`, `if_{_}` are themselves k-cell equations,
so each is its own visible `~>` rather than being folded away.

## Not expressible here

Listed at the point they arise in each file, and collected here:

- **A function call in expression position** — `makeValue()`,
  `choosePersonMem()`, `makeAccount()`. Where the paper's own first step binds
  the result to a local, that unfolded form is run instead.
- **`push()` as an expression** — `values.push() = e`, `tokens.push().value = v`,
  `T storage lsv = arr.push()`. Desugared to a bare `push();` plus an index
  write, which is the same slot. One case is a genuine difference, not a
  notational one, and is flagged in `StorageExamples.maude` at `:374`: the
  statement `push()` **clears** the appended slot where the paper's binding form
  does not, so that example would read 0 where the paper reads 7.
- **The diamond half of the payment rules** — there is no `selfBalance` cell and
  no sufficient-funds branch in `src/sem/Net.maude`, so `0 <= v <= selfBalance`
  has no image. The box half of every payment example is exact.
- **Bounded integers** — `uint8 x = 250; x += 10;` does not overflow; ints are
  unbounded by design ("Solidity Light").
- **The unsound derivation for `m[i++] = i;`** is absent *by construction*:
  `Order.maude` implements the paper's Repair 1, so the rule that made the
  original derivation unsound does not exist. Both repairs are shown.
