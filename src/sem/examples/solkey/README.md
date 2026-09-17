# SolKey cross-check suite

These files re-express the SolKey / SolidiKeY example corpus as Maude Hoare
triples, so we can check that this executable semantics **agrees with what
SolKey proves**. The mirror source is
`~/projects/solkey/keyext.solidity.examples/TestSuite.sol` (~199 functions,
each proved by SolKey as `\<{ f()@TestSuite; }\>(true)` with the spec inline
as `assert`s); the `Net.maude` mirrors come from the hand-written `.key`
obligations in `keyext.solidity.examples/net/`. Each mirrored function body
becomes a `red < body > (post) .` that reduces to `true` exactly when SolKey
closes the corresponding proof.

Run them all (each file is standalone; expected result in a trailing `***`
comment on every line):

```sh
bash ../../run-tests.sh            # includes this suite
maude -no-banner Storage.maude     # or one category
```

## Files ↔ SolKey categories

| File | Mirrors (`TestSuite.sol` functions unless noted) | Triples |
|---|---|---|
| `Store.maude` | shared TestSuite.sol field vocabulary + sorts (no tests) | — |
| `Arithmetic.maude` | `addition*`, `subtraction*`, `unaryMinus`, `multiplication`, `division`, `modulo`, `power`, `less/greater*`, `notEqual`, `logicalAnd/Or/Not` | 25 |
| `Storage.maude` | `storageField*` (read/write/copy/delete/compound/inc-dec), `storageAlias*`, `storageIndex*` (arrays + mappings) | 31 |
| `Copy.maude` | `testCopy*` ("mapping members stay the target's own"), `storage*DeleteThenCopy*`, `storage/copyKeepsMapping.key` | 22 |
| `Memory.maude` | `memory*` (decl/default/deep-field/alias/delete/array-index/to-storage) | 10 |
| `PushPop.maude` | `storagePush*`, `storagePop*` | 8 |
| `Net.maude` | `net/*.key` (msg.value/sender, transfer, capture) | 7 |
| `MainFeatures.maude` | `test*` end-to-end assert programs | 8 |
| `Bool.maude` | `storageBool*` (root/field/mapping/array reads and copies) | 6 |
| `Branching.maude` | `if{,Else}{Unfold,Split}`, `ternary*` (desugared), `logical*ShortCircuitRhs` | 8 |
| `NseIndex.maude` | `*Nse*` non-simple-expression indices (storage + memory) | 7 |
| `Matrix.maude` | `storageMatrix*`, `storageIndexDecompos*` (uint[][]) | 4 |
| `Bounds.maude` | the `inBounds`/`outOfBounds` goal pair on every storage array index taclet | 16 |
| `EvalOrder.maude` | `addition*`/`subtraction*`/`lessThan*` operand order, `testStorage*ImpureIndex*`, `testStorageEvaluationOrder`, `testNestedIndexWrite*`, `testStoragePushImpureReceiver`, `testCompoundAssignImpureReceiver` | 20 |
| `ComplexReceiver.maude` | `testStorageComplexReceiver*`, `testStoragePush*Lvalue*`, `*PushReturnAlias` | 9 |
| `CrossCopy.maude` | `testMemoryToStorageCopy*`, `testStorageToMemoryCopy*`, `testMemoryFieldShallowCopy` | 8 |

## Translation dictionary

| SolKey | Maude |
|---|---|
| `\<{ f()@TestSuite; }\>(true)` | `< body-of-f > (post)` (diamond, from empty storage) |
| `/// @custom:key box` + `require(x == v)` pin | `var 'x = v ;` initializer |
| `require(arr.length == n)` size pin | `n` leading pushes (zero-init ⇒ length 0). **Mandatory**, not cosmetic: storage array indices are bounds-checked, so an unpinned index reverts |
| `pre -> \<{ P }\>(Q)` | set `pre` up inside `P`, or `[ storage ]< P > (Q)` |
| `\[{ P }\](false)` (box blocks) | `< P > reverts` |
| `alice.age` | `$alice . $age` |
| `values[1]`, `values.push(x)` | `$values [ 1 ]`, `$values .push(x)` |
| `TRUE` / `FALSE` | `1` / `0` (bools are EVM ints) |
| `find<[int]>(storage, cons2(A,B))` | `$A . $B` (read in the postcondition) |
| `find<[Struct]>` at an Int key | the container field's `RefMapField`/`RefArrField` sort |
| `selectSt<[int]>(net, at(a))` | `net[a]` |

## Field sorts

`Store.maude` stamps each field constant with the sort SolKey's parser would
give it (`fieldSortFor` + the mapping/array value sorts): value members are
`PrimField`, struct/array members `RefField`, mapping members `MapField`, and
the element-kind refinements `RefArrField < RefField` / `RefMapField <
MapField` mark containers whose *elements* are structs — the executable
stand-in for SolKey's `find<[Struct]>` cast, and what makes whole-entry
copies like `accountMap[2] = accountMap[1]` reduce.

## Known divergences / out of scope (found by this cross-check)

Documented at the point they arise (file headers):

1. **Increment as an expression** — *resolved*, see `EvalOrder.maude`. `++`/`--`
   are now `Exp` constructors and `Order.maude` imposes solc's legacy-pipeline
   order (right operand before left; RHS → receiver → index). Two changes had
   to land together: making `++` an expression, and cutting `Int` out of `Exp`'s
   kind so `+` and `*` stopped inheriting the prelude's `assoc comm` — under AC
   `'i ++ + 'i` and `'i + 'i ++` were the *same term*, so at most one of them
   could ever have been right. Residuals:
   - an impure **right operand of `&&`/`||`**: short-circuiting means it must
     not be hoisted, and evaluating it in place would need an effectful `eval`;
   - an impure **`while` guard**: the guard is re-evaluated per iteration, so
     hoisting it would change the loop. `pureS(while …)` is `true` by design;
   - SolKey's **receiver snapshot** for a *simple* receiver that the index
     expression reassigns (`testIndexWriteReceiverReadsMutatedVar`). Nested
     index writes are handled — each index is pinned into a temp as `linL`
     walks — but a storage-alias local mutated by the index is not re-read.
   Any shape `lin` does not cover leaves a stuck `eval(…)` term that
   `run-tests.sh` catches, so the failure mode is loud, never silently wrong.
2. **Genuinely unbounded inputs** (`localArithmeticInRange`,
   `signedUnaryMinusInRange`: `require(1 <= x && x <= 100)`; and the
   `wellFormed*` functions, `/// @custom:key wellformed`, i.e.
   `wellFormed(storage) -> \<{f()}\>(true)` over *every* storage matching
   the layout): the Hoare front end runs one concrete execution, so a
   *range* cannot be pinned to a single initializer — only `require(x == v)`
   pins are expressible — and a universally quantified storage cannot be
   expressed at all. (Symbolic cells are not an option: a guard that does
   not reduce to a numeral is discharged by `=/= 0` in `Flow.maude`, so a
   symbolic `assert`/`require`/`if` would pass vacuously.) The *structural* half of `wellFormed` — the
   three facts the Lean twin found its `wellTypedStorageB` predicate misses (a
   mapping default is the type default, keys are unique, a struct has exactly
   its declared fields) — is instead built into the sorts of
   `src/StorageCanonical.maude`, where a storage is well-formed iff it has a
   sort; only the arithmetic (range) half stays out of scope.
3. **`push()` as an expression** (`arr.push().value = v`, `arr.push() = x`,
   `T storage t = arr.push()`): `push` is a statement here; the
   `ComplexReceiver.maude` mirrors desugar to push-then-index/alias, which is
   the same slot. One consequence to keep in mind: the statement `push()`
   *clears* the appended slot (SolKey `storagePushLengthSave`), whereas
   SolKey's binding form `lsv = arr.push()` deliberately does not. The
   desugaring therefore clears where SolKey would not — harmless in every
   mirrored example, since the slot is fresh there, but it is a real
   difference in the general case.
4. **Uninitialized storage locals** (`storageLocalDeclSkip`: `Person storage p;`):
   `storage 'q = LV ;` requires an initializer.
5. **Bounded-int obligations**: ints are unbounded ("Solidity Light"), so
   width/overflow behaviour is out of scope by design.
6. **Delete-reset whole-struct read corner** — *closed* by
   `src/StorageCopy.maude`. The exact read of a deleted struct slot is now the
   delete-marked struct `delNode(…)` rather than `0`, mirroring SolKey's
   `delValue`/`delNode`, so `delete a[i] ; p = a[i] ;` composes and the
   `RefArrField`/`RefMapField` sort stamp is respected on that corner. See the
   discriminating triples in `Copy.maude`. Closing it also turned up, and
   fixed, a second divergence in the same area: a **delete of a strict
   descendant used to be lost when an ancestor was copied**
   (`delete b.xs ; a = b ;` copied the *pre-delete* `b`), because a whole-path
   `find` fell through `delAt`'s disjoint-path passthrough. SolKey never had
   this — `selectOnDelAtCons` peels one selector at a time and rebuilds
   `delAt(selectSt(st,a1), flds)` — so `StorageCopy.maude` now re-suspends the
   delete on the extracted subtree. `src/Storage.maude` still has both.

Everything else in the suite agrees with SolKey. (The former divergence
`testStorageMapStructCopy` — whole-struct copy from an Int-keyed slot — is
now supported via the `RefMapField` element-kind sort; see `MainFeatures.maude`.)
