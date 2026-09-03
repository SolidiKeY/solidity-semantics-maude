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
| `Memory.maude` | `memory*` (decl/default/deep-field/alias/delete/array-index/to-storage) | 10 |
| `PushPop.maude` | `storagePush*`, `storagePop*` | 8 |
| `Net.maude` | `net/*.key` (msg.value/sender, transfer, capture) | 7 |
| `MainFeatures.maude` | `test*` end-to-end assert programs | 8 |
| `Bool.maude` | `storageBool*` (root/field/mapping/array reads and copies) | 6 |
| `Branching.maude` | `if{,Else}{Unfold,Split}`, `ternary*` (desugared), `logical*ShortCircuitRhs` | 8 |
| `NseIndex.maude` | `*Nse*` non-simple-expression indices (storage + memory) | 7 |
| `Matrix.maude` | `storageMatrix*`, `storageIndexDecompos*` (uint[][]) | 4 |
| `ComplexReceiver.maude` | `testStorageComplexReceiver*`, `testStoragePush*Lvalue*`, `*PushReturnAlias` | 9 |
| `CrossCopy.maude` | `testMemoryToStorageCopy*`, `testStorageToMemoryCopy*`, `testMemoryFieldShallowCopy` | 8 |
| `WellFormed.maude` | `wellFormed*` (`@custom:key wellformed`) + the `WellFormedTacletGenerator` layout expansion | 6 symbolic + 6 concrete + 5 predicate checks |

## Translation dictionary

| SolKey | Maude |
|---|---|
| `\<{ f()@TestSuite; }\>(true)` | `< body-of-f > (post)` (diamond, from empty storage) |
| `/// @custom:key box` + `require(x == v)` pin | `var 'x = v ;` initializer |
| `require(arr.length == n)` size pin | `n` leading pushes (zero-init ⇒ length 0) |
| `pre -> \<{ P }\>(Q)` | set `pre` up inside `P`, or `[ storage ]< P > (Q)` |
| `\[{ P }\](false)` (box blocks) | `< P > reverts` |
| `/// @custom:key wellformed`, i.e. `wellFormed(storage) -> \<{f()}\>(true)` | `[ stW ]< body > true` — `stW`'s observed cells pinned to fresh **`Nat`** constants (the sort *is* the `0 <=` conjunct) |
| `\forall int k; 0 <= find(storage, m·at(k))` (mapping conjunct) | a `Nat`-valued operator `op mW : Int -> Nat .` |
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

1. **Increment as an expression** (`a[++i] = ++i`, `testStorageEvaluationOrder`;
   also `testMemory*Array*{in,de}crement`): here `++`/`--` are statements, not
   side-effecting expressions, and desugaring would destroy the
   evaluation-order property under test.
2. **Genuinely unbounded inputs** (`localArithmeticInRange`,
   `signedUnaryMinusInRange`: `require(1 <= x && x <= 100)`): the Hoare front
   end runs one concrete execution, so a *range* cannot be pinned to a single
   initializer — only `require(x == v)` pins are expressible. *Partly lifted*
   by `WellFormed.maude`: a universally-quantified **non-negative** cell is
   expressible as a fresh `Nat`-sorted constant plus the `NAT-LEMMAS` theorem
   equations (the `wellFormed*` mirrors run symbolically); an asymmetric range
   like `1 <= x <= 100` still is not. Caveat: the base model's `=/=` path
   guards compare normal forms, so a program comparing a *symbolic* index
   against a *concrete* one would unsoundly pass through — no mirrored
   example does (see `WellFormed.maude`'s header).
3. **`push()` as an expression** (`arr.push().value = v`, `arr.push() = x`,
   `T storage t = arr.push()`): `push` is a statement here; the
   `ComplexReceiver.maude` mirrors desugar to push-then-index/alias, which is
   the same slot.
4. **Uninitialized storage locals** (`storageLocalDeclSkip`: `Person storage p;`):
   `storage 'q = LV ;` requires an initializer.
5. **Bounded-int obligations**: ints are unbounded ("Solidity Light"), so
   width/overflow behaviour is out of scope by design.
6. **Delete-reset whole-struct read corner**: after `delete a[i]` on a
   struct-element container, the base model's exact-read equation yields `0`
   rather than `mtSt` for a *whole-struct* read of that slot (field reads are
   correct). A specialization would be nonconfluent with the exact-read /
   passthrough pair in `src/Storage.maude`; no SolKey example exercises it.

Everything else in the suite agrees with SolKey. (The former divergence
`testStorageMapStructCopy` — whole-struct copy from an Int-keyed slot — is
now supported via the `RefMapField` element-kind sort; see `MainFeatures.maude`.)
