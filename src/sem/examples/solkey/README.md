# SolKey cross-check suite

These files re-express the SolKey / SolidiKeY example problems
(`~/projects/solkey/keyext.solidity.examples`) as Maude Hoare triples, so we
can check that this executable semantics **agrees with what SolKey proves**.
Each SolKey `.key` diamond problem `\<{ P }\>(Q)` becomes a `red < P > (Q) .`
that reduces to `true` exactly when SolKey closes the corresponding proof.

Run them all (each file is standalone; expected result in a trailing `***`
comment on every line):

```sh
bash ../../run-tests.sh            # includes this suite
maude -no-banner Storage.maude     # or one category
```

## Files ↔ SolKey categories

| File | Mirrors (SolKey `taclets/` unless noted) | Triples |
|---|---|---|
| `Store.maude` | shared PaperStore.sol field vocabulary (no tests) | — |
| `Arithmetic.maude` | `addition-*`, `multiplication`, `division`, `modulo`, `power`, `less/greater-*`, `not-equal`, `logical-and/or/not` | 22 |
| `Storage.maude` | `storage-field-*` (read/write/copy/delete/compound/inc-dec), `storage-alias-*`, `storage-index-*` (arrays + mappings) | 28 |
| `Memory.maude` | `memory-*` (decl/default/deep-field/alias/delete/array-index/to-storage) | 10 |
| `PushPop.maude` | `storage-push-*`, `storage-pop-*` | 8 |
| `Net.maude` | `net-*` (msg.value/sender, transfer, capture) | 7 |
| `MainFeatures.maude` | `mainFeatures/` end-to-end assert programs | 7 |

## Translation dictionary

| SolKey `.key` | Maude |
|---|---|
| `\<{ P }\>(Q)` | `< P > (Q)` (diamond, from empty storage) |
| `pre -> \<{ P }\>(Q)` | set `pre` up inside `P`, or `[ storage ]< P > (Q)` |
| `\[{ P }\](false)` (box blocks) | `< P > reverts` |
| `alice.age` | `$alice . $age` |
| `values[1]`, `values.push(x)` | `$values [ 1 ]`, `$values .push(x)` |
| `TRUE` / `FALSE` | `1` / `0` (bools are EVM ints) |
| `find<[int]>(storage, cons2(A,B))` | `$A . $B` (read in the postcondition) |
| `selectSt<[int]>(net, at(a))` | `net[a]` |

## Known divergences (found by this cross-check)

Two SolKey-provable behaviours are **out of scope** for this untyped model,
and are documented at the point they arise (`MainFeatures.maude` header):

1. **Increment as an expression** (`a[++i] = ++i`, `testStorageEvaluationOrder`):
   here `++`/`--` are statements, not side-effecting expressions.
2. **Whole-struct copy from an Int-keyed slot** (`accountMap[2] = accountMap[1]`,
   `testStorageMapStructCopy`): SolKey disambiguates the read by type
   (`find<[Struct]>` vs `find<[int]>`); this model has no types, so it cannot
   tell an Int-keyed struct slot from an Int-keyed primitive slot for a
   whole-value read. Field-by-field copy works and is shown instead.

Everything else in the suite agrees with SolKey.
