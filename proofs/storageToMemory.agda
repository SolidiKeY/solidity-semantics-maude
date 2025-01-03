open import Data.List

open import memory
open import proof-select-save renaming (Value to ValueSS)

ValueS = ValueSS A

copySt : (mem : Memory) (pId : PrimIdentity) (val : ValueS) → Memory
copySt mem pId mtst = mem
copySt mem pId (var x) = write mem ⟨ pId , [] ⟩ {!!} {!!}
copySt mem pId (store val fld val₁) = {!!}
