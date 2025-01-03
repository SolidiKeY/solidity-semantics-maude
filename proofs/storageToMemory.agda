{-# OPTIONS --rewriting #-}

open import Data.List

open import Field
open import memory
open import mutual-ind renaming (Value to ValueS)


copySt : (mem : Memory) (id : Identity) (st : Struct) → Memory
copySt mem id mtst = mem
copySt mem id (store st pf@(pSel _) (prim x)) = write (copySt mem id st) id pf {!!}
copySt mem id (store st pf@(pSel _) (stv x)) = write (copySt mem id st) id pf {!!}
copySt mem id (store st (idSel x) value) = {!!}
