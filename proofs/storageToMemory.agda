{-# OPTIONS --rewriting #-}

open import Data.List

open import Field
open import memory
open import mutual-ind renaming (Value to ValueS)

postulate
  impossibleCase : Memory

copySt : (mem : Memory) (id : Identity) (st : Struct) → Memory
copySt mem id mtst = mem
copySt mem id (store st pf@(pSel _) (prim x)) = write (copySt mem id st) id pf (pSel x)
copySt mem id (store st pf@(pSel _) (stv x)) = impossibleCase
copySt mem id (store st (idSel x) (prim _)) = impossibleCase
copySt mem id (store st (idSel x) (stv st2)) = {!!}
  where

  restMemSt : Memory
  restMemSt = copySt mem id st

  addId : Memory
  addId = add restMemSt id
