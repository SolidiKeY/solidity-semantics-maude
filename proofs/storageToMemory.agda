{-# OPTIONS --rewriting #-}

open import Function hiding (id)
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
copySt mem id (store st x@(idSel _) (stv st2)) = copiedSt2 $ addId $ restMemSt mem
  where

  restMemSt : Memory → Memory
  restMemSt mem = copySt mem id st

  addId : Memory → Memory
  addId mem = add mem id

  copiedSt2 : Memory → Memory
  copiedSt2 mem = copySt mem (id · x) st2
