{-# OPTIONS --rewriting #-}

open import Function hiding (id)
open import Data.List
open import Relation.Binary.PropositionalEquality renaming (trans to _∙_)
open import Relation.Nullary.Decidable

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

readSkip : (mem : Memory) (pId pIdR : PrimIdentity) (st : Struct) (fxs : List Field) (fld : Field)
 (pIds≠ : pId ≢ pIdR)
  → read (copySt mem ⟪ pId ⟫ st) ⟨ pIdR , fxs ⟩ fld ≡ read mem ⟨ pIdR , fxs ⟩ fld
readSkip mem pId pIdR mtst fxs fld pIds≠ = refl
readSkip mem pId pIdR (store st (pSel y) (prim x)) fxs fld pIds≠
  rewrite dec-no (pId ≟ₚ pIdR) pIds≠ = readSkip mem pId pIdR st fxs fld pIds≠
readSkip mem pId pIdR (store st (pSel y) (stv x)) fxs fld pIds≠ = {!!}
readSkip mem pId pIdR (store st (idSel x) (prim _)) fxs fld pIds≠ = {!!}
readSkip mem pId pIdR (store st f@(idSel _) (stv st2)) fxs fld pIds≠ =
  readSkip (add (copySt mem ⟪ pId ⟫ st) ⟪ pId ⟫) pId pIdR {!st2!} {!!} {!!} {!!} ∙ {!!}
