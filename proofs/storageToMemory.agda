{-# OPTIONS --rewriting #-}

open import Function hiding (id)
open import Data.List
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 5 _∙_)
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
copySt mem id (store st x@(idSel _) (stv st2)) = let

  restMemSt : Memory → Memory
  restMemSt mem = copySt mem id st

  addId : Memory → Memory
  addId mem = add mem id

  copiedSt2 : Memory → Memory
  copiedSt2 mem = copySt mem (id · x) st2

  in copiedSt2 $ addId $ restMemSt mem

readSkip : (mem : Memory) (pId pIdR : PrimIdentity) (st : Struct) (fxsL fxsR : List Field) (fld : Field)
 (pIds≠ : pId ≢ pIdR)
  → read (copySt mem ⟨ pId , fxsL ⟩ st) ⟨ pIdR , fxsR ⟩ fld ≡ read mem ⟨ pIdR , fxsR ⟩ fld
readSkip mem pId pIdR mtst fxsL fxsR fld pIds≠ = refl
readSkip mem pId pIdR (store st (pSel y) (prim x)) fxsL fxsR fld pIds≠
  rewrite dec-no (pId ≟ₚ pIdR) pIds≠ = readSkip mem pId pIdR st fxsL fxsR fld pIds≠
readSkip mem pId pIdR (store st (pSel y) (stv x)) fxsL fxsR fld pIds≠ = {!!}
readSkip mem pId pIdR (store st (idSel x) (prim _)) fxsL fxsR fld pIds≠ = {!!}
readSkip mem pId pIdR (store st f@(idSel x) (stv st2)) fxsL fxsR fld pIds≠ =
    readSkip (add (copySt mem ⟨ pId , fxsL ⟩ st) ⟨ pId , fxsL ⟩) pId pIdR st2 (fxsL ∷ᵣ f) fxsR fld pIds≠
  ∙ help

  where
  help : read (add (copySt mem ⟨ pId , fxsL ⟩ st) ⟨ pId , fxsL ⟩) ⟨ pIdR , fxsR ⟩ fld ≡
    read mem ⟨ pIdR , fxsR ⟩ fld
  help rewrite dec-no (pId ≟ₚ pIdR) pIds≠ = readSkip mem pId pIdR st fxsL fxsR fld pIds≠
