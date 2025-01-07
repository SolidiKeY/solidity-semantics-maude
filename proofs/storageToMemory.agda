{-# OPTIONS --rewriting #-}

open import Function hiding (id)
open import Data.Empty
open import Data.Nat
open import Data.List
open import Data.List.Relation.Binary.Suffix.Heterogeneous as S
open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties
open import Data.List.Relation.Binary.Pointwise.Properties renaming (refl to refll)
open import Data.Sum
open import Data.Product using (_×_; proj₂) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
  renaming (trans to infixl 5 _∙_) hiding ([_])
open import Relation.Nullary.Decidable
open import Relation.Nullary

open import Field
open import memory
open import mutual-ind renaming (Value to ValueS)

postulate
  impossible : ∀ {ℓ} {A : Set ℓ} → A
  notPossibleYet : ∀ {ℓ} {A : Set ℓ} → A

copyStAux : (mem : Memory) (id : Identity) (st : Struct) → Memory
copyStAux mem id mtst = mem
copyStAux mem id (store st pf@(pSel _) (prim x)) = write (copyStAux mem id st) id pf (pSel x)
copyStAux mem id (store st pf@(pSel _) (stv x)) = impossible
copyStAux mem id (store st (idSel x) (prim _)) = impossible
copyStAux mem id (store st x@(idSel _) (stv st2)) = let

  restMemSt : Memory → Memory
  restMemSt mem = copyStAux mem id st

  copiedSt2 : Memory → Memory
  copiedSt2 mem = copyStAux mem (id · x) st2

  in copiedSt2 $ restMemSt mem

copySt : (mem : Memory) (id : PrimIdentity) (st : Struct) → Memory
copySt mem id = copyStAux (add mem id) ⟨ id , [] ⟩

readSkip : (mem : Memory) (pId pIdR : PrimIdentity) (st : Struct) (fxsL fxsR : List Field) (fld : Field)
 (pIds≠⊎sufix : pId ≢ pIdR ⊎ pId ≡ pIdR × ¬ (Suffix _≡_ fxsL fxsR))
  → read (copyStAux mem ⟨ pId , fxsL ⟩ st) ⟨ pIdR , fxsR ⟩ fld ≡ read mem ⟨ pIdR , fxsR ⟩ fld
readSkip mem pId pIdR mtst fxsL fxsR fld (inj₁ pIds≠)
  rewrite dec-no (pId ≟ₚ pIdR) pIds≠ = refl
readSkip mem pId pIdR mtst fxsL fxsR fld (pSel (refl ,, _)) = refl
readSkip mem pId pIdR (store st (pSel y) (prim x)) fxsL fxsR fld pIds≠≠@(inj₁ pIds≠)
  rewrite dec-no (pId ≟ₚ pIdR) pIds≠ | dec-no (pId ≟ₚ pIdR) pIds≠ =
    readSkip mem pId pIdR st fxsL fxsR fld pIds≠≠
readSkip mem pId pIdR (store st (pSel y) (prim x)) fxsL fxsR fld (pSel (refl ,, nSuf))
  rewrite dec-no (⟨ pId , fxsL ⟩ ≟ᵢ ⟨ pId , fxsR ⟩) λ where refl → nSuf (fromPointwise (refll refl))
  = readSkip mem pId pIdR st fxsL fxsR fld (inj₂ (refl ,, nSuf))
readSkip mem pId pIdR (store st (pSel y) (stv x)) fxsL fxsR fld pIds≠ = impossible
readSkip mem pId pIdR (store st (idSel x) (prim _)) fxsL fxsR fld pIds≠ = impossible
readSkip mem pId pIdR (store st f@(idSel x) (stv st2)) fxsL fxsR fld ¬s@(pSel (refl ,, ¬suf))
  rewrite readSkip (copyStAux mem ⟨ pId , fxsL ⟩ st) pId pIdR st2 (fxsL ∷ᵣ f) fxsR fld (pSel (refl ,, ¬suf ∘ S.tail))
  = readSkip mem pId pIdR st fxsL fxsR fld ¬s
readSkip mem pId pIdR (store st f@(idSel x) (stv st2)) fxsL fxsR fld pIds≠≠@(inj₁ pIds≠)
  rewrite readSkip (copyStAux mem ⟨ pId , fxsL ⟩ st) pId pIdR st2 (fxsL ∷ᵣ f) fxsR fld (inj₁ pIds≠)
      | dec-no (pId ≟ₚ pIdR) pIds≠
      | readSkip mem pId pIdR st fxsL fxsR fld (inj₁ pIds≠)
  = refl

-- readGetId : (mem : Memory) (pId : PrimIdentity) (st : Struct) (fxs : List Field)
--   (fld : ℕ)
--   → read (copyStAux mem ⟪ pId ⟫ st) ⟨  pId , fxs ⟩ (idSel fld)
--     ≡ idSel (⟨ pId , fxs ∷ᵣ idSel fld ⟩)
-- readGetId mem pId mtst fxs fld rewrite
--   dec-yes (pId ≟ₚ pId ) refl .proj₂ = refl
-- readGetId mem pId (store st (pSel y) (prim x)) [] fld
--   rewrite dec-yes (⟪ pId ⟫ ≟ᵢ ⟪ pId ⟫) refl .proj₂
--     | dec-yes (pId ≟ₚ pId) refl .proj₂ = refl
-- readGetId mem pId (store st (pSel y) (prim x)) (fxs ∷ᵣ xn) fld
--   rewrite dec-no (⟪ pId ⟫ ≟ᵢ ⟨ pId , fxs ∷ᵣ xn ⟩) (λ p → {!!})
--     | dec-yes (pId ≟ₚ pId) refl .proj₂ = refl
-- readGetId mem pId (store st (pSel y) (stv x)) fxs fld = {!!}
-- readGetId mem pId (store st (idSel x) (prim _)) fxs fld = {!!}
-- readGetId mem pId (store st f@(idSel x) (stv st2)) fxs fld = {!!}
