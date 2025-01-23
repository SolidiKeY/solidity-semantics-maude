{-# OPTIONS --rewriting #-}

open import Function hiding (id)
open import Data.Empty
open import Data.Bool.Base
open import Data.Bool.Properties hiding (_≟_)
open import Data.List
import Data.List.Relation.Binary.Pointwise as P
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

copyStAux : (mem : Memory) (id : Identity) (st : Struct) {wf : WellFormed st} → Memory
copyStAux mem id mtst = mem
copyStAux mem id (store st pf@(pSel _) (prim x)) {wf} = write (copyStAux mem id st {wf}) id pf (pSel x)
copyStAux mem id (store st x@(idSel _) (stv st2)) {wf1 ,, wf2} =
  copyStAux (copyStAux mem id st {wf1}) (id · x) st2 {wf2}

copySt : (mem : Memory) (id : PrimIdentity) (st : Struct) {wf : WellFormed st} → Memory
copySt mem id st {wf} = copyStAux (add mem id) ⟨ id , [] ⟩ st {wf}

readSkip : (mem : Memory) (pId pIdR : PrimIdentity) (st : Struct) (fxsL fxsR : List Field) (fld : Field)
  {wf : WellFormed st}
  (pIds≠⊎sufix : pId ≢ pIdR ⊎ pId ≡ pIdR × ¬ (Suffix _≡_ fxsL (fxsR ∷ᵣ fld)))
  → read (copyStAux mem ⟨ pId , fxsL ⟩ st {wf}) ⟨ pIdR , fxsR ⟩ fld ≡ read mem ⟨ pIdR , fxsR ⟩ fld
readSkip mem pId pIdR mtst fxsL fxsR fld (inj₁ pIds≠)
  rewrite dec-no (pId ≟ₚ pIdR) pIds≠ = refl
readSkip mem pId pIdR mtst fxsL fxsR fld (pSel (refl ,, _)) = refl
readSkip mem pId pIdR (store st (pSel y) (prim x)) fxsL fxsR fld pIds≠≠@(inj₁ pIds≠)
  rewrite dec-no (pId ≟ₚ pIdR) pIds≠ | dec-no (pId ≟ₚ pIdR) pIds≠ =
    readSkip mem pId pIdR st fxsL fxsR fld pIds≠≠
readSkip mem pId pIdR (store st (pSel y) (prim x)) fxsL fxsR fld (pSel (refl ,, nSuf))
  rewrite dec-no (⟨ pId , fxsL ⟩ ≟ᵢ ⟨ pId , fxsR ⟩) λ where refl → nSuf (S.tail (fromPointwise (refll refl)))
  = readSkip mem pId pIdR st fxsL fxsR fld (inj₂ (refl ,, nSuf))
readSkip mem pId pIdR (store st f@(idSel x) (stv st2)) fxsL fxsR fld {wf1 ,, wf2} ¬s@(pSel (refl ,, ¬suf))
  rewrite readSkip (copyStAux mem ⟨ pId , fxsL ⟩ st {wf1}) pId pIdR st2 (fxsL ∷ᵣ f) fxsR fld {wf2} (pSel (refl ,, ¬suf ∘ S.tail))
  = readSkip mem pId pIdR st fxsL fxsR fld {wf1} ¬s
readSkip mem pId pIdR (store st f@(idSel x) (stv st2)) fxsL fxsR fld {wf1 ,, wf2} pIds≠≠@(inj₁ pIds≠)
  rewrite readSkip (copyStAux mem ⟨ pId , fxsL ⟩ st {wf1}) pId pIdR st2 (fxsL ∷ᵣ f) fxsR fld {wf2} (inj₁ pIds≠)
      | dec-no (pId ≟ₚ pIdR) pIds≠
      | readSkip mem pId pIdR st fxsL fxsR fld {wf1} (inj₁ pIds≠)
  = refl

readFind : (mem : Memory) (id : PrimIdentity) (st : Struct) (fxs : List Field) (f : FB) {wf : WellFormed st}
  → read (copySt mem id st {wf}) ⟪ id ⟫ (pSel f) ≡ pSel (v→p (select⁺ st (pSel f)))
readFind mem id mtst fxs f = refl
readFind mem id (store st (idSel idS) (stv sv)) fxs f wf@{wf1 ,, wf2} = res

  where
  help : ¬ Suffix _≡_ [ idSel idS ] ([] ∷ᵣ pSel f)
  help (here (() P.∷ _))
  help (there (here ()))

  res : read (copySt mem id (store st (idSel idS) (stv sv)) {wf}) ⟪ id ⟫ (pSel f) ≡
    pSel (v→p (if idSel idS ≟ᵇ pSel f then stv sv else select⁺ st (pSel f)))
  res rewrite readSkip (copyStAux (add mem id) ⟪ id ⟫ st {wf1}) id id sv [ idSel idS ] [] (pSel f) {wf2} (inj₂ (refl ,, help))
      | readFind mem id st [] f {wf1}
      | dec-no (idSel idS ≟ pSel f) λ ()
    = cong pSel refl
readFind mem id (store st (pSel p) (prim v)) fxs f with p ≟ᶠᵇ f
... | yes refl rewrite dec-yes (⟪ id ⟫ ≟ᵢ ⟪ id ⟫) refl .proj₂ = refl
... | no p≢f rewrite
    dec-yes (⟪ id ⟫ ≟ᵢ ⟪ id ⟫) refl .proj₂
  | dec-no (pSel p ≟ pSel f) λ where refl → p≢f refl = readFind mem id st fxs f

private
  false-right : ∀ {b} → b ∧ false ≡ false
  false-right = ∧-zeroʳ _

{-# REWRITE false-right #-}

skipIdRead : (mem : Memory) (idC idR : Identity) (st : Struct)  (fld : FA) {wf : WellFormed st}
  →   read (copyStAux mem idC st {wf}) idR (idSel fld)
    ≡ read mem idR (idSel fld)
skipIdRead mem idC idR mtst fld = refl
skipIdRead mem ⟨ idC , fldsC ⟩ ⟨ idR , fldsR ⟩ (store st (pSel y) (prim x)) fld
  rewrite dec-no (pSel y ≟ᶠ idSel fld) (λ where ()) = skipIdRead mem ⟨ idC , fldsC ⟩ ⟨ idR , fldsR ⟩ st fld
skipIdRead mem idC idR (store st (idSel id) (stv v)) fld =
  skipIdRead (copyStAux mem idC st) (idC · idSel id) idR v fld ∙
  skipIdRead mem idC idR st fld

readGetId : (mem : Memory) (pId : PrimIdentity) (st : Struct) (fxs : List Field) (fld : FA) {wf : WellFormed st}
  → read (copySt mem pId st {wf}) ⟨  pId , fxs ⟩ (idSel fld)
    ≡ idSel (⟨ pId , fxs ∷ᵣ idSel fld ⟩)
readGetId mem pId st fxs fld = skipIdRead (add mem pId) ⟪ pId ⟫ ⟨ pId , fxs ⟩ st fld
