open import Level
open import Data.Bool
open import Data.Nat as ℕ
open import Data.Sum
open import Data.Sum.Properties as ⊎
open import Data.List
open import Data.List.Properties as L

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Field

postulate
  PrimIdentity : Set ℓ
  _≟ₚ_ : DecidableEquality PrimIdentity

record Identity : Set ℓ where
  constructor ⟨_,_⟩
  field
    prim : PrimIdentity
    flds : List Field

_≟ˡ_ : DecidableEquality Identity
⟨ prim1 , flds1 ⟩ ≟ˡ ⟨ prim2 , flds2 ⟩ with prim1 ≟ₚ prim2 | flds1 ≟ˡᶠ flds2
... | yes refl | yes refl = yes refl
... | no na | _ = no (λ where refl → na refl)
... | _ | no nb = no (λ where refl → nb refl)


_≟ᵢ_ : DecidableEquality Identity
⟨ prim1 , flds1 ⟩ ≟ᵢ ⟨ prim2 , flds2 ⟩ with prim1 ≟ₚ prim2 | flds1 ≟ˡᶠ flds2
... | no ¬a | _ = no λ where refl → ¬a refl
... | yes refl | no ¬b = no λ where refl → ¬b refl
... | yes refl | yes refl = yes refl

Value = Identity ⊎ A

data Memory : Set ℓ where
  mtm : Memory
  write : (mem : Memory) (id : Identity) (fld : Field) (value : Value) → Memory
  add : (mem : Memory) (pId : Identity) → Memory


read : (mem : Memory) (id : Identity) (fld : Field) → Value
read mtm id fld = inj₂ v0
read (write mem idM fldM value) id fld with ⌊ idM ≟ᵢ id ⌋ ∧ ⌊ fldM ≟ᶠ fld ⌋
... | true = value
... | false = read mem id fld
read (add mem pId) idd@(⟨ id , _ ⟩) fld with ⌊ pId ≟ˡ idd ⌋
... | false = read mem idd fld
read (add mem pId) ⟨ id , ids ⟩ f@(idSel _) | true = idSel ⟨ id , ids ∷ᵣ f ⟩
read (add mem pId) ⟨ id , _ ⟩ (pSel y) | true = pSel v0
