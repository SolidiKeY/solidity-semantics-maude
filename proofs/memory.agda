open import Level
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.List

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

Field = ℕ ⊎ ℕ

pattern idSel x = inj₁ x
pattern pSel x = inj₂ x
pattern _∷ᵣ_ xs x = _∷_ x xs

postulate
  ℓ : Level
  A PrimIdentity : Set ℓ
  v0 : A
  _≟ₚ_ : DecidableEquality PrimIdentity

record Identity : Set ℓ where
  constructor ⟨_,_⟩
  field
    prim : PrimIdentity
    flds : List ℕ

data Memory : Set ℓ where
  mtm : Memory
  write : (mem : Memory) (id : Identity) (value : A) → Memory
  add : (mem : Memory) (pId : PrimIdentity) → Memory


read : (mem : Memory) (id : Identity) (fld : Field) → Identity ⊎ A
read mtm id fld = inj₂ v0
read (write mem ⟨ pId1 , flds1 ⟩ value) id@(⟨ pId2 , flds2 ⟩) fld with ⌊ pId1 ≟ₚ pId2 ⌋
... | true = {!!}
... | false = read mem id fld
read (add mem pId) idd@(⟨ id , _ ⟩) fld with ⌊ pId ≟ₚ id ⌋
... | false = read mem idd fld
read (add mem pId) ⟨ id , ids ⟩ (idSel f) | true = idSel ⟨ id , ids ∷ᵣ f ⟩
read (add mem pId) ⟨ id , _ ⟩ (pSel y) | true = pSel v0
