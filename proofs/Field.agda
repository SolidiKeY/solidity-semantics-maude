open import Data.Nat as ℕ
open import Data.Sum
open import Data.Sum.Properties as ⊎
open import Data.List
open import Data.List.Properties as L

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

Field = ℕ ⊎ ℕ

_≟ᶠ_ : DecidableEquality Field
_≟ᶠ_ = ⊎.≡-dec ℕ._≟_ ℕ._≟_

_≟ˡᶠ_ : DecidableEquality (List Field)
_≟ˡᶠ_ = L.≡-dec _≟ᶠ_


pattern idSel x = inj₁ x
pattern pSel x = inj₂ x
pattern _∷ᵣ_ xs x = _∷_ x xs
