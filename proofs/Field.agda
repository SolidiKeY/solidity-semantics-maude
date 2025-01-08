{-# OPTIONS --rewriting #-}

open import Level
open import Data.Nat as ℕ
open import Data.Bool
open import Data.Sum
open import Data.Sum.Properties as ⊎
open import Data.List
open import Data.List.Properties as L
open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

postulate
  ℓ : Level
  A FA FB : Set ℓ
  v0 : A
  _≟ᶠᵃ_ : DecidableEquality FA
  _≟ᶠᵇ_ : DecidableEquality FB

Field = FA ⊎ FB

_≟ᶠ_ : DecidableEquality Field
_≟ᶠ_ = ⊎.≡-dec _≟ᶠᵃ_ _≟ᶠᵇ_

_≟ˡᶠ_ : DecidableEquality (List Field)
_≟ˡᶠ_ = L.≡-dec _≟ᶠ_

pattern idSel x = inj₁ x
pattern pSel x = inj₂ x
pattern _∷ᵣ_ xs x = _∷_ x xs

dec-eq-fa : ∀ {k} → does (k ≟ᶠᵃ k) ≡ true
dec-eq-fa {k} = dec-true (k ≟ᶠᵃ k) refl

dec-eq-fb : ∀ {k} → does (k ≟ᶠᵇ k) ≡ true
dec-eq-fb {k} = dec-true (k ≟ᶠᵇ k) refl

dec-eq-lb : ∀ {k} → does (L.≡-dec _≟ᶠ_ k k) ≡ true
dec-eq-lb {k} = dec-true (k ≟ˡᶠ k) refl

{-# REWRITE dec-eq-fa dec-eq-fb dec-eq-lb #-}
