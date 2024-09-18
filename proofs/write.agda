{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude renaming (_≡_ to _≣_)
open import Cubical.Data.Prod
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Equality
open import Cubical.Relation.Nullary

private variable
  ℓ : Level

data Heap : Type₀ where
  empt : Heap
  write : (hp : Heap) (key value : ℕ) → Heap

impossible : write (write empt 0 0) 0 0 ≡ write empt 0 0 → ⊥
impossible ()

read : Heap → ℕ
read empt = {!!}
read (write hp key value) = {!!}
-- it can happen that read (write (write hp key value₂) key value₁) ≢ read (write hp key value₁)

NotIn : Heap → ℕ → Type₀
NotIn empt n = Unit
NotIn (write hp key value) keyNotIn = (¬ key ≡ keyNotIn) × NotIn hp keyNotIn

WellFormed : Heap → Type
WellFormed empt = Unit
WellFormed (write hp key value) = NotIn hp key × WellFormed hp

readWellFormed : (hp : Heap) (wellFormed : WellFormed hp) → ℕ
readWellFormed empt wellFormed = {!!}
readWellFormed (write hp key value) wellFormed = {!!}

data HeapQuotient : Type₀ where
  empt : HeapQuotient
  write : (hp : Heap) (key value : ℕ) → HeapQuotient
  writeSame : (hp : Heap) (key value₁ value₂ : ℕ) → write (write hp key value₂) key value₁ ≣ write hp key value₁
  writeDifferent : (hp : Heap) (key₁ key₂ value₁ value₂ : ℕ) (key₁≢key₂ : ¬ (key₁ ≣ key₂))
    → write (write hp key₂ value₂) key₁ value₁ ≣ write hp key₁ value₁

readQuotient : HeapQuotient → ℕ
readQuotient empt = {!!}
readQuotient (write hp key value) = {!!}
readQuotient (writeSame hp key value₁ value₂ i) = {!!}
  -- has to prove that readQuotient (write (write hp key value₂) key value₁) ≡ readQuotient (write hp key value₁)
readQuotient (writeDifferent hp key₁ key₂ value₁ value₂ key₁≢key₂ i) = {!!}
