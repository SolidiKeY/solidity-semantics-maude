{-# OPTIONS --rewriting #-}

open import Level
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Sum.Properties
open import Data.List
open import Data.Refinement
open import Data.Bool hiding (_≟_)

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary

variable
  ℓ′ : Level
  C : Set ℓ′

postulate
  ℓ : Level
  A B : Set ℓ
  _≟_ : DecidableEquality A


data Value : Set ℓ
data Struct : Set ℓ

data Value where
  prim : B → Value
  stv : Struct → Value

_≟ᵇ_ : A → A → Bool
x ≟ᵇ y = does (x ≟ y)

data Struct where
  mtst : Struct
  store : (st : Struct) (k : A) (value : Value) → Struct

IsNotEmpty : List C → Set _
IsNotEmpty [] = ⊥
IsNotEmpty (_ ∷ _) = ⊤

List⁺ : (A : Set ℓ) → Set _
List⁺ A = Refinement (List A) IsNotEmpty

postulate
  v→s : Value → Struct
  v→st≡st : ∀ {st} → v→s (stv st) ≡ st

{-# REWRITE v→st≡st #-}

save : (st : Struct) (fields : List⁺ A) (v : Value) → Struct
save mtst (k ∷ rest , _) v = store mtst k (restV rest)
  where
  restV : List A → Value
  restV [] = v
  restV rest'@(rest ∷ _) = stv (save mtst (rest' , _) v)
save (store st k v) r@(k' ∷ rest , _) v' =
  if
    k ≟ᵇ k'
  then
    store st k (restV rest)
  else
    store (save st r v') k v
  where
  restV : List A → Value
  restV [] = v'
  restV rest@(_ ∷ _) = stv (save (v→s v) (rest , _) v')

select : (st : Struct) (k : A) → Value
select mtst k = stv mtst
select (store st k v) k' = if (k ≟ᵇ k') then v else select st k'

select-save : ∀ (st : Struct) k (path'@(path , _) : List⁺ A) v k' →
  select (save st (k ∷ path , _) v) k' ≡
  (if k ≟ᵇ k' then stv (save (v→s (select st k')) path' v) else select st k')
select-save mtst _ (_ ∷ _ , _) _ _ = refl
select-save (store st k''' v) k path'@(p ∷ path , _) v' k' with k''' ≟ k | k ≟ k' | k''' ≟ k'
... | yes refl | yes refl | yes refl rewrite dec-true (k''' ≟ k''') refl = refl
... | yes refl | yes refl | no k≢k with () ← k≢k refl
... | yes refl | no ¬p | yes refl with () ← ¬p refl
... | yes refl | no ¬p | no _ rewrite dec-false (k''' ≟ k') ¬p = refl
... | no k≢k | yes refl | yes refl with () ← k≢k refl
... | no ¬a | yes refl | no ¬c rewrite dec-false (k''' ≟ k) ¬a =
  trans (select-save st _ _ _ _) help
  where
  help : (if k ≟ᵇ k then _ else _) ≡ _
  help rewrite dec-true (k ≟ k) refl = refl
... | no ¬a | no ¬p | yes refl rewrite dec-true (k''' ≟ k''') refl = refl
... | no ¬a | no ¬b | no ¬c rewrite dec-false (k''' ≟ k') ¬c =
  trans (select-save st _ _ _ _) help
  where
  help : (if k ≟ᵇ k' then _ else _) ≡ _
  help rewrite dec-false (k ≟ k') ¬b = refl
