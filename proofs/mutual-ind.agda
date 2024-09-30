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
open import Relation.Binary

variable
  ℓ₁ : Level
  D : Set ℓ₁

postulate
  ℓ : Level
  A B C : Set ℓ
  _≟a_ : DecidableEquality A
  _≟b_ : DecidableEquality B


data Value : Set ℓ
data Struct : Set ℓ

data Value where
  prim : C → Value
  stv : Struct → Value

AB = A ⊎ B

_≟_ : DecidableEquality AB
_≟_ = ≡-dec _≟a_ _≟b_

_≟ᵇ_ : AB → AB → Bool
x ≟ᵇ y = does (x ≟ y)

data Struct where
  mtst : Struct
  store : (st : Struct) (k : AB) (value : Value) → Struct

IsNotEmpty : List D → Set _
IsNotEmpty [] = ⊥
IsNotEmpty (_ ∷ _) = ⊤

List⁺ : (A : Set ℓ) → Set _
List⁺ A = Refinement (List A) IsNotEmpty

AB-Value-correct : AB → Value → Set
AB-Value-correct (inj₁ _) (prim _) = ⊤
AB-Value-correct (inj₁ _) (stv _)  = ⊥
AB-Value-correct (inj₂ _) (prim _) = ⊥
AB-Value-correct (inj₂ _) (stv _)  = ⊤

WellformSt : Struct → Set _
WellformSt mtst = ⊤
WellformSt (store st (inj₁ _) (prim _)) = WellformSt st
WellformSt (store st (inj₂ _) (prim _)) = ⊥
WellformSt (store st (inj₁ _) (stv _))  = ⊥
WellformSt (store st (inj₂ _) (stv v))  = WellformSt st × WellformSt v

v→s : Value → Struct
v→s (prim _) = mtst
v→s (stv st) = st

save : (st : Struct) (fields : List⁺ AB) (v : Value) → Struct
save mtst (k ∷ rest , _) v = store mtst k (restV rest)
  where
  restV : List AB → Value
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
  restV : List AB → Value
  restV [] = v'
  restV rest@(_ ∷ _) = stv (save (v→s v) (rest , _) v')

select : (st : Struct) (k : AB) → Value
select mtst k = stv mtst
select (store st k v) k' = if (k ≟ᵇ k') then v else select st k'

if-true : ∀ {b} {a d : D} → b ≡ true → (if b then a else d) ≡ a
if-true refl = refl

wellformed-down : ∀ {st k v} → WellformSt (store st k v) → WellformSt st
wellformed-down {k = inj₁ _} {prim _} x = x
wellformed-down {k = inj₂ _} {stv _} (x , _) = x

select-save : ∀ (st : Struct) k (path'@(path , _) : List⁺ AB) v k' (wf : WellformSt st) →
  select (save st (k ∷ path , _) v) k' ≡
  (if k ≟ᵇ k' then stv (save (v→s (select st k')) path' v) else select st k')
select-save mtst _ (_ ∷ _ , _) _ _ _ = refl
select-save (store st k''' v) k path'@(p ∷ path , _) v' k' wf with k''' ≟ k | k ≟ k' | k''' ≟ k'
... | yes refl | yes refl | yes refl rewrite dec-true (k''' ≟ k''') refl = refl
... | yes refl | yes refl | no k≢k with () ← k≢k refl
... | yes refl | no ¬p | yes refl with () ← ¬p refl
... | yes refl | no ¬p | no _ rewrite dec-false (k''' ≟ k') ¬p = refl
... | no k≢k | yes refl | yes refl with () ← k≢k refl
... | no ¬a | yes refl | no ¬c rewrite dec-false (k''' ≟ k) ¬a =
  trans (select-save st _ _ _ _ (wellformed-down {k = k'''} wf)) help
  where
  help : (if k ≟ᵇ k then _ else _) ≡ _
  help rewrite dec-true (k ≟ k) refl = refl
... | no ¬a | no ¬p | yes refl rewrite dec-true (k''' ≟ k''') refl = refl
... | no ¬a | no ¬b | no ¬c rewrite dec-false (k''' ≟ k') ¬c =
  trans (select-save st _ _ _ _ (wellformed-down {k = k'''} wf)) help
  where
  help : (if k ≟ᵇ k' then _ else _) ≡ _
  help rewrite dec-false (k ≟ k') ¬b = refl
