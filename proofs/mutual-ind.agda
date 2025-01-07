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
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary

open import Field renaming (A to PrimValue)

private variable
  ℓ′ : Level
  A : Set ℓ′

postulate
  _≟_ : DecidableEquality Field


data Value  : Set ℓ
data Struct : Set ℓ

data Value where
  prim : PrimValue → Value
  stv  : Struct → Value

_≟ᵇ_ : Field → Field → Bool
x ≟ᵇ y = does (x ≟ y)

data Struct where
  mtst : Struct
  store : (st : Struct) (k : Field) (value : Value) → Struct

IsNotEmpty : List A → Set _
IsNotEmpty [] = ⊥
IsNotEmpty (_ ∷ _) = ⊤

List⁺ : (A : Set ℓ′) → Set _
List⁺ A = Refinement (List A) IsNotEmpty

variable
  st : Struct
  path : List Field
  f : Field
  v : Value
  vp : PrimValue

postulate
  v→s : Value → Struct
  v→st≡st : v→s (stv st) ≡ st

  v→p : Value → PrimValue
  v→pv≡pv : v→p (prim vp) ≡ vp
  v→pv≡v0 : v→p (stv mtst) ≡ v0

{-# REWRITE v→st≡st v→pv≡pv v→pv≡v0 #-}

save⁺ : (st : Struct) (fields : List⁺ Field) (v : Value) → Struct
save⁺ mtst (k ∷ rest , _) v = store mtst k (restV rest)
  where
  restV : List Field → Value
  restV [] = v
  restV rest'@(rest ∷ _) = stv (save⁺ mtst (rest' , _) v)
save⁺ (store st k v) r@(k' ∷ rest , _) v' =
  if
    k ≟ᵇ k'
  then
    store st k (restV rest)
  else
    store (save⁺ st r v') k v
  where
  restV : List Field → Value
  restV [] = v'
  restV rest@(_ ∷ _) = stv (save⁺ (v→s v) (rest , _) v')

postulate
  save : (st : Struct) (path : List Field) (v : Value) → Struct
  save≡save⁺ : save st (f ∷ path) v ≡ save⁺ st (f ∷ path , _) v

{-# REWRITE save≡save⁺ #-}

select⁺ : (st : Struct) (k : Field) → Value
select⁺ mtst k = stv mtst
select⁺ (store st k v) k' = if (k ≟ᵇ k') then v else select⁺ st k'

select : (st : Struct) (path : List Field) → Value
select st [] = stv st
select mtst (f ∷ path) = stv mtst
select (store st k v) pAll@(k' ∷ path) =
  if
    k ≟ᵇ k'
  then
    fromCases path
  else
    select st pAll
  where
  fromCases : List Field → _
  fromCases [] = v
  fromCases path@(_ ∷ _) = select (v→s v) path

select≡select⁺ : (st : Struct) (k : Field) → select st [ k ] ≡ select⁺ st k
select≡select⁺ mtst k = refl
select≡select⁺ (store st k v) k' rewrite select≡select⁺ st k' = refl

selectOfSelects : (st : Struct) (k k' : Field) (path : List Field) → select st (k ∷ k' ∷ path) ≡
  select (v→s (select st [ k ])) (k' ∷ path)
selectOfSelects mtst k k' [] = refl
selectOfSelects (store st k'' v) k k' [] with k'' ≟ k
... | yes refl = refl
... | no _ rewrite selectOfSelects st k k' []  = refl
selectOfSelects mtst k k' (k'' ∷ path) = refl
selectOfSelects (store st k''' v) k k' (k'' ∷ path) with k''' ≟ k
... | yes refl = refl
... | no np rewrite selectOfSelects st k k' (k'' ∷ path) = refl

selectOfSelect⁺ : (st : Struct) (k k' : Field) (path : List Field)
  → select st (k ∷ k' ∷ path) ≡ select (v→s (select⁺ st k)) (k' ∷ path)
selectOfSelect⁺ st k k' path rewrite selectOfSelects st k k' path | select≡select⁺ st k = refl

{-# REWRITE select≡select⁺ selectOfSelect⁺ #-}

save-path : (st : Struct) (k : Field) (path : List Field) (v : Value) → Value
save-path st k [] v = v
save-path st k path@(_ ∷ _) v = stv (save (v→s (select⁺ st k)) path v)

save-path≡ : ∀ (st : Struct) k k' (path : List Field) v v' (k'≢k : k' ≢ k)
  → save-path st k path v' ≡ save-path (store st k' v) k path v'
save-path≡ st k k' [] v v' k≢k' = refl
save-path≡ st k k' (x ∷ path) v v' k'≢k rewrite dec-false (k' ≟ k) k'≢k = refl

dec-eq : ∀ {k} → does (k ≟ k) ≡ true
dec-eq {k} = dec-true (k ≟ k) refl

{-# REWRITE dec-eq #-}

select⁺-save : ∀ (st : Struct) k (path : List Field) v k' →
  select⁺ (save st (k ∷ path) v) k' ≡
  (if k ≟ᵇ k' then save-path st k path v else select⁺ st k')
select⁺-save mtst _ [] _ _ = refl
select⁺-save mtst _ (_ ∷ _) _ _ = refl
select⁺-save (store st k''' v) k path v' k'  with k''' ≟ k | k ≟ k' | k''' ≟ k'
select⁺-save (store st k''' v) k [] v' k' | yes refl | yes refl | yes refl = refl
select⁺-save (store st k''' value₁) k (x ∷ path) v k' | yes refl | yes refl | yes refl
   = refl
... | yes refl | yes refl | no k≢k with () ← k≢k refl
... | yes refl | no ¬p | yes refl with () ← ¬p refl
... | yes refl | no ¬p | no _ rewrite dec-false (k''' ≟ k') ¬p = refl
... | no k≢k | yes refl | yes refl with () ← k≢k refl
... | no ¬a | yes refl | no ¬c rewrite dec-false (k''' ≟ k) ¬a =
  trans (select⁺-save st _ _ _ _) (save-path≡ st _ _ path _ _ ¬a)
... | no ¬a | no ¬p | yes refl = refl
... | no ¬a | no ¬b | no ¬c rewrite dec-false (k''' ≟ k') ¬c =
  trans (select⁺-save st _ _ _ _) help
  where
  help : (if k ≟ᵇ k' then _ else _) ≡ _
  help rewrite dec-false (k ≟ k') ¬b = refl
