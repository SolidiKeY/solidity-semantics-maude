open import Level
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Refinement
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool hiding (_≟_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

private variable
  ℓ : Level
  A B C : Set ℓ

data Value (A : Set ℓ) : Set ℓ
data Struct (A : Set ℓ) : Set ℓ

data Value A where
  prim : A → Value A
  stv : Struct A → Value A

N2 = ℕ ⊎ ℕ

data Struct A where
  mtst : Struct A
  store : (st : Struct A) (k : N2) (value : Value A) → Struct A

IsNotEmpty : List A → Set _
IsNotEmpty [] = ⊥
IsNotEmpty (_ ∷ _) = ⊤

List⁺ : (A : Set ℓ) → Set _
List⁺ A = Refinement (List A) IsNotEmpty

WellformSt : Struct A → Set _
WellformSt mtst = ⊤
WellformSt (store st (inj₁ _) (prim _)) = WellformSt st
WellformSt (store st (inj₂ _) (prim _)) = ⊥
WellformSt (store st (inj₁ _) (stv _))  = ⊥
WellformSt (store st (inj₂ _) (stv _))  = WellformSt st

AreStructs : List⁺ N2 → Set _
AreStructs (_ ∷ [] , p) = ⊤
AreStructs (inj₁ _ ∷ _ ∷ v , p) = ⊥
AreStructs (inj₂ _ ∷ rest@(_ ∷ _) , p) = AreStructs (rest , _)

last⁺ : List⁺ A → A
last⁺ (x ∷ [] , _) = x
last⁺ (x ∷ rest@(_ ∷ _) , proof) = last⁺ (rest , _)


save : (st : Struct A) (wf : WellformSt st) (fields : List⁺ N2) {_ : AreStructs fields} (v : Value A) → Struct A
save mtst wf (k ∷ rest , _) v = store mtst k (sv rest)
  where
  sv : List N2 → Value _
  sv [] = v
  sv rest@(_ ∷ _) = stv (save mtst _ (rest , _) v)
save (store st k (prim x)) wf (k' ∷ rest , _) v' = if {!!} then {!!} else {!!}
save (store st k (stv x)) wf (k' ∷ rest , _) v' = if {!!} then {!!} else {!!}
  where
  sv : List N2 → Value _
  sv [] = v'
  sv rest@(_ ∷ _) = stv (save {!!} {!!} (rest , _) v')


-- save : Value A → List ℕ → Value A → Value A
-- save mtst [] v = v
-- save mtst (k ∷ xs) v = store mtst k (save mtst xs v)
-- save (var _) _ v = v
-- save (store st x v) [] v' = store st x v'
-- save (store st k v) xs@(k' ∷ ys) v' = if k ≡ᵇ k' then store st k (save v ys v') else store (save st xs v') k v

-- select : Value A → ℕ → Value A
-- select mtst n = mtst
-- select (var st) n = mtst
-- select (store xs k v) n = if k ≡ᵇ n then v else select xs n

-- same-bool : ∀ m → (m ≡ᵇ m) ≡ true
-- same-bool m with m ≡ᵇ m | ≡⇒≡ᵇ m m refl
-- ... | true | _ = refl

-- diff-bool : ∀ {m n} → m ≢ n → (m ≡ᵇ n) ≡ false
-- diff-bool {ℕ.zero} {ℕ.zero} m≢n with () ← m≢n refl
-- diff-bool {ℕ.zero} {ℕ.suc n} m≢n = refl
-- diff-bool {ℕ.suc m} {ℕ.zero} m≢n = refl
-- diff-bool {ℕ.suc m} {ℕ.suc n} m≢n = diff-bool (λ eq → m≢n (cong ℕ.suc eq))

-- IsStruct : (st : Value A) → Set
-- IsStruct mtst = ⊤
-- IsStruct (var _) = ⊥
-- IsStruct (store st _ mtst) = IsStruct st
-- IsStruct (store st _ (var x)) = IsStruct st
-- IsStruct (store st _ st2@(store v x v₁)) = IsStruct st × IsStruct st2

-- isStructInside : ∀ {st : Value A} k v → IsStruct (store st k v) → IsStruct st
-- isStructInside {st = st} k mtst x = x
-- isStructInside {st = st} k (var x₁) x = x
-- isStructInside {st = st} k (store v x₁ v₁) (fst , snd) = fst

-- select-save : ∀ (st : Value A) k path v k' (wf : IsStruct st) → select (save st (k ∷ path) v) k' ≡
--   (if k ≡ᵇ k' then save (select st k') path v else select st k')
-- select-save mtst k path v k' _ = refl
-- select-save (var _) k path v k' ()
-- select-save (store st k''' v) k path v' k' wf with k''' ≟ k | k ≟ k' | k''' ≟ k'
-- ... | yes refl | yes refl | _ rewrite same-bool k''' | same-bool k''' = refl
-- ... | yes refl | no np | _ rewrite same-bool k''' | diff-bool np  = refl
-- ... | no np | yes refl | _ rewrite diff-bool np | diff-bool np | same-bool k = trans (select-save st _ _ _ _ (isStructInside k''' v wf)) help
--   where
--   help : (if k ≡ᵇ k then save (select st k) path v' else select st k) ≡ save (select st k) path v'
--   help  rewrite same-bool k = refl
-- ... | no np | no npp | yes refl rewrite diff-bool np | diff-bool npp | same-bool k''' = refl
-- ... | no np | no npp | no eqn rewrite diff-bool np | diff-bool npp | diff-bool eqn = trans (select-save st _ _ _ _ (isStructInside k''' v wf)) help
--   where
--   help : (if k ≡ᵇ k' then save (select st k') path v' else select st k') ≡ select st k'
--   help rewrite diff-bool npp = refl
