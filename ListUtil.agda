
module ListUtil where

open import Level
open import Function
open import Function.Inverse
open import Function.Equality
open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum
open import Data.List hiding (any)
open import Data.List.All hiding (map)
open import Data.List.All.Properties
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Data.List.Any.Properties using () renaming (++↔ to ++↔-any)
open import Data.Maybe using (Maybe; just; nothing; Eq) renaming (setoid to eq-setoid)

open import Relation.Binary.PropositionalEquality using (_≡_; subst) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open Data.List.Any.Membership-≡


----------------------------------------------------------------------------------------------------

-- Finite binary relations. 
-- I hadn't found them in stdlib, so I had to implement them myself.

FinRel : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
FinRel A B = List (A × B)

⟪_⟫ : ∀ {a b} {A : Set a} {B : Set b} → FinRel A B → A → B → Set (a ⊔ b)
⟪ f ⟫ x y = (x , y) ∈ f

functional : ∀ {a b} {A : Set a} {B : Set b} → FinRel A B → Set (a ⊔ b)
functional {A = A} {B = B} table = 
  (p1 p2 : A × B) → p1 ∈ table → p2 ∈ table → proj₁ p1 ≡ proj₁ p2 → proj₂ p1 ≡ proj₂ p2

keys : ∀ {a b} {A : Set a} {B : Set b} → 
       FinRel A B → List A
keys table = Data.List.map proj₁ table

values : ∀ {a b} {A : Set a} {B : Set b} → 
         FinRel A B → List B
values table = Data.List.map proj₂ table

-- f has x means that there is y such that f relates x to y.

_has_ : ∀ {a b} {A : Set a} {B : Set b} → 
        FinRel A B → A → Set (a ⊔ b)
f has x = ∃ λ y → ⟪ f ⟫ x y

-- actually "f has x" is the same thing as x ∈ keys f

has→∈keys : ∀ {a b} {A : Set a} {B : Set b} {f : FinRel A B} {x : A} →
            f has x → x ∈ keys f
has→∈keys (y , here px) rewrite (≡-sym px) = here ≡-refl
has→∈keys (y , there pxs) with has→∈keys (y , pxs)
... | ∈keys-xs = there ∈keys-xs

-- If ≡ for A is decidable then _has_ is decidable.

has-decidable : ∀ {a b} {A : Set a} {B : Set b} → 
                Decidable (_≡_ {A = A}) → Decidable {A = FinRel A B} {B = A} _has_
has-decidable {B = B} dec [] x = no fun
  where
    fun : Σ B (λ y → Any (_≡_ (x , y)) []) → Data.Empty.⊥
    fun (_ , ())
has-decidable {B = B} dec ((x , y) ∷ ps) x' with dec x x'
... | yes x≡x' rewrite x≡x' =  yes (y , here ≡-refl)
... | no x≢x' with has-decidable dec ps x'
... | yes (y' , ps-x'-y') = yes (y' , there ps-x'-y')
... | no ¬ps-has-x' = no fun
  where
    fun : Σ B (λ y' → Any (_≡_ (x' , y')) ((x , y) ∷ ps)) → Data.Empty.⊥
    fun (y' , here px) rewrite px = x≢x' (≡-cong proj₁ (≡-sym px))
    fun (y' , there pxs) = ¬ps-has-x' (y' , pxs)

-- Given key ∈ keys, returns a corresponding value.
-- (One of them, there may be multiple corresponding to the same key)

at' : ∀ {a b} {A : Set a} {B : Set b} → 
     (table : FinRel A B) → {key : A} → (key ∈ keys table) → B
at' [] ()
at' (x ∷ xs) (here px) = proj₂ x
at' (x ∷ xs) (there pxs) = at' xs pxs

-- Finds a corresponding value given the decidability of ≡.

at : ∀ {a b} {A : Set a} {B : Set b} → Decidable (_≡_ {A = A}) →
     (table : FinRel A B) → A → Maybe B
at dec table x with has-decidable dec table x
... | yes (y , _) = just y
... | no _ = nothing

----------------------------------------------------------------------------------------------------

-- I think these should be in the stdlib but I haven't found them.

++→-any : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
          Any P xs → Any P (xs ++ ys)
++→-any pxs = Inverse.to ++↔-any ⟨$⟩ (inj₁ pxs)

++→-any₂ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
          Any P ys → Any P (xs ++ ys)
++→-any₂ {xs = xs} {ys = ys} pxs = Inverse.to (++↔-any {xs = xs} {ys = ys}) ⟨$⟩ (inj₂ pxs)


----------------------------------------------------------------------------------------------------

-- Decidability of ∈ and ⊆ given decidability of ≡.

∈-decidable : ∀ {a} {A : Set a} → Decidable (_≡_ {A = A}) → Decidable (_∈_ {A = A})
∈-decidable _≟_ x = any (_≟_ x)

⊆-decidable : ∀ {a} {A : Set a} → Decidable (_≡_ {A = A}) → Decidable (_⊆_ {A = A})
⊆-decidable _≟_ [] l2 = yes (λ ())
⊆-decidable {A = A} _≟_ (x ∷ xs) l2 with ∈-decidable _≟_ x l2
... | no x∉l2 = no (λ z → x∉l2 (z (here ≡-refl)))
... | yes x∈l2 with ⊆-decidable _≟_ xs l2
... | no xs⊈l2 = no (λ z → xs⊈l2 (λ {x'} z' → z (there z')))
... | yes xs⊆l2 = yes whyyes
  where
    whyyes : {x' : A} → x' ∈ (x ∷ xs) → x' ∈ l2
    whyyes (here ≡-refl) = x∈l2
    whyyes (there pxs) = xs⊆l2 pxs

----------------------------------------------------------------------------------------------------

-- This is a trick to build decidability of ≡ using injective functions.
-- Again, it should be in stdlib, but I haven't found it there.

make-≟ : ∀ {a b} {A : Set a} {B : Set b} → 
         (to : A → B) → (∀ {x y} → to x ≡ to y → x ≡ y) → 
         Decidable (_≡_ {A = B}) → Decidable (_≡_ {A = A})
make-≟ to inj _~_ x y with to x ~ to y
... | yes tox≡toy = yes (inj tox≡toy)
... | no ¬tox≡toy = no (λ x≡y → ¬tox≡toy (≡-cong to x≡y))

_×-≟_ : ∀ {a b} {A : Set a} {B : Set b} →
        Decidable (_≡_ {A = A}) → Decidable (_≡_ {A = B}) →
        Decidable (_≡_ {A = A × B})
_×-≟_ _~A_  _~B_ (a1 , b1) (a2 , b2) 
  with a1 ~A a2 | b1 ~B b2
... | yes a | yes b rewrite a | b = yes ≡-refl
... | no na | _ = no (λ x → na (≡-cong proj₁ x))
... | _ | no nb = no (λ x → nb (≡-cong proj₂ x))

≡-head : ∀ {a} {A : Set a} {x1 x2 : A} {xs1 xs2 : List A} →
         (_≡_ {A = List A} (x1 ∷ xs1) (x2 ∷ xs2)) → x1 ≡ x2
≡-head ≡-refl = ≡-refl

≡-tail : ∀ {a} {A : Set a} {x1 x2 : A} {xs1 xs2 : List A} →
         (_≡_ {A = List A} (x1 ∷ xs1) (x2 ∷ xs2)) → xs1 ≡ xs2
≡-tail ≡-refl = ≡-refl

[]-≟ : ∀ {a} {A : Set a} →
       Decidable (_≡_ {A = A}) → Decidable (_≡_ {A = List A})
[]-≟ _~_ [] [] = yes ≡-refl
[]-≟ _~_ [] (x ∷ xs) = no (λ ())
[]-≟ _~_ (x ∷ xs) [] = no (λ ())
[]-≟ {A = A} _~_ (x ∷ xs) (x' ∷ xs') with x ~ x'
... | no np = no (λ x0 → np (≡-head x0))
... | yes p rewrite p with []-≟ _~_ xs xs'
... | yes ps rewrite ps = yes ≡-refl
... | no nps = no (λ x0 → nps (≡-tail x0))
