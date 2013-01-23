
module Hypergraph.Fin.Pushout where

open import Function
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Empty
open import Data.Nat renaming (compare to compareℕ; pred to predℕ)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _<_) renaming (_+_ to _+'_)
open import Data.Fin.Props
open import Data.Product hiding (map)
open import Data.Sum renaming ([_,_] to [_,_]-sum; map to _⊕_)
import Relation.Binary.EqReasoning

open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; _≗_; inspect) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans; [_] to i[_])

open StrictTotalOrder Data.Nat.Properties.strictTotalOrder using () renaming (compare to cmp)
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (trans to ≤-trans)


open import Hypergraph.Fin.Coequalizer

----------------------------------------------------------------------------------------------------

-- Pushout. Implemented using coequalizers.
-- For details see D.E. Rydeheard, R.M. Burstall, Computational Category Theory.

pushout : ∀ {k m n} → (Fin k → Fin m) → (Fin k → Fin n) → ∃ λ l → (Fin m → Fin l) × (Fin n → Fin l)
pushout {k} {m} {n} f g = go
  where 
    k+m+n = k + m + n
    in-k : Fin k → Fin k+m+n
    in-k = inject+ n ∘ inject+ m
    in-m : Fin m → Fin k+m+n
    in-m = inject+ n ∘ raise k
    in-n : Fin n → Fin k+m+n
    in-n = raise (k + m)

    go : ∃ λ l → (Fin m → Fin l) × (Fin n → Fin l)
    go 
      with coequalizer in-k (in-m ∘ f)
    ... | k' , ε 
      with coequalizer (ε ∘ in-k) (ε ∘ in-n ∘ g)
    ... | l , δ = l , δ ∘ ε ∘ in-m , δ ∘ ε ∘ in-n

-- More convenient notation.

_⊞_ : ∀ {k m n} → (f : Fin k → Fin m) → (g : Fin k → Fin n) → Set
f ⊞ g = Fin (proj₁ (pushout f g))

_⇈[_] : ∀ {k m n} → (f : Fin k → Fin m) → (g : Fin k → Fin n) → (Fin n → f ⊞ g)
f ⇈[ g ] = proj₂ (proj₂ (pushout f g))

_⇉[_] : ∀ {k m n} → (g : Fin k → Fin n) → (f : Fin k → Fin m) → (Fin m → f ⊞ g)
g ⇉[ f ] = proj₁ (proj₂ (pushout f g))