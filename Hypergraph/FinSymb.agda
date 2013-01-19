
open import Util

module Hypergraph.FinSymb (semantics : Semantics) where

open import ListUtil

open import Function
open import Function.Inverse hiding (_∘_; map; id)
open import Function.Equality hiding (_∘_; id)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Nat hiding (compare)
open import Data.Fin renaming (_+_ to _+'_)
open import Data.Product hiding (map)
open import Data.Maybe using (Maybe; just; nothing; Eq; maybeToBool) renaming (setoid to eq-setoid)
open import Data.Bool using (T)
open import Data.Sum renaming ([_,_] to [_,_]-sum; map to _⊕_)
open import Data.List hiding (any)
open import Data.List.Properties
open import Data.List.All hiding (map)
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to RelList)
open import Data.List.Any.Properties using (map↔) renaming (++↔ to ++↔-any)
open import Data.List.All.Properties using (++↔)
import Relation.Binary.EqReasoning

open import Relation.Binary.PropositionalEquality using (_≡_; subst; _≗_) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans)
open Data.List.Any.Membership-≡ 

open Semantics semantics
open Setoid domain using (_≈_)
  renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans; refl to ≈-refl) 


import Hypergraph.Core
open Hypergraph.Core semantics

import Hypergraph.Interpretation
open Hypergraph.Interpretation semantics


-- This helper function just creates a map that "glues" f to g'.

coequalizer1-helper : ∀ {n} → (f : Fin (suc n)) → (g' : Fin′ f) → Fin (suc n) → Fin n
coequalizer1-helper {n} f g' k with compare k f
coequalizer1-helper {n} .f g' .(inject k') | less f k' = inject! k'
coequalizer1-helper {n} .f g' .f | equal f = inject! g'
coequalizer1-helper .(inject f') g' .(suc k) | greater (suc k) f' = k
coequalizer1-helper .(inject f') g' .zero | greater zero f' with f'
... | ()

-- Coequalizer for the special case when m = 1

coequalizer1 : ∀ {n} → Fin n → Fin n → ∃ λ k → (Fin n → Fin k)
coequalizer1 {zero} () ()
coequalizer1 {suc n} f g with compare f g
coequalizer1 {suc n} f .f | equal .f = suc n , Function.id
coequalizer1 {suc n} .f .(inject g') | greater f g' = n , coequalizer1-helper f g'
coequalizer1 {suc n} .(inject f') .g | less g f' = n , coequalizer1-helper g f'

-- Coequalizer for finite sets.

coequalizer : ∀ {m n} → (Fin m → Fin n) → (Fin m → Fin n) → ∃ λ k → (Fin n → Fin k)
coequalizer {0} {n} f g = n , Function.id
coequalizer {suc m'} {n} f g with coequalizer {m'} (f ∘ inject₁) (g ∘ inject₁)
... | k' , q with coequalizer1 (q (f (fromℕ m'))) (q (g (fromℕ m')))
... | k , r = k , r ∘ q

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

----------------------------------------------------------------------------------------------------
