
open import Util

module Hypergraph.FinSymb (semantics : Semantics) where

open import ListUtil

import Level
open import Function
open import Function.Inverse hiding (_∘_; map; id; sym)
open import Function.Equality hiding (_∘_; id)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Empty
open import Data.Nat renaming (compare to compareℕ; pred to predℕ)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _<_) renaming (_+_ to _+'_)
open import Data.Fin.Props
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

open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; _≗_; inspect) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans; [_] to i[_])
open Data.List.Any.Membership-≡ 

open StrictTotalOrder Data.Nat.Properties.strictTotalOrder using () renaming (compare to cmp)
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (trans to ≤-trans)

open Semantics semantics
open Setoid domain using (_≈_)
  renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans; refl to ≈-refl) 


import Hypergraph.Core
open Hypergraph.Core semantics

import Hypergraph.Interpretation
open Hypergraph.Interpretation semantics

open import Hypergraph.Fin.Coequalizer
open import Hypergraph.Fin.Pushout

----------------------------------------------------------------------------------------------------

-- Pushout interacts in a nice way with ⇛.
-- This is the main result of this module.

pushout-⇛ : ∀ {m n l} {f : Fin m → Fin n} {g : Fin m → Fin l} 
            {g1 : Hypergraph (Fin m)} {g2 : Hypergraph (Fin n)} →
            g1 ⇛[ f ] g2 → hmap g g1 ⇛[ f ⇈[ g ] ] hmap (g ⇉[ f ]) g2
pushout-⇛ {m} {n} {l} {f} {g} {g1} {g2} g1⇛g2 il il⊨hmapg1 = {!!}