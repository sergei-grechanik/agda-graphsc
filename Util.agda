
module Util where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product
open import Data.List
open import Data.Maybe using (Maybe; Eq)
import Data.List.Any
open Data.List.Any.Membership-≡ 
open import Relation.Binary.List.Pointwise using () renaming (Rel to RelList)

record Symbol : Set₁ where
  field
    Carrier : Set
    ≡-decidable : Decidable (_≡_ {A = Carrier})
    fresh : (l : List Carrier) → ∃ (λ s → s ∉ l)

record Semantics : Set₁ where
  field
    Label : Set
    label-≡-decidable : Decidable (_≡_ {A = Label})
    domain : Setoid Level.zero Level.zero
    ⟦_⟧L_ : Label → List (Setoid.Carrier domain) → Maybe (Setoid.Carrier domain)
    respect : {l : Label} → {ds1 ds2 : List (Setoid.Carrier domain)} → 
              RelList (Setoid._≈_ domain) ds1 ds2 → Eq (Setoid._≈_ domain) (⟦ l ⟧L ds1) (⟦ l ⟧L ds2)