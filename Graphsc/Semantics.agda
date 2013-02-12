
module Graphsc.Semantics where

open import Level hiding (suc; _⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List
open import Data.Maybe using (Maybe; Eq)
open import Relation.Binary.List.Pointwise using () renaming (Rel to RelList)

record Semantics : Set₁ where
  field
    Label : Set
    label-≡-decidable : Decidable (_≡_ {A = Label})
    domain : Setoid Level.zero Level.zero
    ⟦_⟧L : Label → List (Setoid.Carrier domain) → Maybe (Setoid.Carrier domain)
    respect : {l : Label} {ds1 ds2 : List (Setoid.Carrier domain)} → 
              RelList (Setoid._≈_ domain) ds1 ds2 → Eq (Setoid._≈_ domain) (⟦ l ⟧L ds1) (⟦ l ⟧L ds2)