
module Util where

open import Level
open import Relation.Binary
open import Data.Product
open import Data.List
open import Data.Maybe using (Maybe)
import Data.List.Any

record Symbol : Set₁ where
  field
    decSetoid : DecSetoid zero zero
  open DecSetoid decSetoid
  open Data.List.Any.Membership setoid
  field
    fresh : (l : List Carrier) → ∃ (λ s → s ∉ l)

  open DecSetoid decSetoid public

record Semantics : Set₁ where
  field
    Label : Set
    domain : Setoid Level.zero Level.zero
    ⟦_⟧L_ : Label → List (Setoid.Carrier domain) → Maybe (Setoid.Carrier domain)