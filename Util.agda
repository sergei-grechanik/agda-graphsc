
module Util where

open import Level
open import Relation.Binary
open import Data.Product
open import Data.List
import Data.List.Any


record Symbol : Set₁ where
  field
    decSetoid : DecSetoid zero zero
  open DecSetoid decSetoid
  open Data.List.Any.Membership setoid
  field
    fresh : (l : List Carrier) → ∃ (λ s → s ∉ l)

  open DecSetoid decSetoid public
