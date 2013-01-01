
open import Util

module ExampleArithmetic (symbol : Symbol) where

open import Data.Nat
open import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (setoid)
import Hypergraph

data ArithLabel : Set where
  [+] [*] [0] [suc] : ArithLabel

eval : ArithLabel → List ℕ → Maybe ℕ
eval [+] (m ∷ n ∷ []) = just (m + n)
eval [*] (m ∷ n ∷ []) = just (m * n)
eval [suc] (n ∷ []) = just (suc n)
eval [0] [] = just 0
eval _ _ = nothing

ArithSemantics : Semantics
ArithSemantics =
  record {
    Label = ArithLabel;
    domain = setoid ℕ;
    ⟦_⟧L_ = eval
  }

open Semantics ArithSemantics
open Hypergraph symbol ArithSemantics

_,,_ : {A : Set} → (a b : A) → List A
_,,_ a b = a ∷ b ∷ []

[+]-symm : {sig : Sig} → {a b c : Node sig} → 
           [ a ▷ [+] ▷ (b ,, c) ]  ⇚⇛  [ a ▷ [+] ▷ (c ,, b) ]
[+]-symm = {!!}
