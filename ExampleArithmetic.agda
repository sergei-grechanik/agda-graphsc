
open import Util

module ExampleArithmetic (symbol : Symbol) where

open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Maybe using (Maybe; just; nothing; drop-just)
open import Relation.Binary.PropositionalEquality using (setoid)
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable
open import Algebra.Structures
import Hypergraph

open import ListUtil

open IsCommutativeSemiring isCommutativeSemiring using (+-comm)

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
    label-≡-decidable = {!!};
    domain = setoid ℕ;
    ⟦_⟧L_ = eval;
    respect = {!!}
  }

open Semantics ArithSemantics
open Symbol ℕ-symbol renaming (Carrier to Symb)
open Hypergraph ℕ-symbol ArithSemantics

{-
symbols : ℕ → List Symb
sym : ℕ → Symb

sym n = proj₁ (fresh (symbols n))

symbols zero = []
symbols (suc n) = sym n ∷ symbols n
-}

_,,_ : {A : Set} → (a b : A) → List A
_,,_ a b = a ∷ b ∷ []

[+]-comm : [ 0 ▷ [+] ▷ (1 ,, 2) ]  ⇄  [ 0 ▷ [+] ▷ (2 ,, 1) ]
[+]-comm =
  (λ i i⊨l → (restrict auto-⊆ i) , restrict-≍ i , (yes auto-∈ auto-⊆ (just (
    begin
      i ⟦ 0 ⟧
    ≡⟨ drop-just (to-eq (head i⊨l)) ⟩
      i ⟦ 1 ⟧ + i ⟦ 2 ⟧
    ≡⟨ +-comm (i ⟦ 1 ⟧) (i ⟦ 2 ⟧) ⟩
      i ⟦ 2 ⟧ + i ⟦ 1 ⟧
    ∎
  ))) ∷ []) , 
  {!!} , 
  auto-⊆
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning