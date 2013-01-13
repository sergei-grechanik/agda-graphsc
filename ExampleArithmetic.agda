
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

open IsCommutativeSemiring isCommutativeSemiring using (+-comm; *-comm)

data ArithLabel : Set where
  [+] [*] [0] [1] [=] : ArithLabel

eval : ArithLabel → List ℕ → Maybe ℕ
eval [+] (m ∷ n ∷ []) = just (m + n)
eval [*] (m ∷ n ∷ []) = just (m * n)
eval [1] [] = just 1
eval [0] [] = just 0
eval [=] (m ∷ []) = just m
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

[[_,_]] : {A : Set} → (a b : A) → List A
[[_,_]] a b = a ∷ b ∷ []

{-
auto-⇛ : {g1 g2 : Hypergraph} →
         {i : Interpretation (nodes g1)} → 
         (i⊨g1 : i ⊨ g1) → 
         {g2⊆g1 : True (⊆-decidable ≡-decidable (nodes g2) (nodes g1))} →
         (restrict (toWitness g2⊆g1) i) ⊨ g2 →
           Interpretation (nodes g2) × 
           (i ≍ (restrict (toWitness g2⊆g1) i)) × 
           ((restrict (toWitness g2⊆g1) i) ⊨ g2)
auto-⇛ {g1} {g2} {i} i⊨g1 {g2⊆g1} i⊨g2  =
  (restrict (toWitness g2⊆g1) i) ,
  (restrict-≍ i) ,
  i⊨g2 -}


open Relation.Binary.PropositionalEquality.≡-Reasoning

[+]-comm : [ 0 ▷ [+] ▷ [[ 1 , 2 ]] ]  ⇄  [ 0 ▷ [+] ▷ [[ 2 , 1 ]] ]
[+]-comm =
  (λ i i⊨l → (restrict auto-⊆ i) , restrict-≍ i , auto-⊨[] (
    begin
      i ⟦ 0 ⟧
    ≡⟨ drop-just (to-eq (head i⊨l)) ⟩
      i ⟦ 1 ⟧ + i ⟦ 2 ⟧
    ≡⟨ +-comm (i ⟦ 1 ⟧) (i ⟦ 2 ⟧) ⟩
      i ⟦ 2 ⟧ + i ⟦ 1 ⟧
    ∎
  ) ∷ []) ,
  (λ i i⊨l → (restrict auto-⊆ i) , restrict-≍ i , auto-⊨[] (
    begin
      i ⟦ 0 ⟧
    ≡⟨ drop-just (to-eq (head i⊨l)) ⟩
      i ⟦ 2 ⟧ + i ⟦ 1 ⟧
    ≡⟨ +-comm (i ⟦ 2 ⟧) (i ⟦ 1 ⟧) ⟩
      i ⟦ 1 ⟧ + i ⟦ 2 ⟧
    ∎
  ) ∷ []) , 
  auto-⊆

[+]-id : [[ (0 ▷ [+] ▷ (1 ∷ 2 ∷ [])) , (1 ▷ [0] ▷ []) ]]  ⇛  [ 0 ▷ [=] ▷ (2 ∷ []) ]
[+]-id = {!!}

[*]-comm : [ 0 ▷ [*] ▷ (1 ∷ 2 ∷ []) ]  ⇄  [ 0 ▷ [*] ▷ (2 ∷ 1 ∷ []) ]
[*]-comm =
  (λ i i⊨l → (restrict auto-⊆ i) , restrict-≍ i , auto-⊨[] (
    begin
      i ⟦ 0 ⟧
    ≡⟨ drop-just (to-eq (head i⊨l)) ⟩
      i ⟦ 1 ⟧ * i ⟦ 2 ⟧
    ≡⟨ *-comm (i ⟦ 1 ⟧) (i ⟦ 2 ⟧) ⟩
      i ⟦ 2 ⟧ * i ⟦ 1 ⟧
    ∎
  ) ∷ []) ,
  (λ i i⊨l → (restrict auto-⊆ i) , restrict-≍ i , auto-⊨[] (
    begin
      i ⟦ 0 ⟧
    ≡⟨ drop-just (to-eq (head i⊨l)) ⟩
      i ⟦ 2 ⟧ * i ⟦ 1 ⟧
    ≡⟨ *-comm (i ⟦ 2 ⟧) (i ⟦ 1 ⟧) ⟩
      i ⟦ 1 ⟧ * i ⟦ 2 ⟧
    ∎
  ) ∷ []) , 
  auto-⊆