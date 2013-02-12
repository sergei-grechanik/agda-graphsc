
module Graphsc.ExampleArithmetic where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _<_) renaming (_+_ to _+'_)
open import Data.Fin.Dec
open import Data.Fin.Props hiding (setoid) renaming (_≟_ to Fin-≟)
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Maybe using (Maybe; just; nothing; drop-just; Eq)
open import Relation.Binary
open import Relation.Binary.List.Pointwise using ([]; _∷_; Rel≡⇒≡; ≡⇒Rel≡) renaming (Rel to RelList)
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable
open import Algebra.Structures

open import Relation.Binary.PropositionalEquality using (_≡_; inspect; subst; cong₂) renaming 
  (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans)

open import Graphsc.Semantics

import Graphsc.Hypergraph
import Graphsc.Interpretation
import Graphsc.Transformation

open IsCommutativeSemiring isCommutativeSemiring using (+-comm; *-comm)

data ArithLabel : Set where
  [+] [*] [0] [1] : ArithLabel

-- Agda's automatic solver is quite good at generating this kind of stuff.
arithlabel-≟ : Decidable (_≡_ {A = ArithLabel})
arithlabel-≟ [+] [+] = yes _≡_.refl
arithlabel-≟ [+] [*] = no (λ ())
arithlabel-≟ [+] [0] = no (λ ())
arithlabel-≟ [+] [1] = no (λ ())
arithlabel-≟ [*] [+] = no (λ ())
arithlabel-≟ [*] [*] = yes _≡_.refl
arithlabel-≟ [*] [0] = no (λ ())
arithlabel-≟ [*] [1] = no (λ ())
arithlabel-≟ [0] [+] = no (λ ())
arithlabel-≟ [0] [*] = no (λ ())
arithlabel-≟ [0] [0] = yes _≡_.refl
arithlabel-≟ [0] [1] = no (λ ())
arithlabel-≟ [1] [+] = no (λ ())
arithlabel-≟ [1] [*] = no (λ ())
arithlabel-≟ [1] [0] = no (λ ())
arithlabel-≟ [1] [1] = yes _≡_.refl

eval : ArithLabel → List ℕ → Maybe ℕ
eval [+] (m ∷ n ∷ []) = just (m + n)
eval [*] (m ∷ n ∷ []) = just (m * n)
eval [1] [] = just 1
eval [0] [] = just 0
eval _ _ = nothing

Eq-≡-reflexive : ∀ {a} {A : Set a} {x y : Maybe A} → x ≡ y → Eq _≡_ x y
Eq-≡-reflexive {a} {A} {just x} ≡-refl = just ≡-refl
Eq-≡-reflexive {a} {A} {nothing} ≡-refl = nothing

arith-respect : {l : ArithLabel} {ds1 ds2 : List ℕ} →
                RelList _≡_ ds1 ds2 → Eq _≡_ (eval l ds1) (eval l ds2)
arith-respect {l} {ds1} {ds2} eq rewrite (Rel≡⇒≡ eq) = Eq-≡-reflexive ≡-refl

ArithSemantics : Semantics
ArithSemantics =
  record {
    Label = ArithLabel;
    label-≡-decidable = arithlabel-≟;
    domain = ≡-setoid ℕ;
    ⟦_⟧L = eval;
    respect = λ {l} {ds1} {ds2} → arith-respect {l} {ds1} {ds2}
  }

open Semantics ArithSemantics
open Graphsc.Hypergraph ArithSemantics
open Graphsc.Interpretation ArithSemantics
open Graphsc.Transformation ArithSemantics

open Relation.Binary.PropositionalEquality.≡-Reasoning

_⟦_⟧ : ∀ {m} (i : Interpretation (Fin m)) (k : ℕ)
       {_ : True (suc k ≤? m) } → ℕ
_⟦_⟧ i k {t} = i (fromℕ≤ (toWitness t))

[+]-comm : SimpleTrans _⇄[_]_
[+]-comm = 
  simpleTrans-⇄ 
    [ 0 ▷ [+] ▷ (1 ∷ 2 ∷ []) ] 
    [ 0 ▷ [+] ▷ (2 ∷ 1 ∷ []) ]
    []
    ((λ i1 i1⊨g1 → i1 , ≍-refl , 
      just (
        begin
          i1 ⟦ 0 ⟧
        ≡⟨ drop-just (head i1⊨g1) ⟩
          i1 ⟦ 1 ⟧ + i1 ⟦ 2 ⟧
        ≡⟨ +-comm (i1 ⟦ 1 ⟧) (i1 ⟦ 2 ⟧) ⟩
          i1 ⟦ 2 ⟧ + i1 ⟦ 1 ⟧        
        ∎
      ) ∷ []) , 
     {!!})

{-
-    begin
-      i ⟦ 0 ⟧
-    ≡⟨ drop-just (to-eq (head i⊨l)) ⟩
-      i ⟦ 1 ⟧ + i ⟦ 2 ⟧
-    ≡⟨ +-comm (i ⟦ 1 ⟧) (i ⟦ 2 ⟧) ⟩
-      i ⟦ 2 ⟧ + i ⟦ 1 ⟧
-    ∎
-}