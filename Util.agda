
module Util where

open import Level hiding (suc; _⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Algebra.Structures
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
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

----------------------------------------------------------------------------------------------------

-- It wasn't me! Agda generated it by itself (well, almost).
m≤n⇒m⊔k≤n⊔k : ∀ {m n k} → m ≤ n → m ⊔ k ≤ n ⊔ k
m≤n⇒m⊔k≤n⊔k {ℕ.zero} {ℕ.zero} {ℕ.zero} m≤n = z≤n
m≤n⇒m⊔k≤n⊔k {ℕ.zero} {ℕ.zero} {suc n} m≤n = s≤s (m≤n⇒m⊔k≤n⊔k m≤n)
m≤n⇒m⊔k≤n⊔k {ℕ.zero} {suc ℕ.zero} {ℕ.zero} m≤n = z≤n
m≤n⇒m⊔k≤n⊔k {ℕ.zero} {suc ℕ.zero} {suc n} m≤n = s≤s {m = n} {n = n} (m≤n⇒m⊔k≤n⊔k {m = ℕ.zero} {n = ℕ.zero} z≤n)
m≤n⇒m⊔k≤n⊔k {ℕ.zero} {suc (suc n)} {ℕ.zero} m≤n = z≤n
m≤n⇒m⊔k≤n⊔k {ℕ.zero} {suc (suc n)} {suc n'} m≤n = s≤s {m = n'} {n = suc n ⊔ n'} (m≤n⇒m⊔k≤n⊔k {m = ℕ.zero} {n = suc n} z≤n)
m≤n⇒m⊔k≤n⊔k {suc ℕ.zero} {ℕ.zero} {ℕ.zero} m≤n = m≤n
m≤n⇒m⊔k≤n⊔k {suc ℕ.zero} {ℕ.zero} {suc n} m≤n = s≤s {m = n} {n = n} (m≤n⇒m⊔k≤n⊔k {m = ℕ.zero} {n = ℕ.zero} z≤n)
m≤n⇒m⊔k≤n⊔k {suc ℕ.zero} {suc n} {ℕ.zero} m≤n = s≤s z≤n
m≤n⇒m⊔k≤n⊔k {suc ℕ.zero} {suc n} {suc n'} m≤n = s≤s {m = n'} {n = n ⊔ n'} (m≤n⇒m⊔k≤n⊔k {m = ℕ.zero} {n = n} z≤n)
m≤n⇒m⊔k≤n⊔k {suc (suc n)} {ℕ.zero} {ℕ.zero} m≤n = m≤n
m≤n⇒m⊔k≤n⊔k {suc (suc n)} {ℕ.zero} {suc ℕ.zero} ()
m≤n⇒m⊔k≤n⊔k {suc (suc n)} {ℕ.zero} {suc (suc n')} ()
m≤n⇒m⊔k≤n⊔k {suc (suc n)} {suc n'} {ℕ.zero} m≤n = m≤n
m≤n⇒m⊔k≤n⊔k {suc (suc n)} {suc n'} {suc n0} (s≤s m≤n) = s≤s (m≤n⇒m⊔k≤n⊔k m≤n)

ℕ-fresh : (l : List ℕ) → ∃ (λ n → n ∉ l)
ℕ-fresh l = suc (foldr _⊔_ 0 l) , (λ x → 1+n≰n (m≤max x))
  where
    open ≤-Reasoning
    -- private sucks
    open IsDistributiveLattice isDistributiveLattice using (∧-comm)
    m≤max : {l' : List ℕ} → {m : ℕ} → m ∈ l' → m ≤ foldr _⊔_ 0 l'
    m≤max {[]} ()
    m≤max {n ∷ ns} {.n} (Data.List.Any.here refl) = m≤m⊔n n (foldr _⊔_ 0 ns)
    m≤max {n ∷ ns} {m} (Data.List.Any.there pxs) = 
      begin
          m 
        ≤⟨ m≤m⊔n m n ⟩
          m ⊔ n 
        ≤⟨ m≤n⇒m⊔k≤n⊔k (m≤max pxs) ⟩ 
          (foldr _⊔_ 0 ns) ⊔ n 
        ≡⟨ ∧-comm (foldr Data.Nat._⊔_ 0 ns) n ⟩ 
          n ⊔ (foldr _⊔_ 0 ns)
      ∎        

ℕ-symbol : Symbol
ℕ-symbol = 
  record {
    Carrier = ℕ;
    ≡-decidable = _≟_;
    fresh = ℕ-fresh
  }