
module Graphsc.NatUtil where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Algebra.Structures
open import Data.Nat renaming (compare to compareℕ; pred to predℕ)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _<_) renaming (_+_ to _+'_)
open import Data.Fin.Props
open import Data.Empty
open import Data.Product
open import Data.List
open import Data.Maybe using (Maybe; Eq)
import Data.List.Any
open Data.List.Any.Membership-≡ 
open import Relation.Binary.List.Pointwise using () renaming (Rel to RelList)

open import Relation.Binary.PropositionalEquality using (_≡_; inspect; subst; cong₂) renaming
  (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans)
open Data.List.Any.Membership-≡

open StrictTotalOrder Data.Nat.Properties.strictTotalOrder using () renaming (compare to cmp)
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)
open IsDistributiveLattice isDistributiveLattice using () renaming (∧-comm to ⊔-comm)

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


----------------------------------------------------------------------------------------------------

m≤max : {l : List ℕ} → {m : ℕ} → m ∈ l → m ≤ foldr _⊔_ 0 l
m≤max {[]} ()
m≤max {n ∷ ns} {.n} (Data.List.Any.here ≡-refl) = m≤m⊔n n (foldr _⊔_ 0 ns)
m≤max {n ∷ ns} {m} (Data.List.Any.there pxs) =
      begin
          m
        ≤⟨ m≤m⊔n m n ⟩
          m ⊔ n
        ≤⟨ m≤n⇒m⊔k≤n⊔k (m≤max pxs) ⟩
          (foldr _⊔_ 0 ns) ⊔ n
        ≡⟨ ⊔-comm (foldr Data.Nat._⊔_ 0 ns) n ⟩
          n ⊔ (foldr _⊔_ 0 ns)
      ∎
      where
        open ≤-Reasoning

----------------------------------------------------------------------------------------------------
-- Some lemmas I haven't found in stdlib

toℕ-inj : ∀ {n} {x y : Fin n} → toℕ x ≡ toℕ y → x ≡ y
toℕ-inj {zero} {()} e
toℕ-inj {suc n} {zero} {zero} ≡-refl = ≡-refl
toℕ-inj {suc n} {zero} {suc i} ()
toℕ-inj {suc n} {suc i} {zero} ()
toℕ-inj {suc n} {suc i} {suc i'} e = ≡-cong suc (toℕ-inj (≡-cong predℕ e))

inject!-lemma : ∀ {n} {i : Fin (suc n)} (j : Fin′ i) →
                toℕ (inject! j) ≡ toℕ j
inject!-lemma {n} {zero} ()
inject!-lemma {zero} {suc ()} zero
inject!-lemma {suc n} {suc i} zero = ≡-refl
inject!-lemma {zero} {suc ()} (suc i')
inject!-lemma {suc n} {suc i} (suc i') = ≡-cong suc (inject!-lemma i')

inject₁∘inject! : ∀ {n} {i : Fin (suc n)} (j : Fin′ i) →
                  inject₁ (inject! j) ≡ inject j
inject₁∘inject! j = toℕ-inj (
  begin
    toℕ (inject₁ (inject! j))
  ≡⟨ inject₁-lemma (inject! j) ⟩
    toℕ (inject! j)
  ≡⟨ inject!-lemma j ⟩
    toℕ j
  ≡⟨ ≡-sym (inject-lemma j) ⟩
    toℕ (inject j)
  ∎)
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

----------------------------------------------------------------------------------------------------

-- For some reason this property is private in stdlib.
-- That's why I hate "private".

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero    n = ≡-refl
m+1+n≡1+m+n (suc m) n = ≡-cong suc (m+1+n≡1+m+n m n)

-- reduce-raise lemma

reduce≥-raise : ∀ {m} n (i : Fin m) (ok : toℕ (raise n i) ≥ n) →
                reduce≥ (raise n i) ok ≡ i
reduce≥-raise {m} zero i ok = ≡-refl
reduce≥-raise {m} (suc n) i (s≤s m≤n) = reduce≥-raise n i m≤n

-- raise-reduce lemma

raise-reduce≥ : ∀ {m} n (i : Fin (n + m)) (ok : toℕ i ≥ n) →
                raise n (reduce≥ i ok) ≡ i
raise-reduce≥ zero i ok = ≡-refl
raise-reduce≥ (suc n) zero ()
raise-reduce≥ (suc n) (suc i) (s≤s m≤n) = ≡-cong suc (raise-reduce≥ n i m≤n)

----------------------------------------------------------------------------------------------------

bad : ∀ {a} {A : Set a} {n : ℕ} {l : Fin n} → _≡_ {A = Fin (suc n)} (suc l) (zero) → A
bad ()

unsuc : ∀ {m} → {x y : Fin m} → _≡_ {A = Fin (suc m)} (suc x) (suc y) → _≡_ {A = Fin m} x y
unsuc ≡-refl = ≡-refl

clip : ∀ {m n} → (x : Fin m) → Fin (suc n)
clip {m} {n} x with cmp m (suc n)
clip {.(suc n)} {n} x | tri≈ ¬a ≡-refl ¬c = x
... | tri< a ¬b ¬c = inject≤ x (≤⇒pred≤ (suc m) (suc n) a)
... | tri> ¬a ¬b c with suc (toℕ x) ≤? suc n
... | yes x<sn = fromℕ≤ x<sn
... | no _ = zero

----------------------------------------------------------------------------------------------------