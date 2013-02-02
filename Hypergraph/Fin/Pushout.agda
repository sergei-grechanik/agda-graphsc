
module Hypergraph.Fin.Pushout where

open import Level hiding (suc; zero)
open import Function
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Empty
open import Data.Nat hiding (_⊔_) renaming (compare to compareℕ; pred to predℕ)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _<_) renaming (_+_ to _+'_)
open import Data.Fin.Props
open import Data.Product hiding (map)
open import Data.Sum renaming ([_,_] to [_,_]-sum; map to _⊕_)
import Relation.Binary.EqReasoning

open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; _≗_; inspect) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans; [_] to i[_])

open StrictTotalOrder Data.Nat.Properties.strictTotalOrder using () renaming (compare to cmp)
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (trans to ≤-trans)


open import Hypergraph.Fin.Coequalizer

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

Coproduct : ∀ {s t} {a b c} (A : Set a) (B : Set b) (C : Set c)
            (f : A → C) (g : B → C) → Set (c ⊔ (b ⊔ (a ⊔ (Level.suc t ⊔ Level.suc s))))
Coproduct {s = s} {t = t} A B C f g = 
  (∀ (S : Setoid s t) f2 g2 →
    ∃! (lift→ (Setoid._≈_ S)) λ h → 
      (h ∘ f ⟨ lift→ (Setoid._≈_ S) ⟩ f2) ×
      (h ∘ g ⟨ lift→ (Setoid._≈_ S) ⟩ g2))

----------------------------------------------------------------------------------------------------

Pushout : ∀ {s t} {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B) (g : A → C) (f' : B → D) (g' : C → D) → Set (Level.suc t ⊔ (Level.suc s ⊔ (d ⊔ (c ⊔ (b ⊔ a)))))
Pushout {s = s} {t = t} f g f' g' = 
  commutative-□ (_≡_) f g f' g' × 
  (∀ (S : Setoid s t) f2 g2 → commutative-□ (Setoid._≈_ S) f g f2 g2 → 
    ∃! (lift→ (Setoid._≈_ S)) λ h → 
      (h ∘ f' ⟨ lift→ (Setoid._≈_ S) ⟩ f2) ×
      (h ∘ g' ⟨ lift→ (Setoid._≈_ S) ⟩ g2))

----------------------------------------------------------------------------------------------------

-- Coproduct of finite sets.

coproduct : ∀ {s t} {m n} → 
            Coproduct {s} {t} (Fin m) (Fin n) (Fin (m + n)) (inject+ n) (raise m)
coproduct {m = m} {n = n} S f2 g2 = h , (h-f2 , h-g2) , only
  where
    h : Fin (m + n) → Setoid.Carrier S
    h x with suc (toℕ x) ≤? m
    ... | yes x<m = f2 (fromℕ≤ x<m)
    ... | no  x≮m = g2 (reduce≥ {m} {n} x (≤-pred (≰⇒> x≮m)))

    h-f2 : ∀ x → Setoid._≈_ S ((h ∘ inject+ n) x) (f2 x)
    h-f2 x with suc (toℕ (inject+ n x)) ≤? m
    ... | yes x<m rewrite ≡-sym (inject+-lemma n x) | fromℕ≤-toℕ x x<m = Setoid.refl S
    ... | no  x≮m  = ⊥-elim (x≮m (subst (λ t → t < m) (inject+-lemma n x) (bounded x)))

    h-g2 : ∀ x → Setoid._≈_ S ((h ∘ raise m) x) (g2 x)
    h-g2 x with suc (toℕ (raise m x)) ≤? m
    ... | yes m+<m rewrite toℕ-raise m x = 
      ⊥-elim (¬i+1+j≤i m (begin 
        m + suc (toℕ x)
      ≡⟨ m+1+n≡1+m+n m (toℕ x) ⟩
        suc (m + toℕ x)
      ≤⟨ m+<m ⟩
        m
      ∎))
      where
        open ≤-Reasoning
    ... | no np rewrite reduce≥-raise m x (≤-pred (≰⇒> np)) = Setoid.refl S

    only : {y : Fin (m + n) → Setoid.Carrier S} →
           Σ ((x : Fin m) → Setoid._≈_ S (y (inject+ n x)) (f2 x))
           (λ x → (x' : Fin n) → Setoid._≈_ S (y (raise m x')) (g2 x')) →
           (x : Fin (m + n)) →
           Setoid._≈_ S (h x) (y x)
    only {y} (y-f2 , y-g2) x with suc (toℕ x) ≤? m
    ... | yes x<m = 
      Setoid.trans S 
        (Setoid.sym S (y-f2 (fromℕ≤ x<m))) 
        (Setoid.reflexive S (≡-cong y (toℕ-inj (
          begin 
            toℕ (inject+ n (fromℕ≤ x<m)) 
          ≡⟨ ≡-sym (inject+-lemma n (fromℕ≤ x<m)) ⟩ 
            toℕ (fromℕ≤ x<m)
          ≡⟨ toℕ-fromℕ≤ x<m ⟩
            toℕ x 
          ∎))))
      where
        open Relation.Binary.PropositionalEquality.≡-Reasoning
    ... | no  x≮m = 
      Setoid.trans S 
        (Setoid.sym S (y-g2 (reduce≥ x (≤-pred (≰⇒> x≮m))))) 
        (Setoid.reflexive S (≡-cong y (raise-reduce≥ m x (≤-pred (≰⇒> x≮m)))))

----------------------------------------------------------------------------------------------------

-- Pushout. Implemented using coequalizers.
-- For details see D.E. Rydeheard, R.M. Burstall, Computational Category Theory.

pushout : ∀ {s t} {k m n} → (f : Fin k → Fin m) → (g : Fin k → Fin n) → 
          ∃ λ l → Σ (Fin m → Fin l) λ f' → Σ (Fin n → Fin l) λ g' → Pushout {s} {t} f g f' g'
pushout f g = {!!}

{-
pushout : ∀ {k m n} → (Fin k → Fin m) → (Fin k → Fin n) → ∃ λ l → (Fin m → Fin l) × (Fin n → Fin l)
pushout {k} {m} {n} f g = go
  where 
    k+m+n = k + m + n
    in-k : Fin k → Fin k+m+n
    in-k = inject+ n ∘ inject+ m
    in-m : Fin m → Fin k+m+n
    in-m = inject+ n ∘ raise k
    in-n : Fin n → Fin k+m+n
    in-n = raise (k + m)

    go : ∃ λ l → (Fin m → Fin l) × (Fin n → Fin l)
    go 
      with coequalizer in-k (in-m ∘ f)
    ... | k' , ε 
      with coequalizer (ε ∘ in-k) (ε ∘ in-n ∘ g)
    ... | l , δ = l , δ ∘ ε ∘ in-m , δ ∘ ε ∘ in-n

-- More convenient notation.

_⊞_ : ∀ {k m n} → (f : Fin k → Fin m) → (g : Fin k → Fin n) → Set
f ⊞ g = Fin (proj₁ (pushout f g))

_⇈[_] : ∀ {k m n} → (f : Fin k → Fin m) → (g : Fin k → Fin n) → (Fin n → f ⊞ g)
f ⇈[ g ] = proj₂ (proj₂ (pushout f g))

_⇉[_] : ∀ {k m n} → (g : Fin k → Fin n) → (f : Fin k → Fin m) → (Fin m → f ⊞ g)
g ⇉[ f ] = proj₁ (proj₂ (pushout f g))
-}
----------------------------------------------------------------------------------------------------
{-
pushout-≗ : ∀ {k m n} (f : Fin k → Fin m) (g : Fin k → Fin n) →
            f ⇈[ g ] ∘ g ≗ g ⇉[ f ] ∘ f
pushout-≗ {k} {m} {n} f g x
  with pushout f g
... | l , g' , f' = {!!}
-}
----------------------------------------------------------------------------------------------------
{-
pushout-universal-∃ : ∀ {a b k m n} {C : Setoid a b} (f : Fin k → Fin m) (g : Fin k → Fin n) 
                        (d : Fin n → Setoid.Carrier C) →
                        (∀ x → d (f x) ⟨ Setoid._≈_ C ⟩ d (g x)) → 
                        Σ (Fin (proj₁ (coequalizer f g)) → Setoid.Carrier C) 
                          λ h → ∀ x → h (proj₂ (coequalizer f g) x) ⟨ Setoid._≈_ C ⟩ d x
-}