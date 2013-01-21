
open import Util

module Hypergraph.FinSymb (semantics : Semantics) where

open import ListUtil

open import Function
open import Function.Inverse hiding (_∘_; map; id)
open import Function.Equality hiding (_∘_; id)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Empty
open import Data.Nat renaming (compare to compareℕ; pred to predℕ)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _<_) renaming (_+_ to _+'_)
open import Data.Fin.Props
open import Data.Product hiding (map)
open import Data.Maybe using (Maybe; just; nothing; Eq; maybeToBool) renaming (setoid to eq-setoid)
open import Data.Bool using (T)
open import Data.Sum renaming ([_,_] to [_,_]-sum; map to _⊕_)
open import Data.List hiding (any)
open import Data.List.Properties
open import Data.List.All hiding (map)
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to RelList)
open import Data.List.Any.Properties using (map↔) renaming (++↔ to ++↔-any)
open import Data.List.All.Properties using (++↔)
import Relation.Binary.EqReasoning

open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; _≗_; inspect) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans; [_] to i[_])
open Data.List.Any.Membership-≡ 

open StrictTotalOrder Data.Nat.Properties.strictTotalOrder using () renaming (compare to cmp)
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (trans to ≤-trans)

open Semantics semantics
open Setoid domain using (_≈_)
  renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans; refl to ≈-refl) 


import Hypergraph.Core
open Hypergraph.Core semantics

import Hypergraph.Interpretation
open Hypergraph.Interpretation semantics



-- This helper function just creates a map that "glues" f to g.

coequalizer1-helper : ∀ {n} (f : Fin (suc n)) (g : Fin (suc n)) →
                      toℕ f < toℕ g → Fin (suc n) → Fin n
coequalizer1-helper f g f<g k with cmp (toℕ k) (toℕ g)
... | tri≈ ¬a b ¬c = fromℕ≤ (≤-trans f<g (≤-pred (bounded g)))
... | tri< k<g ¬b ¬c = fromℕ≤ (≤-trans k<g (≤-pred (bounded g)))
... | tri> ¬a ¬b c with k
coequalizer1-helper f g f<g k | tri> ¬a ¬b () | zero
... | suc k' = fromℕ≤ (≤-pred (bounded (suc k')))

-- Coequalizer for the special case when m = 1

coequalizer1 : ∀ {n} → Fin n → Fin n → ∃ λ k → (Fin n → Fin k)
coequalizer1 {zero} () ()
coequalizer1 {suc n} f g with cmp (toℕ f) (toℕ g)
... | tri≈ ¬a b ¬c = suc n , id
... | tri< a ¬b ¬c = n , coequalizer1-helper f g a
... | tri> ¬a ¬b c = n , coequalizer1-helper g f c

-- Coequalizer for finite sets.

coequalizer : ∀ {m n} → (Fin m → Fin n) → (Fin m → Fin n) → ∃ λ k → (Fin n → Fin k)
coequalizer {0} {n} f g = n , Function.id
coequalizer {suc m'} {n} f g with coequalizer {m'} (f ∘ inject₁) (g ∘ inject₁)
... | k' , q with coequalizer1 (q (f (fromℕ m'))) (q (g (fromℕ m')))
... | k , r = k , r ∘ q

-- Pushout. Implemented using coequalizers.
-- For details see D.E. Rydeheard, R.M. Burstall, Computational Category Theory.

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
-- Here we prove that coequalizer equalizes.

coequalizer1-helper-≡ : ∀ {n} (f g : Fin (suc n)) (f<g : toℕ f < toℕ g) → 
                        coequalizer1-helper f g f<g f ≡ coequalizer1-helper f g f<g g
coequalizer1-helper-≡ {n} f g f<g with cmp (toℕ f) (toℕ g)
... | tri≈ ¬a b ¬c = ⊥-elim (¬a f<g)
... | tri> ¬a ¬b c = ⊥-elim (¬a f<g)
... | tri< a ¬b ¬c with cmp (toℕ g) (toℕ g)
... | tri< a' ¬b' ¬c' = ⊥-elim (¬c' a')
... | tri> ¬a' ¬b' c' = ⊥-elim (¬b' ≡-refl)
... | tri≈ ¬a' b' ¬c' = toℕ-inj (
  begin
    toℕ (fromℕ≤ (≤-trans a (≤-pred (bounded g))))
  ≡⟨ toℕ-fromℕ≤ _ ⟩
    toℕ f
  ≡⟨ ≡-sym (toℕ-fromℕ≤ _) ⟩
    toℕ (fromℕ≤ (≤-trans f<g (≤-pred (bounded g))))
  ∎)
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

coequalizer1-≗ : ∀ {n} (f g : Fin n) →
                 proj₂ (coequalizer1 f g) f ≡ proj₂ (coequalizer1 f g) g
coequalizer1-≗ {zero} () ()
coequalizer1-≗ {suc n} f g with cmp (toℕ f) (toℕ g)
... | tri≈ ¬a b ¬c = toℕ-inj b
... | tri< a ¬b ¬c = coequalizer1-helper-≡ f g a
... | tri> ¬a ¬b c = ≡-sym (coequalizer1-helper-≡ g f c)

-- The actual theorem.

coequalizer-≗ : ∀ {m n} (f g : Fin m → Fin n) →
               proj₂ (coequalizer f g) ∘ f ≗ proj₂ (coequalizer f g) ∘ g
coequalizer-≗ {zero} _ _ ()
coequalizer-≗ {suc m'} {n} f g x with fromℕ m' | inspect fromℕ m' | compare x (fromℕ m')
coequalizer-≗ {suc m'} f g x | .(inject l) | i[ fromℕ-m'=inj-l ] | greater .x l = 
  let l<x = bounded l
      x<=m' = ≤-pred (bounded x)
      m'=l = subst₂ _≡_ (to-from m') (inject-lemma l) (≡-cong toℕ fromℕ-m'=inj-l)
      x<=l = subst (λ t → toℕ x ≤ t) m'=l x<=m'
  in ⊥-elim (1+n≰n {toℕ l} (≤-trans l<x x<=l))
coequalizer-≗ {suc m'} f g .mm | mm | _ | equal .mm = 
  coequalizer1-≗ 
    (proj₂ (coequalizer (λ x' → f (inject₁ x')) (λ x' → g (inject₁ x'))) (f mm)) 
    (proj₂ (coequalizer (λ x' → f (inject₁ x')) (λ x' → g (inject₁ x'))) (g mm))
coequalizer-≗ {suc m'} f g .(inject least) | mm | _ | less .mm least
  rewrite ≡-sym (inject₁∘inject! least) 
        | coequalizer-≗ {m'} (f ∘ inject₁) (g ∘ inject₁) (inject! least)
  = ≡-refl
