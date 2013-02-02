
module Hypergraph.Fin.Coequalizer where

open import Level hiding (zero; suc)
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

lift→ : ∀ {a b c ℓ} {A : Set a} {B : Set b} {X : Set ℓ} → 
        (A → B → Set c) → (X → A) → (X → B) → Set (ℓ ⊔ c)
lift→ _∼_ f g = ∀ x → f x ∼ g x

----------------------------------------------------------------------------------------------------

commutative-□ : ∀ {a b c d ℓ} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
                (_∼_ : D → D → Set ℓ)
                (f : A → B) (g : A → C) (f' : B → D) (g' : C → D) → Set (ℓ ⊔ a)
commutative-□ (_∼_) f g f' g' = ∀ x → f' (f x) ∼ g' (g x)

Coequalizer : ∀ {s t} {a b d} {A : Set a} {B : Set b} {D : Set d}
            (f : A → B) (g : A → B) (e : B → D) → Set (Level.suc t ⊔ (Level.suc s ⊔ (d ⊔ (b ⊔ a))))
Coequalizer {s = s} {t = t} f g e = 
  commutative-□ (_≡_) f g e e × 
  (∀ (S : Setoid s t) e2 → commutative-□ (Setoid._≈_ S) f g e2 e2 → 
    ∃! (lift→ (Setoid._≈_ S)) λ h → 
      h ∘ e ⟨ lift→ (Setoid._≈_ S) ⟩ e2)

----------------------------------------------------------------------------------------------------
-- Here we define coequalizer for finite sets.
-- The style we use here is called "externalism" and it sucks.

-- This helper function just creates a map that "glues" g to f.

coequalizer-impl1-helper : ∀ {n} (f : Fin (suc n)) (g : Fin (suc n)) →
                      toℕ f < toℕ g → Fin (suc n) → Fin n
coequalizer-impl1-helper f g f<g k with cmp (toℕ k) (toℕ g)
... | tri≈ ¬a b ¬c = fromℕ≤ (≤-trans f<g (≤-pred (bounded g)))
... | tri< k<g ¬b ¬c = fromℕ≤ (≤-trans k<g (≤-pred (bounded g)))
... | tri> ¬a ¬b c with k
coequalizer-impl1-helper f g f<g k | tri> ¬a ¬b () | zero
... | suc k' = fromℕ≤ (≤-pred (bounded (suc k')))

-- Coequalizer-impl for the special case when m = 1

coequalizer-impl1 : ∀ {n} → Fin n → Fin n → ∃ λ k → (Fin n → Fin k)
coequalizer-impl1 {zero} () ()
coequalizer-impl1 {suc n} f g with cmp (toℕ f) (toℕ g)
... | tri≈ ¬a b ¬c = suc n , id
... | tri< a ¬b ¬c = n , coequalizer-impl1-helper f g a
... | tri> ¬a ¬b c = n , coequalizer-impl1-helper g f c

-- Coequalizer-impl for finite sets.

coequalizer-impl : ∀ {m n} → (Fin m → Fin n) → (Fin m → Fin n) → ∃ λ k → (Fin n → Fin k)
coequalizer-impl {0} {n} f g = n , Function.id
coequalizer-impl {suc m'} {n} f g with coequalizer-impl {m'} (f ∘ inject₁) (g ∘ inject₁)
... | k' , q with coequalizer-impl1 (q (f (fromℕ m'))) (q (g (fromℕ m')))
... | k , r = k , r ∘ q

----------------------------------------------------------------------------------------------------
-- Here we prove that coequalizer-impl equalizes.

coequalizer-impl1-helper-≡ : ∀ {n} (f g : Fin (suc n)) (f<g : toℕ f < toℕ g) → 
                        coequalizer-impl1-helper f g f<g f ≡ coequalizer-impl1-helper f g f<g g
coequalizer-impl1-helper-≡ {n} f g f<g with cmp (toℕ f) (toℕ g)
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

coequalizer-impl1-≗ : ∀ {n} (f g : Fin n) →
                 proj₂ (coequalizer-impl1 f g) f ≡ proj₂ (coequalizer-impl1 f g) g
coequalizer-impl1-≗ {zero} () ()
coequalizer-impl1-≗ {suc n} f g with cmp (toℕ f) (toℕ g)
... | tri≈ ¬a b ¬c = toℕ-inj b
... | tri< a ¬b ¬c = coequalizer-impl1-helper-≡ f g a
... | tri> ¬a ¬b c = ≡-sym (coequalizer-impl1-helper-≡ g f c)

-- The actual theorem.

coequalizer-impl-≗ : ∀ {m n} (f g : Fin m → Fin n) →
               proj₂ (coequalizer-impl f g) ∘ f ≗ proj₂ (coequalizer-impl f g) ∘ g
coequalizer-impl-≗ {zero} _ _ ()
coequalizer-impl-≗ {suc m'} {n} f g x with fromℕ m' | inspect fromℕ m' | compare x (fromℕ m')
coequalizer-impl-≗ {suc m'} f g x | .(inject l) | i[ fromℕ-m'=inj-l ] | greater .x l = 
  let l<x = bounded l
      x<=m' = ≤-pred (bounded x)
      m'=l = subst₂ _≡_ (to-from m') (inject-lemma l) (≡-cong toℕ fromℕ-m'=inj-l)
      x<=l = subst (λ t → toℕ x ≤ t) m'=l x<=m'
  in ⊥-elim (1+n≰n {toℕ l} (≤-trans l<x x<=l))
coequalizer-impl-≗ {suc m'} f g .mm | mm | _ | equal .mm = 
  coequalizer-impl1-≗ 
    (proj₂ (coequalizer-impl (λ x' → f (inject₁ x')) (λ x' → g (inject₁ x'))) (f mm)) 
    (proj₂ (coequalizer-impl (λ x' → f (inject₁ x')) (λ x' → g (inject₁ x'))) (g mm))
coequalizer-impl-≗ {suc m'} f g .(inject least) | mm | _ | less .mm least
  rewrite ≡-sym (inject₁∘inject! least) 
        | coequalizer-impl-≗ {m'} (f ∘ inject₁) (g ∘ inject₁) (inject! least)
  = ≡-refl

----------------------------------------------------------------------------------------------------
-- Here we prove that coequalizer-impl has a right inverse.

-- Right inverse of a coequalizer-impl1-helper.

coequalizer-impl1-helper-rinv : ∀ {n} (f g : Fin (suc n)) (f<g : toℕ f < toℕ g) → 
                           Σ (Fin n → Fin (suc n))
                             λ e' → (coequalizer-impl1-helper f g f<g) ∘ e' ≗ Function.id
coequalizer-impl1-helper-rinv {n} f g f<g = e' , rinv
  where
    e' : Fin n → Fin (suc n)
    e' x with (toℕ g) ≤? (toℕ x)
    ... | yes _ = suc x
    ... | no  _ = inject₁ x

    rinv-g≤x : (x : Fin n) → toℕ g ≤ toℕ x → (coequalizer-impl1-helper f g f<g) (e' x) ≡ x
    rinv-g≤x x g≤x with (toℕ g) ≤? (toℕ x)
    ... | no  g>x = ⊥-elim (g>x g≤x)
    ... | yes _ with cmp (suc (toℕ x)) (toℕ g)
    ... | tri≈ ¬a b ¬c = ⊥-elim (¬c (s≤s g≤x))
    ... | tri< a ¬b ¬c = ⊥-elim (¬c (s≤s g≤x))
    ... | tri> ¬a ¬b c = toℕ-inj (toℕ-fromℕ≤ _)

    rinv-g>x : (x : Fin n) → toℕ g ≰ toℕ x → (coequalizer-impl1-helper f g f<g) (e' x) ≡ x
    rinv-g>x x g>x with (toℕ g) ≤? (toℕ x)
    ... | yes g≤x = ⊥-elim (g>x g≤x)
    ... | no  _ with cmp (toℕ (inject₁ x)) (toℕ g)
    ... | tri≈ ¬a b ¬c = ⊥-elim (subst (λ t → suc t ≤ toℕ g → ⊥) (inject₁-lemma x) ¬a (≰⇒> g>x))
    ... | tri> ¬a ¬b c = ⊥-elim (subst (λ t → suc t ≤ toℕ g → ⊥) (inject₁-lemma x) ¬a (≰⇒> g>x))
    ... | tri< a ¬b ¬c = toℕ-inj (
      begin
        toℕ (fromℕ≤ (≤-trans a (≤-pred (bounded g))))
      ≡⟨ toℕ-fromℕ≤ _ ⟩
        toℕ (inject₁ x)
      ≡⟨ inject₁-lemma x ⟩
        toℕ x
      ∎)
      where
        open Relation.Binary.PropositionalEquality.≡-Reasoning

    rinv : (coequalizer-impl1-helper f g f<g) ∘ e' ≗ Function.id
    rinv x = case (toℕ g) ≤? (toℕ x) of λ {
        (yes g≤x) → rinv-g≤x x g≤x;
        (no  g>x) → rinv-g>x x g>x
      }


-- Right inverse of a coequalizer-impl1.

coequalizer-impl1-rinv : ∀ {n} (f g : Fin n) → 
                   Σ (Fin (proj₁ (coequalizer-impl1 f g)) → Fin n) 
                     λ e' → (proj₂ (coequalizer-impl1 f g)) ∘ e' ≗ Function.id
coequalizer-impl1-rinv {zero} () ()
coequalizer-impl1-rinv {suc n} f g with cmp (toℕ f) (toℕ g)
... | tri≈ ¬a b ¬c = id , (λ x → ≡-refl)
... | tri< a ¬b ¬c = coequalizer-impl1-helper-rinv f g a
... | tri> ¬a ¬b c = coequalizer-impl1-helper-rinv g f c


-- Right inverse of a coequalizer-impl.
-- We need it to prove the uniqueness.

coequalizer-impl-rinv : ∀ {m n} (f g : Fin m → Fin n) → 
                   Σ (Fin (proj₁ (coequalizer-impl f g)) → Fin n) 
                     λ e' → (proj₂ (coequalizer-impl f g)) ∘ e' ≗ id
coequalizer-impl-rinv {0} {n} f g = id , (λ x → ≡-refl)
coequalizer-impl-rinv {suc m'} {n} f g 
  with coequalizer-impl {m'} (f ∘ inject₁) (g ∘ inject₁)
     | coequalizer-impl1 (proj₂ (coequalizer-impl {m'} (f ∘ inject₁) (g ∘ inject₁)) (f (fromℕ m'))) 
                    (proj₂ (coequalizer-impl {m'} (f ∘ inject₁) (g ∘ inject₁)) (g (fromℕ m')))
     | coequalizer-impl-rinv {m'} (f ∘ inject₁) (g ∘ inject₁)
     | coequalizer-impl1-rinv (proj₂ (coequalizer-impl {m'} (f ∘ inject₁) (g ∘ inject₁)) (f (fromℕ m'))) 
                         (proj₂ (coequalizer-impl {m'} (f ∘ inject₁) (g ∘ inject₁)) (g (fromℕ m')))
... | k' , q | k , r | q' , q'-rinv | r' , r'-rinv = 
  q' ∘ r' , (λ x →
    begin
      r (q (q' (r' x)))
    ≡⟨ ≡-cong r (q'-rinv (r' x)) ⟩
      r (r' x)
    ≡⟨ r'-rinv x ⟩
      x
    ∎)
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

----------------------------------------------------------------------------------------------------
-- Here we prove that coequalizer-impl is universal.
-- We start with the existence part of universality.

coequalizer-impl1-helper-universal-∃ : ∀ {a b n} {C : Setoid a b} (f g : Fin (suc n)) (f<g : toℕ f < toℕ g) 
                          (d : Fin (suc n) → Setoid.Carrier C) →
                          d f ⟨ Setoid._≈_ C ⟩ d g → 
                          Σ (Fin n → Setoid.Carrier C) 
                            λ h → ∀ x → h (coequalizer-impl1-helper f g f<g x) ⟨ Setoid._≈_ C ⟩ d x
coequalizer-impl1-helper-universal-∃ {n = n} {C = C} f g f<g d d-eq = 
  h , he=d
  where
    h : Fin n → Setoid.Carrier C
    h x with (toℕ g) ≤? (toℕ x)
    ... | yes _ = d (suc x)
    ... | no  _ = d (inject₁ x)
    
    he=d≈ : ∀ x → toℕ x ≡ toℕ g → h (fromℕ≤ (≤-trans f<g (≤-pred (bounded g)))) ⟨ Setoid._≈_ C ⟩ d x
    he=d≈ x x=g with toℕ g ≤? toℕ (fromℕ≤ (≤-trans f<g (≤-pred (bounded g))))
    ... | yes g≤f rewrite toℕ-fromℕ≤ (≤-trans f<g (≤-pred (bounded g))) = ⊥-elim (1+n≰n (≤-trans f<g g≤f))
    ... | no    _ rewrite toℕ-fromℕ≤ (≤-trans f<g (≤-pred (bounded g))) =
      Setoid.trans C d-stuff=d-g (Setoid.reflexive C (≡-cong d (≡-sym (toℕ-inj x=g))))
      where
        d-stuff=d-g = 
          Setoid.trans C
            (Setoid.reflexive C (≡-cong d (toℕ-inj ( 
              begin
                toℕ (inject₁ (fromℕ≤ (≤-trans f<g (≤-pred (bounded g)))))
              ≡⟨ inject₁-lemma _ ⟩
                toℕ (fromℕ≤ (≤-trans f<g (≤-pred (bounded g))))
              ≡⟨ toℕ-fromℕ≤ _ ⟩
                toℕ f
              ∎))))
            d-eq
          where
            open Relation.Binary.PropositionalEquality.≡-Reasoning

    he=d< : ∀ x → (x<g : toℕ x < toℕ g) → h (fromℕ≤ (≤-trans x<g (≤-pred (bounded g)))) ⟨ Setoid._≈_ C ⟩ d x
    he=d< x x<g with toℕ g ≤? toℕ (fromℕ≤ (≤-trans x<g (≤-pred (bounded g))))
    ... | yes g≤x rewrite toℕ-fromℕ≤ (≤-trans x<g (≤-pred (bounded g))) = ⊥-elim (1+n≰n (≤-trans x<g g≤x))
    ... | no    _ rewrite toℕ-fromℕ≤ (≤-trans x<g (≤-pred (bounded g))) = 
      Setoid.reflexive C (≡-cong d (toℕ-inj (
        begin
          toℕ (inject₁ (fromℕ≤ (≤-trans x<g (≤-pred (bounded g)))))
        ≡⟨ inject₁-lemma _ ⟩
          toℕ (fromℕ≤ (≤-trans x<g (≤-pred (bounded g))))
        ≡⟨ toℕ-fromℕ≤ _ ⟩
          toℕ x
        ∎)))
      where
        open Relation.Binary.PropositionalEquality.≡-Reasoning

    he=d : ∀ x → h (coequalizer-impl1-helper f g f<g x) ⟨ Setoid._≈_ C ⟩ d x
    he=d x with cmp (toℕ x) (toℕ g)
    ... | tri≈ ¬a b ¬c = he=d≈ x b
    ... | tri< a ¬b ¬c = he=d< x a
    he=d zero | tri> ¬a ¬b ()
    he=d (suc x) | tri> ¬a ¬b c with toℕ g ≤? toℕ (fromℕ≤ (bounded x))
    ... | no  g≰x rewrite toℕ-fromℕ≤ (bounded x) = ⊥-elim (g≰x (≤-pred c))
    ... | yes g≤x = 
      Setoid.reflexive C (≡-cong d (toℕ-inj (
        begin
          suc (toℕ (fromℕ≤ (bounded x)))
        ≡⟨ ≡-cong suc (toℕ-fromℕ≤ _) ⟩
          suc (toℕ x)
        ∎)))
      where
        open Relation.Binary.PropositionalEquality.≡-Reasoning

-------------

coequalizer-impl1-universal-∃ : ∀ {a b n} {C : Setoid a b} (f g : Fin n) (d : Fin n → Setoid.Carrier C) →
                           d f ⟨ Setoid._≈_ C ⟩ d g → 
                           Σ (Fin (proj₁ (coequalizer-impl1 f g)) → Setoid.Carrier C) 
                             λ h → ∀ x → h (proj₂ (coequalizer-impl1 f g) x) ⟨ Setoid._≈_ C ⟩ d x
coequalizer-impl1-universal-∃ {n = zero} () () d d-eq
coequalizer-impl1-universal-∃ {n = suc n} {C = C} f g d d-eq with cmp (toℕ f) (toℕ g)
... | tri≈ ¬a b ¬c = d , (λ x → Setoid.refl C)
... | tri< a ¬b ¬c = coequalizer-impl1-helper-universal-∃ {C = C} f g a d d-eq
... | tri> ¬a ¬b c = coequalizer-impl1-helper-universal-∃ {C = C} g f c d (Setoid.sym C d-eq)

-- The existence of a morphism which in composition with a coequalizer-impl
-- produces the given morphism similar to the coequalizer-impl.

coequalizer-impl-universal-∃ : ∀ {a b m n} {C : Setoid a b} (f g : Fin m → Fin n) (d : Fin n → Setoid.Carrier C) →
                          (∀ x → d (f x) ⟨ Setoid._≈_ C ⟩ d (g x)) → 
                          Σ (Fin (proj₁ (coequalizer-impl f g)) → Setoid.Carrier C) 
                            λ h → ∀ x → h (proj₂ (coequalizer-impl f g) x) ⟨ Setoid._≈_ C ⟩ d x
coequalizer-impl-universal-∃ {m = zero} {n = n} {C = C} f g d d-eq = d , (λ x → Setoid.refl C)
coequalizer-impl-universal-∃ {m = suc m'} {n = n} {C = C} f g d d-eq 
  with coequalizer-impl {m'} (f ∘ inject₁) (g ∘ inject₁)
     | coequalizer-impl1 (q (f (fromℕ m'))) (q (g (fromℕ m')))
     | coequalizer-impl-universal-∃ {m = m'} {C = C} (f ∘ inject₁) (g ∘ inject₁) d (d-eq ∘ inject₁)
     | coequalizer-impl1-universal-∃ {C = C} 
         (q (f (fromℕ m'))) (q (g (fromℕ m'))) h
         hqf=hqg
  where
    open Setoid C renaming (_≈_ to _∼_)
    open Relation.Binary.EqReasoning C
    q = proj₂ (coequalizer-impl {m'} (f ∘ inject₁) (g ∘ inject₁))
    h = proj₁ (coequalizer-impl-universal-∃ {m = m'} {C = C} (f ∘ inject₁) (g ∘ inject₁) d (d-eq ∘ inject₁))
    he=d = proj₂ (coequalizer-impl-universal-∃ {m = m'} {C = C} (f ∘ inject₁) (g ∘ inject₁) d (d-eq ∘ inject₁))
    hqf=hqg : (h (q (f (fromℕ m')))) ∼ (h (q (g (fromℕ m'))))
    hqf=hqg = begin
                (h (q (f (fromℕ m'))))
              ≈⟨ he=d _ ⟩
                d (f (fromℕ m'))
              ≈⟨ d-eq _ ⟩
                d (g (fromℕ m'))
              ≈⟨ sym (he=d _) ⟩
                (h (q (g (fromℕ m'))))
              ∎
... | _ , e | _ , e1 | h , he=d | h1 , h1e1=h = 
  h1 , (λ x → trans (h1e1=h (e x)) (he=d x))
  where
    open Setoid C

----------------------------------------------------------------------------------------------------
-- Now we prove the uniqueness. To do this we use the right inverse.

-- We prove that every morphism with certain properties
-- is equal to the composition d ∘ e' where e' is the right
-- inverse of the coequalizer-impl.

coequalizer-impl-universal-! : ∀ {a b m n} {C : Setoid a b} (f g : Fin m → Fin n) (d : Fin n → Setoid.Carrier C) →
                          (∀ x → d (f x) ⟨ Setoid._≈_ C ⟩ d (g x)) → 
                          (h : Fin (proj₁ (coequalizer-impl f g)) → Setoid.Carrier C) →
                          (∀ x → h (proj₂ (coequalizer-impl f g) x) ⟨ Setoid._≈_ C ⟩ d x) →
                          (∀ x → h x ⟨ Setoid._≈_ C ⟩ (d ∘ proj₁ (coequalizer-impl-rinv f g)) x)
coequalizer-impl-universal-! {C = C} f g d df=dg h he=d x = 
  begin
    h x
  ≡⟨ ≡-cong h (≡-sym (proj₂ (coequalizer-impl-rinv f g) x)) ⟩
    h ((proj₂ (coequalizer-impl f g)) ((proj₁ (coequalizer-impl-rinv f g)) x))
  ≈⟨ he=d _ ⟩
    d ((proj₁ (coequalizer-impl-rinv f g)) x)
  ∎
  where
    open Relation.Binary.EqReasoning C

----------------------------------------------------------------------------------------------------

-- Assemble everything together

coequalizer : ∀ {s t} {m n} (f : Fin m → Fin n) (g : Fin m → Fin n) → 
              ∃ λ k → Σ (Fin n → Fin k) λ e → Coequalizer {s} {t} f g e
coequalizer f g = 
  k , e , coequalizer-impl-≗ f g , 
  (λ S e2 x → 
    proj₁ (coequalizer-impl-universal-∃ {C = S} f g e2 x) , 
    proj₂ (coequalizer-impl-universal-∃ {C = S} f g e2 x) , 
    (λ {y} x' x0 → Setoid.trans S 
                     (coequalizer-impl-universal-! {C = S} f g e2 x
                       (proj₁ (coequalizer-impl-universal-∃ {C = S} f g e2 x))
                       (proj₂ (coequalizer-impl-universal-∃ {C = S} f g e2 x)) x0) 
                     (Setoid.sym S (coequalizer-impl-universal-! {C = S} f g e2 x y x' x0))))
  where
    k = proj₁ (coequalizer-impl f g)
    e = proj₂ (coequalizer-impl f g)