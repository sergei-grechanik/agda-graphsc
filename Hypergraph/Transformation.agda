
open import Util

module Hypergraph.Transformation (semantics : Semantics) where

open import ListUtil

open import Function
open import Function.Equality hiding (_∘_; id)
open import Function.Inverse hiding (_∘_; map; id; zip)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Algebra.Structures
import Relation.Binary.EqReasoning
import Data.Empty
open import Data.Nat renaming (compare to compareℕ; pred to predℕ)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _<_) renaming (_+_ to _+'_)
open import Data.Fin.Dec
open import Data.Fin.Props hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Product hiding (map; zip)
open import Data.Maybe using (Maybe; just; nothing; Eq) renaming (setoid to eq-setoid)
open import Data.Sum hiding (map) renaming ([_,_] to [_,_]-sum)
open import Data.List hiding (any)
open import Data.List.Properties using (map-id)
open import Data.List.All hiding (map)
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Relation.Binary.List.Pointwise using ([]; _∷_; Rel≡⇒≡; ≡⇒Rel≡) renaming (Rel to RelList)
open import Data.List.Any.Properties using (map↔) renaming (++↔ to ++↔-any)

open import Relation.Binary.PropositionalEquality using (_≡_; inspect; subst; cong₂) renaming 
  (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans)
open Data.List.Any.Membership-≡ 

open Semantics semantics
open Setoid domain using (_≈_)
  renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans; refl to ≈-refl) 

import Hypergraph.Core
import Hypergraph.Interpretation
open Hypergraph.Core semantics
open Hypergraph.Interpretation semantics

import Hypergraph.FinSymb
open Hypergraph.FinSymb semantics

open StrictTotalOrder Data.Nat.Properties.strictTotalOrder using () renaming (compare to cmp)
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)
open IsDistributiveLattice isDistributiveLattice using () renaming (∧-comm to ⊔-comm)

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
        


bad : ∀ {a} {A : Set a} {n : ℕ} {l : Fin n} → _≡_ {A = Fin (suc n)} (suc l) (zero) → A
bad ()

unsuc : ∀ {m} → {x y : Fin m} → _≡_ {A = Fin (suc m)} (suc x) (suc y) → _≡_ {A = Fin m} x y
unsuc ≡-refl = ≡-refl

----------------------------------------------------------------------------------------------------

GraphEq : Set₁
GraphEq = ∀ {S1 S2} → (Hypergraph S1) → (S1 → S2) → (Hypergraph S2) → Set

GlueList : Set
GlueList = List (ℕ × ℕ)

Transformation : GraphEq → Set
Transformation _~[_]_ = 
  ∀ {n1} → (G1 : Hypergraph (Fin n1)) → List (∃₂ λ n2 f → Σ (Hypergraph (Fin n2)) λ G2  → G1 ~[ f ] G2 )


fin-n1 : (g1 : Hypergraph ℕ) (l : GlueList) → ℕ
fin-n1 g1 l = suc (foldr _⊔_ 0 (nodes _ g1) ⊔ foldr _⊔_ 0 (map proj₁ l))

fin-n2 : (g2 : Hypergraph ℕ) (l : GlueList) → ℕ
fin-n2 g2 l = suc (foldr _⊔_ 0 (nodes _ g2) ⊔ foldr _⊔_ 0 (map proj₂ l))

fin-g1 : (g1 : Hypergraph ℕ) (l : GlueList) → Hypergraph (Fin (fin-n1 g1 l))
fin-g1 g1 l = map-with-∈ g1 mkfin
  where
  mkfin : {h : Hyperedge ℕ} → h ∈ g1 → Hyperedge (Fin (fin-n1 g1 l))
  mkfin {h} h∈g1 = 
    fromℕ≤ (s≤s (≤-trans (m≤max (edge-nodes-⊆ _ h∈g1 (here ≡-refl))) (m≤m⊔n _ _))) ▷ 
    label _ h ▷ 
    map-with-∈ (dests _ h) (λ {d} d∈ds → fromℕ≤ (s≤s (≤-trans (m≤max (edge-nodes-⊆ _ h∈g1 (there d∈ds))) (m≤m⊔n _ _))))

fin-g2 : (g2 : Hypergraph ℕ) (l : GlueList) → Hypergraph (Fin (fin-n2 g2 l))
fin-g2 g2 l = map-with-∈ g2 mkfin
  where
  mkfin : {h : Hyperedge ℕ} → h ∈ g2 → Hyperedge (Fin (fin-n2 g2 l))
  mkfin {h} h∈g2 = 
    fromℕ≤ (s≤s (≤-trans (m≤max (edge-nodes-⊆ _ h∈g2 (here ≡-refl))) (m≤m⊔n _ _))) ▷ 
    label _ h ▷ 
    map-with-∈ (dests _ h) (λ {d} d∈ds → fromℕ≤ (s≤s (≤-trans (m≤max (edge-nodes-⊆ _ h∈g2 (there d∈ds))) (m≤m⊔n _ _))))


fin-fun : (g1 g2 : Hypergraph ℕ) (l : GlueList) → Fin (fin-n1 g1 l) → Fin (fin-n2 g2 l)
fin-fun g1 g2 l = fun (map-with-∈ l λ {p} p∈l → p , p∈l)
  where
    open ≤-Reasoning
    fun : List (∃ λ p → p ∈ l) → Fin (fin-n1 g1 l) → Fin (fin-n2 g2 l)
    fun [] n = zero
    fun (((m , k) , p∈l) ∷ l') n with toℕ n ≟ m
    ... | yes _ = fromℕ≤ (s≤s (
      begin 
        k 
      ≤⟨ m≤max {l = map proj₂ l} {m = k} (Inverse.to (map↔ {f = proj₂}) ⟨$⟩ any-map (≡-cong proj₂) p∈l) ⟩
        foldr _⊔_ 0 (map proj₂ l)
      ≤⟨ m≤m⊔n _ _ ⟩
        foldr _⊔_ 0 (map proj₂ l) ⊔ foldr _⊔_ 0 (nodes _ g2)
      ≡⟨ ⊔-comm (foldr _⊔_ 0 (map proj₂ l)) (foldr _⊔_ 0 (nodes _ g2)) ⟩ 
        foldr _⊔_ 0 (nodes _ g2) ⊔ foldr _⊔_ 0 (map proj₂ l) 
      ∎))
    ... | no  _ = fun l' n


hmap-⊆-lemma : ∀ {S1 S2 S S'} {f : S1 → S} {g : S2 → S} {f' : S1 → S'} {g' : S2 → S'} {g1 g2} → 
               (∀ {x : S1} {y : S2} → f x ≡ g y → f' x ≡ g' y) → 
               hmap f g1 ⊆ hmap g g2 → hmap f' g1 ⊆ hmap g' g2
hmap-⊆-lemma {S1} {S2} {S} {S'} {f} {g} {f'} {g'} {g1} {g2} prop fg1⊆gg2 h∈f'g1
  with find (Inverse.from map↔ ⟨$⟩ h∈f'g1)
... | x , x∈g1 , ≡-refl with find (fg1⊆gg2 (Inverse.to map↔ ⟨$⟩ lose x∈g1 ≡-refl))
... | .(edge-map f x) , fx∈gg2 , ≡-refl with find (Inverse.from map↔ ⟨$⟩ fx∈gg2)
... | y , y∈g2 , fx=gy = Inverse.to map↔ ⟨$⟩ lose y∈g2 f'x=g'y
  where
    prop-list : {l1 : List S1} {l2 : List S2} → map f l1 ⟨ RelList _≡_ ⟩ map g l2 → map f' l1 ⟨ RelList _≡_ ⟩ map g' l2
    prop-list {[]} {[]} [] = []
    prop-list {x' ∷ xs} {[]} ()
    prop-list {[]} {x' ∷ xs} ()
    prop-list {x' ∷ xs} {x0 ∷ xs'} (x∼y ∷ xs∼ys) = prop x∼y ∷ prop-list xs∼ys

    f'x=g'y : edge-map f' x ≡ edge-map g' y
    f'x=g'y rewrite ≡-cong (label _) fx=gy =
      cong₂ (λ s d → s ▷ label _ y ▷ d) 
        (prop (≡-cong (source _) fx=gy)) 
        (Rel≡⇒≡ (prop-list (≡⇒Rel≡ (≡-cong (dests _) fx=gy))))

hmap-id : ∀ {S} {g : Hypergraph S} → hmap id g ≡ g
hmap-id {g = []} = ≡-refl
hmap-id {S} {(s ▷ l ▷ d) ∷ hs} rewrite map-id d = cong₂ _∷_ ≡-refl (hmap-id {g = hs})


consistent : ∀ {m n} (f g : Fin m → Fin (suc n)) → (k : Fin m) → Dec (f k ≡ g k ⊎ f k ≡ zero ⊎ g k ≡ zero)
consistent f g k with Data.Fin.Props._≟_ (f k) (g k)
... | yes fk=gk = yes (inj₁ fk=gk)
... | no fk≠gk with Data.Fin.Props._≟_ (f k) zero
... | yes fk=0 = yes (inj₂ (inj₁ fk=0))
... | no fk≠0 with Data.Fin.Props._≟_ (g k) zero
... | yes gk=0 = yes (inj₂ (inj₂ gk=0))
... | no gk≠0 = 
  no (λ {
    (inj₁ fk=gk) → fk≠gk fk=gk; 
    (inj₂ (inj₁ fk=0)) → fk≠0 fk=0; 
    (inj₂ (inj₂ gk=0)) → gk≠0 gk=0})


combine : ∀ {m n} (f g : Fin m → Fin (suc n)) → 
          Maybe (Σ (Fin m → Fin (suc n)) λ h → 
            (∀ {k l} → f k ≡ suc l → h k ≡ suc l) ×
            (∀ {k l} → g k ≡ suc l → h k ≡ suc l))
combine {m} {n} f g with all? (consistent f g)
... | no  _ = nothing
... | yes c = just (proj₁ ∘ fun , 
                   (λ {k} {l} → proj₁ (proj₂ (fun k)) l) , 
                   (λ {k} {l} → proj₂ (proj₂ (fun k)) l))
  where
    fun : (k : Fin m) → Σ (Fin (suc n)) λ i → 
             (∀ l → f k ≡ suc l → i ≡ suc l) × 
             (∀ l → g k ≡ suc l → i ≡ suc l)
    fun k with c k
    fun k | inj₁ x = f k , (λ l p → p) , (λ l p → ≡-trans x p)
    fun k | inj₂ (inj₁ x) = g k , (λ l x' → bad (≡-trans (≡-sym x') x)) , (λ l p → p)
    fun k | inj₂ (inj₂ y) = f k , (λ l p → p) , (λ l x → bad (≡-trans (≡-sym x) y))


find-subgraphs' : ∀ {m n} (g : Hypergraph (Fin m)) (G : Hypergraph (Fin n)) → 
                 List (Σ (Fin m → Fin (suc n)) λ f → hmap f g ⊆ hmap suc G)
find-subgraphs' [] G = [ (λ _ → zero) , (λ {x} → λ ()) ]
find-subgraphs' {m} {n} (h ∷ g) G = 
  concatMap (λ p1 → concatMap (λ p2 → comb p1 p2) (find-subgraphs' g G)) (find-subedge h)
  where
    comb : (∃ λ f → hmap f [ h ] ⊆ hmap suc G) → (∃ λ f → hmap f g ⊆ hmap suc G) → List (∃ λ f → hmap f (h ∷ g) ⊆ hmap suc G)
    comb (f1 , f1h⊆G) (f2 , f2g⊆G) with combine f1 f2
    ... | nothing = []
    ... | just (f , ok1 , ok2) = [ f , (λ {x} → f-good {x}) ]
      where
        f-good : hmap f (h ∷ g) ⊆ hmap suc G
        f-good (here p) = hmap-⊆-lemma {g1 = [ h ]} {g2 = G} ok1 f1h⊆G (here p)
        f-good (there pxs) = hmap-⊆-lemma ok2 f2g⊆G pxs

    fun : List (Fin m) → List (Fin (suc n)) → Fin m → Fin (suc n)
    fun l1 l2 k with filter (λ p → ⌊ Data.Fin.Props._≟_ k (proj₁ p) ⌋) (zip l1 l2)
    ... | [] = zero
    ... | (_ , v) ∷ _ = v

    find-subedge : (h : Hyperedge (Fin m)) → List (Σ (Fin m → Fin (suc n)) λ f → hmap f [ h ] ⊆ hmap suc G)
    find-subedge h = gfilter check (map-with-∈ (hmap suc G) (λ {x} x∈ → x , x∈))
      where
        check : Σ (Hyperedge (Fin (suc n))) (λ x → x ∈ hmap suc G) → 
                Maybe (Σ (Fin m → Fin (suc n)) λ f → hmap f [ h ] ⊆ hmap suc G)
        check (x , x∈G) 
          with hyperedge-≡-decidable (edge-map (fun (edge-nodes _ h) (edge-nodes _ x)) h) x
        ... | no  _ = nothing
        ... | yes fh=x = 
          just (fun (edge-nodes _ h) (edge-nodes _ x) , good)
          where
            good : hmap (fun (edge-nodes _ h) (edge-nodes _ x)) [ h ] ⊆ hmap suc G
            good (here ≡-refl) = subst (λ x' → x' ∈ _) (≡-sym fh=x) x∈G
            good (there ())

fin-fun-sequence : ∀ {m n} → (f : Fin m → List (Fin n)) → List (Σ (Fin m → Fin n) λ h → ∀ k → h k ∈ f k)
fin-fun-sequence {zero} f = [ (λ ()), (λ ()) ]
fin-fun-sequence {suc m} {n} f = concatMap mk-funs (fin-fun-sequence (f ∘ suc))
  where
    mk-funs : Σ (Fin m → Fin n) (λ g → ∀ k → g k ∈ f (suc k)) → 
              List (Σ (Fin (suc m) → Fin n) λ h → ∀ k → h k ∈ f k)
    mk-funs (g , g-ok) = map-with-∈ (f zero) (λ {f0} f0∈ → (proj₁ ∘ mk-fun f0 f0∈) , (proj₂ ∘ mk-fun f0 f0∈))
      where
        mk-fun : (f0 : Fin n) → f0 ∈ f zero → (k : Fin (suc m)) → (Σ (Fin n) λ v → v ∈ f k)
        mk-fun f0 f0∈ zero = f0 , f0∈
        mk-fun f0 f0∈ (suc k) = g k , g-ok k

find-subgraphs : ∀ {m n} (g : Hypergraph (Fin m)) (G : Hypergraph (Fin n)) → 
                 List (∃ λ f → hmap f g ⊆ G)
find-subgraphs {m} {n} g G = 
  subst (λ t → List (∃ λ f → hmap f g ⊆ t)) hmap-id (concatMap spec (find-subgraphs' g G))
  where
    all-ns : ∀ n → List (Fin n)
    all-ns zero = []
    all-ns (suc n) = zero ∷ (map suc (all-ns n))

    -- replace zeroes with every possible symbol
    spec : Σ (Fin m → Fin (suc n)) (λ f → hmap f g ⊆ hmap suc G) → List (∃ λ f → hmap f g ⊆ hmap id G)
    spec (f , fg⊆sG) = 
      map (λ {(f' , f'-ok) → f' , (λ {x} x∈f'g → hmap-⊆-lemma (prop f'-ok) fg⊆sG x∈f'g)}) 
          (fin-fun-sequence listfun)
      where
        listfun : Fin m → List (Fin n)
        listfun k with f k
        ... | zero = all-ns n
        ... | suc v = [ v ]

        prop : ∀ {f' : Fin m → Fin n} → (∀ k → f' k ∈ listfun k) → {x : Fin m} {y : Fin n} → f x ≡ suc y → f' x ≡ y
        prop f'-ok {x} {y} fx=sy with f x | f'-ok x
        ... | zero | _ = bad (≡-sym fx=sy)
        ... | suc v | there ()
        ... | suc v | here px = ≡-trans px (unsuc fx=sy)

simpleTrans-⇄ : (g1 g2 : Hypergraph ℕ) (l : GlueList) →
                (fin-g1 g1 l ⇄[ fin-fun g1 g2 l ] fin-g2 g2 l) → Transformation _⇄[_]_
simpleTrans-⇄ g1 g2 l g1-g2 G1 = map transf (find-subgraphs (fin-g1 g1 l) G1)
  where
    transf : (∃ λ f → hmap f (fin-g1 g1 l) ⊆ G1) → ∃₂ λ n2 f → Σ (Hypergraph (Fin n2)) λ G2  → G1 ⇄[ f ] G2
    transf (f , fg1⊆G1) = _ , _ , transform-⇄ g1-g2 f fg1⊆G1

