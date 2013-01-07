
open import Util

module Hypergraph.Transformation (symbol : Symbol) (semantics : Semantics) where

open import Function
open import Function.Inverse hiding (_∘_; map)
open import Function.Equality hiding (_∘_)
open import Relation.Nullary
open import Relation.Binary
import Data.Empty
open import Data.Product hiding (map)
open import Data.Maybe using (Maybe; just; nothing; Eq) renaming (setoid to eq-setoid)
open import Data.Sum hiding (map) renaming ([_,_] to [_,_]-sum)
open import Data.List hiding (any)
open import Data.List.All hiding (map)
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to RelList)
open import Data.List.Any.Properties using () renaming (++↔ to ++↔-any)

open Symbol symbol using (fresh; ≡-decidable) renaming (Carrier to Symb)

open import Relation.Binary.PropositionalEquality using (trans; _≡_) renaming 
  (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym)
open Data.List.Any.Membership-≡ 

open Semantics semantics
open Setoid domain using (_≈_; refl) renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans) 


import Hypergraph.Core
import Hypergraph.Interpretation
open Hypergraph.Core symbol semantics
open Hypergraph.Interpretation symbol semantics

open import Level

-- Finite binary relations. 
-- I hadn't found them in stdlib, so I had to implement them myself.

FinRel : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
FinRel A B = List (A × B)

⟪_⟫ : ∀ {a b} {A : Set a} {B : Set b} → FinRel A B → A → B → Set (a ⊔ b)
⟪ f ⟫ x y = (x , y) ∈ f

functional : ∀ {a b} {A : Set a} {B : Set b} → FinRel A B → Set (a ⊔ b)
functional {A = A} {B = B} table = 
  (key : A) → (p1 p2 : A × B) → p1 ∈ table → p2 ∈ table → proj₂ p1 ≡ proj₂ p2

keys : ∀ {a b} {A : Set a} {B : Set b} → 
       FinRel A B → List A
keys table = Data.List.map proj₁ table

values : ∀ {a b} {A : Set a} {B : Set b} → 
         FinRel A B → List B
values table = Data.List.map proj₂ table

-- f has x means that there is y such that f relates x to y.

_has_ : ∀ {a b} {A : Set a} {B : Set b} → 
        FinRel A B → A → Set (a ⊔ b)
f has x = ∃ λ y → ⟪ f ⟫ x y

-- actually "f has x" is the same thing as x ∈ keys f

has→∈keys : ∀ {a b} {A : Set a} {B : Set b} {f : FinRel A B} {x : A} →
            f has x → x ∈ keys f
has→∈keys (y , here px) rewrite (≡-sym px) = here ≡-refl
has→∈keys (y , there pxs) with has→∈keys (y , pxs)
... | ∈keys-xs = there ∈keys-xs

-- If ≡ for A is decidable then _has_ is decidable.

has-decidable : ∀ {a b} {A : Set a} {B : Set b} → 
                Decidable (_≡_ {A = A}) → Decidable {A = FinRel A B} {B = A} _has_
has-decidable {B = B} dec [] x = no fun
  where
    fun : Σ B (λ y → Any (_≡_ (x , y)) []) → Data.Empty.⊥
    fun (_ , ())
has-decidable {B = B} dec ((x , y) ∷ ps) x' with dec x x'
... | yes x≡x' rewrite x≡x' =  yes (y , here ≡-refl)
... | no x≢x' with has-decidable dec ps x'
... | yes (y' , ps-x'-y') = yes (y' , there ps-x'-y')
... | no ¬ps-has-x' = no fun
  where
    fun : Σ B (λ y' → Any (_≡_ (x' , y')) ((x , y) ∷ ps)) → Data.Empty.⊥
    fun (y' , here px) rewrite px = x≢x' (≡-cong proj₁ (≡-sym px))
    fun (y' , there pxs) = ¬ps-has-x' (y' , pxs)

-- Given key ∈ keys, returns a corresponding value.
-- (One of them, there may be multiple corresponding to the same key)

at' : ∀ {a b} {A : Set a} {B : Set b} → 
     (table : FinRel A B) → {key : A} → (key ∈ keys table) → B
at' [] ()
at' (x ∷ xs) (here px) = proj₂ x
at' (x ∷ xs) (there pxs) = at' xs pxs

-- Finds a corresponding value given the decidability of ≡.

at : ∀ {a b} {A : Set a} {B : Set b} → Decidable (_≡_ {A = A}) →
     (table : FinRel A B) → A → Maybe B
at dec table x with has-decidable dec table x
... | yes (y , _) = just y
... | no _ = nothing




-- Apply a renaming θ to the nodes of g.

rename : (g : Hypergraph) → (θ : FinRel Symb Symb) → nodes g ⊆ keys θ → Hypergraph
rename g θ n⊆k = map edge-ren (edges-with-∈ g)
  where
    edge-ren : (∃ λ h → edge-nodes h ⊆ nodes g) → Hyperedge
    edge-ren (src ▷ l ▷ ds , h⊆g) = 
      at' θ (n⊆k (h⊆g (here ≡-refl))) ▷ l ▷ map-with-∈ ds (λ ∈ds → at' θ (n⊆k (h⊆g (there ∈ds))))


-- This function takes a list of symbols and creates a renaming which maps
-- each symbol from the list into a corresponding symbol from θ or
-- into a fresh symbols (not from forbidden).

extend-θ : (forbidden : List Symb) → (θ : FinRel Symb Symb) → List Symb → FinRel Symb Symb
extend-θ forbidden θ [] = θ
extend-θ forbidden θ (s ∷ ss) with has-decidable ≡-decidable θ s
... | yes _ = extend-θ forbidden θ ss
... | no  _ = 
  let newsymb = proj₁ (fresh forbidden)
  in extend-θ (newsymb ∷ forbidden) ((s , newsymb) ∷ θ) ss

-- θ is a subrelation of its extension.

θ⊆extend-θ : {forb : List Symb} → {θ : FinRel Symb Symb} → {list : List Symb} → 
             θ ⊆ extend-θ forb θ list
θ⊆extend-θ {forb} {θ} {[]} z = z
θ⊆extend-θ {forb} {θ} {s ∷ ss} ∈θ with has-decidable ≡-decidable θ s
... | yes θ-has-s = θ⊆extend-θ {forb} {θ} {ss} ∈θ
... | no ¬θ-has-s = θ⊆extend-θ {list = ss} (there ∈θ)

-- The relation produced by extend-θ contains all symbols from list.

extend-θ-⊆keys : {forbidden : List Symb} → {θ : FinRel Symb Symb} → {list : List Symb} →
                 list ⊆ keys (extend-θ forbidden θ list)
extend-θ-⊆keys {forbidden} {θ} {[]} ()
extend-θ-⊆keys {forbidden} {θ} {s ∷ ss} (here px) 
  rewrite px
  with has-decidable ≡-decidable θ s
... | yes (y , sy∈θ) = has→∈keys (y , θ⊆extend-θ {list = ss} sy∈θ)
... | no _ = has→∈keys (proj₁ (fresh forbidden) , θ⊆extend-θ {list = ss} (here ≡-refl))
extend-θ-⊆keys {forbidden} {θ} {s ∷ ss} (there pxs)
  with has-decidable ≡-decidable θ s
... | yes _ = extend-θ-⊆keys {list = ss} pxs
... | no  _ = extend-θ-⊆keys {list = ss} pxs

-- Rename each node of a graph by either using the renaming θ or
-- creating a fresh symbol.

rename-or-fresh : (forbidden : List Symb) → (θ : FinRel Symb Symb) → 
                  Hypergraph → Hypergraph
rename-or-fresh forbidden θ g = 
  rename g newθ g⊆new
  where
    newθ = extend-θ forbidden θ (nodes g)
    g⊆new : nodes g ⊆ keys newθ
    g⊆new ∈g = extend-θ-⊆keys ∈g

-- The effect of renaming on ⇛.

rename-⇛ : {g1 g2 : Hypergraph} → {θ : FinRel Symb Symb} → {forbidden : List Symb} →
           (g1⊆θ : nodes g1 ⊆ keys θ) → nodes (rename g1 θ g1⊆θ) ⊆ forbidden →
           g1 ⇛ g2 → rename g1 θ g1⊆θ ⇛ rename-or-fresh forbidden θ g2
rename-⇛ {g1} {g2} {θ} {forb} g1⊆θ reng1⊆forb g1⇛g2 i i⊨reng1 = 
  {!!} , 
  {!!} , 
  {!!}

-- Replace a subgraph of g equivalent to g1 with g2.

transform : (g1 g2 g : Hypergraph) →
            (∃ λ θ → Σ (nodes g1 ⊆ keys θ) λ g1⊆θ → rename g1 θ g1⊆θ ⊆ g) →
            Hypergraph
transform g1 g2 g (θ , g1⊆θ , ren⊆g) =
  rename-or-fresh (nodes g) θ g2 ++ (g − rename g1 θ g1⊆θ)

-- 

transform-⇛ : {g1 g2 g : Hypergraph} →
              (g1-subgraph : ∃ λ θ → Σ (nodes g1 ⊆ keys θ) λ g1⊆θ → rename g1 θ g1⊆θ ⊆ g) →
              g1 ⇛ g2 → g ⇛ transform g1 g2 g g1-subgraph
transform-⇛ (θ , g1⊆θ , reng1⊆g) g1⇛g2 = {!!}

--find-subgraphs : (g g1 : Hypergraph) → List ∃ λ θ → ∃ λ g1⊆θ → rename g1 θ g1⊆θ ⊆ g
--find-subgraphs g g1
