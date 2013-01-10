
open import Util

module Hypergraph.Core (symbol : Symbol) (semantics : Semantics) where

open import ListUtil

open import Function
open import Function.Inverse
open import Function.Equality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum
open import Data.List hiding (any)
open import Data.List.All hiding (map)
open import Data.List.All.Properties
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Data.List.Any.Properties using () renaming (++↔ to ++↔-any)
import Algebra

open Symbol symbol using (≡-decidable) renaming (Carrier to Symb)

open import Relation.Binary.PropositionalEquality using (_≡_; subst) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open Data.List.Any.Membership-≡ 

open Semantics semantics


-- A hyperedge is a source, label and a list of dests.

data Hyperedge : Set where
  _▷_▷_ : Symb → Label → List Symb → Hyperedge

source : Hyperedge → Symb
source (s ▷ l ▷ ds) = s

dests : Hyperedge → List Symb
dests (s ▷ l ▷ ds) = ds

label : Hyperedge → Label
label (s ▷ l ▷ ds) = l

edge-nodes : Hyperedge → List Symb
edge-nodes (source ▷ _ ▷ dests) = source ∷ dests

-- ≡ is decidable for hyperedges

hyperedge2tuple : Hyperedge → Symb × Label × List Symb
hyperedge2tuple h = source h , label h , dests h

hyperedge2tuple-inj : ∀ {h1 h2} → hyperedge2tuple h1 ≡ hyperedge2tuple h2 → h1 ≡ h2
hyperedge2tuple-inj {y ▷ y' ▷ y0} {.y ▷ .y' ▷ .y0} ≡-refl = ≡-refl

hyperedge-≡-decidable : Decidable (_≡_ {A = Hyperedge})
hyperedge-≡-decidable = 
  make-≟ hyperedge2tuple hyperedge2tuple-inj 
         (≡-decidable ×-≟ (label-≡-decidable ×-≟ []-≟ ≡-decidable))

-- A hypergraph is a list of hyperedges.

Hypergraph : Set
Hypergraph = List Hyperedge

-- If we want a node to be present in the hypergraph
-- then we should have at least one hyperedge containing it.
-- Even s = s will do.

nodes : Hypergraph → List Symb
nodes [] = []
nodes (h ∷ hs) = edge-nodes h ++ nodes hs

-- For each symbol in a graph there is a hyperedge containing it.

∈-nodes-lemma : {g : Hypergraph} → All (λ s → Any (λ h → s ∈ edge-nodes h) g) (nodes g)
∈-nodes-lemma {[]} = []
∈-nodes-lemma {h ∷ hs} with ∈-nodes-lemma {hs}
... | hs-good = 
  Inverse.to ++↔ ⟨$⟩ (
    tabulate (λ x' → here x') , 
    tabulate (λ x' → there (lookup hs-good x')))

-- If there is a hyperedge containing a symbol then the symbol is in the graph.

∈-nodes-lemma-inv : {g : Hypergraph} → {s : Symb} → Any (λ h → s ∈ edge-nodes h) g → s ∈ nodes g
∈-nodes-lemma-inv {[]} ()
∈-nodes-lemma-inv {h ∷ hs} (here s∈h) = Inverse.to ++↔-any ⟨$⟩ inj₁ s∈h
∈-nodes-lemma-inv {h ∷ hs} (there s∈hs) = Inverse.to (++↔-any {xs = edge-nodes h}) ⟨$⟩ inj₂ s∈hs-nodes
  where
    s∈hs-nodes = ∈-nodes-lemma-inv s∈hs

-- If a graph is a subgraph of another graph then 
-- the set of its nodes is a subset of the set of the nodes of this another graph.

nodes-⊆ : {g1 g2 : Hypergraph} → g1 ⊆ g2 → nodes g1 ⊆ nodes g2
nodes-⊆ {g1} {g2} sub s∈g1 with ∈-nodes-lemma {g1}
... | all-ok with find s∈g1
... | (s' , s'∈g1 , s≈s') = any-map (λ s'≈z → ≡-trans s≈s' s'≈z) (weaker s'∈g1)
  where
    f : ∀ {s} → Any (λ h → s ∈ edge-nodes h) g1 → Any (λ h → s ∈ edge-nodes h) g2
    f in-g1 with find in-g1
    ... | (h , h∈g1 , s∈h) = lose (sub h∈g1) s∈h

    weaker : {x : Symb} → x ∈ nodes g1 → x ∈ nodes g2
    weaker {x} x∈g1 = ∈-nodes-lemma-inv {g2} (f (lookup all-ok x∈g1))

-- If a graph contains a hyperedge then it contains all its nodes.

edge-nodes-⊆ : {g : Hypergraph} → {h : Hyperedge} → h ∈ g → edge-nodes h ⊆ nodes g
edge-nodes-⊆ h∈g s∈h = ∈-nodes-lemma-inv (lose h∈g s∈h)

-- We can represent a hypergraph as a list of hyperedges with witnesses of
-- their nodes being contained by the hypergraph.

edges-with-∈ : (g : Hypergraph) → List (∃ λ h → edge-nodes h ⊆ nodes g)
edges-with-∈ g = map-with-∈ g (λ {h} h∈g → h , (λ {_} → edge-nodes-⊆ h∈g))

-- If we glue two graphs then we may do the same to their nodes.
-- This statement is too strong, a set equality would do as well.

nodes-++ : {g1 g2 : Hypergraph} → nodes (g1 ++ g2) ≡ nodes g1 ++ nodes g2
nodes-++ {[]} = ≡-refl
nodes-++ {x ∷ xs} {g2} = 
  ≡-trans 
    (≡-cong (_++_ (edge-nodes x)) (nodes-++ {xs} {g2})) 
    (≡-sym (assoc (edge-nodes x) (nodes xs) (nodes g2)))
  where
    open Algebra.Monoid (Data.List.monoid Symb)

-- The previous lemma instantiated for special cases.

∈-nodes-++ : {g1 g2 : Hypergraph} → {s : Symb} → s ∈ nodes (g1 ++ g2) → s ∈ (nodes g1 ++ nodes g2)
∈-nodes-++ {g1} {g2} {s} s∈g1g2 =
  subst (_∈_ s) (nodes-++ {g1} {g2}) s∈g1g2

∈-nodes-++-inv : {g1 g2 : Hypergraph} → {s : Symb} → s ∈ (nodes g1 ++ nodes g2) → s ∈ nodes (g1 ++ g2)
∈-nodes-++-inv {g1} {g2} {s} s∈g1g2 =
  subst (_∈_ s) (≡-sym (nodes-++ {g1} {g2})) s∈g1g2


----------------------------------------------------------------------------------------------------

⊆-++ : {g1 g2 : Hypergraph} → g1 ⊆ (g1 ++ g2)
⊆-++ x∈g1 = ++→-any x∈g1

⊆-++₂ : {g1 g2 : Hypergraph} → g2 ⊆ (g1 ++ g2)
⊆-++₂ {g1} {g2} x∈g2 = ++→-any₂ {xs = g1} {ys = g2} x∈g2

----------------------------------------------------------------------------------------------------

-- Hypergraph subtraction.

_−_ : (g1 g2 : Hypergraph) → Hypergraph
[] − g2 = []
(h ∷ hs) − g2 with any (hyperedge-≡-decidable h) g2
... | yes h∈g2 = hs − g2
... | no _ = h ∷ hs − g2

−-∈ : {g1 g2 : Hypergraph} → {h : Hyperedge} →
      h ∈ g1 → ¬ (h ∈ g2) → h ∈ (g1 − g2)
−-∈ {[]} () ¬h∈g2
−-∈ {x ∷ xs} {g2} {h} (there pxs) ¬h∈g2 with any (hyperedge-≡-decidable x) g2
... | yes h∈g2 = −-∈ pxs ¬h∈g2
... | no _ = there (−-∈ pxs ¬h∈g2)
−-∈ {.h ∷ xs} {g2} {h} (here ≡-refl) ¬h∈g2 with any (hyperedge-≡-decidable h) g2
... | yes h∈g2 = ⊥-elim (¬h∈g2 h∈g2)
... | no _ = here ≡-refl

−-∈-inv : {g1 g2 : Hypergraph} → {h : Hyperedge} →
          h ∈ (g1 − g2) → h ∈ g1 × ¬ (h ∈ g2)
−-∈-inv {[]} ()
−-∈-inv {x ∷ xs} {g2} {h} h∈g1−g2 with any (hyperedge-≡-decidable x) g2
... | yes x∈g2 = Data.Product.map there Function.id (−-∈-inv h∈g1−g2)
−-∈-inv {.h ∷ xs} {g2} {h} (here ≡-refl) | no x∉g2 = here ≡-refl , x∉g2
−-∈-inv {x ∷ xs} {g2} {h} (there pxs) | no x∉g2 = 
  Data.Product.map there Function.id (−-∈-inv pxs)

-- And its connection to ++ and ⊆.

−-++-⊆ : {g1 g2 : Hypergraph} →
         g1 ⊆ (g2 ++ (g1 − g2))
−-++-⊆ {g1} {g2} {x = x} x∈g1 with any (hyperedge-≡-decidable x) g2
... | (yes x∈g2) = ⊆-++ x∈g2
... | (no ¬x∈g2) = ⊆-++₂ {g2} {g1 − g2} (−-∈ x∈g1 ¬x∈g2)

−-++-⊆-inv : {g1 g2 : Hypergraph} →
             g2 ⊆ g1 →
             (g2 ++ (g1 − g2)) ⊆ g1
−-++-⊆-inv {g1} {g2} g2⊆g1 h∈++ with Inverse.from (++↔-any {xs = g2} {ys = g1 − g2}) ⟨$⟩ h∈++
... | inj₂ h∈g1−g2 = proj₁ (−-∈-inv h∈g1−g2)
... | inj₁ h∈g2 = g2⊆g1 h∈g2

----------------------------------------------------------------------------------------------------

-- Useful to prove inclusion of one set of symbols into another.

auto-⊆ : {l1 l2 : List Symb} → {_ : True (⊆-decidable ≡-decidable l1 l2)} → l1 ⊆ l2
auto-⊆ {l1} {l2} {t} = toWitness t

auto-∈ : {l : List Symb} → {x : Symb} → {_ : True (∈-decidable ≡-decidable x l)} → x ∈ l
auto-∈ {l} {x} {t} = toWitness t