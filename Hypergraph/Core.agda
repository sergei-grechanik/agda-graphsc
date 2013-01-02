
open import Util

module Hypergraph.Core (symbol : Symbol) (semantics : Semantics) where

open import Function
open import Function.Inverse
open import Function.Equality
open import Relation.Binary
open import Data.Product hiding (map)
open import Data.Sum
open import Data.List hiding (any)
open import Data.List.All hiding (map)
open import Data.List.All.Properties
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Data.List.Any.Properties using () renaming (++↔ to ++↔-any)
import Algebra

open Symbol symbol using () renaming (Carrier to Symb)

open import Relation.Binary.PropositionalEquality using (_≡_; subst) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open Data.List.Any.Membership-≡ 

open Semantics semantics


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


Hypergraph : Set
Hypergraph = List Hyperedge

nodes : Hypergraph → List Symb
nodes [] = []
nodes (h ∷ hs) = edge-nodes h ++ nodes hs

∈-nodes-lemma : {g : Hypergraph} → All (λ s → Any (λ h → s ∈ edge-nodes h) g) (nodes g)
∈-nodes-lemma {[]} = []
∈-nodes-lemma {h ∷ hs} with ∈-nodes-lemma {hs}
... | hs-good = 
  Inverse.to ++↔ ⟨$⟩ (
    tabulate (λ x' → here x') , 
    tabulate (λ x' → there (lookup hs-good x')))

∈-nodes-lemma-inv : {g : Hypergraph} → {s : Symb} → Any (λ h → s ∈ edge-nodes h) g → s ∈ nodes g
∈-nodes-lemma-inv {[]} ()
∈-nodes-lemma-inv {h ∷ hs} (here s∈h) = Inverse.to ++↔-any ⟨$⟩ inj₁ s∈h
∈-nodes-lemma-inv {h ∷ hs} (there s∈hs) = Inverse.to (++↔-any {xs = edge-nodes h}) ⟨$⟩ inj₂ s∈hs-nodes
  where
    s∈hs-nodes = ∈-nodes-lemma-inv s∈hs


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

edge-nodes-⊆ : {g : Hypergraph} → {h : Hyperedge} → h ∈ g → edge-nodes h ⊆ nodes g
edge-nodes-⊆ h∈g s∈h = ∈-nodes-lemma-inv (lose h∈g s∈h)

edges-with-∈ : (g : Hypergraph) → List (∃ λ h → edge-nodes h ⊆ nodes g)
edges-with-∈ g = map-with-∈ g (λ {h} h∈g → h , (λ {_} → edge-nodes-⊆ h∈g))

nodes-++ : {g1 g2 : Hypergraph} → nodes (g1 ++ g2) ≡ nodes g1 ++ nodes g2
nodes-++ {[]} = ≡-refl
nodes-++ {x ∷ xs} {g2} = 
  ≡-trans 
    (≡-cong (_++_ (edge-nodes x)) (nodes-++ {xs} {g2})) 
    (≡-sym (assoc (edge-nodes x) (nodes xs) (nodes g2)))
  where
    open Algebra.Monoid (Data.List.monoid Symb)

∈-nodes-++ : {g1 g2 : Hypergraph} → {s : Symb} → s ∈ nodes (g1 ++ g2) → s ∈ (nodes g1 ++ nodes g2)
∈-nodes-++ {g1} {g2} {s} s∈g1g2 =
  subst (_∈_ s) (nodes-++ {g1} {g2}) s∈g1g2

∈-nodes-++-inv : {g1 g2 : Hypergraph} → {s : Symb} → s ∈ (nodes g1 ++ nodes g2) → s ∈ nodes (g1 ++ g2)
∈-nodes-++-inv {g1} {g2} {s} s∈g1g2 =
  subst (_∈_ s) (≡-sym (nodes-++ {g1} {g2})) s∈g1g2