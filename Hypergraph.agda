
open import Util

module Hypergraph (symbol : Symbol) (semantics : Semantics) where

open import Function
open import Function.Inverse
open import Function.Equivalence
open import Function.Equality
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Core using (yes; no)
open import Data.Empty
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum
open import Data.Maybe using (Maybe; just; nothing; Eq) renaming (setoid to eq-setoid)
open import Data.List hiding (any)
open import Data.List.All hiding (map)
open import Data.List.All.Properties
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Data.List.Any.Properties using () renaming (++↔ to ++↔-any)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to RelList)

open Symbol symbol using (fresh) renaming (Carrier to Symb)

open import Relation.Binary.PropositionalEquality using (trans) renaming (setoid to ≡-setoid; refl to ≡-refl)
open Data.List.Any.Membership-≡ 

open Semantics semantics
open Setoid domain using (_≈_; refl) renaming (Carrier to Dom) 

Sig : Set
Sig = List Symb


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
... | (s' , s'∈g1 , s≈s') = any-map (λ s'≈z → trans s≈s' s'≈z) (weaker s'∈g1)
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




record Interpretation (sig : Sig) : Set where
  field
    int : (s : Symb) → (s ∈ sig) → Dom
    unambiguity : {s : Symb} → {w1 w2 : s ∈ sig} → int s w1 ≈ int s w2

_⟦_,_⟧ : {sig : Sig} → Interpretation sig → (s : Symb) → s ∈ sig → Dom
_⟦_,_⟧ i s s-ok = Interpretation.int i s s-ok

unambiguity : {sig : Sig} → (i : Interpretation sig) → {s : Symb} → {w1 w2 : s ∈ sig} → i ⟦ s , w1 ⟧ ≈ i ⟦ s , w2 ⟧
unambiguity {sig} i {s} {w1} {w2} = Interpretation.unambiguity i {s} {w1} {w2}

intlist : {sig : Sig} → Interpretation sig → (lst : List Symb) → lst ⊆ sig → List Dom
intlist i lst lst⊆sig = map-with-∈ lst (λ {x} x∈lst → i ⟦ x , (lst⊆sig x∈lst) ⟧)

intedge : {sig : Sig} → Interpretation sig → (h : Hyperedge) → source h ∈ sig → dests h ⊆ sig → Set
intedge i h srcok dstok = 
  Eq (Setoid._≈_ domain) (just (i ⟦ source h , srcok ⟧)) (⟦ label h ⟧L (intlist i (dests h) dstok))

data _⊨[_] {sig : Sig} (i : Interpretation sig) (h : Hyperedge) : Set where
  yes : (srcok : source h ∈ sig) → (dstok : dests h ⊆ sig) → intedge i h srcok dstok → i ⊨[ h ]


modelled : (g : Hypergraph) → (i : Interpretation (nodes g)) → Set
modelled g i = All (_⊨[_] i) g

syntax modelled g i = i ⊨ g



_≍_ : {sig sig' : Sig} → (i : Interpretation sig) → (i' : Interpretation sig') → Set
_≍_ {sig} {sig'} i i' = (n : Symb) → {nok : n ∈ sig} → {nok' : n ∈ sig'} → i ⟦ n , nok ⟧ ≈ i' ⟦ n , nok' ⟧

≍-refl : {sig : Sig} → Reflexive (_≍_ {sig} {sig})
≍-refl {sig} {i} n = unambiguity i

≍-intedge : {sig sig' : Sig} → {i : Interpretation sig} → {i' : Interpretation sig'} → i ≍ i' →
            {h : Hyperedge} → {srcok : source h ∈ sig} → {dsok : dests h ⊆ sig} → 
            {srcok' : source h ∈ sig'} → {dsok' : dests h ⊆ sig'} → 
            intedge i h srcok dsok → intedge i' h srcok' dsok'
≍-intedge {sig} {sig'} {i} {i'} i≍i' {src ▷ l ▷ ds} {srcok} {dsok} {srcok'} {dsok'} agrees =
  eq-trans (eq-trans (eq-sym intseq) agrees) edgeseq
  where
    open Setoid (eq-setoid domain) using () renaming (sym to eq-sym; trans to eq-trans)

    intseq : Eq _≈_ (just (i ⟦ src , srcok ⟧)) (just (i' ⟦ src , srcok' ⟧))
    intseq = just (i≍i' src)

    listeq : {ds : List Symb} → {dsok : ds ⊆ sig} → {dsok' : ds ⊆ sig'} → 
             RelList _≈_ (intlist i ds dsok) (intlist i' ds dsok')
    listeq {[]} = []
    listeq {x ∷ xs} = (i≍i' x) ∷ listeq
    
    edgeseq : Eq _≈_ (⟦ l ⟧L intlist i ds dsok) (⟦ l ⟧L intlist i' ds dsok')
    edgeseq = respect listeq



≍-⊨ : {sig sig' : Sig} → {i : Interpretation sig} → {i' : Interpretation sig'} → i ≍ i' → 
      {h : Hyperedge} → (edge-nodes h ⊆ sig') → i ⊨[ h ] → i' ⊨[ h ]
≍-⊨ {sig} {sig'} {i} {i'} i≍i' {src ▷ l ▷ ds} h⊆sig' (yes srcok dstok y) = 
  yes (h⊆sig' (here ≡-refl)) (λ d∈ds → h⊆sig' (there d∈ds)) 
      (≍-intedge {i = i} {i' = i'} i≍i' {src ▷ l ▷ ds} y)

restrict : {sig sig' : Sig} → sig' ⊆ sig → Interpretation sig → Interpretation sig'
restrict sub i =
  record {
    int = λ s sok → i ⟦ s , sub sok ⟧;
    unambiguity = unambiguity i
  }

restrict-≍ : {sig sig' : Sig} → {sub : sig' ⊆ sig} → (i : Interpretation sig) → i ≍ (restrict sub i)
restrict-≍ i n = unambiguity i

_⇛_ : Hypergraph → Hypergraph → Set
_⇛_ g1 g2 = (i : Interpretation (nodes g1)) → i ⊨ g1 → Σ (Interpretation (nodes g2)) (λ i' → i ≍ i' × (i' ⊨ g2))

_⇄_ : Hypergraph → Hypergraph → Set
_⇄_ g1 g2 = (g1 ⇛ g2) × (g2 ⇛ g1) × nodes g1 ⊆ nodes g2



superset→⇛ : {g1 g2 : Hypergraph} →
             (g2 ⊆ g1) →
             g1 ⇛ g2
superset→⇛ {g1} {g2} sup i i⊨g1 = 
  newi ,  
  are-≍  , 
  tabulate f
  where
    newi : Interpretation (nodes g2)
    newi = restrict (nodes-⊆ sup) i
    are-≍ : i ≍ newi
    are-≍ = restrict-≍ i
    f : {h : Hyperedge} → h ∈ g2 → restrict (nodes-⊆ sup) i ⊨[ h ]
    f h∈g2 = ≍-⊨ are-≍ (edge-nodes-⊆ h∈g2) (lookup i⊨g1 (sup h∈g2))

shuffle→⇄ : {g1 g2 : Hypergraph} →
             (g1 ∼[ set ] g2) →
             g1 ⇄ g2
shuffle→⇄ {g1} {g2} equ = 
  (superset→⇛ g2⊆g1) , (superset→⇛ g1⊆g2) , nodes-⊆ g1⊆g2
  where
    open import Function.Equivalence
    open import Function.Equality
    open Data.List.Any.Membership-≡
    g1⊆g2 : (g1 ∼[ subset ] g2)
    g1⊆g2 z∈g1 = Equivalence.to equ ⟨$⟩ z∈g1
    g2⊆g1 : (g2 ∼[ subset ] g1)
    g2⊆g1 z∈g2 = Equivalence.from equ ⟨$⟩ z∈g2