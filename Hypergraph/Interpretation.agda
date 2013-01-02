
open import Util

module Hypergraph.Interpretation (symbol : Symbol) (semantics : Semantics) where

open import Function
open import Function.Inverse
open import Function.Equality
open import Relation.Binary
open import Data.Product hiding (map)
open import Data.Maybe using (Maybe; just; nothing; Eq) renaming (setoid to eq-setoid)
open import Data.Sum renaming ([_,_] to [_,_]-sum)
open import Data.List hiding (any)
open import Data.List.All hiding (map)
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to RelList)
open import Data.List.Any.Properties using () renaming (++↔ to ++↔-any)

open Symbol symbol using () renaming (Carrier to Symb)

open import Relation.Binary.PropositionalEquality using (trans; _≡_) renaming (setoid to ≡-setoid; refl to ≡-refl)
open Data.List.Any.Membership-≡ 

open Semantics semantics
open Setoid domain using (_≈_; refl) renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans) 


import Hypergraph.Core
open Hypergraph.Core symbol semantics


Sig : Set
Sig = List Symb

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

≍-sym : {sig sig' : Sig} → Sym (_≍_ {sig} {sig'}) (_≍_ {sig'} {sig})
≍-sym {sig} {sig'} f n {nok} {nok'} = ≈-sym (f n)

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
             (g2 ⊆ g1) → g1 ⇛ g2
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
            (g1 ∼[ set ] g2) → g1 ⇄ g2
shuffle→⇄ {g1} {g2} equ = 
  (superset→⇛ g2⊆g1) , (superset→⇛ g1⊆g2) , nodes-⊆ g1⊆g2
  where
    open import Function.Equivalence
    g1⊆g2 : (g1 ∼[ subset ] g2)
    g1⊆g2 z∈g1 = Equivalence.to equ ⟨$⟩ z∈g1
    g2⊆g1 : (g2 ∼[ subset ] g1)
    g2⊆g1 z∈g2 = Equivalence.from equ ⟨$⟩ z∈g2


++→-any : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
          Any P xs → Any P (xs ++ ys)
++→-any pxs = Inverse.to ++↔-any ⟨$⟩ (inj₁ pxs)

++→-any₂ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
          Any P ys → Any P (xs ++ ys)
++→-any₂ {xs = xs} {ys = ys} pxs = Inverse.to (++↔-any {xs = xs} {ys = ys}) ⟨$⟩ (inj₂ pxs)

⊆-++ : {g1 g2 : Hypergraph} → g1 ⊆ (g1 ++ g2)
⊆-++ x∈g1 = ++→-any x∈g1

⊆-++₂ : {g1 g2 : Hypergraph} → g2 ⊆ (g1 ++ g2)
⊆-++₂ {g1} {g2} x∈g2 = ++→-any₂ {xs = g1} {ys = g2} x∈g2


split-int : {g1 g2 : Hypergraph} → {i : Interpretation (nodes (g1 ++ g2))} →
            i ⊨ (g1 ++ g2) → ∃ λ i1 → ∃ λ i2 → i ≍ i1 × i ≍ i2 × (i1 ⊨ g1) × (i2 ⊨ g2)
split-int {g1} {g2} {i} i⊨g1++g2 
  with superset→⇛ (⊆-++ {g1} {g2}) i i⊨g1++g2
... | (i1 , i≍i1 , i1⊨g1)
  with superset→⇛ (⊆-++₂ {g1} {g2}) i i⊨g1++g2
... | (i2 , i≍i2 , i2⊨g2) = 
  i1 , i2 , i≍i1 , i≍i2 , i1⊨g1 , i2⊨g2

join-int : {g1 g2 : Hypergraph} → {i1 : Interpretation (nodes g1)} → {i2 : Interpretation (nodes g2)} →
           i1 ⊨ g1 → i2 ⊨ g2 → i1 ≍ i2 → ∃ λ i → i1 ≍ i × i2 ≍ i × (i ⊨ (g1 ++ g2))
join-int {g1} {g2} {i1} {i2} i1⊨g1 i2⊨g2 i1≍i2 =
  newi , 
  i1≍newi , 
  i2≍newi , 
  tabulate newi⊨gs
  where
    int : (s : Symb) → (s ∈ nodes (g1 ++ g2)) → Dom
    int s s∈gs = f (Inverse.from ++↔-any ⟨$⟩ ∈-nodes-++ {g1} {g2} s∈gs)
      where
        f : (s ∈ nodes g1) ⊎ (s ∈ nodes g2) → Dom
        f = [ _⟦_,_⟧ i1 s , _⟦_,_⟧ i2 s ]-sum

    unamb : {s : Symb} → {w1 w2 : s ∈ nodes (g1 ++ g2)} → int s w1 ≈ int s w2
    unamb {s} {w1} {w2}
      with Inverse.from (++↔-any {xs = nodes g1} {ys = nodes g2} ) ⟨$⟩ ∈-nodes-++ {g1} {g2} w1
         | Inverse.from (++↔-any {xs = nodes g1} {ys = nodes g2} ) ⟨$⟩ ∈-nodes-++ {g1} {g2} w2
    ... | (inj₁ x11) | (inj₁ x21) = unambiguity i1
    ... | (inj₁ x11) | (inj₂ x22) = i1≍i2 s
    ... | (inj₂ x12) | (inj₁ x21) = ≈-sym (i1≍i2 s)
    ... | (inj₂ x12) | (inj₂ x22) = unambiguity i2

    newi : Interpretation (nodes (g1 ++ g2))
    newi = 
      record { 
        int = int ;
        unambiguity = unamb
      }

    i1≍newi : i1 ≍ newi
    i1≍newi n {n∈g1} {n∈gs} with Inverse.from (++↔-any {xs = nodes g1} {ys = nodes g2} ) ⟨$⟩ ∈-nodes-++ {g1} {g2} n∈gs
    ... | (inj₁ _) = unambiguity i1
    ... | (inj₂ n∈g2) = i1≍i2 n

    i2≍newi : i2 ≍ newi
    i2≍newi n {n∈g2} {n∈gs} with Inverse.from (++↔-any {xs = nodes g1} {ys = nodes g2} ) ⟨$⟩ ∈-nodes-++ {g1} {g2} n∈gs
    ... | (inj₁ n∈g1) = ≈-sym (i1≍i2 n)
    ... | (inj₂ _) = unambiguity i2

    newi⊨gs : {h : Hyperedge} → h ∈ (g1 ++ g2) → newi ⊨[ h ]
    newi⊨gs {h} h∈gs with Inverse.from (++↔-any {xs = g1} {ys = g2}) ⟨$⟩ h∈gs
    ... | (inj₁ h∈g1) = ≍-⊨ i1≍newi (edge-nodes-⊆ (⊆-++ h∈g1)) (lookup i1⊨g1 h∈g1)
    ... | (inj₂ h∈g2) = ≍-⊨ i2≍newi (edge-nodes-⊆ (⊆-++₂ {g1} {g2} h∈g2)) (lookup i2⊨g2 h∈g2)

⇛-++ : {g1 g2 g : Hypergraph} → 
       ({s : Symb} → s ∈ nodes g2 → s ∈ nodes g → s ∈ nodes g1) → -- no name collisions
       g1 ⇛ g2 → (g1 ++ g) ⇛ (g2 ++ g)
⇛-++ {g1} {g2} {g} nocol g1⇛g2 i1 i1⊨g1++g with split-int i1⊨g1++g
... | (j1 , j , i1≍j1 , i1≍j , j1⊨g1 , j⊨g) with g1⇛g2 j1 j1⊨g1
... | (j2 , j1≍j2 , j2⊨g2) with join-int j2⊨g2 j⊨g j2≍j
    where
      j2≍j : j2 ≍ j
      j2≍j n {n∈g2} {n∈g} = 
        let n∈g1 = nocol n∈g2 n∈g 
            n∈g1++g = ∈-nodes-++-inv {g1 = g1} {g2 = g} (++→-any n∈g1)
        in ≈-trans (≈-sym (j1≍j2 n {n∈g1} {n∈g2})) (≈-trans (≈-sym (i1≍j1 n {n∈g1++g} {n∈g1})) (i1≍j n {n∈g1++g} {n∈g}))
... | (i2 , j2≍i2 , j≍i2 , i2⊨g2++g) =
  i2 , (i1≍i2) , i2⊨g2++g
  where
    i1≍i2 : i1 ≍ i2
    i1≍i2 n {n∈g1++g} {n∈g2++g} 
      with Inverse.from (++↔-any {xs = nodes g1} {ys = nodes g} ) ⟨$⟩ ∈-nodes-++ {g1} {g} n∈g1++g
         | Inverse.from (++↔-any {xs = nodes g2} {ys = nodes g} ) ⟨$⟩ ∈-nodes-++ {g2} {g} n∈g2++g
    ... | (inj₁ x11) | (inj₁ x21) = 
        ≈-trans (i1≍j1 n {n∈g1++g} {x11}) 
                (≈-trans (j1≍j2 n {x11} {x21}) 
                         (j2≍i2 n {x21} {n∈g2++g}))
    ... | (inj₁ x11) | (inj₂ x22) = ≈-trans (i1≍j n {n∈g1++g} {x22}) (j≍i2 n)
    ... | (inj₂ x12) | (inj₁ x21) = ≈-trans (i1≍j n {n∈g1++g} {x12}) (j≍i2 n)
    ... | (inj₂ x12) | (inj₂ x22) = ≈-trans (i1≍j n {n∈g1++g} {x12}) (j≍i2 n)
