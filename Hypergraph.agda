
import Relation.Binary.PropositionalEquality
open import Function
open import Data.Empty
open import Util
open import Data.Nat
import Level
open import Relation.Binary
open import Data.Product hiding (map)
open import Data.List
import Data.List.Any
open import Data.List.All hiding (map)
open import Data.Maybe using (Maybe; just; nothing)

module Hypergraph (symbol : Symbol) (Label : Set)
                  (domain : Setoid Level.zero Level.zero) 
                  (⟦_⟧L_ : Label → List (Setoid.Carrier domain) → Maybe (Setoid.Carrier domain)) where

Symb : Set
Symb = Symbol.Carrier symbol

SymbSetoid : Setoid Level.zero Level.zero
SymbSetoid = Symbol.setoid symbol

open Data.List.Any.Membership SymbSetoid using (_⊆_;_∈_)
open Setoid domain

Sig : Set
Sig = List Symb

Node : Sig → Set
Node sig = ∃ (λ s → s ∈ sig)

node2node : {sig1 sig2 : Sig} → sig1 ⊆ sig2 → Node sig1 → Node sig2
node2node sub (s , s∈sig1) = s , sub s∈sig1

record Hyperedge (sig : Sig) : Set where
  field
    source : Node sig
    dests : List (Node sig)
    label : Label

  nodes : List (Node sig)
  nodes = source ∷ dests

  extsig : {sig' : Sig} → sig ⊆ sig' → Hyperedge sig'
  extsig sub = 
    record {
      source = node2node sub source;
      dests = map (node2node sub) dests;
      label = label
    }

record Hypergraph (sig : Sig) : Set₁ where
  field
    hyperedges : List (Hyperedge sig)

  nodes : List (Node sig)
  nodes = concatMap Hyperedge.nodes hyperedges

  extsig : {sig' : Sig} → sig ⊆ sig' → Hypergraph sig'
  extsig sub = record { hyperedges = map (λ h → Hyperedge.extsig h sub) hyperedges }


record Interpretation (sig : Sig) : Set₁ where
  open Data.List.Any.Membership SymbSetoid
  field
    ⟦_⟧ : Node sig → Setoid.Carrier domain

_⊨-h_ : {sig : Sig} → Interpretation sig → Hyperedge sig → Set
_⊨-h_ i h with ⟦ label ⟧L (Data.List.map ⟦_⟧ dests)
  where
    open Interpretation i
    open Hyperedge h
... | nothing = ⊥
... | (just v) = ⟦ source ⟧ ≈ v
  where
    open Interpretation i
    open Hyperedge h


open Interpretation

data _⊨_ {sig : Sig} (i : Interpretation sig) (g : Hypergraph sig) : Set where
  yes : All (_⊨-h_ i) (Hypergraph.hyperedges g) → i ⊨ g

data _Extends_ {sig sig' : Sig} (i' : Interpretation sig') (i : Interpretation sig) : Set where
  yes : (sub : sig ⊆ sig') → ((n : Node sig) → ⟦_⟧ i n ≈ ⟦_⟧ i' (node2node sub n)) → i' Extends i

Extends-refl : {sig : Sig} → Reflexive (_Extends_ {sig} {sig})
Extends-refl {sig} {i} = yes sub f
  where
    sub : sig ⊆ sig
    sub = λ z → z
    f : (n : Node sig) → ⟦_⟧ i n ≈ ⟦_⟧ i (node2node sub n)
    f (proj₁ , proj₂) = refl

_⇛_ : {sig1 sig2 : Sig} → Hypergraph sig1 → Hypergraph sig2 → Set₁
_⇛_ {sig1} {sig2} g1 g2 = (i : Interpretation sig1) → i ⊨ g1 → ∃ (λ i' → (i' Extends i) × (i' ⊨ g2))

_⇚_ : {sig1 sig2 : Sig} → Hypergraph sig1 → Hypergraph sig2 → Set₁
_⇚_ {sig1} {sig2} g1 g2 = (i : Interpretation sig2) → i ⊨ g2 → ∃ (λ i' → (i Extends i') × (i' ⊨ g1))

_⇚⇛_ : {sig1 sig2 : Sig} → Hypergraph sig1 → Hypergraph sig2 → Set₁
_⇚⇛_ g1 g2 = (g1 ⇛ g2) × (g1 ⇚ g2)

{-
extsig-⇚⇛ : {sig1 sig2 : Sig} → {sub : sig1 ⊆ sig2} → {g : Hypergraph sig1} → 
            g ⇚⇛ Hypergraph.extsig g sub
extsig-⇚⇛ {sig1} {sig2} {sub} {g} = 
  (λ i x → {!!} , {!!}) , 
  {!!}
-}

open Data.List.Any.Membership-≡ using (_∼[_]_;set;subset;superset)

superset→⇛ : {sig  : Sig} → {g1 g2 : Hypergraph sig} →
            (Hypergraph.hyperedges g2 ∼[ subset ] Hypergraph.hyperedges g1) →
            g1 ⇛ g2
superset→⇛ {sig} {g1} {g2} sup i (yes allh1) = 
  i , Extends-refl , yes (anti-mono sup allh1)
  where
    open import Data.List.All.Properties

subset→⇚ : {sig  : Sig} → {g1 g2 : Hypergraph sig} →
            (Hypergraph.hyperedges g1 ∼[ subset ] Hypergraph.hyperedges g2) →
            g1 ⇚ g2
subset→⇚ {sig} {g1} {g2} sub i (yes allh2) = 
  i , (Extends-refl , yes (anti-mono sub allh2))
  where
    open import Data.List.All.Properties


shuffle→⇚⇛ : {sig  : Sig} → {g1 g2 : Hypergraph sig} →
             (Hypergraph.hyperedges g1 ∼[ set ] Hypergraph.hyperedges g2) →
             g1 ⇚⇛ g2
shuffle→⇚⇛ {sig} {g1} {g2} equ = 
  (superset→⇛ g2⊆g1) , (subset→⇚ g1⊆g2)
  where
    open import Function.Equivalence
    open import Function.Equality
    open Data.List.Any.Membership-≡
    g1⊆g2 : (Hypergraph.hyperedges g1 ∼[ subset ] Hypergraph.hyperedges g2)
    g1⊆g2 z∈g1 = Equivalence.to equ ⟨$⟩ z∈g1
    g2⊆g1 : (Hypergraph.hyperedges g2 ∼[ subset ] Hypergraph.hyperedges g1)
    g2⊆g1 z∈g2 = Equivalence.from equ ⟨$⟩ z∈g2
