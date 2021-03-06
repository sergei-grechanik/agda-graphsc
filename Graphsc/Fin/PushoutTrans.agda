
open import Graphsc.Semantics

module Graphsc.Fin.PushoutTrans (semantics : Semantics) where

open import Graphsc.NatUtil

import Level
open import Function
open import Function.Inverse hiding (_∘_; map; id; sym)
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


import Graphsc.Hypergraph
import Graphsc.Interpretation
open Graphsc.Hypergraph semantics
open Graphsc.Interpretation semantics

open import Graphsc.Fin.Coequalizer
open import Graphsc.Fin.Pushout

----------------------------------------------------------------------------------------------------

-- Import some useful hypergraph functions specialized to finite sets.

private
  module Dummy {n : ℕ} where
    open Graphsc.Hypergraph.HDec semantics (Fin n) (Data.Fin.Props._≟_ {n = n}) public

open Dummy public

----------------------------------------------------------------------------------------------------

-- Pushout interacts in a nice way with ⇛.

pushout-⇛ : ∀ {m n l} {f : Fin m → Fin l} {g : Fin m → Fin n}
            {g1 : Hypergraph (Fin m)} {g2 : Hypergraph (Fin n)} →
            g1 ⇛[ g ] g2 → hmap f g1 ⇛[ g ⇈[ f ] ] hmap (f ⇉[ g ]) g2
pushout-⇛ {m} {n} {l} {f} {g} {g1} {g2} g1⇛g2 il il⊨hmapg1
  with pushout' f g
... | f'f=g'g , push-uni 
  with g1⇛g2 (il ∘ f) (⊨-hmap il⊨hmapg1) 
... | i2 , i2g=ilf , i2⊨g2 
  with push-uni domain il i2 i2g=ilf
... | ik , (ikf'=il , ikg'=i2) , ik-! = 
  ik , ≈-sym ∘ ikf'=il , ⊨-hmap-inv (≍-⊨ (≍-sym ikg'=i2) i2⊨g2)


----------------------------------------------------------------------------------------------------

-- Pushouts interact nicely with ⇚ too.

pushout-⇚ : ∀ {m n l} {f : Fin m → Fin l} {g : Fin m → Fin n}
            {g1 : Hypergraph (Fin m)} {g2 : Hypergraph (Fin n)} →
            g1 ⇚[ g ] g2 → hmap f g1 ⇚[ g ⇈[ f ] ] hmap (f ⇉[ g ]) g2
pushout-⇚ {m} {n} {l} {f} {g} {g1} {g2} g1⇚g2 ik ik⊨hmapg2
  with pushout' {Level.zero} {Level.zero} f g
... | f'f=g'g , push-uni
  with g1⇚g2 (ik ∘ (f ⇉[ g ])) (⊨-hmap ik⊨hmapg2)
... | im , im=ikg'g , im⊨g1 =
  ik ∘ (g ⇈[ f ]) , (λ s → ≈-refl) , il⊨hmapg1
  where
    ikg'g=ikf'f : ik ∘ (f ⇉[ g ]) ∘ g ≍ ik ∘ (g ⇈[ f ]) ∘ f
    ikg'g=ikf'f s = Setoid.reflexive domain (≡-cong ik (≡-sym (f'f=g'g s)))

    il⊨hmapg1 : (ik ∘ (g ⇈[ f ])) ⊨ hmap f g1
    il⊨hmapg1 = ⊨-hmap-inv (≍-⊨ ikg'g=ikf'f (≍-⊨ im=ikg'g im⊨g1))


----------------------------------------------------------------------------------------------------

-- If we have a transformation (g1 ⇛[ g ] g2) then we can use
-- it to transform a graph.

transform-⇛ : ∀ {m l n} {g1 : Hypergraph (Fin m)} {g2 : Hypergraph (Fin n)} 
              {g : Fin m → Fin n} {G1 : Hypergraph (Fin l)} →
              g1 ⇛[ g ] g2 → (f : Fin m → Fin l) → hmap f g1 ⊆ G1 → ∃ λ G2 → G1 ⇛[ g ⇈[ f ] ] G2
transform-⇛ {g1 = g1} {g2 = g2} {g = g} {G1 = G1} g1⇛g2 f g1⊆G1 = 
  G2 , ⇛-trans (⇛-id (⊨-⊆ (−-++-⊆-inv g1⊆G1))) (⇛-++ (pushout-⇛ g1⇛g2))
  where
    G2 : Hypergraph (f ⊞ g)
    G2 = hmap (f ⇉[ g ]) g2 ++ hmap (g ⇈[ f ]) (G1 − hmap f g1)

-- Note that in this direction we don't need hmapped g1 to be a subgraph of G1.

transform-⇚ : ∀ {m l n} {g1 : Hypergraph (Fin m)} {g2 : Hypergraph (Fin n)} 
              {g : Fin m → Fin n} {G1 : Hypergraph (Fin l)} →
              g1 ⇚[ g ] g2 → (f : Fin m → Fin l) → ∃ λ G2 → G1 ⇚[ g ⇈[ f ] ] G2
transform-⇚ {g1 = g1} {g2 = g2} {g = g} {G1 = G1} g1⇚g2 f = 
  G2 , ⇚-trans (⇚-id (⊨-⊆ (−-++-⊆ {g2 = hmap f g1}))) G1⇚G2-almost 
  where
    G2 : Hypergraph (f ⊞ g)
    G2 = hmap (f ⇉[ g ]) g2 ++ hmap (g ⇈[ f ]) (G1 − hmap f g1)

    G1⇚G2-almost : (hmap f g1 ++ (G1 − hmap f g1)) ⇚[ g ⇈[ f ] ] G2
    G1⇚G2-almost = ⇚-++ {g = G1 − hmap f g1} (pushout-⇚ g1⇚g2)

-- Both ways

transform-⇄ : ∀ {m l n} {g1 : Hypergraph (Fin m)} {g2 : Hypergraph (Fin n)} 
              {g : Fin m → Fin n} {G1 : Hypergraph (Fin l)} →
              g1 ⇄[ g ] g2 → (f : Fin m → Fin l) → hmap f g1 ⊆ G1 → ∃ λ G2 → G1 ⇄[ g ⇈[ f ] ] G2
transform-⇄ {g1 = g1} {g2 = g2} {g = g} {G1 = G1} g1⇄g2 f g1⊆G1 =
  hmap (f ⇉[ g ]) g2 ++ hmap (g ⇈[ f ]) (G1 − hmap f g1) ,
  proj₂ (transform-⇛ (proj₁ g1⇄g2) f g1⊆G1) ,
  proj₂ (transform-⇚ (proj₂ g1⇄g2) f)
