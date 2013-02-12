
open import Graphsc.Semantics

module Graphsc.Fin.SugarTrans (semantics : Semantics) where

open import Graphsc.NatUtil

import Level
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

import Graphsc.Hypergraph
import Graphsc.Interpretation
import Graphsc.Fin.PushoutTrans
import Graphsc.Fin.Transformation
open Graphsc.Hypergraph semantics
open Graphsc.Interpretation semantics
open Graphsc.Fin.PushoutTrans semantics
open Graphsc.Fin.Transformation semantics

open StrictTotalOrder Data.Nat.Properties.strictTotalOrder using () renaming (compare to cmp)
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)
open IsDistributiveLattice isDistributiveLattice using () renaming (∧-comm to ⊔-comm)

----------------------------------------------------------------------------------------------------
-- Here we define a method of defining simple transformations.

-- This is a list of pairs. First elements are mapped to the corresponding secod elements.

GlueList : Set
GlueList = List (ℕ × ℕ)

-- For convenience we use ℕ to describe graph patterns.
-- But since we work with Fin we should transform these ℕ.

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

-- Create a gluing function from two sample graphs and a glue list.

fin-fun : (g1 g2 : Hypergraph ℕ) (l : GlueList) → Fin (fin-n1 g1 l) → Fin (fin-n2 g2 l)
fin-fun g1 g2 l = fun (map-with-∈ l λ {p} p∈l → p , p∈l)
  where
    open ≤-Reasoning
    fun : List (∃ λ p → p ∈ l) → Fin (fin-n1 g1 l) → Fin (fin-n2 g2 l)
    fun [] n = clip n
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

----------------------------------------------------------------------------------------------------

-- Build a simple fixed-pattern-based transformation.

simpleTrans-⇄ : (g1 g2 : Hypergraph ℕ) (l : GlueList) →
                (fin-g1 g1 l ⇄[ fin-fun g1 g2 l ] fin-g2 g2 l) → SimpleTrans _⇄[_]_
simpleTrans-⇄ g1 g2 l g1-g2 = _ , _ , fin-g1 g1 l , fin-g2 g2 l , fin-fun g1 g2 l , g1-g2