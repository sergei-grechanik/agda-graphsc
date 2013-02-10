
open import Graphsc.Semantics

module Graphsc.Interpretation (semantics : Semantics) where

open import Graphsc.ListUtil

open import Function
open import Function.Inverse hiding (_∘_; map; id)
open import Function.Equality hiding (_∘_; id)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Product hiding (map)
open import Data.Maybe using (Maybe; just; nothing; Eq; maybeToBool) renaming (setoid to eq-setoid)
open import Data.Bool using (T)
open import Data.Sum renaming ([_,_] to [_,_]-sum; map to _⊕_)
open import Data.List hiding (any)
open import Data.List.Properties
open import Data.List.All hiding (map)
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Relation.Binary.List.Pointwise using ([]; _∷_; Rel≡⇒≡; ≡⇒Rel≡) renaming (Rel to RelList)
open import Data.List.Any.Properties using (map↔) renaming (++↔ to ++↔-any)
open import Data.List.All.Properties using (++↔; anti-mono)
import Relation.Binary.EqReasoning

open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong₂) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans)
open Data.List.Any.Membership-≡ 

open Semantics semantics
open Setoid domain using (_≈_)
  renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans; refl to ≈-refl) 


import Graphsc.Hypergraph
open Graphsc.Hypergraph semantics


----------------------------------------------------------------------------------------------------

pointwise-map : ∀ {a b} {A : Set a} {B : Set b} {_∼_ : B → B → Set b} {f g : A → B} {l : List A} →
                ((x : A) → f x ∼ g x) → RelList _∼_ (map f l) (map g l)
pointwise-map {l = []} f∼g = []
pointwise-map {l = x ∷ xs} f∼g = f∼g x ∷ pointwise-map {l = xs} f∼g

----------------------------------------------------------------------------------------------------

edge-map : {S1 S2 : Set} → (S1 → S2) → Hyperedge S1 → Hyperedge S2
edge-map f h = f (source _ h) ▷ label _ h ▷ map f (dests _ h)

hmap : {S1 S2 : Set} → (S1 → S2) → Hypergraph S1 → Hypergraph S2
hmap f g = map (edge-map f) g

----------------------------------------------------------------------------------------------------

-- This lemma is used by the Transformation module.

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

-- If we apply id to a graph we get the same graph.

hmap-id : ∀ {S} {g : Hypergraph S} → hmap id g ≡ g
hmap-id {g = []} = ≡-refl
hmap-id {S} {(s ▷ l ▷ d) ∷ hs} rewrite map-id d = cong₂ _∷_ ≡-refl (hmap-id {g = hs})

----------------------------------------------------------------------------------------------------

-- An interpretation.

Interpretation : Set → Set
Interpretation Symb = Symb → Dom

-- i ⊨[ h ] means that i agrees with h, i.e. the interpretation
-- of the source is equal to the composition of dests' interpretations.

_⊨[_] : {S : Set} → Interpretation S → Hyperedge S → Set
i ⊨[ h ] =
  Eq (Setoid._≈_ domain) (just (i (source _ h))) (⟦ label _ h ⟧L (map i (dests _ h)))

-- An interpretation is a model of a hypergraph if it agrees with all its hyperedges.
-- Written i ⊨ g.

_⊨_ : {S : Set} → Interpretation S → Hypergraph S → Set
i ⊨ g = All (_⊨[_] i) g


-- A simple property.
-- i ⊨ hmap f g  =  (i ∘ f) ⊨ g

⊨-hmap : {S1 S2 : Set} {i : Interpretation S2} {g : Hypergraph S1} {f : S1 → S2} →
         i ⊨ hmap f g → (i ∘ f) ⊨ g
⊨-hmap {S1} {S2} {i} {[]} _ = []
⊨-hmap {S1} {S2} {i} {x ∷ xs} {f} (px ∷ pxs) = 
  subst (λ ● → Eq _≈_ (just (i (f (source _ x)))) (⟦ label _ x ⟧L ● )) 
        (≡-sym (map-compose (dests _ x))) px 
  ∷ ⊨-hmap {g = xs} pxs

⊨-hmap-inv : {S1 S2 : Set} {i : Interpretation S2} {g : Hypergraph S1} {f : S1 → S2} →
             (i ∘ f) ⊨ g → i ⊨ hmap f g
⊨-hmap-inv {S1} {S2} {i} {[]} _ = []
⊨-hmap-inv {S1} {S2} {i} {x ∷ xs} {f} (px ∷ pxs) = 
  subst (λ ● → Eq _≈_ (just (i (f (source _ x)))) (⟦ label _ x ⟧L ● )) 
        (map-compose (dests _ x)) px 
  ∷ ⊨-hmap-inv {g = xs} pxs  

-- If i models a sum of graphs then it model each element of the sum.

⊨-++₁ : {S : Set} {i : Interpretation S} {g1 g2 : Hypergraph S} →
        i ⊨ (g1 ++ g2) → i ⊨ g1
⊨-++₁ i⊨gs = proj₁ (Inverse.from ++↔ ⟨$⟩ i⊨gs)

⊨-++₂ : {S : Set} {i : Interpretation S} {g1 g2 : Hypergraph S} →
        i ⊨ (g1 ++ g2) → i ⊨ g2
⊨-++₂ {g1 = g1} {g2 = g2} i⊨gs = proj₂ (Inverse.from (++↔ {xs = g1} {ys = g2}) ⟨$⟩ i⊨gs)

-- If g1 is a subgraph of g2 then a model of g2 is also a model of g1.

⊨-⊆ : {S : Set} {i : Interpretation S} {g1 g2 : Hypergraph S} →
      g1 ⊆ g2 → i ⊨ g2 → i ⊨ g1
⊨-⊆ = anti-mono

----------------------------------------------------------------------------------------------------

-- Pointwise equality for interpretations

infix 4 _≍_

_≍_ : {S : Set} (i1 i2 : Interpretation S) → Set
_≍_ {S} i1 i2 = (s : S) → i1 s ≈ i2 s

≍-sym : {S : Set} → Symmetric (_≍_ {S = S})
≍-sym i1≗i2 s = ≈-sym (i1≗i2 s)

-- i1 ≈[ f ] i2  means that i2 is an extension of i1, i.e. i1 can be reconstructed
-- by composing i2 and f, i.e. i1 ≗ i2 ∘ f

_≈[_]_ : {S1 S2 : Set} (i1 : Interpretation S1) (f : S1 → S2) (i2 : Interpretation S2) → Set
_≈[_]_ {S1} {S2} i1 f i2 = i1 ≍ (i2 ∘ f)


-- Equivalent interpretations agree on hyperedges and hypergraphs.

≍-⊨[] : {S : Set} {i1 i2 : Interpretation S} {h : Hyperedge S} →
        i1 ≍ i2 → i1 ⊨[ h ] → i2 ⊨[ h ]
≍-⊨[] {S} {i1} {i2} {h} i1≍i2 i1⊨h = 
  begin
    just (i2 (source _ h))
  ≈⟨ just (≈-sym (i1≍i2 _)) ⟩
    just (i1 (source _ h))
  ≈⟨ i1⊨h ⟩
    ⟦ label _ h ⟧L (map i1 (dests _ h))
  ≈⟨ respect (pointwise-map i1≍i2) ⟩
    ⟦ label _ h ⟧L (map i2 (dests _ h))
  ∎
  where
    open Relation.Binary.EqReasoning (Data.Maybe.setoid domain)

≍-⊨ : {S : Set} {i1 i2 : Interpretation S} {g : Hypergraph S} →
      i1 ≍ i2 → i1 ⊨ g → i2 ⊨ g
≍-⊨ {g = []} i1≍i2 [] = []
≍-⊨ {g = h ∷ hs} i1≍i2 (ph ∷ phs) = 
  (≍-⊨[] {h = h} i1≍i2 ph) ∷ ≍-⊨ {g = hs} i1≍i2 phs

-- "Equivalent" interpretations agree on corresponding hyperedges.

≈[]-⊨[] : {S1 S2 : Set} {i1 : Interpretation S1} {f : S1 → S2} {i2 : Interpretation S2} {h : Hyperedge S1} →
          i1 ≈[ f ] i2 → i1 ⊨[ h ] → i2 ⊨[ edge-map f h ]
≈[]-⊨[] {S1} {S2} {i1} {f} {i2} {h} i1≈i2 i1⊨h = 
  begin
    just (i2 (f (source _ h)))
  ≈⟨ ≍-⊨[] {h = h} i1≈i2 i1⊨h ⟩
    ⟦ label _ h ⟧L (map (i2 ∘ f) (dests _ h))
  ≡⟨ ≡-cong ⟦ label _ h ⟧L (map-compose (dests _ h)) ⟩
    ⟦ label _ h ⟧L (map i2 (map f (dests _ h)))
  ∎
  where
    open Relation.Binary.EqReasoning (Data.Maybe.setoid domain)

-- "Equivalent" interpretations agree on corresponding hypergraphs.

≈[]-⊨ : {S1 S2 : Set} {i1 : Interpretation S1} {f : S1 → S2} {i2 : Interpretation S2} {g : Hypergraph S1} →
          i1 ≈[ f ] i2 → i1 ⊨ g → i2 ⊨ hmap f g
≈[]-⊨ i1≈i2 i1⊨g = ⊨-hmap-inv (≍-⊨ i1≈i2 i1⊨g)

----------------------------------------------------------------------------------------------------

-- g1 ⇛[ f ] g2 means that g2 is a consequence of g1, that is
-- for every interpretation of g1 there is an "equivalent" (≈[ f ])
-- interpretation of g2.

_⇛[_]_ : {S1 S2 : Set} (g1 : Hypergraph S1) (f : S1 → S2) (g2 : Hypergraph S2) → Set
_⇛[_]_ {S1} {S2} g1 f g2 = 
  (i1 : Interpretation S1) → i1 ⊨ g1 → Σ (Interpretation S2) (λ i2 → (i1 ≈[ f ] i2) × (i2 ⊨ g2))

-- g1 ⇚[ f ] g2 means that g1 is a consequence of g2, that is
-- for every interpretation of g2 there is an "equivalent" (≈[ f ])
-- interpretation of g1. This property is a bit simpler than 
-- the previous one since f and ⇚ go in opposite directions.

_⇚[_]_ : {S1 S2 : Set} (g1 : Hypergraph S1) (f : S1 → S2) (g2 : Hypergraph S2) → Set
_⇚[_]_ {S1} {S2} g1 f g2 = 
  (i2 : Interpretation S2) → i2 ⊨ g2 → Σ (Interpretation S1) (λ i1 → (i1 ≈[ f ] i2) × (i1 ⊨ g1))

-- An alternative formulation could be like this:
-- (i2 : Interpretation S2) → i2 ⊨ g2 → i2 ⊨ hmap f g1

-- g1 ⇄ g2 means that these graphs are equal on their "common" nodes 
-- and there are no nodes removed in g2 (but some nodes may be glued).
-- This is what we want from transformations: we preserve equivalence
-- and don't throw away any nodes.

_⇄[_]_ : {S1 S2 : Set} (g1 : Hypergraph S1) (f : S1 → S2) (g2 : Hypergraph S2) → Set
g1 ⇄[ f ] g2 = (g1 ⇛[ f ] g2) × (g1 ⇚[ f ] g2)

----------------------------------------------------------------------------------------------------

-- Transitivity

⇛-trans : {S1 S2 S3 : Set} {g1 : Hypergraph S1} {g2 : Hypergraph S2} {g3 : Hypergraph S3}
          {f : S1 → S2} {g : S2 → S3} → g1 ⇛[ f ] g2 → g2 ⇛[ g ] g3 → g1 ⇛[ g ∘ f ] g3
⇛-trans {f = f} g1-g2 g2-g3 i1 i1⊨g1 with g1-g2 i1 i1⊨g1
... | i2 , i1-i2 , i2⊨g2 with g2-g3 i2 i2⊨g2
... | i3 , i2-i3 , i3⊨g3 =
  i3 , (λ s → ≈-trans (i1-i2 s) (i2-i3 (f s))) , i3⊨g3

⇚-trans : {S1 S2 S3 : Set} {g1 : Hypergraph S1} {g2 : Hypergraph S2} {g3 : Hypergraph S3}
          {f : S1 → S2} {g : S2 → S3} → g1 ⇚[ f ] g2 → g2 ⇚[ g ] g3 → g1 ⇚[ g ∘ f ] g3
⇚-trans {f = f} g1-g2 g2-g3 i3 i3⊨g3 with g2-g3 i3 i3⊨g3
... | i2 , i2-i3 , i2⊨g2 with g1-g2 i2 i2⊨g2
... | i1 , i1-i2 , i1⊨g1 =
  i1 , (λ s → ≈-trans (i1-i2 s) (i2-i3 (f s))) , i1⊨g1

⇄-trans : {S1 S2 S3 : Set} {g1 : Hypergraph S1} {g2 : Hypergraph S2} {g3 : Hypergraph S3}
          {f : S1 → S2} {g : S2 → S3} → g1 ⇄[ f ] g2 → g2 ⇄[ g ] g3 → g1 ⇄[ g ∘ f ] g3
⇄-trans g1-g2 g2-g3 = ⇛-trans (proj₁ g1-g2) (proj₁ g2-g3) , ⇚-trans (proj₂ g1-g2) (proj₂ g2-g3)

----------------------------------------------------------------------------------------------------

-- These functions are meant to be used with ⊨-⊆.

⇛-id : {S : Set} {g1 : Hypergraph S} {g2 : Hypergraph S} →
       ({i : Interpretation S} → i ⊨ g1 → i ⊨ g2) → g1 ⇛[ id ] g2
⇛-id f i i⊨g1 = i , (λ s → ≈-refl) , f i⊨g1

⇚-id : {S : Set} {g1 : Hypergraph S} {g2 : Hypergraph S} →
       ({i : Interpretation S} → i ⊨ g2 → i ⊨ g1) → g1 ⇚[ id ] g2
⇚-id f i i⊨g2 = i , (λ s → ≈-refl) , f i⊨g2

⇄-id : {S : Set} {g1 : Hypergraph S} {g2 : Hypergraph S} →
       ({i : Interpretation S} → i ⊨ g1 → i ⊨ g2) → ({i : Interpretation S} → i ⊨ g2 → i ⊨ g1) → 
       g1 ⇄[ id ] g2
⇄-id f g = ⇛-id f , ⇚-id g

----------------------------------------------------------------------------------------------------

-- Subgraph replacement theorems.
-- Informally if we replace a subgraph with an equivalent one then the whole resultant graph
-- will be equivalent to the original.

⇛-++ : {S1 S2 : Set} {g : Hypergraph S1} {g1 : Hypergraph S1} {g2 : Hypergraph S2} {f : S1 → S2} →
       g1 ⇛[ f ] g2 → (g1 ++ g) ⇛[ f ] (g2 ++ hmap f g)
⇛-++ {S1} {S2} {g} {g1} {g2} {f} g1⇛g2 i1 i1⊨g1g
  with g1⇛g2 i1 (⊨-++₁ i1⊨g1g)
... | i2 , i1≈i2 , i2⊨g2 = 
  i2 , 
  i1≈i2 , 
  tabulate i2⊨g2g
  where
    i2⊨g2g : ∀ {h} → h ∈ (g2 ++ hmap f g) → i2 ⊨[ h ]
    i2⊨g2g h∈gs with Inverse.from (++↔-any {xs = g2} {ys = hmap f g} ) ⟨$⟩ h∈gs
    ... | inj₁ h∈g2 = lookup i2⊨g2 h∈g2
    ... | inj₂ h∈g' = lookup (⊨-hmap-inv (≍-⊨ i1≈i2 (⊨-++₂ {g1 = g1} {g2 = g} i1⊨g1g))) h∈g'

-- This case is symmetric to the previous.

⇚-++ : {S1 S2 : Set} {g : Hypergraph S1} {g1 : Hypergraph S1} {g2 : Hypergraph S2} {f : S1 → S2} →
       g1 ⇚[ f ] g2 → (g1 ++ g) ⇚[ f ] (g2 ++ hmap f g)
⇚-++ {S1} {S2} {g} {g1} {g2} {f} g1⇚g2 i2 i2⊨g2g
  with g1⇚g2 i2 (⊨-++₁ i2⊨g2g)
... | i1 , i1≈i2 , i1⊨g1 = 
  i1 , 
  i1≈i2 , 
  tabulate i1⊨g1g
  where
    i1⊨g1g : ∀ {h} → h ∈ (g1 ++ g) → i1 ⊨[ h ]
    i1⊨g1g h∈gs with Inverse.from (++↔-any {xs = g1} {ys = g} ) ⟨$⟩ h∈gs
    ... | inj₁ h∈g1 = lookup i1⊨g1 h∈g1
    ... | inj₂ h∈g = lookup (≍-⊨ (≍-sym i1≈i2) (⊨-hmap (⊨-++₂ {g1 = g2} {g2 = hmap f g} i2⊨g2g))) h∈g

-- And their combination.

⇄-++ : {S1 S2 : Set} {g : Hypergraph S1} {g1 : Hypergraph S1} {g2 : Hypergraph S2} {f : S1 → S2} →
      g1 ⇄[ f ] g2 → (g1 ++ g) ⇄[ f ] (g2 ++ hmap f g)
⇄-++ (g1⇛g2 , g1⇚g2) = ⇛-++ g1⇛g2 , ⇚-++ g1⇚g2

----------------------------------------------------------------------------------------------------

