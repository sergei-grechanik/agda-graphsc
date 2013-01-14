
open import Util

module Hypergraph.Transformation (symbol : Symbol) (semantics : Semantics) where

open import ListUtil

open import Function
open import Function.Inverse hiding (_∘_; map)
open import Function.Equality hiding (_∘_)
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.EqReasoning
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

open import Relation.Binary.PropositionalEquality using (trans; _≡_; inspect; subst) renaming 
  (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym)
open Data.List.Any.Membership-≡ 

open Semantics semantics
open Setoid domain using (_≈_; refl) renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans) 

import Hypergraph.Core
import Hypergraph.Interpretation
open Hypergraph.Core symbol semantics
open Hypergraph.Interpretation symbol semantics


-- Apply a renaming θ to the nodes of a hyperedge h.

edge-rename : (h : Hyperedge) → (θ : FinRel Symb Symb) → edge-nodes h ⊆ keys θ → Hyperedge
edge-rename h θ n⊆k =  
      at' θ (n⊆k (here ≡-refl)) ▷ label h ▷ list-at' θ (dests h) (n⊆k ∘ there)

-- Apply a renaming θ to the nodes of g.

rename : (g : Hypergraph) → (θ : FinRel Symb Symb) → nodes g ⊆ keys θ → Hypergraph
rename g θ g⊆θ = map-with-∈ g edge-ren
  where
    edge-ren : {h : Hyperedge} → h ∈ g → Hyperedge
    edge-ren {h} h∈g = edge-rename h θ (g⊆θ ∘ edge-nodes-⊆ h∈g)

-- If a symbols is in (edge-nodes h) then its image is in (edge-nodes (edge-rename h ...)).

edge-rename-nodes-lemma : 
  {h : Hyperedge} → {θ : FinRel Symb Symb} → {h⊆θ : edge-nodes h ⊆ keys θ} → {s : Symb} →
  (s∈h : s ∈ edge-nodes h) → at' θ (h⊆θ s∈h) ∈ edge-nodes (edge-rename h θ h⊆θ)
edge-rename-nodes-lemma {Hypergraph.Core._▷_▷_ src l ds} (here ≡-refl) = here ≡-refl
edge-rename-nodes-lemma {Hypergraph.Core._▷_▷_ src l ds} {θ} {h⊆θ} {s} (there pxs) = 
  there (go ds (h⊆θ ∘ there) pxs)
  where
    go : (ds' : List Symb) → (sub : ds' ⊆ keys θ) → (s∈ds' : s ∈ ds') → 
         at' θ (sub s∈ds') ∈ map-with-∈ ds' (λ ∈ds → at' θ (sub ∈ds))
    go [] sub ()
    go (.s ∷ xs) sub (here ≡-refl) = here ≡-refl
    go (x ∷ xs) sub (there pxs') = there (go xs (sub ∘ there) pxs')

-- If a hyperedge is in g then its image is in (rename g ...).

rename-edges-lemma : {g : Hypergraph} → {θ : FinRel Symb Symb} → {g⊆θ : nodes g ⊆ keys θ} → 
                     {h : Hyperedge} → (h∈g : h ∈ g) → 
                     edge-rename h θ (g⊆θ ∘ edge-nodes-⊆ h∈g) ∈ rename g θ g⊆θ
rename-edges-lemma {[]} ()
rename-edges-lemma {x ∷ xs} (here ≡-refl) = here ≡-refl
rename-edges-lemma {x ∷ xs} {θ} {g⊆θ} (there pxs) =
  there (rename-edges-lemma {xs} {θ} {g⊆θ ∘ (++→-any₂ {xs = edge-nodes x} )} pxs)

-- If a symbol is in (nodes g) then its image is in (nodes (rename g ...)).
-- We require θ to be functional because it is much more difficult
-- to prove this lemma otherwise.

rename-nodes-lemma : {g : Hypergraph} → {θ : FinRel Symb Symb} → {g⊆θ : nodes g ⊆ keys θ} → 
                     (fun : functional θ) → {s : Symb}
                     (s∈g : s ∈ nodes g) → at' θ (g⊆θ s∈g) ∈ nodes (rename g θ g⊆θ)
rename-nodes-lemma {g} {θ} {g⊆θ} fun {s} s∈g 
  with find (lookup (∈-nodes-lemma {g}) s∈g)
... | (h , h∈g , s∈h) = 
         subst (λ x → x ∈ nodes (rename g θ g⊆θ)) eq 
               (∈-nodes-lemma-inv (lose h'∈g' (edge-rename-nodes-lemma {h} {θ} {g⊆θ ∘ edge-nodes-⊆ h∈g} s∈h)))
  where
    eq : at' θ (g⊆θ (edge-nodes-⊆ h∈g s∈h)) ≡ at' θ (g⊆θ s∈g)
    eq = at'-functional fun _ _
    h'∈g' : edge-rename h θ (g⊆θ ∘ edge-nodes-⊆ h∈g) ∈ rename g θ g⊆θ
    h'∈g' = rename-edges-lemma {g} {θ} {g⊆θ} h∈g
    


----------------------------------------------------------------------------------------------------

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
           (fun : functional θ) → (g1⊆θ : nodes g1 ⊆ keys θ) → 
           nodes (rename g1 θ g1⊆θ) ⊆ forbidden → g1 ⇛ g2 → 
           rename g1 θ g1⊆θ ⇛ rename-or-fresh forbidden θ g2
rename-⇛ {g1} {g2} {θ} {forb} fun g1⊆θ reng1⊆forb g1⇛g2 i i⊨reng1 = 
  {!!} , 
  {!!} , 
  {!!}
  where
    unamb : {s : Symb} {w1 w2 : s ∈ nodes g1} → 
            (Interpretation.int i (at' θ (g1⊆θ w1)) (rename-nodes-lemma {g = g1} {g⊆θ = g1⊆θ} fun w1)) ≈
            (Interpretation.int i (at' θ (g1⊆θ w2)) (rename-nodes-lemma {g = g1} {g⊆θ = g1⊆θ} fun w2))
    unamb {s} {w1} {w2} = 
      unambiguity' i (at'-functional fun (g1⊆θ w1) (g1⊆θ w2))

    θi : Interpretation (nodes g1)
    θi = record {
           int = λ s s∈g1 → 
             Interpretation.int i (at' θ (g1⊆θ s∈g1)) 
                                  (rename-nodes-lemma {g = g1} {g⊆θ = g1⊆θ} fun s∈g1);
           unambiguity = unamb
         }
    
    θi⊨g1-untab : {h : Hyperedge} → h ∈ g1 → θi ⊨[ h ]
    θi⊨g1-untab {h} h∈g1 = yes _ _
      (begin
        just (θi ⟦ source h ⟧⟨ (edge-nodes-⊆ h∈g1 (here ≡-refl)) ⟩)
      ≡⟨ ≡-refl ⟩
        just (i ⟦ at' θ _ ⟧⟨ _ ⟩)
      ≈⟨ just (unambiguity i) ⟩
        just (i ⟦ at' θ _ ⟧⟨ _ ⟩)
      ≈⟨ get-intedge (lookup i⊨reng1 (rename-edges-lemma {g⊆θ = g1⊆θ} h∈g1)) ⟩
        ⟦ label h ⟧L (intlist i (list-at' θ (dests h) ((g1⊆θ ∘ edge-nodes-⊆ h∈g1) ∘ there)) _)
      ≈⟨ respect (intlist-unamb i _ _) ⟩
        ⟦ label h ⟧L (intlist i (list-at' θ (dests h) ((g1⊆θ ∘ edge-nodes-⊆ h∈g1) ∘ there)) _)
      ≡⟨ ≡-cong (λ x → ⟦ label h ⟧L (intlist i x _)) (list-at'-functional fun _ _) ⟩
        ⟦ label h ⟧L (intlist i (list-at' θ (dests h) _) (get-dstok (lookup i⊨reng1 (rename-edges-lemma {g⊆θ = g1⊆θ} h∈g1))))
      ≡⟨ ≡-refl ⟩
        ⟦ label h ⟧L (map-with-∈ (list-at' θ (dests h) _) (λ {x} x∈lst → i ⟦ _ ⟧⟨ _ ⟩))
      ≡⟨ ≡-cong (λ x → ⟦ label h ⟧L x) (map-with-∈-list-at' θ (dests h) _) ⟩
        ⟦ label h ⟧L (map-with-∈ (dests h) (λ {x} x∈lst → i ⟦ _ ⟧⟨ _ ⟩))
      ≡⟨ ≡-refl ⟩
        {!!} --⟦ label h ⟧L (intlist θi (dests h) _)
      ≈⟨ {!!} ⟩
        ⟦ label h ⟧L (map-with-∈ (dests h) (λ {x} x∈lst → i ⟦ at' θ (g1⊆θ ((edge-nodes-⊆ h∈g1 ∘ there) x∈lst)) ⟧⟨ rename-nodes-lemma {g = g1} {g⊆θ = g1⊆θ} fun ((edge-nodes-⊆ h∈g1 ∘ there) x∈lst) ⟩))
      ≡⟨ ≡-refl ⟩
        ⟦ label h ⟧L (map-with-∈ (dests h) (λ {x} x∈lst → θi ⟦ x ⟧⟨ ((edge-nodes-⊆ h∈g1 ∘ there)) x∈lst ⟩))
      ≡⟨ ≡-refl ⟩
        ⟦ label h ⟧L (intlist θi (dests h) (edge-nodes-⊆ h∈g1 ∘ there))
      ∎)
      where
        open Relation.Binary.EqReasoning (Data.Maybe.setoid domain)
        i⊨renh : i ⊨[ edge-rename h θ (g1⊆θ ∘ edge-nodes-⊆ h∈g1) ]
        i⊨renh = lookup i⊨reng1 (rename-edges-lemma {g⊆θ = g1⊆θ} h∈g1)
    --yes (edge-nodes-⊆ h∈g1 (here ≡-refl)) (edge-nodes-⊆ h∈g1 ∘ there)  

    θi⊨g1 : θi ⊨ g1
    θi⊨g1 = tabulate θi⊨g1-untab 


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
