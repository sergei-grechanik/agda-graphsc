
open import Util

module Hypergraph.Interpretation (symbol : Symbol) (semantics : Semantics) where

open import ListUtil

open import Function
open import Function.Inverse hiding (_∘_)
open import Function.Equality hiding (_∘_)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Product hiding (map)
open import Data.Maybe using (Maybe; just; nothing; Eq; maybeToBool) renaming (setoid to eq-setoid)
open import Data.Bool using (T)
open import Data.Sum renaming ([_,_] to [_,_]-sum)
open import Data.List hiding (any)
open import Data.List.All hiding (map)
open import Data.List.Any using (Any; any; here; there) renaming (map to any-map)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to RelList)
open import Data.List.Any.Properties using () renaming (++↔ to ++↔-any)

open Symbol symbol using (≡-decidable) renaming (Carrier to Symb)

open import Relation.Binary.PropositionalEquality using (trans; _≡_; subst) 
  renaming (setoid to ≡-setoid; refl to ≡-refl; cong to ≡-cong; sym to ≡-sym)
open Data.List.Any.Membership-≡ 

open Semantics semantics
open Setoid domain using (_≈_; refl) renaming (Carrier to Dom; sym to ≈-sym; trans to ≈-trans) 


import Hypergraph.Core
open Hypergraph.Core symbol semantics

-- A signature is just a list of symbols.

Sig : Set
Sig = List Symb

-- An interpretation.
-- It contains a function int that takes a symbol and a 
-- witness that it belongs to the signature, and returns
-- its corresponding value (interpretation) in Dom.
--
-- It also contains a statement unambiguity that states
-- that the function int returns the same thing for each witness.

record Interpretation (sig : Sig) : Set where
  field
    int : (s : Symb) → (s ∈ sig) → Dom
    unambiguity : {s : Symb} → {w1 w2 : s ∈ sig} → int s w1 ≈ int s w2

-- i ⟦ s , s∈sig ⟧ returns the value of s.

_⟦_⟧⟨_⟩ : {sig : Sig} → Interpretation sig → (s : Symb) → s ∈ sig → Dom
_⟦_⟧⟨_⟩ i s s-ok = Interpretation.int i s s-ok

-- Same thing, but easy to use (in some contexts) because it decides s ∈ sig by itself.

_⟦_⟧ : {sig : Sig} → Interpretation sig → (s : Symb) → {_ : True (∈-decidable ≡-decidable s sig)} → Dom
_⟦_⟧ i s {t} = i ⟦ s ⟧⟨ toWitness t ⟩

-- Well, unambiguity.

unambiguity : {sig : Sig} → (i : Interpretation sig) → {s : Symb} → {w1 w2 : s ∈ sig} → i ⟦ s ⟧⟨ w1 ⟩ ≈ i ⟦ s ⟧⟨ w2 ⟩
unambiguity {sig} i {s} {w1} {w2} = Interpretation.unambiguity i {s} {w1} {w2}

-- Sometimes this version is more convenient.

unambiguity' : {sig : Sig} → (i : Interpretation sig) → 
              {s1 s2 : Symb} → {w1 : s1 ∈ sig} {w2 : s2 ∈ sig} → 
              s1 ≡ s2 → i ⟦ s1 ⟧⟨ w1 ⟩ ≈ i ⟦ s2 ⟧⟨ w2 ⟩
unambiguity' {sig} i {s} {.s} {w1} {w2} ≡-refl = 
  Interpretation.unambiguity i {s} {w1} {w2}

-- intlist returns a list of values for a list of symbols.

intlist : {sig : Sig} → Interpretation sig → (lst : List Symb) → lst ⊆ sig → List Dom
intlist i lst lst⊆sig = map-with-∈ lst (λ {x} x∈lst → i ⟦ x ⟧⟨ (lst⊆sig x∈lst) ⟩)

-- intedge returns the interpretation of a hyperedge which is true or false
-- depending on the values of symbols (generally speaking 
-- it's undecidable whether it's true or false).

intedge : {sig : Sig} → Interpretation sig → (h : Hyperedge) → source h ∈ sig → dests h ⊆ sig → Set
intedge i h srcok dstok = 
  Eq (Setoid._≈_ domain) (just (i ⟦ source h ⟧⟨ srcok ⟩)) (⟦ label h ⟧L (intlist i (dests h) dstok))


-- i ⊨[ h ] means that i agrees with the hyperedge h 
-- (i.e. the source of h is equivalent to the composition of its dests and label)

data _⊨[_] {sig : Sig} (i : Interpretation sig) (h : Hyperedge) : Set where
  yes : (srcok : source h ∈ sig) → (dstok : dests h ⊆ sig) → intedge i h srcok dstok → i ⊨[ h ]

-- Construct i ⊨[ h ], automatically deciding
-- some obvious statements.

auto-⊨[] : {sig : Sig} {i : Interpretation sig} {h : Hyperedge}
           {t-src : True (∈-decidable ≡-decidable (source h) sig)}
           {t-dst : True (⊆-decidable ≡-decidable (dests h) sig)} 
           {t-just : T (maybeToBool ((⟦ label h ⟧L (intlist i (dests h) (toWitness t-dst)))))} →
           (Setoid._≈_ domain) 
             (i ⟦ source h ⟧⟨ toWitness t-src ⟩) 
             (unjust (⟦ label h ⟧L (intlist i (dests h) (toWitness t-dst))) {t-just}) →
           i ⊨[ h ]
auto-⊨[] {i = i} {h = h} {t-src = t-src} {t-dst = t-dst} {t-just = t-just} eq  = 
  yes (toWitness t-src) (toWitness t-dst) 
      (subst (Eq (Setoid._≈_ domain) (just (i ⟦ source h ⟧⟨ toWitness t-src ⟩))) ju (just eq))
  where
    ju : just (unjust (⟦ label h ⟧L (intlist i (dests h) (toWitness t-dst))) {t-just}) ≡ 
                      (⟦ label h ⟧L (intlist i (dests h) (toWitness t-dst)))
    ju = just-unjust 

-- An interpretation is a model of a hypergraph if it agrees with all its hyperedges.
-- Written i ⊨ g.

modelled : (g : Hypergraph) → (i : Interpretation (nodes g)) → Set
modelled g i = All (_⊨[_] i) g

syntax modelled g i = i ⊨ g

----------------------------------------------------------------------------------------------------

-- i1 ≍ i2 means that they are equal on the intersection of their signatures.
-- This relation is reflexive, symmetric, but not transitive.

_≍_ : {sig sig' : Sig} → (i : Interpretation sig) → (i' : Interpretation sig') → Set
_≍_ {sig} {sig'} i i' = (n : Symb) → {n∈sig : n ∈ sig} → {n∈sig' : n ∈ sig'} → i ⟦ n ⟧⟨ n∈sig ⟩ ≈ i' ⟦ n ⟧⟨ n∈sig' ⟩

≍-refl : {sig : Sig} → Reflexive (_≍_ {sig} {sig})
≍-refl {sig} {i} n = unambiguity i

≍-sym : {sig sig' : Sig} → Sym (_≍_ {sig} {sig'}) (_≍_ {sig'} {sig})
≍-sym {sig} {sig'} f n {nok} {nok'} = ≈-sym (f n)

-- Lemma which we need to prove the next statement.

≍-intedge : {sig sig' : Sig} → {i : Interpretation sig} → {i' : Interpretation sig'} → i ≍ i' →
            {h : Hyperedge} → {srcok : source h ∈ sig} → {dsok : dests h ⊆ sig} → 
            {srcok' : source h ∈ sig'} → {dsok' : dests h ⊆ sig'} → 
            intedge i h srcok dsok → intedge i' h srcok' dsok'
≍-intedge {sig} {sig'} {i} {i'} i≍i' {src ▷ l ▷ ds} {srcok} {dsok} {srcok'} {dsok'} agrees =
  eq-trans (eq-trans (eq-sym intseq) agrees) edgeseq
  where
    open Setoid (eq-setoid domain) using () renaming (sym to eq-sym; trans to eq-trans)

    intseq : Eq _≈_ (just (i ⟦ src ⟧⟨ srcok ⟩)) (just (i' ⟦ src ⟧⟨ srcok' ⟩))
    intseq = just (i≍i' src)

    listeq : {ds : List Symb} → {dsok : ds ⊆ sig} → {dsok' : ds ⊆ sig'} → 
             RelList _≈_ (intlist i ds dsok) (intlist i' ds dsok')
    listeq {[]} = []
    listeq {x ∷ xs} = (i≍i' x) ∷ listeq
    
    edgeseq : Eq _≈_ (⟦ l ⟧L intlist i ds dsok) (⟦ l ⟧L intlist i' ds dsok')
    edgeseq = respect listeq


-- "Equivalent" interpretations agree on hyperedges made of their common symbols.

≍-⊨ : {sig sig' : Sig} → {i : Interpretation sig} → {i' : Interpretation sig'} → i ≍ i' → 
      {h : Hyperedge} → (edge-nodes h ⊆ sig') → i ⊨[ h ] → i' ⊨[ h ]
≍-⊨ {sig} {sig'} {i} {i'} i≍i' {src ▷ l ▷ ds} h⊆sig' (yes srcok dstok y) = 
  yes (h⊆sig' (here ≡-refl)) (λ d∈ds → h⊆sig' (there d∈ds)) 
      (≍-intedge {i = i} {i' = i'} i≍i' {src ▷ l ▷ ds} y)

-- Get a witness of equality from the fact that h agrees with i. 
-- Since witnesses of source and dests being in the signature 
-- may be different, we should perform some transformations.
-- We define this function here because we need the lemma above. 
--
-- Usage: drop-just (to-eq (...))

to-eq : {sig : Sig} → {i : Interpretation sig} → {h : Hyperedge} →
        {t-src : True (∈-decidable ≡-decidable (source h) sig)} →
        {t-dst : True (⊆-decidable ≡-decidable (dests h) sig)} →
        (i⊨h : i ⊨[ h ]) → 
        Eq (Setoid._≈_ domain) 
          (just (i ⟦ source h ⟧⟨ toWitness t-src ⟩))
          (⟦ label h ⟧L (intlist i (dests h) (toWitness t-dst)))
to-eq {sig = sig} {i = i} {h = h} {t-src = t-src} {t-dst = t-dst} (yes srcok dsok p) = 
  ≍-intedge {i = i} {i' = i} (≍-refl {sig} {i}) {h = h} {srcok = srcok} {dsok = dsok} p

-- We can restrict an interpretation to a subsignature.

restrict : {sig sig' : Sig} → sig' ⊆ sig → Interpretation sig → Interpretation sig'
restrict sub i =
  record {
    int = λ s sok → i ⟦ s ⟧⟨ sub sok ⟩;
    unambiguity = unambiguity i
  }

-- The restricted interpretation is "equivalent" to the original one.

restrict-≍ : {sig sig' : Sig} → {sub : sig' ⊆ sig} → (i : Interpretation sig) → i ≍ (restrict sub i)
restrict-≍ i n = unambiguity i

----------------------------------------------------------------------------------------------------

-- g1 ⇛ g2 means that g2 is a consequence of g1, that is
-- for every interpretation of g1 there is an "equivalent" (≍)
-- interpretation of g2.

_⇛_ : Hypergraph → Hypergraph → Set
_⇛_ g1 g2 = (i : Interpretation (nodes g1)) → i ⊨ g1 → Σ (Interpretation (nodes g2)) (λ i' → i ≍ i' × (i' ⊨ g2))

-- g1 ⇄ g2 means that these graphs are equal on their common nodes 
-- and there are no nodes removed in g2.
-- It is what we want from transformations: we preserve equivalence
-- and don't throw away any nodes.

_⇄_ : Hypergraph → Hypergraph → Set
_⇄_ g1 g2 = (g1 ⇛ g2) × (g2 ⇛ g1) × nodes g1 ⊆ nodes g2

-- ⇄ is transitive.
-- Note that ⇛ is not transitive

⇄-trans : Transitive _⇄_
⇄-trans {i = g1} {j = g2} {k = g3} (g1⇛g2 , g2⇛g1 , g1⊆g2) (g2⇛g3 , g3⇛g2 , g2⊆g3) = 
  g1⇛g3 , g3⇛g1 , g2⊆g3 ∘ g1⊆g2
  where
    g1⇛g3 : g1 ⇛ g3
    g1⇛g3 i i⊨g1 with g1⇛g2 i i⊨g1
    ... | (i' , i≍i' , i'⊨g2) with g2⇛g3 i' i'⊨g2
    ... | (i'' , i'≍i'' , i''⊨g3) = (i'' , i≍i'' , i''⊨g3)
      where
        i≍i'' : i ≍ i''
        i≍i'' n {n∈g1} {n∈g3} = ≈-trans (i≍i' n {n∈g1} {g1⊆g2 n∈g1}) (i'≍i'' n)
    g3⇛g1 : g3 ⇛ g1
    g3⇛g1 i i⊨g3 with g3⇛g2 i i⊨g3
    ... | (i' , i≍i' , i'⊨g2) with g2⇛g1 i' i'⊨g2
    ... | (i'' , i'≍i'' , i''⊨g1) = (i'' , i≍i'' , i''⊨g1)
      where
        i≍i'' : i ≍ i''
        i≍i'' n {n∈g3} {n∈g1} = ≈-trans (i≍i' n {n∈g3} {g1⊆g2 n∈g1}) (i'≍i'' n)

----------------------------------------------------------------------------------------------------

-- If a we add hyperedges to a graph then we get a
-- graph-consequence.

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

-- If we shuffle hyperedges in a graph then we get
-- an equivalent graph.

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

-- Almost the same thing.

subsuper→⇄ : {g1 g2 : Hypergraph} →
             (g1 ⊆ g2) → (g2 ⊆ g1) → g1 ⇄ g2
subsuper→⇄ g1⊆g2 g2⊆g1 =
  (superset→⇛ g2⊆g1) , (superset→⇛ g1⊆g2) , nodes-⊆ g1⊆g2

----------------------------------------------------------------------------------------------------
-- Some important lemmas and theorems about subgraph.


-- We can split an interpretation into two.

split-int : {g1 g2 : Hypergraph} → {i : Interpretation (nodes (g1 ++ g2))} →
            i ⊨ (g1 ++ g2) → ∃ λ i1 → ∃ λ i2 → i ≍ i1 × i ≍ i2 × (i1 ⊨ g1) × (i2 ⊨ g2)
split-int {g1} {g2} {i} i⊨g1++g2 
  with superset→⇛ (⊆-++ {g1} {g2}) i i⊨g1++g2
... | (i1 , i≍i1 , i1⊨g1)
  with superset→⇛ (⊆-++₂ {g1} {g2}) i i⊨g1++g2
... | (i2 , i≍i2 , i2⊨g2) = 
  i1 , i2 , i≍i1 , i≍i2 , i1⊨g1 , i2⊨g2


-- If we have two interpretations for two graphs
-- and they are ≍ then we can glue them together.

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
        f = [ _⟦_⟧⟨_⟩ i1 s , _⟦_⟧⟨_⟩ i2 s ]-sum

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


-- The main theorem.
-- If we replace a subgraph of a graph with a subraph-consequence
-- then we get a graph that is a consequence of the original graph.
-- There is an important precondition: 
-- {s : Symb} → s ∈ nodes g2 → s ∈ nodes g → s ∈ nodes g1
-- i.e.  g2 ∩ g ⊆ g1
-- It means that the subgraph-consequence (g2) can contain either
-- symbols from old subgraph (g1) or fresh symbols (that aren't from 
-- the unchanged part of the graph), so there is no name collision.
--
-- The proof is quite straightforward: split the interpretation,
-- transform the left part, then join it back.
-- The only problem is the lack of transitivity of ≍. That's why
-- we need the nocol precondition.

⇛-++ : {g1 g2 g : Hypergraph} → 
       ({s : Symb} → s ∈ nodes g2 → s ∈ nodes g → s ∈ nodes g1) →
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


-- Corollary.
-- We can replace a subgraph with an equivalent subgraph if
-- there are no name collisions.

⇄-++ : {g1 g2 g : Hypergraph} → 
       ({s : Symb} → s ∈ nodes g2 → s ∈ nodes g → s ∈ nodes g1) →
       g1 ⇄ g2 → (g1 ++ g) ⇄ (g2 ++ g)
⇄-++ {g1} {g2} {g} nocol (g1⇛g2 , g2⇛g1 , g1⊆g2) = 
  ⇛-++ {g1} {g2} {g} nocol g1⇛g2 , 
  ⇛-++ {g2} {g1} {g} (λ s∈g1 s∈g → g1⊆g2 s∈g1) g2⇛g1 , 
  sub
  where
    sub : nodes (g1 ++ g) ⊆ nodes (g2 ++ g)
    sub x' with Inverse.from (++↔-any {xs = nodes g1} {ys = nodes g}) ⟨$⟩ ∈-nodes-++ {g1} {g} x'
    ... | (inj₁ s∈g1) = 
      ∈-nodes-++-inv {g2} {g} 
        (Inverse.to (++↔-any {xs = nodes g2} {ys = nodes g}) ⟨$⟩ inj₁ (g1⊆g2 s∈g1))
    ... | (inj₂ s∈g) = 
      ∈-nodes-++-inv {g2} {g}
        (Inverse.to (++↔-any {xs = nodes g2} {ys = nodes g}) ⟨$⟩ inj₂ s∈g)


-- If we have a transformation that creates a graph-consequence
-- then we can make from it another transformation that
-- just appends a new graph to the original. This new
-- transformation will preserve equivalence.
-- In short, (A → B) → (A ↔ A × B)

⇛-++-⇄ : {g1 g2 : Hypergraph} →
         g1 ⇛ g2 → g1 ⇄ (g2 ++ g1)
⇛-++-⇄ {g1} {g2} g1⇛g2 = 
  ⇄-trans {g1} {g1 ++ g1} {g2 ++ g1} g1⇄g1g1 g1g1⇄g2g1
  where
    g1⇄g1g1 : g1 ⇄ (g1 ++ g1)
    g1⇄g1g1 = subsuper→⇄ ⊆-++ (λ h∈g1g1 → [ (λ x → x) , (λ x → x) ]′ (Inverse.from (++↔-any {xs = g1} {ys = g1}) ⟨$⟩ h∈g1g1))

    g1g1⇄g2g1 : (g1 ++ g1) ⇄ (g2 ++ g1)
    g1g1⇄g2g1 = 
      (⇛-++ {g1} {g2} {g1} (λ ∈g2 ∈g1 → ∈g1) g1⇛g2) , 
      superset→⇛ g1g1⊆g2g1 ,
      nodes-⊆ g1g1⊆g2g1
      where
        g1g1⊆g2g1 : (g1 ++ g1) ⊆ (g2 ++ g1)
        g1g1⊆g2g1 ∈g1g1 = 
          ⊆-++₂ {g2} {g1} 
            ([ (λ x → x) , (λ x → x) ]′ (Inverse.from (++↔-any {xs = g1} {ys = g1}) ⟨$⟩ ∈g1g1))

-- Same thing for ⇄.

⇄-++-⇄ : {g1 g2 : Hypergraph} →
         g1 ⇄ g2 → g1 ⇄ (g2 ++ g1)
⇄-++-⇄ {g1} {g2} (g1⇛g2 , _ , _) = ⇛-++-⇄ {g1} {g2} g1⇛g2
