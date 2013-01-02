
open import Util

module Hypergraph (symbol : Symbol) (semantics : Semantics) where

import Hypergraph.Core
import Hypergraph.Interpretation
open Hypergraph.Core symbol semantics public
open Hypergraph.Interpretation symbol semantics public