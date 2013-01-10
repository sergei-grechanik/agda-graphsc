
open import Util

module Hypergraph (symbol : Symbol) (semantics : Semantics) where

import Hypergraph.Core
import Hypergraph.Interpretation
--import Hypergraph.Transformation
open Hypergraph.Core symbol semantics public
open Hypergraph.Interpretation symbol semantics public
--open Hypergraph.Transformation symbol semantics public